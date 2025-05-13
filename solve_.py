from typing import Mapping, Sequence, Any
from z3 import Int, Bool, sat, And, Implies, Solver, Not, Or, is_true, Then
from networkx import max_weight_matching, Graph
import time
import json
import copy
import settings

PYSAT_ENCODING = 2  # default choice: sequential counter


def collisionExtract(
        list_gate_qubits: Sequence[Sequence[int]]) -> Sequence[Sequence[int]]:
    """Extract collision relations between the gates,
    If two gates g_1 and g_2 both acts on a qubit (at different time),
    we say that g_1 and g_2 collide on that qubit, which means that
    (1,2) will be in collision list.

    Args:
        list_gate_qubits (Sequence[Sequence[int]]): a list of gates in OLSQ IR

    Returns:
        Sequence[Sequence[int]]: a list of collisions between the gates
    """

    list_collision = list()
    # We sweep through all the gates.  For each gate, we sweep through all the
    # gates after it, if they both act on some qubit, append them in the list.
    for g in range(len(list_gate_qubits)):
        for gg in range(g + 1, len(list_gate_qubits)):

            if list_gate_qubits[g][0] == list_gate_qubits[gg][0]:
                list_collision.append((g, gg))

            if len(list_gate_qubits[gg]) == 2:
                if list_gate_qubits[g][0] == list_gate_qubits[gg][1]:
                    list_collision.append((g, gg))

            if len(list_gate_qubits[g]) == 2:
                if list_gate_qubits[g][1] == list_gate_qubits[gg][0]:
                    list_collision.append((g, gg))
                if len(list_gate_qubits[gg]) == 2:
                    if list_gate_qubits[g][1] == list_gate_qubits[gg][1]:
                        list_collision.append((g, gg))

    return tuple(list_collision)


def maxDegree(list_gate_qubits: Sequence[Sequence[int]],
              count_program_qubit: int) -> int:
    """calculate the max number of gates on a qubit.

    Args:
        list_gate_qubits (Sequence[Sequence[int]]):
        count_program_qubit (int):  the number of logical/program qubit

    Returns:
        int: the max number of gates on a qubit
    """

    cnt = [0 for _ in range(count_program_qubit)]
    for g in list_gate_qubits:
        cnt[g[0]] += 1
        if len(g) == 2:
            cnt[g[1]] += 1
    return max(cnt)


def dependencyExtract(list_gate_qubits: Sequence[Sequence[int]],
                      count_program_qubit: int) -> Sequence[Sequence[int]]:
    """Extract dependency relations between the gates.
    If two gates g_1 and g_2 both acts on a qubit *and there is no gate
    between g_1 and g_2 that act on this qubit*, we then say that
    g2 depends on g1, which means that (1,2) will be in dependency list.

    Args:
        list_gate_qubits (Sequence[Sequence[int]]):
        count_program_qubit (int):

    Returns:
        Sequence[Sequence[int]]: a list of dependency between the gates
    """

    list_dependency = []
    list_last_gate = [-1 for i in range(count_program_qubit)]
    # list_last_gate records the latest gate that acts on each qubit.
    # When we sweep through all the gates, this list is updated and the
    # dependencies induced by the update is noted.
    for i, qubits in enumerate(list_gate_qubits):

        if list_last_gate[qubits[0]] >= 0:
            list_dependency.append((list_last_gate[qubits[0]], i))
        list_last_gate[qubits[0]] = i

        if len(qubits) == 2:
            if list_last_gate[qubits[1]] >= 0:
                list_dependency.append((list_last_gate[qubits[1]], i))
            list_last_gate[qubits[1]] = i

    return tuple(list_dependency)


def pushLeftDepth(list_gate_qubits: Sequence[Sequence[int]],
                  count_program_qubit: int) -> int:
    """calculate the depth of circuit pushing every gate as left as possible.

    Args:
        list_gate_qubits (Sequence[Sequence[int]]):
        count_program_qubit (int):

    Returns:
        int: depth of the ASAP (as left as possible) circuit
    """

    push_forward_depth = [0 for _ in range(count_program_qubit)]
    for qubits in list_gate_qubits:
        if len(qubits) == 1:
            push_forward_depth[qubits[0]] += 1
        else:
            tmp_depth = push_forward_depth[qubits[0]]
            if tmp_depth < push_forward_depth[qubits[1]]:
                tmp_depth = push_forward_depth[qubits[1]]
            push_forward_depth[qubits[1]] = tmp_depth + 1
            push_forward_depth[qubits[0]] = tmp_depth + 1
    return max(push_forward_depth)


class PAC:

    def __init__(self, name: str, dir: str = None, print_detail: bool = False):
        self.dir = dir
        self.n_t = 1
        self.n_q = 0
        self.print_detail = print_detail
        self.all_commutable = False
        self.satisfiable = False
        self.all_aod = False
        self.no_transfer = False
        self.result_json = {}
        self.result_json['name'] = name
        self.result_json['layers'] = []
        self.row_per_site = 3
        self.cardenc = "pysat"
        self.optimal_ratio = 0
        self.non_front_g_q = []
        self.non_front_g_s = []
        self.non_front_g_i = []

        self.frozen_active_flag = False
        self.frozen_virt_qubits = []
        self.active_virt_qubits = []
        self.global_flag = False

    def active_frozen_settings(self, on: bool, active_virt_qubits, frozen_virt_qubits):
        if not on:
            self.frozen_active_flag = False
            self.frozen_virt_qubits = []
            self.active_virt_qubits = []
        else:
            print(f'frozen active mode ON')
            self.frozen_active_flag = True
            self.frozen_virt_qubits = list(frozen_virt_qubits)
            self.active_virt_qubits = list(active_virt_qubits)

    def add_active_frozen_constraints(self, x, y, a, num_stage):
        for froz in self.frozen_virt_qubits:
            (self.pac).add(a[froz][num_stage - 1] == False)
    def global_settings(self, on, groupp):
        if on:
            print(f'global mode ON')
            self.global_flag = True
            self.groupp = copy.deepcopy(groupp)
            self.rq_xy0 = copy.deepcopy(groupp.rq_xy0)
        else:
            self.global_flag = False
            self.rq_xy0 = None

    def add_global_frozen_constraints(self, x, y, a, c, r, num_stages):

        # working on frozen positions is forbidden
        frozen_qubits_in_group01 = self.groupp.frozen_qubits_in_group01
        frozen_sites = []
        for frozq in frozen_qubits_in_group01:
            frozen_sites.append((self.groupp.rq_xy0[frozq][0], self.groupp.rq_xy0[frozq][1]))
        for q in range(self.n_q):
            for ttt in range(num_stages):
                for site in frozen_sites:
                    (self.pac).add(Not(And(x[q][ttt] == site[0], y[q][ttt] == site[1], a[q][ttt] == False)))

    def add_global_inherit_constraints(self, x, y, a, c, r, num_stages):
        rq_xy0 = self.groupp.rq_xy0
        rq_a = self.groupp.rq_a
        stage = 0
        realqubits_in_global_not_in_active_frozen = set()
        for q in range(self.n_q):
            realq = self.groupp.virtual2real[q]
            if realq in rq_xy0.keys():
                print(f'virt{q}(real{realq}) at stage{stage} (x,y) = ({rq_xy0[realq][0]}, {rq_xy0[realq][1]})')
                (self.pac).add(x[q][stage] == rq_xy0[realq][0])
                (self.pac).add(y[q][stage] == rq_xy0[realq][1])
            else:
                realqubits_in_global_not_in_active_frozen.add(q)

        rq_cr0 = self.groupp.rq_cr0
        stage = 0
        qlist = list(range(self.n_q))
        q_c_list = []
        for q in qlist:
            if q in self.groupp.virtual2real.keys():
                realq = self.groupp.virtual2real[q]
                if realq in rq_a.keys():
                    q_c_list.append((q, rq_cr0[realq][0]))
        q_c_list_sorted = sorted(q_c_list, key=lambda x: x[1])
        for qc1, qc2 in zip(q_c_list_sorted, q_c_list_sorted[1:]):
            if qc1[1] < qc2[1]:
                (self.pac).add(c[qc1[0]][stage] < c[qc2[0]][stage])
            elif qc1[1] == qc2[1]:
                (self.pac).add(c[qc1[0]][stage] == c[qc2[0]][stage])
            else:
                raise ValueError(F'Error while sort')

        q_r_list = []
        for q in qlist:
            if q in self.groupp.virtual2real.keys():
                realq = self.groupp.virtual2real[q]
                if realq in rq_a.keys():
                    q_r_list.append((q, rq_cr0[realq][1]))
        q_r_list_sorted = sorted(q_r_list, key=lambda x: x[1])
        for qr1, qr2 in zip(q_r_list_sorted, q_r_list_sorted[1:]):
            if qr1[1] < qr2[1]:
                (self.pac).add(r[qr1[0]][stage] < r[qr2[0]][stage])
            elif qr1[1] == qr2[1]:
                (self.pac).add(r[qr1[0]][stage] == r[qr2[0]][stage])
            else:
                raise ValueError(F'Error while sort')

    def setOptimalRatio(self, ratio: float):
        self.optimal_ratio = ratio

    def setArchitecture(self, bounds: Sequence[int]):
        self.n_x, self.n_y, self.n_c, self.n_r = bounds

    def setProgram(self, program: Sequence[Sequence[int]], nqubit: int = None):
        self.n_g = len(program)
        self.g_i = [i for i in range(self.n_g)]
        tmp = [(min(pair), max(pair)) for pair in program]
        self.g_q = tuple(tmp)
        self.g_s = tuple(['CRZ' for _ in range(self.n_g)])
        if not nqubit:
            for gate in program:
                self.n_q = max(gate[0], self.n_q)
                self.n_q = max(gate[1], self.n_q)
            self.n_q += 1
        else:
            self.n_q = nqubit
        self.dependencies = dependencyExtract(self.g_q, self.n_q)
        self.n_t = pushLeftDepth(self.g_q, self.n_q)
        self.collisions = collisionExtract(self.g_q)

        self.updateGateIndexMatrix()

    def updateGateIndexMatrix(self):
        self.gate_index = {}
        for i in range(self.n_q):
            for j in range(i + 1, self.n_q):
                self.gate_index[(i, j)] = []
        for i in range(self.n_g):
            self.gate_index[self.g_q[i]].append(i)

    def setCommutation(self):
        self.all_commutable = True
        self.n_t = maxDegree(self.g_q, self.n_q)
        self.dependencies = []

    def setAOD(self):
        self.all_aod = True

    def setDepth(self, depth: int):
        self.n_t = depth

    def setNoTransfer(self):
        self.no_transfer = True

    def setRowSite(self, row_per_site: int):
        self.row_per_site = row_per_site

    def addMetadata(self, metadata: Mapping[str, Any]):
        self.result_json = {}
        for k, v in metadata.items():
            self.result_json[k] = v

    def writeSettingJson(self):
        self.result_json['sat'] = self.satisfiable
        self.result_json['n_t'] = self.n_t
        self.result_json['n_q'] = self.n_q
        self.result_json['all_commutable'] = self.all_commutable
        self.result_json['all_aod'] = self.all_aod
        self.result_json['no_transfer'] = self.no_transfer
        self.result_json['n_c'] = self.n_c
        self.result_json['n_r'] = self.n_r
        self.result_json['n_x'] = self.n_x
        self.result_json['n_y'] = self.n_y
        self.result_json['row_per_site'] = self.row_per_site
        self.result_json['n_g'] = self.n_g
        self.result_json['g_q'] = self.g_q
        self.result_json['g_s'] = self.g_s

    def remove_gates(self, gate_ids: Sequence[int]):
        new_g_q = []
        new_g_s = []
        new_g_i = []
        for i in range(len(self.g_q)):
            if i not in gate_ids:
                new_g_q.append(self.g_q[i])
                new_g_s.append(self.g_s[i])
                new_g_i.append(self.g_i[i])
        new_g_q += self.non_front_g_q
        new_g_s += self.non_front_g_s
        new_g_i += self.non_front_g_i
        self.g_q = tuple(new_g_q)
        self.g_s = tuple(new_g_s)
        self.g_i = tuple(new_g_i)

        self.n_g = len(self.g_q)
        self.updateGateIndexMatrix()
        self.collisions = collisionExtract(self.g_q)
        self.dependencies = dependencyExtract(self.g_q, self.n_q)

    def constraint_all_aod(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]]
    ):
        if self.all_aod:
            for q in range(self.n_q):
                for s in range(num_stage):
                    (self.pac).add(a[q][s])

    def constraint_no_transfer(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]]
    ):
        if self.no_transfer:
            for q in range(self.n_q):
                for s in range(1, num_stage):
                    (self.pac).add(a[q][s] == a[q][0])

    def constraint_var_bounds(
            self,
            num_stage: int,
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):
        for q in range(self.n_q):
            for s in range(num_stage):
                # starting from s=1 since the values with s=0 are loaded
                (self.pac).add(x[q][s] >= 0)
                (self.pac).add(x[q][s] < self.n_x)
                (self.pac).add(y[q][s] >= 0)
                (self.pac).add(y[q][s] < self.n_y)
            for s in range(num_stage):
                # starting from s=0 since the solver finds these values
                (self.pac).add(c[q][s] >= 0)
                (self.pac).add(c[q][s] < self.n_c)
                (self.pac).add(r[q][s] >= 0)
                (self.pac).add(r[q][s] < self.n_r)

    def constraint_fixed_slm(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
    ):
        for q in range(self.n_q):
            for s in range(num_stage - 1):
                (self.pac).add(Implies(Not(a[q][s]), x[q][s] == x[q][s + 1]))
                (self.pac).add(Implies(Not(a[q][s]), y[q][s] == y[q][s + 1]))

    def constraint_aod_move_together(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):
        for q in range(self.n_q):
            for s in range(num_stage - 1):
                (self.pac).add(Implies(a[q][s], c[q][s + 1] == c[q][s]))
                (self.pac).add(Implies(a[q][s], r[q][s + 1] == r[q][s]))
        for q0 in range(self.n_q):
            for q1 in range(q0 + 1, self.n_q):
                for s in range(num_stage - 1):
                    (self.pac).add(Implies(
                        And(a[q0][s], a[q1][s], c[q0][s] == c[q1][s]),
                        x[q0][s + 1] == x[q1][s + 1]))
                    (self.pac).add(Implies(
                        And(a[q0][s], a[q1][s], r[q0][s] == r[q1][s]),
                        y[q0][s + 1] == y[q1][s + 1]))

    def constraint_aod_order_from_slm(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):
        for q in range(self.n_q):
            for qq in range(self.n_q):
                for s in range(num_stage - 1):
                    if q != qq:
                        (self.pac).add(
                            Implies(And(a[q][s], a[qq][s], c[q][s] < c[qq][s]),
                                    x[q][s + 1] <= x[qq][s + 1]))
                        (self.pac).add(
                            Implies(And(a[q][s], a[qq][s], r[q][s] < r[qq][s]),
                                    y[q][s + 1] <= y[qq][s + 1]))

    def constraint_slm_order_from_aod(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):
        # row/col constraints when atom transfer from SLM to AOD
        for q in range(self.n_q):
            for qq in range(self.n_q):
                for s in range(num_stage):
                    if q != qq:
                        (self.pac).add(
                            Implies(And(a[q][s], a[qq][s], x[q][s] < x[qq][s]),
                                    c[q][s] < c[qq][s]))
                        (self.pac).add(
                            Implies(And(a[q][s], a[qq][s], y[q][s] < y[qq][s]),
                                    r[q][s] < r[qq][s]))

    def constraint_aod_crowding(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):
        # not too many AOD columns/rows can be together, default 3
        for q in range(self.n_q):
            for qq in range(self.n_q):
                for s in range(num_stage - 1):
                    if q != qq:
                        (self.pac).add(
                            Implies(And(
                                a[q][s],
                                a[qq][s],
                                c[q][s] - c[qq][s] > self.row_per_site - 1),
                                x[q][s + 1] > x[qq][s + 1]))
                        (self.pac).add(
                            Implies(And(
                                a[q][s],
                                a[qq][s],
                                r[q][s] - r[qq][s] > self.row_per_site - 1),
                                y[q][s + 1] > y[qq][s + 1]))

    def constraint_aod_crowding_init(
            self,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):
        # not too many AOD cols/rows can be together, default 3, for init stage
        for q in range(self.n_q):
            for qq in range(self.n_q):
                if q != qq:
                    (self.pac).add(
                        Implies(And(
                            a[q][0],
                            a[qq][0],
                            c[q][0] - c[qq][0] > self.row_per_site - 1),
                            x[q][0] > x[qq][0]))
                    (self.pac).add(
                        Implies(And(
                            a[q][0],
                            a[qq][0],
                            r[q][0] - r[qq][0] > self.row_per_site - 1),
                            y[q][0] > y[qq][0]))

    def constraint_site_crowding(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):

        # bound number of atoms in each site, needed if not double counting
        for q0 in range(self.n_q):
            for q1 in range(q0 + 1, self.n_q):
                for s in range(num_stage):
                    (self.pac).add(
                        Implies(And(a[q0][s], a[q1][s]),
                                Or(c[q0][s] != c[q1][s],
                                   r[q0][s] != r[q1][s])))
                    (self.pac).add(
                        Implies(And(Not(a[q0][s]), Not(a[q1][s])),
                                Or(x[q0][s] != x[q1][s],
                                   y[q0][s] != y[q1][s])))

    def constraint_no_swap(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
    ):
        # no atom transfer if two atoms meet
        for q0 in range(self.n_q):
            for q1 in range(q0 + 1, self.n_q):
                for s in range(1, num_stage):
                    (self.pac).add(
                        Implies(
                            And(x[q0][s] == x[q1][s], y[q0][s] == y[q1][s]),
                            And(a[q0][s] == a[q0][s - 1], a[q1][s] == a[q1][s - 1])
                        ))

    def solver_init(self, num_stage: int = 2):
        # define the variables and add the constraints that do not depend on
        # the gates to execute. return the variable arrays a, c, r, x, y

        # variables
        a = [[Bool(f"a_q{q}_t{t}") for t in range(num_stage)]
             for q in range(self.n_q)]
        # for col and row, the data does not matter if atom in SLM
        c = [[Int(f"c_q{q}_t{t}") for t in range(num_stage)]
             for q in range(self.n_q)]
        r = [[Int(f"r_q{q}_t{t}") for t in range(num_stage)]
             for q in range(self.n_q)]
        x = [[Int(f"x_q{q}_t{t}") for t in range(num_stage)]
             for q in range(self.n_q)]
        y = [[Int(f"y_q{q}_t{t}") for t in range(num_stage)]
             for q in range(self.n_q)]

        (self.pac) = Solver()
        if self.cardenc == "z3atleast":
            (self.pac) = Then('simplify', 'solve-eqs',
                               'card2bv', 'bit-blast', 'aig', 'sat').solver()

        self.constraint_all_aod(num_stage, a)
        self.constraint_no_transfer(num_stage, a)
        self.constraint_var_bounds(num_stage, x, y, c, r)

        self.constraint_fixed_slm(num_stage, a, x, y)
        self.constraint_aod_move_together(num_stage, a, x, y, c, r)
        self.constraint_aod_order_from_slm(num_stage, a, x, y, c, r)
        self.constraint_slm_order_from_aod(num_stage, a, x, y, c, r)
        self.constraint_aod_crowding(num_stage, a, x, y, c, r)
        self.constraint_aod_crowding_init(a, x, y, c, r)
        self.constraint_site_crowding(num_stage, a, x, y, c, r)
        self.constraint_no_swap(num_stage, a, x, y)

        return a, c, r, x, y

    def constraint_aod_order_from_prev(
            self,
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
    ):
        if len(self.result_json['layers']) > 0:
            vars = self.result_json['layers'][-1]['qubits']
            for q in range(self.n_q):
                # load location info
                if 'x' in vars[q]:
                    (self.pac).add(x[q][0] == vars[q]['x'])
                if 'y' in vars[q]:
                    (self.pac).add(y[q][0] == vars[q]['y'])
            # virtually putting everything down to acillary SLMs
            # let solver pick some qubits to AOD, so we don't set a_q,0
            # we also don't set c_q,0 and r_q,0, but enforce ordering when
            # two qubits are both in AOD last round, i.e., don't swap
            for q0 in range(self.n_q):
                for q1 in range(q0 + 1, self.n_q):
                    if vars[q0]['a'] == 1 and vars[q1]['a'] == 1:
                        if vars[q0]['x'] == vars[q1]['x']:
                            if vars[q0]['c'] < vars[q1]['c']:
                                (self.pac).add(c[q0][0] < c[q1][0])
                            if vars[q0]['c'] > vars[q1]['c']:
                                (self.pac).add(c[q0][0] > c[q1][0])
                            if vars[q0]['c'] == vars[q1]['c']:
                                (self.pac).add(c[q0][0] == c[q1][0])
                        if vars[q0]['y'] == vars[q1]['y']:
                            if vars[q0]['r'] < vars[q1]['r']:
                                (self.pac).add(r[q0][0] < r[q1][0])
                            if vars[q0]['r'] > vars[q1]['r']:
                                (self.pac).add(r[q0][0] > r[q1][0])
                            if vars[q0]['r'] == vars[q1]['r']:
                                (self.pac).add(r[q0][0] == r[q1][0])

    def constraint_dependency_collision(
            self,
            t: Sequence[Any],
    ):
        if self.all_commutable:
            for collision in self.collisions:
                (self.pac).add(Or(t[collision[0]] != t[collision[1]],
                                  t[collision[0]] == 0, t[collision[0]] == 0))
                # stage0 is the 'trash can' for gates where we don't impose
                # connectivity, so if a gate is in stage0, we can ignore all
                # its collisions. If both gates are not in stage0, we impose.
        else:
            for dependency in self.dependencies:
                (self.pac).add(t[dependency[0]] < t[dependency[1]])

    def constraint_connectivity(
            self,
            num_gate: int,
            num_stage: int,
            t: Sequence[Any],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
    ):
        for g in range(num_gate):
            for s in range(1, num_stage):  # since stage 0 is 'trash'
                if len(self.g_q[g]) == 2:
                    q0 = self.g_q[g][0]
                    q1 = self.g_q[g][1]
                    (self.pac).add(Implies(t[g] == s, x[q0][s] == x[q1][s]))
                    (self.pac).add(Implies(t[g] == s, y[q0][s] == y[q1][s]))

    def constraint_interaction_exactness(
            self,
            num_stage: int,
            t: Sequence[Any],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
    ):
        # global CZ switch (only works for graph state circuit)
        for q0 in range(self.n_q):
            for q1 in range(q0 + 1, self.n_q):
                for s in range(1, num_stage):
                    if not self.gate_index[(q0, q1)]:
                        (self.pac).add(
                            Or(x[q0][s] != x[q1][s], y[q0][s] != y[q1][s]))
                    else:
                        (self.pac).add(Implies
                                        (And(x[q0][s] == x[q1][s],
                                             y[q0][s] == y[q1][s]
                                             ),
                                         Or([t[g] == s for g in self.gate_index[(q0, q1)]]))
                                       )

    def constraint_gate_batch(
            self,
            num_stage: int,
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
    ):
        num_gate = len(self.g_q)
        t = [Int(f"t_g{g}") for g in range(num_gate)]
        self.constraint_aod_order_from_prev(x, y, c, r)

        #
        for g in range(num_gate):
            (self.pac).add(t[g] < num_stage)
            (self.pac).add(t[g] >= 0)

        self.constraint_dependency_collision(t)
        self.constraint_connectivity(num_gate, num_stage, t, x, y)
        self.constraint_interaction_exactness(num_stage, t, x, y)

        return t

    def constraint_gate_card_pysat(
            self,
            num_gate: int,
            num_stage: int,
            bound_gate: int,
            t: Sequence[Any],
    ):
        from pysat.card import CardEnc
        offset = num_gate - 1
        numvar = (num_stage - 1) * num_gate + 1

        ancillary = {}
        # get the CNF encoding the cardinality constraint
        cnf = CardEnc.atleast(
            lits=range(1, numvar),
            top_id=numvar - 1,
            bound=bound_gate,
            encoding=PYSAT_ENCODING)
        for conj in cnf:
            or_list = []
            for i in conj:
                val = abs(i)
                idx = val + offset
                if i in range(1, numvar):
                    or_list.append(t[idx % num_gate] == (idx // num_gate))
                elif i in range(-numvar + 1, 0):
                    or_list.append(
                        Not(t[idx % num_gate] == (idx // num_gate)))
                else:
                    if val not in ancillary.keys():
                        ancillary[val] = Bool("anx_{}".format(val))
                    if i < 0:
                        or_list.append(Not(ancillary[val]))
                    else:
                        or_list.append(ancillary[val])
            (self.pac).add(Or(*or_list))

    def constraint_gate_card(
            self,
            bound_gate: int,
            num_stage: int,
            t: Sequence[Any],
    ):
        # add the cardinality constraints on the number of gates

        method = self.cardenc
        num_gate = len(self.g_q)
        if method == "summation":
            raise ValueError()
        elif method == "z3atleast":
            raise ValueError()
        elif method == "pysat":
            self.constraint_gate_card_pysat(num_gate, num_stage, bound_gate, t)
        else:
            raise ValueError("cardinality method unknown")

    def read_partial_solution(
            self,
            s: int,
            model: Any,
            a: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
    ):
        real_s = len(self.result_json['layers'])
        if real_s == 0 and s == 0:
            real_s = -1
        if self.print_detail:
            print(f"        stage {real_s}:")
        layer = {}
        layer['qubits'] = []
        for q in range(self.n_q):
            layer['qubits'].append({
                'id': q,
                'a': 1 if is_true(model[a[q][s]]) else 0,
                'x': model[x[q][s]].as_long(),
                'y': model[y[q][s]].as_long(),
                'c': model[c[q][s]].as_long(),
                'r': model[r[q][s]].as_long()})
            if is_true(model[a[q][s]]):
                if self.print_detail:
                    print(
                        f"        q_{q} is at ({model[x[q][s]].as_long()}, "
                        f"{model[y[q][s]].as_long()})"
                        f" AOD c_{model[c[q][s]].as_long()},"
                        f" r_{model[r[q][s]].as_long()}"
                    )
            else:
                if self.print_detail:
                    print(
                        f"        q_{q} is at ({model[x[q][s]].as_long()}, "
                        f"{model[y[q][s]].as_long()}) SLM"
                        f" c_{model[c[q][s]].as_long()},"
                        f" r_{model[r[q][s]].as_long()}"
                    )
        return layer

    def process_partial_solution(
            self,
            num_stage: int,
            a: Sequence[Sequence[Any]],
            c: Sequence[Sequence[Any]],
            r: Sequence[Sequence[Any]],
            x: Sequence[Sequence[Any]],
            y: Sequence[Sequence[Any]],
            t: Sequence[Any],
    ):
        model = (self.pac).model()

        for s in range(num_stage):
            layer = self.read_partial_solution(s, model, a, c, r, x, y)

            if s == 0 and self.result_json['layers']:
                for q in range(self.n_q):
                    self.result_json['layers'][-1]['qubits'][q]['a'] = \
                        1 if is_true(model[a[q][s]]) else 0
                    self.result_json['layers'][-1]['qubits'][q]['c'] = \
                        model[c[q][s]].as_long()
                    self.result_json['layers'][-1]['qubits'][q]['r'] = \
                        model[r[q][s]].as_long()

            if s > 0:
                layer['gates'] = []
                gates_done = []
                for g in range(len(self.g_q)):
                    if model[t[g]].as_long() == s:
                        if self.print_detail:
                            print(
                                f"        CZ(q_{self.g_q[g][0]},"
                                f" q_{self.g_q[g][1]})"
                            )
                        layer['gates'].append(
                            {
                                'id': self.g_i[g],
                                'q0': self.g_q[g][0],
                                'q1': self.g_q[g][1]
                            })
                        gates_done.append(g)

                self.result_json['layers'].append(layer)

        self.remove_gates(gates_done)

    def hybrid_strategy(self):
        if self.optimal_ratio == None:
            self.setOptimalRatio(1 if self.n_q < 30 else 0.05)
        if self.optimal_ratio == 1 and self.n_q < 30:
            self.setNoTransfer()

    def get_front_layer(self):
        if self.all_commutable:
            return

        new_idx = []
        self.non_front_g_q = []
        self.non_front_g_s = []
        self.non_front_g_i = []
        all_dest = [d for (_, d) in self.dependencies]
        for g in range(self.n_g):
            if g not in all_dest:
                new_idx.append(g)
            else:
                self.non_front_g_q.append(self.g_q[g])
                self.non_front_g_s.append(self.g_s[g])
                self.non_front_g_i.append(self.g_i[g])

        self.g_q = [self.g_q[g] for g in new_idx]
        self.g_s = [self.g_s[g] for g in new_idx]
        self.g_i = [self.g_i[g] for g in new_idx]

        self.n_g = len(self.g_q)
        self.updateGateIndexMatrix()
        self.collisions = collisionExtract(self.g_q)
        self.dependencies = dependencyExtract(self.g_q, self.n_q)

    def solve_greedy(self, step: int, ):
        total_g_q = len(self.g_q)
        t_curr = 1
        print(f'{len(self.g_q)}gates: {self.g_q} before solving...')
        while len(self.g_q) > 0:
            step = 1

            a, c, r, x, y = self.solver_init(step + 1)

            # global
            if self.global_flag:
                print(f'solve_greedy: Adding global FROZEN constaints...')
                self.add_global_frozen_constraints(x, y, a, c, r, step + 1)

            print(f"gate batch {t_curr}")


            (self.pac).push()  # gate related constraints

            self.get_front_layer()

            t = self.constraint_gate_batch(step + 1, c, r, x, y)

            if self.global_flag and not self.first_solve_finished:
                print(f'solve_greedy: Adding global INHERIT constaints...')
                self.add_global_inherit_constraints(x, y, a, c, r, step + 1)

            G = Graph()
            G.add_edges_from(self.g_q)
            bound_gate = len(max_weight_matching(G))

            (self.pac).push()

            if bound_gate == G.number_of_edges() and self.frozen_active_flag:
                print(f'Adding active_frozen_constraints in solve_greedy:')
                self.add_active_frozen_constraints(x, y, a, step + 1)

            self.constraint_gate_card(bound_gate, step + 1, t)

            solved_batch_gates = True if (self.pac).check() == sat else False

            if solved_batch_gates:
                self.first_solve_finished = True

            while not solved_batch_gates:
                print(f"    no solution, bound_gate={bound_gate} too large")
                (self.pac).pop()
                bound_gate -= 1
                if bound_gate <= 0:
                    if self.print_detail:
                        print(f"    no solution, step={step} too small")
                    step += 1
                    a, c, r, x, y = self.solver_init(step + 1)
                    (self.pac).push()

                    t = self.constraint_gate_batch(step + 1, c, r, x, y)
                    if self.print_detail:
                        print(self.g_q)
                    bound_gate = 1

                (self.pac).push()  # new gate bound
                self.constraint_gate_card(bound_gate, step + 1, t)

                solved_batch_gates = \
                    True if (self.pac).check() == sat else False

                if solved_batch_gates:
                    self.first_solve_finished = True

            print(f"    found solution with {bound_gate} gates in {step} step")
            self.process_partial_solution(step + 1, a, c, r, x, y, t)

            print(f'last gates：{len(self.g_q)}')
            (self.pac).pop()  # the gate bound constraints for solved batch
            t_curr += 1
            (self.pac).pop()  # the gate related constraints for solved batch

    def solve_optimal(self, step: int):
        bound_gate = len(self.g_q)

        a, c, r, x, y = self.solver_init(step + 1)
        t = self.constraint_gate_batch(step + 1, c, r, x, y)

        # global
        if self.global_flag:
            print(f'solve_optimal: Adding global FROZEN  constaints in solve_optimal...')
            self.add_global_frozen_constraints(x, y, a, c, r, step + 1)

        if self.global_flag and not self.first_solve_finished:
            print(f'solve_optimal: Adding global INHERIT constaints...')
            self.add_global_inherit_constraints(x, y, a, c, r, step + 1)

        if self.frozen_active_flag:
            print(f'Adding active_frozen_constraints in solve_optimal:')
            self.add_active_frozen_constraints(x, y, a, step + 1)


        self.constraint_gate_card(bound_gate, step + 1, t)

        solved_batch_gates = True if (self.pac).check() == sat else False
        if solved_batch_gates:
            self.first_solve_finished = True

        while not solved_batch_gates:
            if self.print_detail:
                print(f"    no solution, step={step} too small")
            step += 1
            a, c, r, x, y = self.solver_init(step + 1)  # cleaned
            t = self.constraint_gate_batch(step + 1, c, r, x, y)
            if self.print_detail:
                print(self.g_q)
            self.constraint_gate_card(bound_gate, step + 1, t)

            solved_batch_gates = \
                True if (self.pac).check() == sat else False
            if solved_batch_gates:
                self.first_solve_finished = True


        if self.print_detail:
            print(f"    found solution with {bound_gate} gates in {step} step")
        self.process_partial_solution(step + 1, a, c, r, x, y, t)

    def solve(self, save_file: bool = True):
        if self.n_q > self.n_x * self.n_y:
            print("#qubits > #sites. There may be a problem.")
        self.writeSettingJson()
        t_s = time.time()
        step = 1  # compile for 1 step, or 2 stages each time
        total_g_q = len(self.g_q)
        self.first_solve_finished = False
        status = self.solve_greedy(step)
        if len(self.g_q) > 0:
            if self.print_detail:
                print(f'final {len(self.g_q) / total_g_q * 100} percent')
            self.solve_optimal(step)

        self.result_json['timestamp'] = str(time.time())
        self.result_json['duration'] = str(time.time() - t_s)
        self.result_json['n_t'] = len(self.result_json['layers'])
        if self.print_detail:
            print(f"runtime {self.result_json['duration']}")

        if save_file:
            if not self.dir:
                self.dir = "./results/smt/"
            with open(self.dir + f"{self.result_json['name']}.json", 'w') as f:
                json.dump(self.result_json, f)

        return self.result_json
