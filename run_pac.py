import json
import networkx as nx
import random
import math
import pickle
import settings
import KL_algo
import copy
import multiprocessing
from solve_ import PAC
import time
import os
import shutil
import itertools
import auxi
class group():
    def __init__(self):
        self.nodes = []
        self.edges = []
        self.edges_virtual = []
        self.virtual2real = {}
        self.real2virtual = {}
        self.frontier = None
        self.frontier_virt = None
        self.exclusive = None
        self.exclusive_virt = None
        self.rq_xy0 = None
        pass

def run_pac_olsq(name, groupp:group, architecture, phase):
    edges = groupp.edges_virtual
    tmp = PAC(
        name = fr'{name}',
        dir = './results/smt/',
        print_detail=True
        )
    # row_per_site
    tmp.row_per_site = settings.row_per_site

    tmp.setArchitecture(architecture)
    tmp.setProgram(edges)

    if settings.commutable:
        tmp.setCommutation()
    if phase == 'active-frozen':
        tmp.active_frozen_settings(True, groupp.frontier_virt, groupp.exclusive_virt)
    elif phase == 'global':
        tmp.global_settings(True, groupp)
    tmp.hybrid_strategy()
    result = tmp.solve(save_file=True)
    return result

def map_two_group(nodes):
    virtual2real = {}
    real2virtual = {}
    for i, qubit in enumerate(nodes):
        virtual2real[i] = qubit
        real2virtual[qubit] = i
    return virtual2real, real2virtual

def get_global_xy_multi(group_list, result_list, bias_list):
    rq_xy0 = {}
    rq_cr0 = {}
    rq_a = {}
    for group_, result_, bias_ in zip(group_list, result_list, bias_list):
        layer_ = result_['layers'][-1]
        virt_qubits_ = layer_['qubits']
        for aaa in virt_qubits_:
            vq = aaa['id']
            rq = group_.virtual2real[vq]
            x = aaa['x']
            y = aaa['y']
            c = aaa['c']
            r = aaa['r']
            rq_xy0[rq] = copy.deepcopy([x+bias_, y+bias_])
            rq_cr0[rq] = copy.deepcopy([c+bias_, r+bias_])
            rq_a[rq] = copy.deepcopy(aaa['a'])
    return rq_xy0, rq_cr0, rq_a

def split_integer_according_to_ratio(grid_x, parts):
    total_parts = sum(parts)
    result = [grid_x * p // total_parts for p in parts]
    remainder = grid_x - sum(result)
    for i in range(remainder):
        result[i] += 1
    return result


if __name__ == '__main__':

    with open('./graphs.json', 'r') as f:
        graphs = json.load(f)
    grid_x = settings.grid_x
    size = settings.size
    id = settings.id

    coupling = graphs[str(size)][id]

    G = nx.Graph()
    G.add_edges_from(coupling)
    num_qubit = G.number_of_nodes()

    sample_dir = rf'final_result/rand3reg_{str(size)}_{str(id)}'
    os.makedirs(sample_dir, exist_ok=True)

    num_split = settings.num_split

    start_time = time.time()

    base_size, remainder = divmod(num_qubit, num_split)
    parts = [base_size + 1] * remainder + [base_size] * (num_split - remainder)

    spare_qubits = random.sample(range(num_qubit), num_qubit)

    final_cross_edges = copy.deepcopy(G.edges)

    group_list = []
    for num in parts:
        tar_qubits = spare_qubits[:num]
        spare_qubits = spare_qubits[num:]
        print(f'Running KL algorithm')
        tar_qubits, spare_qubits, cross_edges, groupa_frontier, groupa_exclusive, groupb_frontier, groupb_exclusive =\
            KL_algo.kernighan_lin(G, set(tar_qubits), set(spare_qubits))
        group_ = group()
        group_.nodes = copy.deepcopy(list(tar_qubits))
        group_.edges = []
        for n1, n2 in G.edges():
            if n1 in tar_qubits and n2 in tar_qubits:
                group_.edges.append((n1,n2))
        final_cross_edges = [item for item in final_cross_edges if item not in group_.edges]
        group_.frontier = list(groupa_frontier)
        group_.exclusive = list(groupa_exclusive)
        group_list.append(copy.deepcopy(group_))
        spare_qubits = list(spare_qubits)
        if not spare_qubits:
            break

    # reconstruct group according to two group of nodes
    all_nodes = list(G.nodes())
    group0 = group_list[0]
    group1 = group_list[1]
    group0nodes = group0.nodes
    group1nodes = group1.nodes
    group0edges = []
    group1edges = []
    group0active = []
    group1active = []
    edge_to_process_in_finalgroup = []
    for edge in G.edges():
        if edge[0] in group0nodes and edge[1] in group0nodes:
            group0edges.append(copy.deepcopy(edge))
        elif edge[0] in group1nodes and edge[1] in group1nodes:
            group1edges.append(copy.deepcopy(edge))
        elif edge[0] in group0nodes and edge[1] in group1nodes:
            group0active.append(copy.deepcopy(edge[0]))
            group1active.append(copy.deepcopy(edge[1]))
            edge_to_process_in_finalgroup.append(copy.deepcopy(edge))
        elif edge[0] in group1nodes and edge[1] in group0nodes:
            group1active.append(copy.deepcopy(edge[0]))
            group0active.append(copy.deepcopy(edge[1]))
            edge_to_process_in_finalgroup.append(copy.deepcopy(edge))

    group0frozen = [copy.deepcopy(kk) for kk in group0nodes if kk not in group0active]
    group1frozen = [copy.deepcopy(kk) for kk in group1nodes if kk not in group1active]
    group0 = group()
    group0.nodes = group0nodes
    group0.edges = group0edges
    group0.frontier = group0active
    group0.exclusive = group0frozen
    group1 = group()
    group1.nodes = group1nodes
    group1.edges = group1edges
    group1.frontier = group1active
    group1.exclusive = group1frozen
    group_list = [group0, group1]
    for group_ in group_list:
        for i, q in enumerate(group_.nodes):
            group_.virtual2real[i] = q
            group_.real2virtual[q] = i
        group_.edges_virtual = [(group_.real2virtual[ee[0]], group_.real2virtual[ee[1]]) for ee in group_.edges]
        group_.frontier_virt = [group_.real2virtual[pp] for pp in group_.frontier]
        group_.exclusive_virt = [group_.real2virtual[pp] for pp in group_.exclusive]

    grid_x_split = split_integer_according_to_ratio(grid_x, parts)

    # local phase
    # parallel solving
    if settings.use_multiprocessing:
        with multiprocessing.Pool(processes=len(group_list)) as pool:
            data = []
            for k in range(len(group_list)):
                data.append((f'part{k}', group_list[k], [grid_x_split[k]] * 4, 'active-frozen'))
            result_list = pool.starmap(run_pac_olsq, data)

    intermediate_time = time.time()

    # extract all qubit positions and construct offset
    bias_list = list(itertools.accumulate([0] + grid_x_split[:-1]))
    # find all qubits' positions
    rq_xy0, rq_cr0, rq_a = get_global_xy_multi(group_list, result_list, bias_list)

    group_final = group()
    group0 = group_list[0]
    group1 = group_list[1]
    group_final.nodes = copy.deepcopy(group0.frontier + group1.frontier)
    group_final.edges = edge_to_process_in_finalgroup
    # virtual2real, real2virtual
    group_final.virtual2real, group_final.real2virtual = copy.deepcopy(map_two_group(group_final.nodes))
    # frozen qubits
    frozen_qubits_in_group01 = copy.deepcopy(group0.exclusive + group1.exclusive)
    group_final.frozen_qubits_in_group01 = frozen_qubits_in_group01

    # rq_xy0
    group_final.rq_xy0 = copy.deepcopy(rq_xy0)
    group_final.rq_cr0 = copy.deepcopy(rq_cr0)
    group_final.rq_a = copy.deepcopy(rq_a)
    # global phase
    for ee in group_final.edges:
        group_final.edges_virtual.append((group_final.real2virtual[ee[0]], group_final.real2virtual[ee[1]]))
    result_final = run_pac_olsq('part_final', group_final,
                                [grid_x, grid_x, grid_x, grid_x], 'global')
    with open(f'{sample_dir}/group_final.pkl', 'wb') as file:
        pickle.dump(group_final, file)

    end_time = time.time()
    activefrozen_time = intermediate_time - start_time
    global_time = end_time - intermediate_time
    time_consumption = end_time - start_time

    current_time = auxi.print_current_time()
    print(f'Solve end at {current_time}, saving results..')

    # save
    for item in os.listdir(f'results/smt'):
        src_item = os.path.join(f'results/smt', item)
        shutil.move(src_item, sample_dir)
    for i,group_ in enumerate(group_list):
        with open(f'{sample_dir}/group_{i}.pkl', 'wb') as file:
            pickle.dump(group_, file)

    with open(fr'{sample_dir}/total_result.txt', 'w') as file:
        file.write(f"# Settings\n")
        file.write(f'Node_edge_factor = {settings.node_edge_factor}\n')
        file.write(f'Grid_x = {grid_x}\n')
        file.write(f'Row_per_site = {settings.row_per_site}\n')
        file.write(f'Use_multiprocessing = {settings.use_multiprocessing}\n\n')

        file.write(f"# Results\n")
        file.write(f"Time Consumption: {time_consumption}\n")

        file.write(f"# Info\n")
        file.write(f'Processed in final stage: {len(group_final.edges)}/{len(G.edges)}\n')
        file.write(f'Processed in final stage ratio: {round(len(group_final.edges)/len(G.edges),3)}\n')

