import networkx as nx
import numpy as np
import settings
import copy

def calculate(group_a, group_b, G):
    group_a_exclusive = copy.deepcopy(group_a)
    group_b_exclusive = copy.deepcopy(group_b)
    ga_frontier = []
    gb_frontier = []
    cross = []
    node_edge = {node:[0,0] for node in list(G.nodes())}
    for edge in G.edges():
        if edge[0] in group_a and edge[1] in group_b:
            # cross edge
            cross.append(copy.deepcopy(edge))
            ga_frontier.append(edge[0])
            gb_frontier.append(edge[1])
            group_a_exclusive.discard(edge[0])
            group_b_exclusive.discard(edge[1])
            node_edge[edge[0]][0] += 1
            node_edge[edge[1]][0] += 1
        elif edge[1] in group_a and edge[0] in group_b:
            # cross edge
            cross.append(copy.deepcopy(edge))
            ga_frontier.append(edge[1])
            gb_frontier.append(edge[0])
            group_a_exclusive.discard(edge[1])
            group_b_exclusive.discard(edge[0])
            node_edge[edge[0]][0] += 1
            node_edge[edge[1]][0] += 1
        elif edge[0] in group_a and edge[1] in group_a:
            # not cross_edge
            node_edge[edge[0]][1] += 1
            node_edge[edge[1]][1] += 1
        elif edge[0] in group_b and edge[1] in group_b:
            # not cross_edge
            node_edge[edge[0]][1] += 1
            node_edge[edge[1]][1] += 1
        else:
            group_a_exclusive.discard(edge[0])
            group_a_exclusive.discard(edge[0])
            group_b_exclusive.discard(edge[1])
            group_a_exclusive.discard(edge[1])
    return cross, set(ga_frontier), group_a_exclusive, set(gb_frontier), group_b_exclusive, node_edge

def kernighan_lin(G, group_a, group_b):
    cross_edges, ga_frontier, group_a_exclusive, gb_frontier, group_b_exclusive, node_edge = calculate(group_a, group_b, G)
    swap_times = 0
    while True:
        a2b = set()
        b2a = set()
        for node in ga_frontier:
            if node_edge[node][0] > node_edge[node][1]:
                a2b.add(node)
        for node in gb_frontier:
            if node_edge[node][0] > node_edge[node][1]:
                b2a.add(node)

        # print(f'KL: iteration = {ite}')
        loss = 0
        best_pair = None
        cross_best, ga_frontier_best, group_a_exclusive_best, gb_frontier_best, group_b_exclusive_best \
            = None, None, None, None, None
        large_set_num = 0
        if a2b:
            swapset_a2b = copy.deepcopy(a2b)
        else:
            swapset_a2b = copy.deepcopy(group_a)
            large_set_num += 1
        if b2a:
            swapset_b2a = copy.deepcopy(b2a)
        else:
            swapset_b2a = copy.deepcopy(group_b)
            large_set_num += 1
        if large_set_num == 2 or swap_times >= 2*len(G.edges()):
            print(f'KL: Iteration quited, swap_times = {swap_times}')
            break

        for a in swapset_a2b:
            for b in swapset_b2a:
                # try swap a and b
                new_group_a = (group_a - {a}) | {b}
                new_group_b = (group_b - {b}) | {a}
                cross_new, ga_frontier_new, group_a_exclusive_new, gb_frontier_new, group_b_exclusive_new, node_edge\
                    = calculate(new_group_a, new_group_b, G)
                # calculate parameter
                cross_d = len(cross_new) - len(cross_edges)
                ga_frontier_d = len(ga_frontier_new) - len(ga_frontier)
                gb_frontier_d = len(gb_frontier_new) - len(gb_frontier)
                k = settings.node_edge_factor
                # loss
                loss_new = k*(ga_frontier_d+gb_frontier_d) + (1-k)*cross_d
                if loss_new <= loss:
                    best_pair = copy.deepcopy((a,b))
                    cross_best, ga_frontier_best, group_a_exclusive_best, gb_frontier_best, group_b_exclusive_best \
                        = (copy.deepcopy(cross_new), copy.deepcopy(ga_frontier_new), copy.deepcopy(group_a_exclusive_new),
                           copy.deepcopy(gb_frontier_new), copy.deepcopy(group_b_exclusive_new))

        if not best_pair:
            print(f'KL: Iteration quited, swap_times = {swap_times}')
            break
        else:
            # apply best swap and update vars
            a, b = best_pair
            group_a.remove(a)
            group_b.add(a)
            group_b.remove(b)
            group_a.add(b)
            cross_edges, ga_frontier, group_a_exclusive, gb_frontier, group_b_exclusive = \
            cross_best, ga_frontier_best, group_a_exclusive_best, gb_frontier_best, group_b_exclusive_best
            swap_times += 1

    return group_a, group_b, cross_edges, ga_frontier, group_a_exclusive, gb_frontier, group_b_exclusive

