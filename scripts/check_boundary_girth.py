"""Exhaustive finite checks of the fresh-edge/short-path criterion.

These tests supplement the mathematical proof. They do not constitute a
Lean formalization of the criterion or of the global successor-tree theorem.
"""
from collections import deque
from itertools import combinations
import json


def incidence_graph(edges):
    graph = {}
    for k, edge in enumerate(edges):
        a = ('e', k)
        graph.setdefault(a, set())
        for vertex in edge:
            b = ('v', vertex)
            graph[a].add(b)
            graph.setdefault(b, set()).add(a)
    return graph


def distance(graph, source, target, omitted=None):
    queue = deque([(source, 0)])
    seen = {source}
    while queue:
        node, d = queue.popleft()
        if node == target:
            return d
        for neighbor in graph.get(node, ()):
            if omitted is not None and frozenset((node, neighbor)) == omitted:
                continue
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append((neighbor, d + 1))
    return float('inf')


def berge_girth(edges):
    graph = incidence_graph(edges)
    shortest = float('inf')
    for node, neighbors in graph.items():
        if node[0] != 'e':
            continue
        for neighbor in neighbors:
            d = distance(graph, node, neighbor, frozenset((node, neighbor)))
            shortest = min(shortest, (d + 1) / 2)
    return shortest


def linear(edges):
    return all(len(a & b) <= 1 for a, b in combinations(edges, 2))


left, right = frozenset((0, 1, 2)), frozenset((3, 4, 5))
clear = (left, right)
path_host = (*clear, frozenset((0, 6, 7)), frozenset((6, 3, 8)))
new_edge = frozenset((0, 3, 9))
assert berge_girth(clear) == berge_girth(path_host) == float('inf')
assert berge_girth((*clear, new_edge)) == float('inf')
assert berge_girth((*path_host, new_edge)) == 3
for x, y in combinations(range(6), 2):
    assert any(x in e and y in e for e in clear) == any(x in e and y in e for e in path_host)

triples = [frozenset(e) for e in combinations(range(6), 3)]
count = old_count = 0
for n in range(5):
    for old in combinations(triples, n):
        if not linear(old):
            continue
        old_count += 1
        graph = incidence_graph(old)
        old_girth = berge_girth(old)
        for x, y in combinations(range(4), 2):
            fresh = frozenset((x, y, 6))
            new_girth = berge_girth((*old, fresh))
            old_path_length = distance(graph, ('v', x), ('v', y)) / 2
            for cutoff in (2, 3, 4):
                assert (new_girth > cutoff) == (old_girth > cutoff and old_path_length > cutoff - 1)
                count += 1

print(json.dumps({
    'linear_old_supports': old_count,
    'fresh_edge_girth_criterion_tests': count,
    'cutoffs': [2, 3, 4],
    'same_pair_shadow_different_girth_extension': True,
    'all_passed': True,
}, indent=2))
