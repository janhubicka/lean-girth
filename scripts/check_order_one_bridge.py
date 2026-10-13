#!/usr/bin/env python3
"""Finite regression for the exact order-one incidence fragment.

Enumerates all two-vertex, three-edge, two-designated-label data with
nonempty physical edges and copy carriers equal to their edge unions.
No hypergraph linearity is imposed: the incidence lemma needs none.
The disjoint sum of designated and raw-edge labels is retained.
This script is a finite check, NOT a Lean certificate.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path


def partitions(n: int):
    if n == 0:
        yield ()
        return
    def rec(prefix):
        if len(prefix) == n:
            yield tuple(prefix)
        else:
            for p in range(max(prefix) + 2):
                yield from rec(prefix + [p])
    yield from rec([0])


def analyse(edge_carriers, copy_edges, parents):
    """Return two separately computed formulations and obligation counts."""
    edge_carriers = tuple(map(frozenset, edge_carriers))
    copy_edges = tuple(map(frozenset, copy_edges))
    ni = len(copy_edges)
    labels = tuple(('copy', i) for i in range(ni)) + tuple(
        ('edge', e) for e in range(len(edge_carriers)))
    edges = {a: copy_edges[a[1]] if a[0] == 'copy' else frozenset([a[1]])
             for a in labels}
    carriers = {a: frozenset().union(*(edge_carriers[e] for e in edges[a]))
                for a in labels}
    meets = {a: {parents[e] for e in edges[a]} for a in labels}
    def bridge(a, x, p):
        return any(parents[e] == p and x in edge_carriers[e] for e in edges[a])
    bound = True
    pair_bound = True
    cycle_count = pair_count = 0
    designated_only_bound = True
    for a, b in itertools.combinations(labels, 2):
        for x in carriers[a] & carriers[b]:
            for p in meets[a] & meets[b]:
                pair_count += 1
                ba, bb = bridge(a, x, p), bridge(b, x, p)
                pair_bound &= ba and bb
                if a[0] == 'copy' or b[0] == 'copy':
                    cycle_count += 1
                    bound &= (a[0] == 'copy' and ba) or (b[0] == 'copy' and bb)
                if a[0] == b[0] == 'copy':
                    designated_only_bound &= ba or bb
    probe_count = 0
    if bound:
        for a in labels:
            for x in carriers[a]:
                for p in meets[a]:
                    for e in range(len(edge_carriers)):
                        if parents[e] == p and x in edge_carriers[e]:
                            probe_count += 1
                            assert bridge(a, x, p), ('edge probe failed', a, x, p, e)
    return {
        'bound': bool(bound), 'both_bridges': bool(pair_bound),
        'designated_only_bound': bool(designated_only_bound),
        'cycles': cycle_count, 'pairs': pair_count, 'probes': probe_count,
    }


def run():
    result = {'models': 0, 'models_with_bound': 0, 'cycle_obligations': 0,
              'pair_obligations': 0, 'edge_probe_instances': 0,
              'equal_carrier_models': 0, 'partition_count': 0,
              'negative_controls': {}}
    edge_options = [{0}, {1}, {0, 1}]
    subsets = [set(e for e in range(3) if mask & (1 << e)) for mask in range(8)]
    ps = list(partitions(3))
    result['partition_count'] = len(ps)
    for ecs in itertools.product(edge_options, repeat=3):
        for ces in itertools.product(subsets, repeat=2):
            for parent in ps:
                a = analyse(ecs, ces, parent)
                assert a['bound'] == a['both_bridges'], (ecs, ces, parent, a)
                result['models'] += 1
                result['models_with_bound'] += a['bound']
                result['cycle_obligations'] += a['cycles']
                result['pair_obligations'] += a['pairs']
                result['edge_probe_instances'] += a['probes']
                carriers = [set().union(*(ecs[e] for e in es)) for es in ces]
                if any(c == e for c in carriers for e in ecs):
                    result['equal_carrier_models'] += 1

    # One source alone need not have a bridge into every wagon it meets.
    ecs = [{0, 1}, {2, 3}]
    a = analyse(ecs, [{0, 1}], [0, 1])
    assert a['bound']
    assert 0 in set().union(*ecs) and 0 not in ecs[1]
    result['negative_controls']['single_source_inference_rejected'] = True

    # The designated-only condition misses the edge probe A x g^+ W.
    a = analyse([{0, 1}, {2, 3}, {0, 4}], [{0, 1}, {2}], [0, 1, 1])
    assert a['designated_only_bound'] and not a['bound']
    result['negative_controls']['designated_only_cycle_bound_rejected'] = True

    # Identical carriers and edge sets do not merge the two label sorts.
    a = analyse([{0, 1}], [{0}], [0])
    assert a['bound'] and a['cycles'] == 2 and a['probes'] == 4
    result['negative_controls']['one_edge_copy_and_raw_edge_kept_distinct'] = True
    result['status'] = 'passed: finite regression only; not a Lean certificate'
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    out = json.dumps(run(), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(out)
    print(out, end='')
