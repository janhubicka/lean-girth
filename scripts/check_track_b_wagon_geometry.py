"""Finite diagnostics for the localized Track B wagon geometry.

These are finite incidence models of the local absorption argument, not
realizations of every relational/partite hypothesis of the Lean theorem.
They check the role of whole-piece strongness and exact restriction and
exercise a positive example with nonlinear output wagons elsewhere.
Kernel checking of the actual attachment theorems is a separate gate.
"""

from itertools import combinations
import json


def partitions(size):
    """Restricted-growth strings, one per partition of labelled edges."""
    if size == 0:
        yield ()
        return

    def extend(prefix):
        if len(prefix) == size:
            yield tuple(prefix)
            return
        for label in range(max(prefix) + 2):
            yield from extend([*prefix, label])

    yield from extend([0])


def wagon_carriers(edges, parents):
    result = {}
    for edge, parent in zip(edges, parents, strict=True):
        result.setdefault(parent, set()).update(edge)
    return {parent: frozenset(vertices) for parent, vertices in result.items()}


def family_linear(carriers):
    return all(len(left & right) <= 1 for left, right in combinations(carriers, 2))


def strong_piece(edges, piece):
    return all(len(edge & piece) <= 1 or edge <= piece for edge in edges)


def restriction_exact(old_parents, output_parents):
    return all(
        (old_parents[i] == old_parents[j])
        == (output_parents[i] == output_parents[j])
        for i in range(len(old_parents))
        for j in range(len(old_parents))
    )


def absorption_failures(edges, parents, piece):
    """An ambient edge meets one localized output block in two vertices."""
    local = [(edge, parent) for edge, parent in zip(edges, parents, strict=True)
             if edge <= piece]
    local_carriers = wagon_carriers(
        [edge for edge, _ in local], [parent for _, parent in local])
    return [
        (index, block, tuple(sorted(edge & vertices)))
        for index, (edge, parent) in enumerate(zip(edges, parents, strict=True))
        for block, vertices in local_carriers.items()
        if len(edge & vertices) >= 2 and parent != block
    ]


def exhaustive_local_absorption():
    # Mixed carrier sizes test the underlying set argument; uniform actual
    # support edges are a special case. Output linearity is deliberately
    # never used as a filter.
    vertices = range(4)
    candidates = [frozenset(edge) for size in (1, 2, 3)
                  for edge in combinations(vertices, size)]
    piece = frozenset((0, 1, 2))
    checked = nonlinear_outputs = 0
    for size in range(5):
        for edges in combinations(candidates, size):
            if not strong_piece(edges, piece):
                continue
            old_positions = [i for i, edge in enumerate(edges) if edge <= piece]
            old_edges = [edges[i] for i in old_positions]
            if not family_linear(old_edges):
                continue
            for parents in partitions(size):
                # Use the exact restricted relation, so reflection is true.
                old_parents = [parents[i] for i in old_positions]
                if not family_linear(wagon_carriers(old_edges, old_parents).values()):
                    continue
                assert restriction_exact(old_parents, old_parents)
                assert not absorption_failures(edges, parents, piece)
                checked += 1
                nonlinear_outputs += not family_linear(
                    wagon_carriers(edges, parents).values())
    assert checked > 0
    return checked, nonlinear_outputs


def omission_counterexamples():
    # Every constituent source edge is strong, and both the old source
    # wagon and ambient edge families are linear. The WHOLE standard is
    # not strong: the outside edge meets it at 0 and 3.
    edges = tuple(map(frozenset, ((0, 1, 2), (3, 4, 5), (0, 3, 6))))
    parents = (0, 0, 1)
    piece = frozenset(range(6))
    assert family_linear(edges)
    assert family_linear(wagon_carriers(edges[:2], parents[:2]).values())
    assert restriction_exact((0, 0), parents[:2])
    assert all(strong_piece(edges, edge) for edge in edges[:2])
    assert not strong_piece(edges, piece)
    assert absorption_failures(edges, parents, piece) == [(2, 0, (0, 3))]

    # The whole source is strong and its genuine old wagon relation is
    # linear, but the output incorrectly merges two old wagons. Forward
    # preservation alone does not suffice: reflection is needed.
    edges = tuple(map(frozenset, ((0, 1), (2, 3), (0, 2))))
    old_parents = (0, 1, 2)
    parents = (0, 0, 1)
    piece = frozenset(range(4))
    assert strong_piece(edges, piece)
    assert family_linear(edges)
    assert family_linear(wagon_carriers(edges, old_parents).values())
    assert all(old_parents[i] != old_parents[j] or parents[i] == parents[j]
               for i in range(3) for j in range(3))
    assert not restriction_exact(old_parents, parents)
    assert absorption_failures(edges, parents, piece) == [(2, 0, (0, 2))]


def positive_nonlinear_output():
    edges = tuple(map(frozenset, (
        (0, 1), (2, 3), (0, 2), (4, 5), (6, 7), (4, 6))))
    parents = (0, 0, 0, 1, 1, 2)
    piece = frozenset(range(4))
    assert strong_piece(edges, piece)
    assert family_linear(edges)
    assert family_linear(wagon_carriers(edges[:3], parents[:3]).values())
    assert restriction_exact((0, 0, 0), parents[:3])
    assert not family_linear(wagon_carriers(edges, parents).values())
    assert not absorption_failures(edges, parents, piece)
    # The pair 0,2 is carried by two different source edges and an actual
    # ambient pair edge, all with the claimed common parent.
    assert 0 in edges[0] and 2 in edges[1] and {0, 2} <= edges[2]
    assert parents[0] == parents[1] == parents[2]
    # Repeating the pair edge as both witnesses also satisfies the claim.
    assert len(edges[2] & edges[2]) == 2


if __name__ == "__main__":
    count, nonlinear = exhaustive_local_absorption()
    omission_counterexamples()
    positive_nonlinear_output()
    print(json.dumps({
        "localized_incidence_models_checked": count,
        "nonlinear_outputs_in_exhaustive_models": nonlinear,
        "whole_piece_strongness_omission_counterexample": True,
        "exact_restriction_omission_counterexample": True,
        "positive_model_with_nonlinear_output_elsewhere": True,
        "repeated_edge_witness_allowed": True,
        "actual_attachment_kernel_proof_required_separately": True,
        "all_passed": True,
    }, indent=2))
