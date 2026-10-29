"""Finite incidence diagnostics for the Track B off-core owner argument.

Source pieces consist of labelled physical edges. Their output wagon
partition restricts to source wagon partitions. We test the consequences of
source wagon linearity, unique off-core ownership, and at most one output
wagon crossing any fixed pair of distinct source pieces.

The last condition is the CONSEQUENCE of the Lean witness order-two theorem;
this script does not purport to verify all system-girth hypotheses. Its
countermodels are incidence models of these three interfaces, not claimed
counterexamples to the actual relational attachment theorem.
"""

from itertools import combinations, product
import json


def partitions(size):
    if not size:
        yield ()
        return

    def extend(prefix):
        if len(prefix) == size:
            yield tuple(prefix)
        else:
            for label in range(max(prefix) + 2):
                yield from extend([*prefix, label])

    yield from extend([0])


def wagon_carriers(edges, parents):
    carriers = {}
    for edge, parent in zip(edges, parents, strict=True):
        carriers.setdefault(parent, set()).update(edge)
    return {p: frozenset(vs) for p, vs in carriers.items()}


def source_linear(edges, owners, parents):
    for owner in set(owners):
        indices = [i for i, source in enumerate(owners) if source == owner]
        carriers = wagon_carriers(
            [edges[i] for i in indices], [parents[i] for i in indices])
        if any(len(a & b) > 1 for a, b in combinations(carriers.values(), 2)):
            return False
    return True


def owners_of_vertices(edges, owners):
    result = {}
    for edge, owner in zip(edges, owners, strict=True):
        for vertex in edge:
            result.setdefault(vertex, set()).add(owner)
    return result


def free_off_core_ownership(edges, owners, core):
    return all(vertex in core or len(sources) == 1
               for vertex, sources in owners_of_vertices(edges, owners).items())


def unique_crossing_wagon(owners, parents):
    touched = {}
    for owner, parent in zip(owners, parents, strict=True):
        touched.setdefault(parent, set()).add(owner)
    for left, right in combinations(set(owners), 2):
        if sum({left, right} <= sources for sources in touched.values()) > 1:
            return False
    return True


def output_overlaps(edges, parents):
    carriers = wagon_carriers(edges, parents)
    return [left & right for left, right in combinations(carriers.values(), 2)]


def exhaustive_models():
    vertices = range(4)
    candidates = [frozenset(edge) for edge in combinations(vertices, 2)]
    cores = [frozenset(v for v, take in zip(vertices, bits, strict=True) if take)
             for bits in product((False, True), repeat=4)]
    checked = nonempty = nonlinear_outputs = mixed_pairs = 0
    for size in range(5):
        for edges in combinations(candidates, size):
            for owners in product(range(2), repeat=size):
                for parents in partitions(size):
                    if not source_linear(edges, owners, parents):
                        continue
                    if not unique_crossing_wagon(owners, parents):
                        continue
                    intersections = output_overlaps(edges, parents)
                    for core in cores:
                        if not free_off_core_ownership(edges, owners, core):
                            continue
                        # This conclusion is stronger than testing one chosen
                        # representative: it examines complete wagon carriers.
                        assert all(len(common - core) <= 1 for common in intersections)
                        checked += 1
                        nonempty += bool(size)
                        nonlinear_outputs += any(len(common) > 1 for common in intersections)
                        mixed_pairs += any(common & core and common - core
                                           for common in intersections)
    assert nonempty > 0 and nonlinear_outputs > 0 and mixed_pairs > 0
    return checked, nonempty, nonlinear_outputs, mixed_pairs


def interface_countermodels():
    # Two wagons through x,y. Distinct private leaves ensure that the
    # underlying physical graph is linear throughout all these examples.
    x, y = 0, 1
    edges = tuple(map(frozenset, ((x, 2), (y, 3), (x, 4), (y, 5))))
    parents = (0, 0, 1, 1)
    assert output_overlaps(edges, parents) == [frozenset((x, y))]

    # Each off-core endpoint has one owner; each source wagon family is
    # linear. Two wagons crossing the SAME source pair are the obstruction.
    owners = (0, 1, 0, 1)
    assert free_off_core_ownership(edges, owners, frozenset())
    assert source_linear(edges, owners, parents)
    assert not unique_crossing_wagon(owners, parents)

    # With a single source, crossing control says nothing. Old wagon
    # linearity is essential in the equal-owner branch.
    owners = (0, 0, 0, 0)
    assert free_off_core_ownership(edges, owners, frozenset())
    assert unique_crossing_wagon(owners, parents)
    assert not source_linear(edges, owners, parents)

    # Losing off-core owner uniqueness cannot be repaired using only
    # source linearity and the crossing theorem.
    owners = (0, 1, 1, 1)
    assert source_linear(edges, owners, parents)
    assert unique_crossing_wagon(owners, parents)
    assert not free_off_core_ownership(edges, owners, frozenset())

    # Declare the multiply owned endpoint x to be core. All three
    # interfaces are now true, but the two output wagons still share the
    # core/off-core pair x,y. This exhibits the exact limitation of the
    # off-core argument; no full system-girth claim is made for this model.
    core = frozenset((x,))
    assert free_off_core_ownership(edges, owners, core)
    assert all(len(common - core) == 1 for common in output_overlaps(edges, parents))
    assert any(len(common) > 1 for common in output_overlaps(edges, parents))


if __name__ == "__main__":
    count, nonempty, nonlinear, mixed = exhaustive_models()
    interface_countermodels()
    print(json.dumps({
        "incidence_models_checked": count,
        "nonempty_models_checked": nonempty,
        "models_with_nonlinear_output": nonlinear,
        "models_with_mixed_core_off_core_overlap": mixed,
        "missing_crossing_control_countermodel": True,
        "missing_source_linearity_countermodel": True,
        "missing_off_core_owner_uniqueness_countermodel": True,
        "mixed_pair_not_decided_by_these_interfaces": True,
        "no_full_system_girth_counterexample_claimed": True,
        "all_passed": True,
    }, indent=2))
