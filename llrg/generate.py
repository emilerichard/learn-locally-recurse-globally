"""A small random-circuit generator for building your own test sets.

This is a toy written for this release. It is NOT the generator used to build the paper's
training and test corpora; its distribution over circuits is different. Use it to make test
sets along whatever axes you like (depth, size, inputs, outputs) and to try your own models.

Sizes follow the paper's convention (llrg.circuit): every gate (AND or OR with 2-4 operands,
XOR with 2, NOT) counts as one, identical sub-circuits are counted once, and the depth of a
circuit is the largest depth over its outputs. The generator draws circuits without repeated
sub-circuits, so the requested number of gates is exact in this convention.

    >>> from llrg import generate as G
    >>> outs = G.random_circuit(n=4, m=2, depth=4, gates=12, seed=0)
    >>> G.size(outs), G.circuit_depth(outs)
    (12, 4)
"""
import numpy as np

from . import circuit as C

# operator -> allowed numbers of operands
_ARITY = {'AND': (2, 3, 4), 'OR': (2, 3, 4), 'XOR': (2,), 'NOT': (1,)}


def node_size(node):
    """Number of gate nodes in an expression tree, repeated sub-trees included."""
    kind = node[0]
    if kind in ('VAR', 'CONST'):
        return 0
    if kind == 'NOT':
        return 1 + node_size(node[1])
    return 1 + sum(node_size(c) for c in node[1])


def size(outputs):
    """Number of gates of a circuit in the paper's convention (same as circuit.circuit_gates)."""
    return C.circuit_gates(outputs)


def circuit_depth(outputs):
    """Depth of a circuit: the largest depth over its outputs (same as circuit.circuit_depth)."""
    return C.circuit_depth(outputs)


def _max_gates(d):
    """Largest tree of depth d (every gate a 4-input AND/OR): 1 + 4 + ... + 4^(d-1)."""
    return (4 ** d - 1) // 3


def _tree(n, d, g, rng, seen, tries=50):
    """Random tree with depth exactly d and exactly g gates, none of whose gates repeats a
    sub-circuit already in `seen`; None if none is found. Adds the new gates to `seen`."""
    for _ in range(tries):
        added = []
        t = _tree_once(n, d, g, rng, seen, added)
        if t is not None:
            return t
        for k in added:                     # undo a failed draw
            seen.discard(k)
    return None


def _tree_once(n, d, g, rng, seen, added):
    """One random draw of a tree with depth d and g gates; None if the draw fails."""
    if d == 0:
        return ('VAR', int(rng.integers(n))) if g == 0 else None
    if not d <= g <= _max_gates(d):
        return None
    ops = ['AND', 'OR', 'XOR', 'NOT']
    op = ops[int(rng.integers(len(ops)))]
    k = int(rng.choice(_ARITY[op]))
    # child 0 carries the depth; the others have depth 0..d-1
    depths = [d - 1] + [int(rng.integers(d)) for _ in range(k - 1)]
    rng.shuffle(depths)
    need = [di for di in depths]                       # minimum gates of each child
    room = [_max_gates(di) - di for di in depths]      # how many more each child can take
    extra = g - 1 - sum(need)
    if extra < 0 or extra > sum(room):
        return None
    # spread the extra gates over the children that have room
    alloc = list(need)
    for _ in range(extra):
        open_ = [i for i in range(k) if alloc[i] - need[i] < room[i]]
        i = open_[int(rng.integers(len(open_)))]
        alloc[i] += 1
    children = []
    for di, gi in zip(depths, alloc):
        child = _tree(n, di, gi, rng, seen)
        if child is None:
            return None
        if di > 0:
            added.extend(_keys(child))
        children.append(child)
    # avoid trivial gates: NOT of NOT, and repeated leaves under one gate when avoidable
    if op == 'NOT':
        if children[0][0] == 'NOT':
            return None
        node = ('NOT', children[0])
    else:
        leaves = [c for c in children if c[0] == 'VAR']
        if len({c[1] for c in leaves}) < len(leaves) and len(leaves) <= n:
            return None
        node = (op, children)
    k = C._key(node)
    if k in seen:
        return None
    seen.add(k)
    added.append(k)
    return node


def _keys(node):
    """Keys of all gates of a tree."""
    if node[0] in ('VAR', 'CONST'):
        return []
    kids = [node[1]] if node[0] == 'NOT' else node[1]
    return [C._key(node)] + [k for c in kids for k in _keys(c)]


def random_circuit(n, m=1, depth=2, gates=None, seed=None, nonconstant=True, max_tries=10000):
    """Random circuit with n inputs and m outputs.

    depth: depth of the circuit (the deepest output has exactly this depth; the others are
        drawn with the same depth too).
    gates: total number of gates, split at random across the outputs. If None, each output
        gets a random size between depth and about three times depth.
    nonconstant: reject circuits with an output that is constant (always 0 or always 1).

    Returns a list of m expression trees (see llrg.circuit). Raises ValueError if no circuit
    with these parameters is found within max_tries draws (e.g. gates < m * depth).
    """
    rng = np.random.default_rng(seed)
    if gates is not None and not m * depth <= gates <= m * _max_gates(depth):
        raise ValueError(f'with m={m} outputs of depth {depth}, gates must be in '
                         f'[{m * depth}, {m * _max_gates(depth)}]')
    X = C.input_table(n)
    for _ in range(max_tries):
        if gates is None:
            budget = [int(rng.integers(depth, 3 * depth + 1)) for _ in range(m)]
        else:
            # split the total into m parts, each at least `depth`
            cuts = np.sort(rng.integers(0, gates - m * depth + 1, size=m - 1))
            parts = np.diff(np.concatenate([[0], cuts, [gates - m * depth]]))
            budget = [depth + int(p) for p in parts]
        seen = set()
        outs = [_tree(n, depth, b, rng, seen) for b in budget]
        if any(o is None for o in outs):
            continue
        if C.circuit_gates(outs) != sum(node_size(o) for o in outs):
            continue                       # a sub-circuit repeats: redraw
        if nonconstant:
            cols = [C._eval(o, X) for o in outs]
            if any(c.all() or not c.any() for c in cols):
                continue
        return outs
    raise ValueError(f'no circuit found for n={n}, m={m}, depth={depth}, gates={gates}')


def test_set(n, m, depth, count, gates=None, seed=0):
    """`count` random circuits with their truth tables, as a list of dicts.

    Each entry has 'circuit' (string in the model's token language), 'truth_table'
    (list of rows), 'n', 'm', 'depth' and 'gates'. Truth tables are distinct.
    """
    rng = np.random.default_rng(seed)
    seen, out = set(), []
    while len(out) < count:
        outs = random_circuit(n, m, depth, gates, seed=int(rng.integers(2 ** 31)))
        Y = C.evaluate(outs, n)
        key = Y.tobytes()
        if key in seen:
            continue
        seen.add(key)
        out.append({'circuit': C.circuit_to_string(outs), 'truth_table': Y.tolist(),
                    'n': n, 'm': m, 'depth': circuit_depth(outs), 'gates': size(outs)})
    return out
