"""Standalone circuit representation: parse, evaluate, measure and draw.

A circuit with m outputs is a list of m expression trees. Nodes are tuples:

    ('VAR', i)                 input x_i
    ('CONST', 0 or 1)          constant
    ('NOT', child)
    ('AND' | 'OR' | 'XOR', [children])   n-ary gate

Truth-table convention: for n inputs, row r of the table corresponds to the binary
expansion of r with x0 as the most significant bit (rows in lexicographic order).
"""
import itertools

import numpy as np

from .vocab import TOKENS

_OPS = {'∧': 'AND', '∨': 'OR', '⊻': 'XOR'}


# ----------------------------------------------------------------------------- parsing
def _parse_expr(toks, pos):
    node, pos = _parse_unary(toks, pos)
    if pos < len(toks) and toks[pos] in _OPS:
        op = toks[pos]
        children = [node]
        while pos < len(toks) and toks[pos] in _OPS:
            if toks[pos] != op:
                raise ValueError(f'mixed operators {op!r} and {toks[pos]!r} without parentheses')
            child, pos = _parse_unary(toks, pos + 1)
            children.append(child)
        node = (_OPS[op], children)
    return node, pos


def _parse_unary(toks, pos):
    if pos >= len(toks):
        raise ValueError('unexpected end of expression')
    t = toks[pos]
    if t == '~':
        child, pos = _parse_unary(toks, pos + 1)
        return ('NOT', child), pos
    if t == '(':
        node, pos = _parse_expr(toks, pos + 1)
        if pos >= len(toks) or toks[pos] != ')':
            raise ValueError('missing closing parenthesis')
        return node, pos + 1
    if t == 'ZERO':
        return ('CONST', 0), pos + 1
    if t == 'ONE':
        return ('CONST', 1), pos + 1
    if t.isdigit():
        return ('VAR', int(t)), pos + 1
    raise ValueError(f'unexpected token {t!r}')


def parse(circuit):
    """Parse a circuit given as a string or as a list of token ids.

    Returns a list of expression trees, one per output.
    """
    if not isinstance(circuit, str):
        circuit = ' '.join(TOKENS[int(i)] for i in circuit)
    circuit = circuit.replace('<start>', '').replace('<end>', '')
    outputs = []
    for line in circuit.split('\n'):
        toks = line.split()
        if not toks:
            raise ValueError('empty output expression')
        node, pos = _parse_expr(toks, 0)
        if pos != len(toks):
            raise ValueError(f'unparsed tokens at the end: {toks[pos:]}')
        outputs.append(node)
    return outputs


# ----------------------------------------------------------------------------- printing
_SYM = {'AND': '∧', 'OR': '∨', 'XOR': '⊻'}


def to_string(node, top=True):
    """Expression tree back to the token language (spaces between tokens)."""
    kind = node[0]
    if kind == 'VAR':
        return str(node[1])
    if kind == 'CONST':
        return 'ONE' if node[1] else 'ZERO'
    if kind == 'NOT':
        inner = to_string(node[1], top=False)
        return '~ ' + inner
    parts = [to_string(c, top=False) for c in node[1]]
    s = f' {_SYM[kind]} '.join(parts)
    return s if top else f'( {s} )'


def circuit_to_string(outputs):
    return '\n'.join(to_string(o) for o in outputs)


def pretty(node, top=True):
    """Readable infix form with x0..x4, e.g. '(x0 AND x1) XOR NOT x2'."""
    kind = node[0]
    if kind == 'VAR':
        return f'x{node[1]}'
    if kind == 'CONST':
        return str(node[1])
    if kind == 'NOT':
        return 'NOT ' + pretty(node[1], top=False)
    s = f' {kind} '.join(pretty(c, top=False) for c in node[1])
    return s if top else f'({s})'


# ----------------------------------------------------------------------------- evaluation
def input_table(n):
    """All 2^n input rows in lexicographic order (x0 is the most significant bit)."""
    return np.array(list(itertools.product([0, 1], repeat=n)), dtype=np.uint8)


def _eval(node, X):
    kind = node[0]
    if kind == 'VAR':
        return X[:, node[1]].astype(bool)
    if kind == 'CONST':
        return np.full(X.shape[0], bool(node[1]))
    if kind == 'NOT':
        return ~_eval(node[1], X)
    vals = [_eval(c, X) for c in node[1]]
    if kind == 'AND':
        return np.logical_and.reduce(vals)
    if kind == 'OR':
        return np.logical_or.reduce(vals)
    return np.logical_xor.reduce(vals)


def evaluate(outputs, n):
    """Truth table of a circuit: array of shape (2^n, m) with 0/1 entries."""
    X = input_table(n)
    for o in outputs:
        for v in _variables(o):
            if v >= n:
                raise ValueError(f'circuit uses x{v} but the table has only {n} inputs')
    return np.stack([_eval(o, X) for o in outputs], axis=1).astype(np.uint8)


def _variables(node):
    if node[0] == 'VAR':
        return {node[1]}
    if node[0] == 'CONST':
        return set()
    if node[0] == 'NOT':
        return _variables(node[1])
    return set().union(*(_variables(c) for c in node[1]))


# ----------------------------------------------------------------------------- size
def depth(node):
    """Number of gate levels; an n-ary gate or a NOT counts as one level."""
    kind = node[0]
    if kind in ('VAR', 'CONST'):
        return 0
    if kind == 'NOT':
        return 1 + depth(node[1])
    return 1 + max(depth(c) for c in node[1])


def gate_count(node):
    """Number of two-input gates plus NOT gates (an n-input gate counts as n-1)."""
    kind = node[0]
    if kind in ('VAR', 'CONST'):
        return 0
    if kind == 'NOT':
        return 1 + gate_count(node[1])
    return len(node[1]) - 1 + sum(gate_count(c) for c in node[1])


def stats(outputs):
    return {'outputs': len(outputs),
            'gates': sum(gate_count(o) for o in outputs),
            'depth': max(depth(o) for o in outputs)}


# ----------------------------------------------------------------------------- building
def xor_of(nodes):
    """XOR of several expression trees, dropping constant-0 terms."""
    terms = [t for t in nodes if t != ('CONST', 0)]
    if not terms:
        return ('CONST', 0)
    if len(terms) == 1:
        return terms[0]
    flat = []
    for t in terms:
        flat.extend(t[1] if t[0] == 'XOR' else [t])
    return ('XOR', flat)


def sop(column, n):
    """Sum-of-products (one minterm per true row) of a single truth-table column."""
    X = input_table(n)
    terms = []
    for r in np.flatnonzero(column):
        lits = [('VAR', i) if X[r, i] else ('NOT', ('VAR', i)) for i in range(n)]
        terms.append(lits[0] if n == 1 else ('AND', lits))
    if not terms:
        return ('CONST', 0)
    return terms[0] if len(terms) == 1 else ('OR', terms)


# ----------------------------------------------------------------------------- drawing
def _schem_expr(node):
    kind = node[0]
    if kind == 'VAR':
        return f'x{node[1]}'
    if kind == 'CONST':
        return 'ONE' if node[1] else 'ZERO'
    if kind == 'NOT':
        return f'(not {_schem_expr(node[1])})'
    word = {'AND': 'and', 'OR': 'or', 'XOR': 'xor'}[kind]
    return '(' + f' {word} '.join(_schem_expr(c) for c in node[1]) + ')'


def draw(outputs, names=None, scale=0.6, max_gates=60):
    """Draw each output as a standard gate-level schematic (AND/OR/XOR/NOT symbols).

    Uses schemdraw's logic parser. Returns a list of schemdraw Drawing objects, one per
    output (constant outputs and outputs larger than ``max_gates`` are skipped).
    """
    from schemdraw.parsing import logicparse
    drawings = []
    for j, o in enumerate(outputs):
        label = names[j] if names else f'y{j}'
        if o[0] == 'CONST':
            print(f'{label} = {o[1]} (constant)')
            continue
        if gate_count(o) > max_gates:
            print(f'{label}: {gate_count(o)} gates, too large to draw (max_gates={max_gates})')
            continue
        if o[0] == 'VAR':
            print(f'{label} = x{o[1]}')
            continue
        d = logicparse(_schem_expr(o), outlabel=label)
        d.config(unit=scale * 3)
        drawings.append(d)
    return drawings
