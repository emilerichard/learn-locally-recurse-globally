"""The outer loop: one-shot inference and XOR residual refinement.

XOR residual refinement (Algorithm 1 of the paper). Starting from the target table Y, the
residual R is the set of cells that are still wrong. At each step the model synthesizes a
circuit C for R; C is accepted only if it strictly decreases the number of wrong cells, and
R <- R xor C(X). If the model's circuit does not help, the residual is split by a random
mask U into R*U and R*(1-U), both halves are synthesized, and their XOR is tried instead.
Whatever remains at the end is written out exactly as a sum of products (SOP completion).
The result is the XOR of all accepted circuits (and the completion), and it is always exact.
"""
import numpy as np

from . import circuit as C


def one_shot(model, Y):
    """Single forward pass. Returns (outputs, predicted table) or (None, None) if unparsable."""
    n = int(np.log2(Y.shape[0]))
    ids = model.synthesize(Y)
    try:
        outs = C.parse(ids)
        pred = C.evaluate(outs, n)
        if pred.shape != Y.shape:
            return None, None, ids
        return outs, pred, ids
    except ValueError:
        return None, None, ids


def xor_refine(model, Y, max_steps=10, mask_budget=20, seed=0, verbose=False):
    """XOR residual refinement with mask retries and SOP completion.

    Returns a dict with the final circuit ('outputs'), the per-step history and whether the
    SOP completion was needed.
    """
    Y = np.asarray(Y, dtype=np.uint8)
    n = int(np.log2(Y.shape[0]))
    m = Y.shape[1]
    rng = np.random.default_rng(seed)
    R = Y.copy()
    terms = []          # accepted circuits, each a list of m expression trees
    history = [{'step': 0, 'residual': R.copy(), 'wrong_cells': int(R.sum()), 'how': 'start'}]

    for step in range(1, max_steps + 1):
        if R.sum() == 0:
            break
        outs, pred, _ = one_shot(model, R)
        how = 'direct'
        if pred is None or (R ^ pred).sum() >= R.sum():
            outs, pred, how = None, None, None
            for k in range(mask_budget):
                U = rng.integers(0, 2, size=R.shape).astype(np.uint8)
                o1, p1, _ = one_shot(model, R & U)
                o2, p2, _ = one_shot(model, R & (1 - U))
                if p1 is None or p2 is None:
                    continue
                if (R ^ p1 ^ p2).sum() < R.sum():
                    outs = [C.xor_of([a, b]) for a, b in zip(o1, o2)]
                    pred, how = p1 ^ p2, f'mask split (try {k + 1})'
                    break
            if outs is None:
                if verbose:
                    print(f'step {step}: no accepted correction, stopping')
                break
        terms.append(outs)
        R = R ^ pred
        history.append({'step': step, 'residual': R.copy(), 'wrong_cells': int(R.sum()), 'how': how,
                        'circuit': outs})
        if verbose:
            print(f'step {step} ({how}): {int(R.sum())} wrong cells left')

    completed = bool(R.sum())
    final = []
    for j in range(m):
        parts = [t[j] for t in terms]
        if R[:, j].any():
            parts.append(C.sop(R[:, j], n))
        final.append(C.xor_of(parts))
    assert (C.evaluate(final, n) == Y).all(), 'harness output is not exact'
    return {'outputs': final, 'history': history, 'steps': len(terms),
            'sop_completion': completed}
