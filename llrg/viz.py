"""Small matplotlib helpers to display truth tables and errors."""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap

from .circuit import input_table


def row_labels(n):
    return [''.join(map(str, r)) for r in input_table(n)]


def show_tables(tables, titles, n, wrong=None, figsize=None):
    """Show several (2^n x m) 0/1 tables side by side.

    wrong: optional list (same length as tables) of boolean masks; True cells are outlined
    in red (e.g. cells where a predicted table differs from the target).
    """
    k = len(tables)
    m = tables[0].shape[1]
    fig, axes = plt.subplots(1, k, figsize=figsize or (1.0 + 1.1 * k * max(m, 2) * 0.5, 0.25 * 2 ** n + 1.2))
    axes = np.atleast_1d(axes)
    cmap = ListedColormap(['#f2f2f2', '#3b6ea8'])
    for i, (T, title) in enumerate(zip(tables, titles)):
        ax = axes[i]
        ax.imshow(T, cmap=cmap, vmin=0, vmax=1, aspect='auto')
        for r in range(T.shape[0]):
            for j in range(T.shape[1]):
                ax.text(j, r, str(int(T[r, j])), ha='center', va='center', fontsize=7,
                        color='white' if T[r, j] else 'black')
        if wrong is not None and wrong[i] is not None:
            for r, j in zip(*np.nonzero(wrong[i])):
                ax.add_patch(plt.Rectangle((j - .5, r - .5), 1, 1, fill=False, ec='red', lw=2))
        ax.set_xticks(range(T.shape[1]))
        ax.set_xticklabels([f'y{j}' for j in range(T.shape[1])], fontsize=8)
        ax.set_yticks(range(T.shape[0]))
        ax.set_yticklabels(row_labels(n) if i == 0 else [], fontsize=7, family='monospace')
        ax.set_title(title, fontsize=9)
    if k:
        axes[0].set_ylabel('inputs x0..x%d' % (n - 1), fontsize=8)
    plt.tight_layout()
    plt.show()
