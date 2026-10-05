# Learn Locally, Recurse Globally: trained model and demo

Inference-only release of the truth-table-to-circuit model from

> **Learn Locally, Recurse Globally: Neural Circuit Synthesis Beyond Training Depth.**
> Emile Richard. NeurIPS 2026.

The model is a 2.2M-parameter encoder-decoder Transformer that reads the truth table of a
Boolean function (up to 5 inputs and 5 outputs) and writes a circuit computing it. It was
trained only on circuits of depth at most 2. On deeper circuits a single forward pass makes
errors; an outer loop, **XOR residual refinement**, calls the same model on the residual
(the cells that are still wrong) and XORs the corrections, which makes the result exact.

This repository contains the trained weights, a minimal inference implementation, the outer
loop, a few test samples and a demo notebook. It does not contain training or data
generation code.

## Contents

```
llrg/
  model.py     inference-only model (truth-table encoder + GPT-2 decoder), greedy decoding
  circuit.py   circuit parser, evaluator, size/depth, sum-of-products, drawing
  harness.py   one-shot inference and XOR residual refinement (Algorithm 1 of the paper)
  vocab.py     the 16-token circuit vocabulary
  viz.py       truth-table plots
weights/       model.pt (state dict) and config.json
samples/       samples.json: test circuits (shallow and deep) with their truth tables
assets/        figures used by the notebooks
notebooks/     00_basics.ipynb (circuits, truth tables, tokens; model architecture)
               demo.ipynb (one-shot inference and the outer loop on test circuits)
```

## Quick start

```bash
python -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
jupyter notebook notebooks/00_basics.ipynb   # then notebooks/demo.ipynb
```

Or from Python:

```python
import numpy as np
from llrg import CircuitSynthesizer, circuit as C, harness as H

model = CircuitSynthesizer.from_pretrained('weights')
Y = C.evaluate(C.parse('( 0 ⊻ 1 ) ∧ ( 2 ∨ ~ 3 )\n~ ( 0 ∨ 3 )'), n=4)   # target truth table
outs, pred, ids = H.one_shot(model, Y)          # one forward pass
res = H.xor_refine(model, Y)                    # outer loop; res['outputs'] is exact
print([C.pretty(o) for o in res['outputs']])
```

## Circuit format

One infix expression per output, outputs separated by newlines. Inputs are the digits
`0`..`4` (x0..x4), gates are `∧` (AND), `∨` (OR), `⊻` (XOR), prefix `~` (NOT), and `ZERO`,
`ONE` are constants. Truth-table rows are in lexicographic order of the inputs, with x0 the
most significant bit.

## Samples

`samples/samples.json` holds circuits drawn from the paper's random generator, in reduced
form, together with their truth tables. Shallow samples (generator depth 2) are synthesized
exactly in one pass; deep samples (generator depth 6, three times the training depth) are
not, and are recovered exactly by the outer loop in two or three steps. None of these truth tables occurs in the depth-2 training corpus of the same
shape.

## Citation

```bibtex
@inproceedings{richard2026learn,
  title     = {Learn Locally, Recurse Globally: Neural Circuit Synthesis Beyond Training Depth},
  author    = {Richard, Emile},
  booktitle = {Advances in Neural Information Processing Systems},
  year      = {2026}
}
```
