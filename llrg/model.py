"""Inference-only truth-table-to-circuit model.

Architecture (2.2M parameters):
  * encoder, no self-attention: each truth-table cell (a bit) gets a learned bit embedding
    of dimension d_b, plus a learned *strided* positional embedding indexed by
    r * m_max + j (row r, output column j, m_max = 5), then a linear projection to d;
  * decoder: a GPT-2 decoder with cross-attention to the encoded table, which emits the
    circuit token by token (greedy decoding).
"""
import json
import os

import numpy as np
import torch
import torch.nn as nn
from transformers import GPT2Config, GPT2LMHeadModel

from .vocab import TOKENS, START, END


def strided_positions(R, m_max, m):
    """Position index r * m_max + j of every cell (row r, column j) of an R x m table."""
    return (torch.arange(R).view(R, 1) * m_max + torch.arange(m).view(1, m)).flatten()


class TruthTableEncoder(nn.Module):
    def __init__(self, n_max, m_max, d_b, d):
        super().__init__()
        self.m_max = m_max
        self.bit_embedding = nn.Embedding(2, d_b)
        self.position_embedding = nn.Embedding(m_max * 2 ** n_max, d_b)
        self.projection = nn.Linear(d_b, d)

    def positions(self, R, m):
        return strided_positions(R, self.m_max, m)

    def forward(self, Y):
        """Y: (B, R, m) tensor of 0/1. Returns (B, R*m, d)."""
        B, R, m = Y.shape
        seq = Y.long().reshape(B, R * m)
        pos = self.positions(R, m).to(Y.device).unsqueeze(0).expand(B, -1)
        return self.projection(self.bit_embedding(seq) + self.position_embedding(pos))


class CircuitSynthesizer(nn.Module):
    def __init__(self, n_max=5, m_max=5, d_b=64, d=128, layers=8, heads=4, max_len=512):
        super().__init__()
        self.n_max, self.m_max, self.max_len = n_max, m_max, max_len
        self.encoder = TruthTableEncoder(n_max, m_max, d_b, d)
        cfg = GPT2Config(vocab_size=len(TOKENS), n_embd=d, n_layer=layers, n_head=heads,
                         n_positions=max_len, add_cross_attention=True, is_decoder=True,
                         activation_function='gelu_new', bos_token_id=START,
                         eos_token_id=END, pad_token_id=START)
        self.decoder = GPT2LMHeadModel(cfg)

    @classmethod
    def from_pretrained(cls, weights_dir, device='cpu'):
        with open(os.path.join(weights_dir, 'config.json')) as f:
            cfg = json.load(f)
        model = cls(**cfg['architecture'])
        state = torch.load(os.path.join(weights_dir, 'model.pt'), map_location='cpu')
        missing, unexpected = model.load_state_dict(state, strict=False)
        # Only non-parameter buffers (e.g. GPT-2 causal-mask buffers) may be absent.
        params = {k for k, _ in model.named_parameters()}
        missing = [k for k in missing if k in params]
        if missing or unexpected:
            raise RuntimeError(f'weights do not match: missing={missing[:5]} unexpected={unexpected[:5]}')
        return model.to(device).eval()

    @torch.no_grad()
    def synthesize(self, Y, max_len=400):
        """Greedy decoding of a circuit for one truth table.

        Y: array of shape (2^n, m) with 0/1 entries, rows in lexicographic order of the
        inputs (x0 most significant). Returns the list of generated token ids, including
        <start> and <end>.
        """
        Y = np.asarray(Y, dtype=np.uint8)
        if Y.ndim != 2 or Y.shape[0] > 2 ** self.n_max or Y.shape[1] > self.m_max:
            raise ValueError(f'table shape {Y.shape} not supported (n <= {self.n_max}, m <= {self.m_max})')
        device = next(self.parameters()).device
        enc = self.encoder(torch.tensor(Y, device=device).unsqueeze(0))
        enc_mask = torch.ones(enc.shape[:2], dtype=torch.long, device=device)
        ids = [START]
        past = None
        inp = torch.tensor([[START]], device=device)
        for _ in range(min(max_len, self.max_len) - 1):
            out = self.decoder(input_ids=inp, encoder_hidden_states=enc,
                               encoder_attention_mask=enc_mask, past_key_values=past,
                               use_cache=True)
            past = out.past_key_values
            nxt = int(out.logits[0, -1].argmax())
            ids.append(nxt)
            if nxt == END:
                break
            inp = torch.tensor([[nxt]], device=device)
        return ids
