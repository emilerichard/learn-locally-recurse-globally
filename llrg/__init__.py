"""Inference-only release of the truth-table-to-circuit model of
"Learn Locally, Recurse Globally: Neural Circuit Synthesis Beyond Training Depth".
"""
from .model import CircuitSynthesizer
from . import circuit, generate, harness, vocab

__all__ = ['CircuitSynthesizer', 'circuit', 'generate', 'harness', 'vocab']
