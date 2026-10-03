"""Token vocabulary of the circuit decoder.

A circuit is a sequence of tokens: ``<start>``, one infix Boolean expression per output
separated by ``\\n``, then ``<end>``. Variables are the digits ``0``..``4`` (input x0..x4),
gates are ``∧`` (AND), ``∨`` (OR), ``⊻`` (XOR) and the prefix ``~`` (NOT), and
``ZERO``/``ONE`` are constants.
"""

TOKENS = ['<start>', '<end>', '∧', '∨', '⊻', '~', 'ZERO', 'ONE', '(', ')', '\n',
          '0', '1', '2', '3', '4']
TOKEN_TO_ID = {t: i for i, t in enumerate(TOKENS)}
START, END = TOKEN_TO_ID['<start>'], TOKEN_TO_ID['<end>']

# Human-readable names of the tokens, for display.
DISPLAY = {'<start>': '<start>', '<end>': '<end>', '∧': 'AND', '∨': 'OR', '⊻': 'XOR',
           '~': 'NOT', 'ZERO': '0', 'ONE': '1', '(': '(', ')': ')', '\n': '<next output>'}
for _i in range(5):
    DISPLAY[str(_i)] = f'x{_i}'


def tokenize(text):
    """Split a circuit string such as ``'( 0 ∧ 1 ) ⊻ ~ 2 \\n 3'`` into token ids.

    The string may or may not contain ``<start>``/``<end>``; they are added if missing.
    """
    toks = []
    for line_i, line in enumerate(text.replace('<start>', '').replace('<end>', '').split('\n')):
        if line_i > 0:
            toks.append('\n')
        toks.extend(line.split())
    ids = [TOKEN_TO_ID[t] for t in toks]
    return [START] + ids + [END]


def detokenize(ids, keep_special=False):
    """Token ids back to the circuit string (outputs separated by newlines)."""
    out = []
    for i in ids:
        t = TOKENS[int(i)]
        if t in ('<start>', '<end>') and not keep_special:
            continue
        out.append(t)
    return ' '.join(out).replace(' \n ', '\n').replace('\n ', '\n').replace(' \n', '\n')
