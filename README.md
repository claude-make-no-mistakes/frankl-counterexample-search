# Frankl counterexample search at 55 members

In each of the four patterns for a smallest 55-member Frankl counterexample, the reduced domination order must have at least **20 incomparable pairs**. Any two distinct maximal points must have at least four common incomparable points. The paper proves these restrictions and an independent reviewer checked them. [Paper](paper.pdf) · [LaTeX source](paper.tex)

The source preprint reports proof-checked exclusion through 54 members. Its four-way 55-member reduction gives the patterns below. The solver in this repository uses those patterns and the new incomparability restrictions. None of the four full cases was resolved by the bounded runs. [Upstream preprint](https://zenodo.org/records/23645724) · [Upstream solver workflow](https://github.com/anaxia-research/eUUR/actions/runs/40210362663)

| Case | Support | Complement blocks R, S, T | Extra block 11 mask |
| --- | ---: | --- | --- |
| boundary | 14 | 14, 14, 14 | absent |
| i-a | 13 | 15, 14, 14 | absent |
| i-b | 13 | 15, 15, 13 | absent |
| ii | 13 | 14, 14, 14 | present |

## Replay

The runs use Python 3.10, Python-SAT, and CaDiCaL 1.9.5. The recorded experiments use the full closure constraints. With the same command omitting `--all-closure`, the solver adds intersection constraints as it encounters violated ones. In both versions, a satisfying assignment qualifies only after independent checking of every union and every element frequency.

```sh
python -m pip install -r requirements.txt
python -m unittest test_primitives
python search.py boundary --all-closure --conflicts 180000 --witness boundary-witness.json
python search.py i-a --all-closure --conflicts 180000 --witness i-a-witness.json
python search.py i-b --all-closure --conflicts 180000 --witness i-b-witness.json
python search.py ii --all-closure --conflicts 180000 --witness ii-witness.json
```

[Run records](evidence/) report the formula sizes and terminal solver statuses. If a run saves a witness, `python verify.py WITNESS.json` checks it using only Python's standard library. Member sets are integer bit masks. The general conjecture remains open, and priority for the structural bound has not been established.
