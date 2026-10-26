# Propose, Decide, Certify

Code, approved Lean statements and benchmarks for the paper *Propose, Decide, Certify* (2026).

An agent chooses a linear PDE template from a problem given as text, data or an image, proposes a finite-difference
scheme, decides its stability and consistency, and certifies the decision in Lean 4. Throughout, three levels of
evidence are kept apart: **[K]** proof checked by the Lean kernel, **[N]** exact or numerical certificate outside Lean
(sympy, z3), **[E]** empirical validation.

## Layout

| Folder | Contents |
|---|---|
| `lean/` | Lean 4 project (Lean 4.34.1, Mathlib v4.34.1). `Esquemas/approved/`: every statement family exactly as approved before any proof attempt, with its SHA-256 (`SHA256SUMS_esquemas*`). `Esquemas/proved/`: the template (A2) and convergence (A4) files with proofs. |
| `tools/` | Statement generator (`generar_esquemas.py`), checkers, the JSON input of each family, the random-stencil generator (A9) and the sympy labeller of the consistency family (A8). |
| `harness/` | The judge and the proposers: `frontera_esquemas.py` (task loader and judge adapter), `frontera.py`, `juez_lean.py`, `selector_modelo.py` (model selection with `claude -p`, no tools), cost ledger, tests. |
| `selector/` | Model-selection benchmark: generators (v1 and v2), the two benchmark archives, the no-LLM baselines and the evaluation script. |
| `baselines/` | Fixed-script baseline, the full fixed pipeline for A9 (Bernstein certificates translated to Lean), and the z3 baseline. |

## Statement families

A1 FTCS · A2 template (`Esquema`, von Neumann, moments) · A3 corpus · A4 consistency and convergence · A5 decide pairs ·
A6 propose–discover loop · A7 hard exact regions · A8 physical templates (molds) and exact-moment consistency ·
A9 v2 random five-point stencils (24 tasks, seed 20261027).

## Protocol

Statements are approved by the first author before any proof is attempted and stored with their SHA-256. A proof is
accepted only if the approved text is intact, it compiles with no `sorry`, no forbidden token appears and
`#print axioms` lists only the standard axioms.

## Reproducing

```
cd lean && lake exe cache get && lake env lean Esquemas/approved/A9v2_Aleatorios.lean   # statements elaborate (with sorry)
python3 selector/problemas_v2.py 20261026 /tmp/bench_v2                                  # regenerates the selector benchmark
python3 selector/base_v2.py /tmp/bench_v2                                               # no-LLM baselines
```

## License

MIT (see `LICENSE`).
