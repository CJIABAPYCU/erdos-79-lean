# Erdős Problem 79 in Lean 4

A Lean 4 formalization (work in progress) of

> **Theorem** (Wigderson 2024). There are infinitely many graphs that are not Ramsey size-linear
> but all of whose proper subgraphs are.

answering Erdős Problem [#79](https://www.erdosproblems.com/79) (Erdős–Faudree–Rousseau–Schelp 1993),
catalogued as JSP-000096 in the Justin Sun Prize problem bank.

- Mathematical source: Y. Wigderson, *Infinitely many minimally non-Ramsey size-linear graphs*,
  [arXiv:2409.05931](https://arxiv.org/abs/2409.05931); European J. Combin. 128 (2025),
  [doi:10.1016/j.ejc.2025.104175](https://doi.org/10.1016/j.ejc.2025.104175).
- Target statement: `Erdos79.erdos_79` from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/89294ea02bd7cd678d59984add52cb4baef3dbf4/FormalConjectures/ErdosProblems/79.lean),
  using that repository's definitions of `graphRamsey` and `IsRamseySizeLinear`.

## Status

Work in progress — the proof is not complete yet.

## Proof outline

The formalization follows Wigderson's argument, replacing the cited tools with elementary ones:

1. Forests are Ramsey size-linear (via 1-degeneracy instead of Chvátal's theorem).
2. A graph with `e(G) ≥ 5 v(G)` is not Ramsey size-linear (first-moment count against `K_n`
   instead of the Lovász Local Lemma).
3. For every `g` there is a graph of girth `≥ g` with `e ≥ 5 v` (greedy Erdős–Sachs construction).
4. A minimal non-Ramsey-size-linear subgraph of such a graph contains a cycle, hence has `≥ g` vertices.

## Build

```bash
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.33.1`; dependencies pinned in `lake-manifest.json`.

AI assistance (Claude) is used in writing this formalization; correctness rests on the Lean kernel.
