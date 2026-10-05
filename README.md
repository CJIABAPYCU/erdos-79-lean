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

**Complete.** `Erdos79Proof.erdos_79` is proved with no `sorry`; `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound` (see `Erdos79/Axioms.lean`).
`Erdos79Proof.erdos_79_matches : type_of% Erdos79.erdos_79` checks, in the kernel, that the
statement proved is exactly the Formal Conjectures statement.

| File | Content |
|---|---|
| `Erdos79/Main.lean` | the statement and the final assembly (minimal counterexample by `v + e`) |
| `Erdos79/Forest.lean` | forests are Ramsey size-linear: `R(F, H) ≤ k·v(H) ≤ 2k·e(H)` |
| `Erdos79/Weighted.lean` | finite first-moment / averaging principle for random subsets |
| `Erdos79/Dense.lean` | `e(G) ≥ 5 v(G)` ⇒ not Ramsey size-linear (random graph vs `K_n`) |
| `Erdos79/Girth.lean` | graphs of girth `≥ g` with `e ≥ 5 v` (Erdős deletion argument) |
| `Erdos79/Basic.lean` | the four ingredients in the form used by `Main.lean` |

## Proof outline

The formalization follows Wigderson's argument, replacing the cited tools with elementary ones:

1. Forests are Ramsey size-linear (via 1-degeneracy instead of Chvátal's theorem).
2. A graph with `e(G) ≥ 5 v(G)` is not Ramsey size-linear (first-moment count in `G(N, 1/k)`
   against `K_n` instead of the Lovász Local Lemma; Ramsey's theorem from Formal Conjectures
   guarantees that `R(G, K_n)` is finite).
3. For every `g` there is a graph of girth `≥ g` with `e ≥ 5 v` (Erdős's deletion argument in
   `G(N, 11/N)`).
4. Among graphs of girth `≥ N` that are not Ramsey size-linear, one minimising `v + e` has all
   proper subgraphs Ramsey size-linear; it is not a forest, so it contains a cycle and has `≥ N`
   vertices.

## Build

```bash
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.33.1`; dependencies pinned in `lake-manifest.json`.

AI assistance (Claude) is used in writing this formalization; correctness rests on the Lean kernel.
