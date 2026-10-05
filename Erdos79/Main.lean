import Erdos79.Basic
import FormalConjectures.ErdosProblems.«79»

/-!
# Erdős Problem 79

The statement below is copied verbatim from
`FormalConjectures/ErdosProblems/79.lean` (google-deepmind/formal-conjectures,
commit `89294ea02bd7cd678d59984add52cb4baef3dbf4`); `erdos_79_matches` checks this by type.
-/

open SimpleGraph

namespace Erdos79Proof

open scoped Classical in
theorem erdos_79 : answer(True) ↔
    ∀ (N : ℕ), ∃ (n : ℕ) (_ : N ≤ n) (G : SimpleGraph (Fin n)),
      ¬ G.IsRamseySizeLinear ∧
      ∀ H : G.Subgraph, H < ⊤ → H.coe.IsRamseySizeLinear := by
  sorry

/-- The theorem proved here has exactly the type of the Formal Conjectures statement. -/
theorem erdos_79_matches : type_of% Erdos79.erdos_79 := erdos_79

end Erdos79Proof
