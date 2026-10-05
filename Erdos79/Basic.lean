import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Girth
import Erdos79.Forest

/-!
# Erdős Problem 79 — ingredients

The four ingredients of Wigderson's argument, stated in the form used by the final assembly:

* `IsRamseySizeLinear.of_iso`          — isomorphism invariance
* `isRamseySizeLinear_of_isAcyclic`   — forests are Ramsey size-linear
* `not_isRamseySizeLinear_of_dense`   — `e ≥ 5 v` ⇒ not Ramsey size-linear
* `exists_large_girth_dense`          — large girth together with `e ≥ 5 v`
-/

open SimpleGraph

namespace Erdos79Proof

/-- Ramsey size-linearity is invariant under graph isomorphism. -/
theorem IsRamseySizeLinear.of_iso {α β : Type*} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {G' : SimpleGraph β} (e : G ≃g G') (h : G.IsRamseySizeLinear) :
    G'.IsRamseySizeLinear := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun n H _ hH => ?_⟩
  have hR : graphRamsey G' H = graphRamsey G H := by
    unfold graphRamsey
    simp_rw [← isContained_congr_left e]
  rw [hR]
  exact h n H hH

/-- Every finite forest is Ramsey size-linear. -/
theorem isRamseySizeLinear_of_isAcyclic {α : Type*} [Fintype α] {F : SimpleGraph α}
    (hF : F.IsAcyclic) : F.IsRamseySizeLinear :=
  isRamseySizeLinear_of_isAcyclic' hF

/-- A nonempty graph with at least five times as many edges as vertices is not
Ramsey size-linear. -/
theorem not_isRamseySizeLinear_of_dense {α : Type*} [Fintype α] [Nonempty α]
    (G : SimpleGraph α) (h : 5 * Fintype.card α ≤ G.edgeSet.ncard) :
    ¬ G.IsRamseySizeLinear := by
  sorry

/-- For every `g` there is a nonempty finite graph of girth at least `g` with at least
five times as many edges as vertices. -/
theorem exists_large_girth_dense (g : ℕ) :
    ∃ (m : ℕ) (_ : 0 < m) (G : SimpleGraph (Fin m)),
      (g : ℕ∞) ≤ G.egirth ∧ 5 * m ≤ G.edgeSet.ncard := by
  sorry

end Erdos79Proof
