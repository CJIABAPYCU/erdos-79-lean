import Erdos79.Basic
import FormalConjectures.ErdosProblems.«79»

/-!
# Erdős Problem 79

The statement below is copied verbatim from
`FormalConjectures/ErdosProblems/79.lean` (google-deepmind/formal-conjectures,
commit `89294ea02bd7cd678d59984add52cb4baef3dbf4`); `erdos_79_matches` checks this by type.

Proof: for a given `N` take a graph of girth `≥ N` with `e ≥ 5 v`; it is not Ramsey size-linear.
Among all graphs on some `Fin n` that are not Ramsey size-linear and have girth `≥ N`, take one
minimising `n + e`. Every proper subgraph is then Ramsey size-linear (it would otherwise be a
smaller such graph after relabelling its vertices), and the graph is not a forest, so it contains
a cycle, whose length is at least `N` and at most `n`.
-/

open SimpleGraph

namespace Erdos79Proof

/-- A cycle has at most as many edges as the graph has vertices. -/
lemma Walk.IsCycle.length_le_card {V : Type*} [Fintype V] {G : SimpleGraph V} {a : V}
    {w : G.Walk a a} (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have h := hw.support_nodup.length_le_card
  rwa [List.length_tail, Walk.length_support, Nat.add_sub_cancel] at h

/-- A non-acyclic graph on `Fin n` of girth at least `N` has at least `N` vertices. -/
lemma le_of_egirth {n N : ℕ} {G : SimpleGraph (Fin n)} (hN : (N : ℕ∞) ≤ G.egirth)
    (hG : ¬ G.IsAcyclic) : N ≤ n := by
  obtain ⟨a, w, hw⟩ : ∃ a, ∃ w : G.Walk a a, w.IsCycle := by
    simpa [IsAcyclic] using hG
  have h1 : (N : ℕ∞) ≤ w.length := hN.trans hw.egirth_le_length
  have h2 := Walk.IsCycle.length_le_card hw
  rw [Fintype.card_fin] at h2
  exact (Nat.cast_le.mp h1).trans h2

/-- A proper subgraph has strictly smaller "vertices + edges". -/
lemma card_add_ncard_lt {n : ℕ} {G : SimpleGraph (Fin n)} {H : G.Subgraph} (hH : H < ⊤) :
    Nat.card H.verts + Nat.card H.coe.edgeSet < n + G.edgeSet.ncard := by
  have he : Nat.card H.coe.edgeSet ≤ H.edgeSet.ncard := by
    rw [Nat.card_coe_set_eq, ← H.image_coe_edgeSet_coe,
      Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  have hv : Nat.card H.verts = H.verts.ncard := Nat.card_coe_set_eq _
  have hsub : H.edgeSet ⊆ G.edgeSet := H.edgeSet_subset
  have hvle : H.verts.ncard ≤ n := by
    simpa using Set.ncard_le_ncard (Set.subset_univ H.verts)
  by_cases hvu : H.verts = Set.univ
  · have hlt : H.edgeSet ⊂ G.edgeSet := by
      refine hsub.ssubset_of_ne fun hEq => hH.ne ?_
      ext a b
      · simp [hvu]
      · simp only [Subgraph.top_adj]
        rw [← Subgraph.mem_edgeSet, hEq, mem_edgeSet]
    have := Set.ncard_lt_ncard hlt
    omega
  · have hlt : H.verts.ncard < n := by
      have := Set.ncard_lt_ncard ((Set.subset_univ H.verts).ssubset_of_ne hvu)
      simpa using this
    have := Set.ncard_le_ncard hsub
    omega

open scoped Classical in
theorem erdos_79 : answer(True) ↔
    ∀ (N : ℕ), ∃ (n : ℕ) (_ : N ≤ n) (G : SimpleGraph (Fin n)),
      ¬ G.IsRamseySizeLinear ∧
      ∀ H : G.Subgraph, H < ⊤ → H.coe.IsRamseySizeLinear := by
  simp only [true_iff]
  intro N
  let P : ℕ → Prop := fun k => ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬ G.IsRamseySizeLinear ∧ (N : ℕ∞) ≤ G.egirth ∧ n + G.edgeSet.ncard = k
  have hP : ∃ k, P k := by
    obtain ⟨m, hm, G0, hg, hd⟩ := exists_large_girth_dense N
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact ⟨_, m, G0, not_isRamseySizeLinear_of_dense G0 (by simpa using hd), hg, rfl⟩
  obtain ⟨n, G, hG, hgir, hk⟩ := Nat.find_spec hP
  have hacyc : ¬ G.IsAcyclic := fun h => hG (isRamseySizeLinear_of_isAcyclic h)
  refine ⟨n, le_of_egirth hgir hacyc, G, hG, fun H hH => ?_⟩
  by_contra hH'
  -- relabel the vertices of `H.coe` by `Fin n'`
  set n' := Fintype.card H.verts
  let G' : SimpleGraph (Fin n') := H.coe.overFin rfl
  have e : H.coe ≃g G' := H.coe.overFinIso rfl
  have hG' : ¬ G'.IsRamseySizeLinear := fun h => hH' (IsRamseySizeLinear.of_iso e.symm h)
  have hgir' : (N : ℕ∞) ≤ G'.egirth := by
    rw [← e.egirth_eq]
    exact hgir.trans H.coe_isContained.egirth_le
  have hmin := Nat.find_min' hP ⟨n', G', hG', hgir', rfl⟩
  have hcard : G'.edgeSet.ncard = Nat.card H.coe.edgeSet := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr e.symm.mapEdgeSet
  have hlt := card_add_ncard_lt hH
  rw [Nat.card_eq_fintype_card] at hlt
  omega

/-- The theorem proved here has exactly the type of the Formal Conjectures statement. -/
theorem erdos_79_matches : type_of% Erdos79.erdos_79 := erdos_79

end Erdos79Proof
