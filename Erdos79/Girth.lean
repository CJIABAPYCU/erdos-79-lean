import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.Fintype.CardEmbedding
import Erdos79.Weighted

/-!
# Graphs of large girth with `e ≥ 5 v`

Erdős's deletion argument. In `G(N, p)` with `p = 11 / N` the expected number of edges is
`11 (N - 1) / 2`, and the expected number of (labelled) cycles of length `L` is at most `11 ^ L`.
Delete one edge from every cycle of length `< g`: for `N = 11 + 2 r 11 ^ (r + 3)`, `r = g - 3`, at
least `5 N` edges survive and the girth is at least `g`.
-/

open SimpleGraph Finset

open scoped Classical

namespace Erdos79Proof

variable {V : Type*} {N : ℕ}

/-- The edges of the closed walk `f 0, f 1, …, f (L - 1), f 0`. -/
noncomputable def cycEdges {L : ℕ} [NeZero L] (f : Fin L → Fin N) : Finset (Sym2 (Fin N)) :=
  univ.image fun i => s(f i, f (i + 1))

lemma card_cycEdges {ℓ : ℕ} (f : Fin (ℓ + 3) ↪ Fin N) : (cycEdges f).card = ℓ + 3 := by
  rw [cycEdges, card_image_of_injective, card_univ, Fintype.card_fin]
  intro i j hij
  rcases Sym2.eq_iff.mp hij with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact f.injective h1
  · have e1 := f.injective h1
    have e2 := f.injective h2
    exfalso
    rw [e1, add_assoc] at e2
    have h0 : (1 + 1 : Fin (ℓ + 3)) = 0 := by
      have := congrArg (· - j) e2
      simpa using this
    have := congrArg Fin.val h0
    rw [Fin.val_add, Fin.val_one, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
    omega

/-- A cycle of length `ℓ + 3` gives an injective labelling `f` of its vertices with all
`f i ~ f (i + 1)`. -/
lemma exists_emb_of_isCycle {G : SimpleGraph V} {a : V} {w : G.Walk a a} (hw : w.IsCycle)
    {ℓ : ℕ} (hL : w.length = ℓ + 3) :
    ∃ f : Fin (ℓ + 3) ↪ V, ∀ i, G.Adj (f i) (f (i + 1)) := by
  have hinj : Set.InjOn w.getVert {i | i ≤ w.length - 1} := hw.getVert_injOn'
  have hmem : ∀ i : Fin (ℓ + 3), (i : ℕ) ∈ {i | i ≤ w.length - 1} := fun i => by
    show (i : ℕ) ≤ w.length - 1
    omega
  refine ⟨⟨fun i => w.getVert i, fun i j h => Fin.ext (hinj (hmem i) (hmem j) h)⟩,
    fun i => ?_⟩
  · show G.Adj (w.getVert i) (w.getVert ((i + 1 : Fin (ℓ + 3)) : ℕ))
    rw [Fin.val_add_one]
    split_ifs with hi
    · have hi' : (i : ℕ) = ℓ + 2 := by rw [hi]; simp
      rw [w.getVert_zero]
      have := w.adj_getVert_succ (i := ℓ + 2) (by omega)
      rwa [show ℓ + 2 + 1 = w.length by omega, w.getVert_length, ← hi'] at this
    · exact w.adj_getVert_succ (by have := i.isLt; omega)

lemma cycEdges_subset {A : Finset (Sym2 (Fin N))} {ℓ : ℕ} (f : Fin (ℓ + 3) ↪ Fin N)
    (hf : ∀ i, (fromEdgeSet (A : Set (Sym2 (Fin N)))).Adj (f i) (f (i + 1))) :
    cycEdges f ⊆ A := by
  intro e he
  obtain ⟨i, -, rfl⟩ := mem_image.mp he
  have := hf i
  rw [fromEdgeSet_adj] at this
  exact_mod_cast this.1

/-- Off-diagonal pairs of `Fin N`. -/
noncomputable def offDiagE (N : ℕ) : Finset (Sym2 (Fin N)) := univ.filter (fun e => ¬ e.IsDiag)

lemma card_offDiagE (N : ℕ) : (offDiagE N).card = N.choose 2 := by
  rw [offDiagE, ← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]

lemma cycEdges_subset_offDiagE {ℓ : ℕ} (f : Fin (ℓ + 3) ↪ Fin N) : cycEdges f ⊆ offDiagE N := by
  intro e he
  obtain ⟨i, -, rfl⟩ := mem_image.mp he
  simp only [offDiagE, mem_filter, mem_univ, true_and, Sym2.mk_isDiag_iff]
  exact f.injective.ne (by simp)

/-- `#edges - #(labelled cycles of length 3, …, r + 2)`. -/
noncomputable def cycX (N r : ℕ) (A : Finset (Sym2 (Fin N))) : ℝ :=
  A.card - ∑ ℓ ∈ range r, ∑ f : Fin (ℓ + 3) ↪ Fin N, (if cycEdges f ⊆ A then (1 : ℝ) else 0)

lemma sum_wt_cycX (N r : ℕ) (p : ℝ) :
    ∑ A ∈ (offDiagE N).powerset, wt p (offDiagE N) A * cycX N r A =
      p * N.choose 2 -
        ∑ ℓ ∈ range r, (N.descFactorial (ℓ + 3) : ℝ) * p ^ (ℓ + 3) := by
  simp only [cycX, mul_sub, sum_sub_distrib, sum_wt_mul_card, card_offDiagE, mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [sum_comm]
  have : ∀ f : Fin (ℓ + 3) ↪ Fin N, ∑ A ∈ (offDiagE N).powerset,
      wt p (offDiagE N) A * (if cycEdges f ⊆ A then (1 : ℝ) else 0) = p ^ (ℓ + 3) := by
    intro f
    have h := sum_wt_superset p (cycEdges_subset_offDiagE f)
    rw [card_cycEdges] at h
    rw [← h]
    refine sum_congr rfl fun A _ => ?_
    split_ifs <;> simp
  rw [sum_congr rfl fun f _ => this f, sum_const, card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]

lemma five_mul_le_sum_wt_cycX {N r : ℕ} (hN : 11 + 2 * r * 11 ^ (r + 3) ≤ N) :
    (5 * N : ℝ) ≤ ∑ A ∈ (offDiagE N).powerset,
      wt (11 / N) (offDiagE N) A * cycX N r A := by
  have hN11 : 11 ≤ N := le_trans (Nat.le_add_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [sum_wt_cycX]
  have hterm : ∀ ℓ ∈ range r,
      (N.descFactorial (ℓ + 3) : ℝ) * (11 / (N : ℝ)) ^ (ℓ + 3) ≤ 11 ^ (r + 3) := by
    intro ℓ hℓ
    have hl := mem_range.mp hℓ
    calc (N.descFactorial (ℓ + 3) : ℝ) * (11 / (N : ℝ)) ^ (ℓ + 3)
        ≤ (N : ℝ) ^ (ℓ + 3) * (11 / (N : ℝ)) ^ (ℓ + 3) := by
          gcongr; exact_mod_cast Nat.descFactorial_le_pow _ _
      _ = 11 ^ (ℓ + 3) := by rw [← mul_pow, mul_div_cancel₀ _ hNpos.ne']
      _ ≤ 11 ^ (r + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsum := sum_le_sum hterm
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  rw [Nat.cast_choose_two]
  have : 11 / (N : ℝ) * (N * (N - 1) / 2) = 11 * (N - 1) / 2 := by field_simp
  rw [this]
  have hNR : (11 : ℝ) + 2 * r * 11 ^ (r + 3) ≤ N := by exact_mod_cast hN
  nlinarith

/-- Deleting one edge from each short cycle. -/
lemma exists_girth_of_cycX {N r : ℕ} {A : Finset (Sym2 (Fin N))} (hAE : A ⊆ offDiagE N) :
    ∃ G : SimpleGraph (Fin N), ((r + 3 : ℕ) : ℕ∞) ≤ G.egirth ∧ cycX N r A ≤ G.edgeSet.ncard := by
  let B : Finset (Σ ℓ, Fin (ℓ + 3) ↪ Fin N) :=
    (range r).sigma fun ℓ => univ.filter fun f => cycEdges f ⊆ A
  let D : Finset (Sym2 (Fin N)) := B.image fun x => s(x.2 0, x.2 1)
  let A' := A \ D
  refine ⟨fromEdgeSet (A' : Set (Sym2 (Fin N))), ?_, ?_⟩
  · rw [le_egirth]
    intro a w hw
    by_contra hlt
    push Not at hlt
    have h3 := hw.three_le_length
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, w.length = ℓ + 3 := ⟨w.length - 3, by omega⟩
    obtain ⟨f, hf⟩ := exists_emb_of_isCycle hw hℓ
    have hsub : cycEdges f ⊆ A' := cycEdges_subset f hf
    have hB : (⟨ℓ, f⟩ : Σ ℓ, Fin (ℓ + 3) ↪ Fin N) ∈ B := by
      simp only [B, mem_sigma, mem_range, mem_filter, mem_univ, true_and]
      refine ⟨?_, hsub.trans sdiff_subset⟩
      rw [hℓ] at hlt
      have : ℓ + 3 < r + 3 := by exact_mod_cast hlt
      omega
    have hD : s(f 0, f 1) ∈ D := mem_image.mpr ⟨_, hB, rfl⟩
    have hA' : s(f 0, f 1) ∈ A' := hsub (mem_image.mpr ⟨0, mem_univ _, by simp⟩)
    exact (mem_sdiff.mp hA').2 hD
  · have hEs : (fromEdgeSet (A' : Set (Sym2 (Fin N)))).edgeSet = (A' : Set (Sym2 (Fin N))) := by
      rw [edgeSet_fromEdgeSet]
      ext e
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, fun hd => ?_⟩
        have := hAE (mem_sdiff.mp h).1
        simp only [offDiagE, mem_filter] at this
        exact this.2 (by simpa using hd)
    rw [hEs, Set.ncard_coe_finset]
    have hBcard : (B.card : ℝ) = ∑ ℓ ∈ range r, ∑ f : Fin (ℓ + 3) ↪ Fin N,
        (if cycEdges f ⊆ A then (1 : ℝ) else 0) := by
      simp only [B, card_sigma, card_filter]
      push_cast
      rfl
    have h1 : A.card ≤ A'.card + D.card := card_le_card_sdiff_add_card
    have h2 : D.card ≤ B.card := card_image_le
    have : (A.card : ℝ) ≤ A'.card + B.card := by exact_mod_cast h1.trans (by omega)
    rw [cycX, ← hBcard]
    linarith

/-- **Large girth and `e ≥ 5 v`.** -/
theorem exists_large_girth_dense' (g : ℕ) :
    ∃ (m : ℕ) (_ : 0 < m) (G : SimpleGraph (Fin m)),
      (g : ℕ∞) ≤ G.egirth ∧ 5 * m ≤ G.edgeSet.ncard := by
  obtain ⟨N, hN⟩ : ∃ N, N = 11 + 2 * (g - 3) * 11 ^ (g - 3 + 3) := ⟨_, rfl⟩
  have hN11 : 11 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < 11 / N := by positivity
  have hp1 : (11 : ℝ) / N ≤ 1 := by rw [div_le_one hNpos]; exact_mod_cast hN11
  obtain ⟨A, hAE, hXA⟩ := exists_ge hp0 hp1 (offDiagE N) (cycX N (g - 3)) _
    (five_mul_le_sum_wt_cycX (le_of_eq hN.symm))
  obtain ⟨G, hG, hGe⟩ := exists_girth_of_cycX (r := g - 3) hAE
  refine ⟨N, by omega, G, le_trans ?_ hG, ?_⟩
  · exact_mod_cast (show g ≤ g - 3 + 3 by omega)
  · exact_mod_cast hXA.trans hGe

end Erdos79Proof
