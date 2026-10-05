import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey
import FormalConjecturesForMathlib.Combinatorics.Ramsey.Diagonal
import Erdos79.Weighted
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Dense graphs are not Ramsey size-linear

If `e(G) ≥ 5 v(G) ≥ 5`, then `R(G, K_n)` grows faster than `e(K_n)`. With `n = 2k² + 1`,
`p = 1/k` and `N = (⌈c⌉ + 1) n²`, the expected number of copies of `G` in the random graph
`G(N, p)` plus the expected number of independent `n`-sets is below `1` for large `k`
(`exists_avoid`), which gives a 2-colouring of `K_N` with no red `G` and no blue `K_n`.
This replaces the Lovász Local Lemma used for [EFRS93, Corollary 1].
-/

open SimpleGraph Finset

open scoped Classical

namespace Erdos79Proof

variable {α W β : Type*}

/-- A set of at least `|β|` pairwise `D`-adjacent vertices gives a copy of `K_β` in `D`. -/
lemma top_isContained_of_pairwise [Fintype β] (D : SimpleGraph W) (S : Finset W)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → D.Adj x y) (h : Fintype.card β ≤ S.card) :
    (⊤ : SimpleGraph β) ⊑ D := by
  obtain ⟨e⟩ : Nonempty (β ↪ S) := by
    rw [Function.Embedding.nonempty_iff_card_le]; simpa using h
  refine ⟨⟨⟨fun b => (e b).1, fun {a b} hab => ?_⟩, fun a b h => e.injective (Subtype.ext h)⟩⟩
  exact hS _ (e a).2 _ (e b).2 fun h => hab.ne (e.injective (Subtype.ext h))

/-- Ramsey's theorem for a graph `G` against `K_n` (from Formal Conjectures' Erdős–Szekeres
bound). -/
lemma exists_ramsey [Fintype α] (G : SimpleGraph α) (n : ℕ) :
    ∃ M, ∀ C : SimpleGraph (Fin M), G ⊑ C ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Cᶜ := by
  refine ⟨(n + Fintype.card α).choose n, fun C => ?_⟩
  let c : Finset (Fin _) → Bool := fun e => decide (∀ x ∈ e, ∀ y ∈ e, x ≠ y → C.Adj x y)
  have key : ∀ x y, x ≠ y → (c {x, y} = true ↔ C.Adj x y) := by
    intro x y hxy
    simp only [c, decide_eq_true_eq]
    constructor
    · intro h; exact h x (by simp) y (by simp) hxy
    · intro h a ha b hb hab
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact h
      · exact h.symm
      · exact absurd rfl hab
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose n (Fintype.card α) c univ (by simp) with
    ⟨S, -, hS, hfalse⟩ | ⟨S, -, hS, htrue⟩
  · right
    refine top_isContained_of_pairwise _ S (fun x hx y hy hxy => ?_) (by simp [hS])
    have h := hfalse {x, y} (by simp [insert_subset_iff, hx, hy]) (card_pair hxy)
    rw [compl_adj]
    refine ⟨hxy, fun hadj => ?_⟩
    rw [(key x y hxy).mpr hadj] at h
    exact Bool.true_eq_false.mp h |>.elim
  · left
    refine (IsContained.of_le (le_top : G ≤ ⊤)).trans
      (top_isContained_of_pairwise _ S (fun x hx y hy hxy => ?_) (by simp [hS]))
    exact (key x y hxy).mp (htrue {x, y} (by simp [insert_subset_iff, hx, hy]) (card_pair hxy))

/-- A 2-colouring of `K_N` with no red `G` and no blue `K_n` shows `N < R(G, K_n)`. -/
lemma lt_graphRamsey [Fintype α] {G : SimpleGraph α} {n N : ℕ} (C0 : SimpleGraph (Fin N))
    (h1 : ¬ G ⊑ C0) (h2 : ¬ (⊤ : SimpleGraph (Fin n)) ⊑ C0ᶜ) :
    N < graphRamsey G (⊤ : SimpleGraph (Fin n)) := by
  obtain ⟨M, hM⟩ := exists_ramsey G n
  unfold graphRamsey
  by_contra hle
  push Not at hle
  have hmem := Nat.sInf_mem (s := {m | ∀ C : SimpleGraph (Fin m),
    G ⊑ C ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Cᶜ}) ⟨M, hM⟩
  let f := Fin.castLEEmb hle
  rcases hmem (C0.comap f) with h | h
  · exact h1 (h.trans ⟨⟨⟨f, fun h => h⟩, f.injective⟩⟩)
  · refine h2 (h.trans ⟨⟨⟨f, fun {a b} hab => ?_⟩, f.injective⟩⟩)
    rw [compl_adj] at hab ⊢
    exact ⟨f.injective.ne hab.1, hab.2⟩

/-- **First moment.** If `N^v p^e + N^n (1-p)^C(n,2) < 1`, some graph on `Fin N` contains
no copy of `G` and no independent `n`-set. -/
lemma exists_good_graph [Fintype α] (G : SimpleGraph α) (N n : ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1)
    (h : (N : ℝ) ^ Fintype.card α * p ^ G.edgeFinset.card +
      (N : ℝ) ^ n * (1 - p) ^ n.choose 2 < 1) :
    ∃ C0 : SimpleGraph (Fin N), ¬ G ⊑ C0 ∧ ¬ (⊤ : SimpleGraph (Fin n)) ⊑ C0ᶜ := by
  let E : Finset (Sym2 (Fin N)) := univ.filter (fun e => ¬ e.IsDiag)
  let S : (α ↪ Fin N) → Finset (Sym2 (Fin N)) := fun f => G.edgeFinset.image (Sym2.map f)
  let T : Finset (Fin N) → Finset (Sym2 (Fin N)) := fun j =>
    j.offDiag.image (Function.uncurry Sym2.mk)
  have hScard : ∀ f, (S f).card = G.edgeFinset.card := fun f =>
    card_image_of_injective _ (Sym2.map.injective f.injective)
  have hTcard : ∀ j ∈ univ.powersetCard n, (T j).card = n.choose 2 := by
    intro j hj; rw [Sym2.card_image_offDiag, (mem_powersetCard.mp hj).2]
  have hSE : ∀ f ∈ (univ : Finset (α ↪ Fin N)), S f ⊆ E := by
    intro f _ e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    simp only [E, mem_filter, mem_univ, true_and]
    rw [Sym2.isDiag_map f.injective]
    exact G.not_isDiag_of_mem_edgeSet (by simpa using he')
  have hTE : ∀ j ∈ univ.powersetCard n, T j ⊆ E := by
    intro j _ e he
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp he
    simp only [E, mem_filter, mem_univ, true_and, Function.uncurry_apply_pair,
      Sym2.mk_isDiag_iff]
    exact (mem_offDiag.mp hxy).2.2
  have hsum : ∑ f ∈ (univ : Finset (α ↪ Fin N)), p ^ (S f).card +
      ∑ j ∈ univ.powersetCard n, (1 - p) ^ (T j).card < 1 := by
    have e1 : ∑ f ∈ (univ : Finset (α ↪ Fin N)), p ^ (S f).card =
        (Fintype.card (α ↪ Fin N) : ℝ) * p ^ G.edgeFinset.card := by
      rw [sum_congr rfl fun f _ => by rw [hScard f], sum_const, card_univ, nsmul_eq_mul]
    have e2 : ∑ j ∈ univ.powersetCard n, (1 - p) ^ (T j).card =
        (N.choose n : ℝ) * (1 - p) ^ n.choose 2 := by
      rw [sum_congr rfl fun j hj => by rw [hTcard j hj], sum_const, card_powersetCard, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [e1, e2, Fintype.card_embedding_eq, Fintype.card_fin]
    refine lt_of_le_of_lt ?_ h
    have h1p : 0 ≤ 1 - p := by linarith
    gcongr
    · exact_mod_cast Nat.descFactorial_le_pow _ _
    · exact_mod_cast Nat.choose_le_pow _ _
  obtain ⟨A, -, hA1, hA2⟩ := exists_avoid hp0 hp1 E univ S hSE (univ.powersetCard n) T hTE hsum
  refine ⟨fromEdgeSet (A : Set (Sym2 (Fin N))), ?_, ?_⟩
  · rintro ⟨g⟩
    apply hA1 g.toEmbedding (mem_univ _)
    intro e he
    obtain ⟨e', he', rfl⟩ := mem_image.mp he
    induction e' using Sym2.ind with
    | h a b =>
      have hadj : G.Adj a b := by simpa using he'
      have := g.toHom.map_adj hadj
      rw [fromEdgeSet_adj] at this
      simpa [Copy.toEmbedding] using this.1
  · rintro ⟨g⟩
    have hj : univ.image g ∈ univ.powersetCard n := by
      rw [mem_powersetCard]
      exact ⟨subset_univ _, by rw [card_image_of_injective _ (show Function.Injective ⇑g from fun a b h => g.injective h)]; simp⟩
    apply hA2 _ hj
    rw [Finset.disjoint_left]
    intro e he heA
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp he
    obtain ⟨hx, hy, hne⟩ := mem_offDiag.mp hxy
    obtain ⟨a, -, rfl⟩ := mem_image.mp hx
    obtain ⟨b, -, rfl⟩ := mem_image.mp hy
    have hab : a ≠ b := fun h => hne (by rw [h])
    have := g.toHom.map_adj (show (⊤ : SimpleGraph (Fin n)).Adj a b from hab)
    rw [compl_adj, fromEdgeSet_adj] at this
    exact this.2 ⟨by simpa using heA, hne⟩

/-- `C(2k² + 1, 2) = k · (k · (2k² + 1))`. -/
lemma choose_two_eq (k : ℕ) : (2 * k ^ 2 + 1).choose 2 = k * (k * (2 * k ^ 2 + 1)) := by
  rw [Nat.choose_two_right, show 2 * k ^ 2 + 1 - 1 = 2 * k ^ 2 by omega,
    show (2 * k ^ 2 + 1) * (2 * k ^ 2) = 2 * (k * (k * (2 * k ^ 2 + 1))) by ring,
    Nat.mul_div_cancel_left _ two_pos]

lemma exp_neg_one_lt_half : Real.exp (-1) < 1 / 2 := by
  have h := Real.add_one_lt_exp (x := 1) one_ne_zero
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

/-- The numerical heart of the first-moment bound. -/
lemma first_moment_bound {C' v e k : ℕ} (hC : 1 ≤ C') (hv : 1 ≤ v) (he : 5 * v ≤ e)
    (hk1 : 1 ≤ k) (hk2 : 18 * C' ≤ k) (hk3 : 36 * C' * k ^ 4 ≤ 2 ^ k) :
    ((C' * (2 * k ^ 2 + 1) ^ 2 : ℕ) : ℝ) ^ v * (1 / (k : ℝ)) ^ e +
      ((C' * (2 * k ^ 2 + 1) ^ 2 : ℕ) : ℝ) ^ (2 * k ^ 2 + 1) *
        (1 - 1 / (k : ℝ)) ^ (2 * k ^ 2 + 1).choose 2 < 1 := by
  set n := 2 * k ^ 2 + 1 with hn
  set N := C' * n ^ 2 with hN
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < k := by linarith
  have hNle : (N : ℝ) ≤ 9 * C' * k ^ 4 := by
    have : n ^ 2 ≤ 9 * k ^ 4 := by
      have : n ≤ 3 * k ^ 2 := by have := Nat.one_le_pow 2 k hk1; omega
      calc n ^ 2 ≤ (3 * k ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
        _ = 9 * k ^ 4 := by ring
    have : N ≤ 9 * C' * k ^ 4 := by
      calc N = C' * n ^ 2 := rfl
        _ ≤ C' * (9 * k ^ 4) := Nat.mul_le_mul_left _ this
        _ = 9 * C' * k ^ 4 := by ring
    exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  -- first term `≤ 1/2`
  have h1 : (N : ℝ) ^ v * (1 / (k : ℝ)) ^ e ≤ 1 / 2 := by
    have hq0 : (0 : ℝ) ≤ 1 / k := by positivity
    have hq1 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact hkR
    calc (N : ℝ) ^ v * (1 / (k : ℝ)) ^ e ≤ (N : ℝ) ^ v * (1 / (k : ℝ)) ^ (5 * v) := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 he) (by positivity)
      _ = ((N : ℝ) * (1 / (k : ℝ)) ^ 5) ^ v := by rw [mul_pow, pow_mul]
      _ ≤ (1 / 2) ^ v := by
          gcongr
          rw [one_div_pow, ← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
          have hC18 : (18 : ℝ) * C' ≤ k := by exact_mod_cast hk2
          calc (N : ℝ) ≤ 9 * C' * k ^ 4 := hNle
            _ = (18 * C') * k ^ 4 / 2 := by ring
            _ ≤ k * k ^ 4 / 2 := by gcongr
            _ = 1 / 2 * k ^ 5 := by ring
      _ ≤ 1 / 2 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  -- second term `≤ 1/4`
  have h2 : (N : ℝ) ^ n * (1 - 1 / (k : ℝ)) ^ n.choose 2 ≤ 1 / 4 := by
    have hb0 : (0 : ℝ) ≤ 1 - 1 / k := by
      have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact hkR
      linarith
    have hexp : (1 - 1 / (k : ℝ)) ^ k ≤ 1 / 2 :=
      (Real.one_sub_div_pow_le_exp_neg (by simpa using hkR)).trans exp_neg_one_lt_half.le
    calc (N : ℝ) ^ n * (1 - 1 / (k : ℝ)) ^ n.choose 2
        = (N : ℝ) ^ n * ((1 - 1 / (k : ℝ)) ^ k) ^ (k * n) := by
          rw [choose_two_eq, ← pow_mul]
      _ ≤ (N : ℝ) ^ n * (1 / 2) ^ (k * n) := by gcongr
      _ = ((N : ℝ) * (1 / 2) ^ k) ^ n := by rw [mul_pow, pow_mul]
      _ ≤ (1 / 4) ^ n := by
          gcongr
          rw [one_div_pow, ← div_eq_mul_one_div, div_le_iff₀ (by positivity)]
          have : (36 : ℝ) * C' * k ^ 4 ≤ 2 ^ k := by exact_mod_cast hk3
          nlinarith
      _ ≤ 1 / 4 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

/-- Suitable `k` exist. -/
lemma exists_good_k (C' : ℕ) (hC : 1 ≤ C') :
    ∃ k : ℕ, 1 ≤ k ∧ 18 * C' ≤ k ∧ 36 * C' * k ^ 4 ≤ 2 ^ k := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 4 (r := 2) (by norm_num)
  have hε : (0 : ℝ) < 1 / (36 * C') := by positivity
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (ht.eventually (Iic_mem_nhds hε))
  refine ⟨max K (18 * C'), by omega, le_max_right _ _, ?_⟩
  have h := hK (max K (18 * C')) (le_max_left _ _)
  set k := max K (18 * C')
  try simp only [Set.mem_Iic] at h
  rw [div_le_iff₀ (by positivity)] at h
  have : (36 * C' * k ^ 4 : ℝ) ≤ 2 ^ k := by
    have h36 : (0 : ℝ) < 36 * C' := by positivity
    calc (36 * C' * k ^ 4 : ℝ) = 36 * C' * ((k : ℝ) ^ 4) := by ring
      _ ≤ 36 * C' * (1 / (36 * C') * 2 ^ k) := by gcongr
      _ = 2 ^ k := by field_simp
  exact_mod_cast this

/-- **Dense graphs are not Ramsey size-linear.** If `e(G) ≥ 5 v(G)` and `G` has a vertex,
then `R(G, K_n) / e(K_n)` is unbounded. -/
theorem not_isRamseySizeLinear_of_dense' [Fintype α] [Nonempty α] (G : SimpleGraph α)
    (h : 5 * Fintype.card α ≤ G.edgeSet.ncard) : ¬ G.IsRamseySizeLinear := by
  rintro ⟨c, hc, hlin⟩
  set C' := ⌈c⌉₊ + 1 with hC'
  have hC1 : 1 ≤ C' := by omega
  have hv : 1 ≤ Fintype.card α := Fintype.card_pos
  have he : 5 * Fintype.card α ≤ G.edgeFinset.card := by
    rwa [← Set.ncard_coe_finset, coe_edgeFinset]
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_good_k C' hC1
  set n := 2 * k ^ 2 + 1 with hn
  set N := C' * n ^ 2 with hN
  have hp1 : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hk1)]; exact_mod_cast hk1
  obtain ⟨C0, h1, h2⟩ := exists_good_graph G N n (p := 1 / k) (by positivity) hp1
    (first_moment_bound hC1 hv he hk1 hk2 hk3)
  have hlt := lt_graphRamsey C0 h1 h2
  have hn2 : 2 ≤ n := by have := Nat.one_le_pow 2 k hk1; omega
  have hR := hlin n ⊤ (fun v => by
    rw [complete_graph_degree, Fintype.card_fin]; omega)
  have hE : (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
    rw [← coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin]
  rw [hE] at hR
  have hch : (n.choose 2 : ℝ) ≤ n ^ 2 := by exact_mod_cast Nat.choose_le_pow n 2
  have hcC : c < C' := by
    rw [hC']; push_cast; linarith [Nat.le_ceil c]
  have hn0 : (0 : ℝ) < n ^ 2 := by positivity
  have : (N : ℝ) < N := by
    calc (N : ℝ) < graphRamsey G (⊤ : SimpleGraph (Fin n)) := by exact_mod_cast hlt
      _ ≤ c * n.choose 2 := hR
      _ ≤ c * n ^ 2 := by gcongr
      _ < C' * n ^ 2 := by gcongr
      _ = N := by rw [hN]; push_cast; ring
  exact lt_irrefl _ this

end Erdos79Proof
