import Mathlib.Tactic

/-!
# A finite first-moment principle

Subsets `A` of a finite ground set `E` are weighted by `p ^ |A| * (1 - p) ^ |E \ A|`, the law of
the random subset containing each element independently with probability `p`. We only need:

* the total weight is `1`;
* the weight of `{A | S ⊆ A}` is `p ^ |S|` and the weight of `{A | Disjoint S A}` is
  `(1 - p) ^ |S|`;
* hence (union bound) if `∑ p ^ |Sᵢ| + ∑ (1 - p) ^ |Tⱼ| < 1`, some `A ⊆ E` contains no `Sᵢ`
  and meets every `Tⱼ`.
-/

open Finset

namespace Erdos79Proof

variable {β : Type*} [DecidableEq β]

/-- The weight of `A ⊆ E` in the random subset of `E` with density `p`. -/
noncomputable def wt (p : ℝ) (E A : Finset β) : ℝ := p ^ A.card * (1 - p) ^ (E \ A).card

lemma wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E A : Finset β) : 0 ≤ wt p E A :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- `ℙ(S ⊆ A) = p ^ |S|`. -/
lemma sum_wt_superset (p : ℝ) {E S : Finset β} (hS : S ⊆ E) :
    ∑ A ∈ E.powerset, (if S ⊆ A then wt p E A else 0) = p ^ S.card := by
  have h := prod_add (fun _ => p) (fun e => if e ∈ S then (0 : ℝ) else 1 - p) E
  have hL : ∏ e ∈ E, (p + if e ∈ S then (0 : ℝ) else 1 - p) = p ^ S.card := by
    have : ∀ e ∈ E, (p + if e ∈ S then (0 : ℝ) else 1 - p) = if e ∈ S then p else 1 := by
      intro e _; split_ifs <;> ring
    rw [prod_congr rfl this, prod_ite_mem, inter_eq_right.mpr hS, prod_const]
  rw [hL] at h
  rw [h]
  refine sum_congr rfl fun A hA => ?_
  rw [prod_const]
  split_ifs with hSA
  · rw [wt]
    congr 1
    rw [prod_congr rfl fun e he => if_neg fun heS => (mem_sdiff.mp he).2 (hSA heS),
      prod_const]
  · obtain ⟨e, heS, heA⟩ := not_subset.mp hSA
    have h0 : ∏ i ∈ E \ A, (if i ∈ S then (0 : ℝ) else 1 - p) = 0 :=
      Finset.prod_eq_zero (mem_sdiff.mpr ⟨hS heS, heA⟩) (if_pos heS)
    rw [h0, mul_zero]

/-- `ℙ(S ∩ A = ∅) = (1 - p) ^ |S|`. -/
lemma sum_wt_disjoint (p : ℝ) {E S : Finset β} (hS : S ⊆ E) :
    ∑ A ∈ E.powerset, (if Disjoint S A then wt p E A else 0) = (1 - p) ^ S.card := by
  have h := prod_add (fun e => if e ∈ S then (0 : ℝ) else p) (fun _ => 1 - p) E
  have hL : ∏ e ∈ E, ((if e ∈ S then (0 : ℝ) else p) + (1 - p)) = (1 - p) ^ S.card := by
    have : ∀ e ∈ E, ((if e ∈ S then (0 : ℝ) else p) + (1 - p)) = if e ∈ S then 1 - p else 1 := by
      intro e _; split_ifs <;> ring
    rw [prod_congr rfl this, prod_ite_mem, inter_eq_right.mpr hS, prod_const]
  rw [hL] at h
  rw [h]
  refine sum_congr rfl fun A hA => ?_
  rw [prod_const]
  split_ifs with hSA
  · rw [wt]
    congr 1
    rw [prod_congr rfl fun e he => if_neg fun heS => disjoint_left.mp hSA heS he, prod_const]
  · obtain ⟨e, heS, heA⟩ := not_disjoint_iff.mp hSA
    have h0 : ∏ i ∈ A, (if i ∈ S then (0 : ℝ) else p) = 0 :=
      Finset.prod_eq_zero heA (if_pos heS)
    rw [h0, zero_mul]

lemma sum_wt (p : ℝ) (E : Finset β) : ∑ A ∈ E.powerset, wt p E A = 1 := by
  simpa using sum_wt_superset p (empty_subset E)

/-- **Union bound.** If the expected number of "bad" events is below `1`, some outcome avoids all
of them: some `A ⊆ E` contains none of the `S i` and meets every `T j`. -/
lemma exists_avoid {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset β)
    {ι κ : Type*} (I : Finset ι) (S : ι → Finset β) (hS : ∀ i ∈ I, S i ⊆ E)
    (J : Finset κ) (T : κ → Finset β) (hT : ∀ j ∈ J, T j ⊆ E)
    (h : ∑ i ∈ I, p ^ (S i).card + ∑ j ∈ J, (1 - p) ^ (T j).card < 1) :
    ∃ A ⊆ E, (∀ i ∈ I, ¬ S i ⊆ A) ∧ (∀ j ∈ J, ¬ Disjoint (T j) A) := by
  by_contra hcon
  push Not at hcon
  -- every outcome is bad: `1 ≤ #bad events`
  have hbad : ∀ A ∈ E.powerset, wt p E A ≤
      ∑ i ∈ I, (if S i ⊆ A then wt p E A else 0) +
        ∑ j ∈ J, (if Disjoint (T j) A then wt p E A else 0) := by
    intro A hA
    have hw := wt_nonneg hp0 hp1 E A
    have hnn1 : ∀ i ∈ I, 0 ≤ (if S i ⊆ A then wt p E A else 0) := fun i _ => by
      split_ifs <;> linarith
    have hnn2 : ∀ j ∈ J, 0 ≤ (if Disjoint (T j) A then wt p E A else 0) := fun j _ => by
      split_ifs <;> linarith
    by_cases hA' : ∃ i ∈ I, S i ⊆ A
    · obtain ⟨i, hi, hiA⟩ := hA'
      have := single_le_sum hnn1 hi
      rw [if_pos hiA] at this
      linarith [sum_nonneg hnn2]
    · push Not at hA'
      obtain ⟨j, hj, hjA⟩ := hcon A (mem_powerset.mp hA) hA'
      have := single_le_sum hnn2 hj
      rw [if_pos hjA] at this
      linarith [sum_nonneg hnn1]
  have := sum_le_sum hbad
  rw [sum_wt, sum_add_distrib, sum_comm, sum_comm (s := E.powerset)] at this
  rw [sum_congr rfl fun i hi => sum_wt_superset p (hS i hi),
    sum_congr rfl fun j hj => sum_wt_disjoint p (hT j hj)] at this
  linarith

/-- `𝔼|A| = p |E|`. -/
lemma sum_wt_mul_card (p : ℝ) (E : Finset β) :
    ∑ A ∈ E.powerset, wt p E A * A.card = p * E.card := by
  have h : ∀ A ∈ E.powerset,
      wt p E A * (A.card : ℝ) = ∑ e ∈ E, (if {e} ⊆ A then wt p E A else 0) := by
    intro A hA
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    rw [filter_congr fun e _ => singleton_subset_iff, filter_mem_eq_inter,
      inter_eq_right.mpr (mem_powerset.mp hA)]
  rw [sum_congr rfl h, sum_comm,
    sum_congr rfl fun e he => sum_wt_superset p (singleton_subset_iff.mpr he)]
  simp [mul_comm]

/-- **Averaging.** If `𝔼 X ≥ m` (and `p > 0`), some outcome has `X ≥ m`. -/
lemma exists_ge {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (E : Finset β) (X : Finset β → ℝ) (m : ℝ)
    (h : m ≤ ∑ A ∈ E.powerset, wt p E A * X A) : ∃ A ⊆ E, m ≤ X A := by
  by_contra hcon
  push Not at hcon
  have hlt : ∑ A ∈ E.powerset, wt p E A * X A < ∑ A ∈ E.powerset, wt p E A * m := by
    apply sum_lt_sum
    · intro A hA
      exact mul_le_mul_of_nonneg_left (hcon A (mem_powerset.mp hA)).le
        (wt_nonneg hp0.le hp1 E A)
    · refine ⟨E, mem_powerset_self E, mul_lt_mul_of_pos_left (hcon E subset_rfl) ?_⟩
      rw [wt, sdiff_self]
      exact mul_pos (pow_pos hp0 _) (by simp)
  rw [← sum_mul, sum_wt, one_mul] at hlt
  linarith

end Erdos79Proof
