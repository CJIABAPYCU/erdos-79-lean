import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# Forests are Ramsey size-linear

For a forest `F` on `k` vertices and a graph `C` not containing `F`, the graph `C` has an
independent set of size at least `|V(C)| / k` (repeatedly remove a vertex of degree `≤ k - 2`
together with its neighbourhood). Hence `R(F, H) ≤ k · v(H) ≤ 2k · e(H)` whenever `H` has no
isolated vertices.
-/

open SimpleGraph Finset

open scoped Classical

namespace Erdos79Proof

variable {α W : Type*}

/-- Every nonempty set of vertices of a forest contains a vertex with at most one neighbour in
the set. -/
lemma exists_card_filter_adj_le_one {F : SimpleGraph α} (hF : F.IsAcyclic)
    (t : Finset α) (ht : t.Nonempty) : ∃ v ∈ t, (t.filter (F.Adj v)).card ≤ 1 := by
  let F' := F.induce (t : Set α)
  have hF' : F'.IsAcyclic := hF.induce _
  have : Nonempty (t : Set α) := ⟨⟨ht.choose, by simpa using ht.choose_spec⟩⟩
  obtain ⟨T, hle, hmax⟩ := exists_maximal_isAcyclic_of_le_isAcyclic (G := ⊤) le_top hF'
  have hT : T.IsTree := (connected_top (V := (t : Set α))).maximal_le_isAcyclic_iff_isTree le_top
    |>.mp hmax
  -- bound the number of neighbours of `w ∈ t` inside `t` by `T.degree`
  have key : ∀ w : (t : Set α), (t.filter (F.Adj w)).card ≤ T.degree w := by
    intro w
    rw [← card_neighborFinset_eq_degree]
    refine card_le_card_of_injOn (fun x => if hx : x ∈ (t : Set α) then ⟨x, hx⟩ else w) ?_ ?_
    · intro x hx
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      simp only [hx.1, dite_true, coe_neighborFinset, mem_coe]
      exact hle (show F'.Adj w ⟨x, hx.1⟩ from hx.2)
    · intro x hx y hy hxy
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
      simpa [hx.1, hy.1] using hxy
  by_cases hnt : Nontrivial (t : Set α)
  · obtain ⟨w, hw⟩ := hT.exists_vert_degree_one_of_nontrivial
    exact ⟨w, by simp, (key w).trans hw.le⟩
  · obtain ⟨v, hv⟩ := ht
    refine ⟨v, hv, ?_⟩
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : t.filter (F.Adj v) = ∅ := by
      refine filter_false_of_mem fun x hx hadj => ?_
      have : (⟨x, hx⟩ : (t : Set α)) = ⟨v, hv⟩ := Subsingleton.elim _ _
      exact hadj.ne (congrArg Subtype.val this).symm
    simp [this]

/-- Greedy embedding: a forest on `k` vertices embeds into any graph containing a nonempty set
`s` of vertices each having at least `k - 1` neighbours in `s`. -/
lemma embed_forest_aux [Fintype α] {F : SimpleGraph α} (hF : F.IsAcyclic) (C : SimpleGraph W)
    (s : Finset W) (hs : ∀ v ∈ s, Fintype.card α - 1 ≤ (s.filter (C.Adj v)).card)
    (hne : s.Nonempty) (t : Finset α) :
    ∃ f : α → W, (∀ a ∈ t, f a ∈ s) ∧ Set.InjOn f t ∧
      ∀ a ∈ t, ∀ b ∈ t, F.Adj a b → C.Adj (f a) (f b) := by
  induction t using Finset.strongInduction with
  | H t ih =>
  rcases t.eq_empty_or_nonempty with rfl | htne
  · exact ⟨fun _ => hne.choose, by simp, by simp, by simp⟩
  obtain ⟨v, hvt, hv⟩ := exists_card_filter_adj_le_one hF t htne
  obtain ⟨f, hfs, hfinj, hfadj⟩ := ih (t.erase v) (erase_ssubset hvt)
  have htk : t.card ≤ Fintype.card α := card_le_univ t
  have hte : (t.erase v).card + 1 = t.card := card_erase_add_one hvt
  -- choose the image `w` of `v`
  obtain ⟨w, hws, hwnot, hwadj⟩ : ∃ w ∈ s, w ∉ (t.erase v).image f ∧
      ∀ u ∈ t.erase v, F.Adj v u → C.Adj (f u) w := by
    by_cases hex : ∃ u ∈ t.erase v, F.Adj v u
    · obtain ⟨u, hu, hvu⟩ := hex
      have huniq : ∀ u' ∈ t.erase v, F.Adj v u' → u' = u := by
        intro u' hu' hvu'
        exact card_le_one.mp hv u' (mem_filter.mpr ⟨mem_of_mem_erase hu', hvu'⟩) u
          (mem_filter.mpr ⟨mem_of_mem_erase hu, hvu⟩)
      have hA := hs (f u) (hfs u hu)
      have hB : (((t.erase v).erase u).image f).card ≤ Fintype.card α - 2 := by
        have := card_image_le (s := (t.erase v).erase u) (f := f)
        have := card_erase_add_one hu
        omega
      have hk : 2 ≤ Fintype.card α := by
        have : 1 ≤ (t.erase v).card := card_pos.mpr ⟨u, hu⟩
        omega
      obtain ⟨w, hwA, hwB⟩ := exists_mem_notMem_of_card_lt_card
        (s := ((t.erase v).erase u).image f) (t := s.filter (C.Adj (f u))) (by omega)
      rw [mem_filter] at hwA
      refine ⟨w, hwA.1, ?_, ?_⟩
      · intro hw
        obtain ⟨u', hu', rfl⟩ := mem_image.mp hw
        by_cases h : u' = u
        · subst h; exact hwA.2.ne rfl
        · exact hwB (mem_image.mpr ⟨u', mem_erase.mpr ⟨h, hu'⟩, rfl⟩)
      · intro u' hu' hvu'
        rw [huniq u' hu' hvu']
        exact hwA.2
    · push Not at hex
      obtain ⟨x, hx⟩ := hne
      have hsx : (s.filter (C.Adj x)).card + 1 ≤ s.card := by
        have : s.filter (C.Adj x) ⊂ s :=
          ⟨filter_subset _ _, fun h => (mem_filter.mp (h hx)).2.ne rfl⟩
        exact card_lt_card this
      have := hs x hx
      have := card_image_le (s := t.erase v) (f := f)
      obtain ⟨w, hw, hwnot⟩ := exists_mem_notMem_of_card_lt_card
        (s := (t.erase v).image f) (t := s) (by omega)
      exact ⟨w, hw, hwnot, fun u hu hvu => absurd hvu (hex u hu)⟩
  have hfw : ∀ a ∈ t.erase v, f a ≠ w := fun a ha h => hwnot (mem_image.mpr ⟨a, ha, h⟩)
  refine ⟨Function.update f v w, ?_, ?_, ?_⟩
  · intro a ha
    by_cases h : a = v
    · subst h; simpa using hws
    · simpa [h] using hfs a (mem_erase.mpr ⟨h, ha⟩)
  · intro a ha b hb hab
    simp only [mem_coe] at ha hb
    by_cases h1 : a = v <;> by_cases h2 : b = v
    · rw [h1, h2]
    · subst h1
      simp only [Function.update_self, Function.update_of_ne h2] at hab
      exact absurd hab.symm (hfw b (mem_erase.mpr ⟨h2, hb⟩))
    · subst h2
      simp only [Function.update_self, Function.update_of_ne h1] at hab
      exact absurd hab (hfw a (mem_erase.mpr ⟨h1, ha⟩))
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2] at hab
      exact hfinj (mem_erase.mpr ⟨h1, ha⟩) (mem_erase.mpr ⟨h2, hb⟩) hab
  · intro a ha b hb hab
    by_cases h1 : a = v <;> by_cases h2 : b = v
    · subst h1; subst h2; exact (hab.ne rfl).elim
    · subst h1
      simp only [Function.update_self, Function.update_of_ne h2]
      exact (hwadj b (mem_erase.mpr ⟨h2, hb⟩) hab).symm
    · subst h2
      simp only [Function.update_self, Function.update_of_ne h1]
      exact hwadj a (mem_erase.mpr ⟨h1, ha⟩) hab.symm
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hfadj a (mem_erase.mpr ⟨h1, ha⟩) b (mem_erase.mpr ⟨h2, hb⟩) hab

lemma isContained_of_forall_le_card_filter [Fintype α] {F : SimpleGraph α} (hF : F.IsAcyclic)
    (C : SimpleGraph W) (s : Finset W)
    (hs : ∀ v ∈ s, Fintype.card α - 1 ≤ (s.filter (C.Adj v)).card) (hne : s.Nonempty) :
    F ⊑ C := by
  obtain ⟨f, -, hinj, hadj⟩ := embed_forest_aux hF C s hs hne univ
  exact ⟨⟨⟨f, fun {a b} h => hadj a (mem_univ a) b (mem_univ b) h⟩,
    fun a b h => hinj (by simp) (by simp) h⟩⟩

/-- A graph not containing the forest `F` on `k` vertices has, inside any finite vertex set `s`,
an independent set `I` with `|s| ≤ k · |I|`. -/
lemma exists_indep_of_free [Fintype α] {F : SimpleGraph α} (hF : F.IsAcyclic) {C : SimpleGraph W}
    (hfree : F.Free C) (s : Finset W) :
    ∃ I ⊆ s, (I : Set W).Pairwise (fun a b => ¬ C.Adj a b) ∧
      s.card ≤ Fintype.card α * I.card := by
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨v, hv, hvdeg⟩ : ∃ v ∈ s, (s.filter (C.Adj v)).card < Fintype.card α - 1 := by
    by_contra h
    push Not at h
    exact hfree (isContained_of_forall_le_card_filter hF C s h hne)
  set N := insert v (s.filter (C.Adj v))
  have hNs : N ⊆ s := insert_subset hv (filter_subset _ _)
  have hNcard : N.card ≤ Fintype.card α - 1 := (card_insert_le _ _).trans (by omega)
  obtain ⟨I, hIs, hIind, hIcard⟩ := ih (s \ N)
    (sdiff_ssubset hNs ⟨v, mem_insert_self _ _⟩)
  have hvI : v ∉ I := fun h => (mem_sdiff.mp (hIs h)).2 (mem_insert_self _ _)
  refine ⟨insert v I, insert_subset hv (hIs.trans sdiff_subset), ?_, ?_⟩
  · rw [coe_insert]
    refine hIind.insert fun b hb _ => ?_
    have hbN : b ∉ N := (mem_sdiff.mp (hIs hb)).2
    have hnot : ¬ C.Adj v b := fun h =>
      hbN (mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp (hIs hb)).1, h⟩))
    exact ⟨hnot, fun h => hnot h.symm⟩
  · rw [card_insert_of_notMem hvI, mul_add, mul_one]
    rw [card_sdiff_of_subset hNs] at hIcard
    have := card_le_card hNs
    omega

/-- **Forests are Ramsey size-linear.** -/
theorem isRamseySizeLinear_of_isAcyclic' [Fintype α] {F : SimpleGraph α} (hF : F.IsAcyclic) :
    F.IsRamseySizeLinear := by
  refine ⟨2 * Fintype.card α + 1, by positivity, fun n H _ hH => ?_⟩
  -- `n ≤ 2 e(H)`
  have hn : n ≤ 2 * H.edgeSet.ncard := by
    have h1 := H.sum_degrees_eq_twice_card_edges
    have h2 : ∑ v : Fin n, 1 ≤ ∑ v : Fin n, H.degree v := sum_le_sum fun v _ => hH v
    rw [← Set.ncard_coe_finset, coe_edgeFinset] at h1
    simpa using h2.trans h1.le
  -- `R(F, H) ≤ k n`
  have hR : graphRamsey F H ≤ Fintype.card α * n := by
    refine Nat.sInf_le fun C => ?_
    by_cases hfree : F.Free C
    · right
      obtain ⟨I, -, hIind, hIcard⟩ := exists_indep_of_free hF hfree (univ : Finset (Fin _))
      rw [card_univ, Fintype.card_fin] at hIcard
      have hnI : n ≤ I.card := by
        rcases Nat.eq_zero_or_pos (Fintype.card α) with hk | hk
        · exfalso; apply hfree
          have : IsEmpty α := Fintype.card_eq_zero_iff.mp hk
          exact IsContained.of_isEmpty
        · exact Nat.le_of_mul_le_mul_left hIcard hk
      obtain ⟨e⟩ : Nonempty (Fin n ↪ I) := by
        rw [Function.Embedding.nonempty_iff_card_le]; simpa using hnI
      refine (IsContained.of_le (le_top : H ≤ ⊤)).trans ⟨⟨⟨fun a => (e a).1, ?_⟩, ?_⟩⟩
      · intro a b hab
        have hne : (e a).1 ≠ (e b).1 := fun h => hab.ne (e.injective (Subtype.ext h))
        exact ⟨hne, hIind (e a).2 (e b).2 hne⟩
      · intro a b h; exact e.injective (Subtype.ext h)
    · left; exact not_not.mp hfree
  calc (graphRamsey F H : ℝ) ≤ Fintype.card α * n := by exact_mod_cast hR
    _ ≤ Fintype.card α * (2 * H.edgeSet.ncard) := by gcongr; exact_mod_cast hn
    _ ≤ (2 * Fintype.card α + 1) * H.edgeSet.ncard := by nlinarith

end Erdos79Proof
