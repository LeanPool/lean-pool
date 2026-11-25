/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026), part A: convex polytopes as bounded
finite
intersections of closed half-spaces, and the refinement argument.

Main result `dissection_additive`: a set function that is additive under every single plane cut of
a convex
polytope is additive over every dissection of a convex polytope into convex polytopes.
(Classical argument: refine the dissection by all the facet planes of the pieces.)
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The solution set of a system of linear inequalities `⟪a i, x⟫ ≤ b i`. -/
def sol {ι : Type} (a : ι → E) (b : ι → ℝ) : Set E := {x | ∀ i, ⟪a i, x⟫ ≤ b i}

/-- The closed half-space `⟪c, x⟫ ≤ d`. -/
def hsLe (c : E) (d : ℝ) : Set E := {x | ⟪c, x⟫ ≤ d}

/-- The opposite closed half-space `d ≤ ⟪c, x⟫`. -/
def hsGe (c : E) (d : ℝ) : Set E := hsLe (-c) (-d)

lemma mem_hsLe {c : E} {d : ℝ} {x : E} : x ∈ hsLe c d ↔ ⟪c, x⟫ ≤ d := Iff.rfl

lemma mem_hsGe {c : E} {d : ℝ} {x : E} : x ∈ hsGe c d ↔ d ≤ ⟪c, x⟫ := by
  simp [hsGe, hsLe, inner_neg_left]

/-- A convex polytope: a bounded intersection of finitely many closed half-spaces. -/
def IsPoly (P : Set E) : Prop :=
  Bornology.IsBounded P ∧ ∃ (ι : Type) (_ : Fintype ι) (a : ι → E) (b : ι → ℝ), P = sol a b

lemma isClosed_sol {ι : Type} (a : ι → E) (b : ι → ℝ) : IsClosed (sol a b) := by
  have : sol a b = ⋂ i, {x | ⟪a i, x⟫ ≤ b i} := by ext x; simp [sol]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

lemma convex_sol {ι : Type} (a : ι → E) (b : ι → ℝ) : Convex ℝ (sol a b) := by
  intro x hx y hy s t hs ht hst
  change ∀ i, ⟪a i, s • x + t • y⟫ ≤ b i
  intro i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  calc s * ⟪a i, x⟫ + t * ⟪a i, y⟫ ≤ s * b i + t * b i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) hs) (mul_le_mul_of_nonneg_left (hy i) ht)
    _ = b i := by rw [← add_mul, hst, one_mul]

lemma IsPoly.isClosed {P : Set E} (hP : IsPoly P) : IsClosed P := by
  obtain ⟨-, ι, _, a, b, rfl⟩ := hP; exact isClosed_sol a b

lemma IsPoly.convex {P : Set E} (hP : IsPoly P) : Convex ℝ P := by
  obtain ⟨-, ι, _, a, b, rfl⟩ := hP; exact convex_sol a b

lemma sol_inter_hsLe {ι : Type} (a : ι → E) (b : ι → ℝ) (c : E) (d : ℝ) :
    sol a b ∩ hsLe c d = sol (fun o : Option ι => o.elim c a) (fun o : Option ι => o.elim d b) := by
  ext x
  simp only [sol, hsLe, mem_inter_iff, mem_ofPred_eq, Option.forall, Option.elim]
  tauto

lemma IsPoly.inter_hsLe {P : Set E} (hP : IsPoly P) (c : E) (d : ℝ) : IsPoly (P ∩ hsLe c d) := by
  obtain ⟨hb, ι, _, a, b, rfl⟩ := hP
  exact ⟨hb.subset inter_subset_left, Option ι, inferInstance, _, _, sol_inter_hsLe a b c d⟩

lemma IsPoly.inter_hsGe {P : Set E} (hP : IsPoly P) (c : E) (d : ℝ) : IsPoly (P ∩ hsGe c d) :=
  hP.inter_hsLe (-c) (-d)

/-- A set squeezed into a plane has empty interior. -/
lemma interior_inter_eq_empty {S C : Set E} {c : E} {d : ℝ} (hC : ¬ C ⊆ hsLe c d)
    (hC' : c ≠ 0 → C ⊆ hsGe c d) (hS : S ⊆ hsLe c d) : interior (S ∩ C) = ∅ := by
  by_cases hc : c = 0
  · subst hc
    obtain ⟨x, hxC, hx⟩ := Set.not_subset.1 hC
    have hd : d < 0 := by simpa [hsLe] using hx
    have hSe : S = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      have h1 := hS hy
      simp only [hsLe, mem_ofPred_eq, inner_zero_left] at h1
      linarith
    simp [hSe]
  · have hC2 := hC' hc
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hx' : (S ∩ C) ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
    have hcont : Continuous fun t : ℝ => x + t • c := by fun_prop
    have h0 : (fun t : ℝ => x + t • c) ⁻¹' (S ∩ C) ∈ nhds (0 : ℝ) := by
      apply hcont.continuousAt.preimage_mem_nhds
      simpa using hx'
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h0
    have hmem : (ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
    have h1 : x + (ε / 2) • c ∈ S ∩ C := hball hmem
    have hxm : x ∈ S ∩ C := mem_of_mem_nhds hx'
    have e1 : ⟪c, x⟫ = d := le_antisymm (hS hxm.1) (mem_hsGe.1 (hC2 hxm.2))
    have e2 : ⟪c, x + (ε / 2) • c⟫ = d := le_antisymm (hS h1.1) (mem_hsGe.1 (hC2 h1.2))
    rw [inner_add_right, inner_smul_right, e1, real_inner_self_eq_norm_sq] at e2
    have h3 : 0 < ‖c‖ ^ 2 := pow_pos (norm_pos_iff.2 hc) 2
    have h4 := mul_pos (half_pos hε) h3
    linarith

/-- A convex set with empty interior lies in a plane. -/
lemma exists_plane_of_interior_empty [FiniteDimensional ℝ E] {Q : Set E} (hQ : Convex ℝ Q)
    (hne : Q.Nonempty) (hint : interior Q = ∅) :
    ∃ (n : E) (e : ℝ), n ≠ 0 ∧ ∀ x ∈ Q, ⟪n, x⟫ = e := by
  have hspan : affineSpan ℝ Q ≠ ⊤ := by
    intro h
    have h1 := (hQ.interior_nonempty_iff_affineSpan_eq_top).2 h
    rw [hint] at h1; exact Set.not_nonempty_empty h1
  have hdir : (affineSpan ℝ Q).direction ≠ ⊤ := by
    intro h
    exact hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty
      (hne.mono (subset_affineSpan ℝ Q))).1 h)
  obtain ⟨n, hn, hn0⟩ : ∃ n ∈ (affineSpan ℝ Q).directionᗮ, n ≠ 0 := by
    have h1 : (affineSpan ℝ Q).directionᗮ ≠ ⊥ := by
      intro h; exact hdir (Submodule.orthogonal_eq_bot_iff.1 h)
    exact (Submodule.ne_bot_iff _).1 h1
  obtain ⟨x0, hx0⟩ := hne
  refine ⟨n, ⟪n, x0⟫, hn0, fun x hx => ?_⟩
  have hv : x - x0 ∈ (affineSpan ℝ Q).direction := by
    simpa using AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ Q hx)
        (subset_affineSpan ℝ Q hx0)
  have h2 : ⟪n, x - x0⟫ = 0 := (Submodule.mem_orthogonal' _ _).1 hn _ hv
  rw [inner_sub_right] at h2
  linarith

/-- Plane-cut additivity forces the value zero on polytopes with empty interior. -/
lemma flat_of_cut [FiniteDimensional ℝ E] [Nontrivial E] {A : Type*} [AddCommGroup A] (D : Set E
    → A)
    (hcut : ∀ Q, IsPoly Q → ∀ (c : E) (d : ℝ), c ≠ 0 → D Q = D (Q ∩ hsLe c d) + D (Q ∩ hsGe c d))
    {Q : Set E} (hQ : IsPoly Q) (hint : interior Q = ∅) : D Q = 0 := by
  rcases Q.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨c, hc⟩ := exists_ne (0 : E)
    have h := hcut ∅ hQ c 0 hc
    rw [empty_inter, empty_inter] at h
    have h2 : D (∅ : Set E) + D ∅ = D ∅ + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  · obtain ⟨n, e, hn, hne'⟩ := exists_plane_of_interior_empty hQ.convex hne hint
    have h := hcut Q hQ n e hn
    have h1 : Q ∩ hsLe n e = Q := inter_eq_left.2 fun x hx => (hne' x hx).le
    have h2 : Q ∩ hsGe n e = Q := inter_eq_left.2 fun x hx => mem_hsGe.2 (hne' x hx).ge
    rw [h1, h2] at h
    have h3 : D Q + D Q = D Q + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h3

/-- The cells of an arrangement of planes: every choice of a side for every plane. -/
def cells : List (E × ℝ) → List (Set E)
  | [] => [Set.univ]
  | h :: t => (cells t).map (fun C => C ∩ hsLe h.1 h.2) ++ (cells t).map (fun C => C ∩ hsGe h.1 h.2)

lemma cells_side : ∀ (L : List (E × ℝ)) (C : Set E), C ∈ cells L →
    ∀ h ∈ L, C ⊆ hsLe h.1 h.2 ∨ C ⊆ hsGe h.1 h.2
  | [], _, _, h, hh => by simp at hh
  | h0 :: t, C, hC, h, hh => by
    simp only [cells, List.mem_append, List.mem_map] at hC
    rcases hC with ⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩
    · rcases List.mem_cons.1 hh with rfl | hh'
      · exact Or.inl inter_subset_right
      · rcases cells_side t C' hC' h hh' with h1 | h1
        · exact Or.inl (inter_subset_left.trans h1)
        · exact Or.inr (inter_subset_left.trans h1)
    · rcases List.mem_cons.1 hh with rfl | hh'
      · exact Or.inr inter_subset_right
      · rcases cells_side t C' hC' h hh' with h1 | h1
        · exact Or.inl (inter_subset_left.trans h1)
        · exact Or.inr (inter_subset_left.trans h1)

lemma cells_poly : ∀ (L : List (E × ℝ)) (C : Set E), C ∈ cells L → ∀ Q : Set E, IsPoly Q
    → IsPoly (Q ∩ C)
  | [], C, hC, Q, hQ => by
    simp only [cells, List.mem_singleton] at hC
    subst hC; simpa using hQ
  | h0 :: t, C, hC, Q, hQ => by
    simp only [cells, List.mem_append, List.mem_map] at hC
    rcases hC with ⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩
    · rw [← inter_assoc]; exact (cells_poly t C' hC' Q hQ).inter_hsLe _ _
    · rw [← inter_assoc]; exact (cells_poly t C' hC' Q hQ).inter_hsGe _ _

/-- Cutting along a whole list of planes, one after the other. -/
lemma cells_sum {A : Type*} [AddCommMonoid A] (D : Set E → A)
    (hcut : ∀ Q, IsPoly Q → ∀ (c : E) (d : ℝ), c ≠ 0 → D Q = D (Q ∩ hsLe c d) + D (Q ∩ hsGe c d)) :
    ∀ (L : List (E × ℝ)), (∀ h ∈ L, h.1 ≠ 0) → ∀ Q, IsPoly Q →
      D Q = ((cells L).map fun C => D (Q ∩ C)).sum
  | [], _, Q, _ => by simp [cells]
  | h :: t, hL, Q, hQ => by
    have ht : ∀ h' ∈ t, h'.1 ≠ 0 := fun h' hh => hL h' (List.mem_cons_of_mem _ hh)
    have h1 := cells_sum D hcut t ht _ (hQ.inter_hsLe h.1 h.2)
    have h2 := cells_sum D hcut t ht _ (hQ.inter_hsGe h.1 h.2)
    have e1 : ∀ C : Set E, Q ∩ hsLe h.1 h.2 ∩ C = Q ∩ (C ∩ hsLe h.1 h.2) := fun C => by
      ext x; simp only [mem_inter_iff]; tauto
    have e2 : ∀ C : Set E, Q ∩ hsGe h.1 h.2 ∩ C = Q ∩ (C ∩ hsGe h.1 h.2) := fun C => by
      ext x; simp only [mem_inter_iff]; tauto
    rw [hcut Q hQ h.1 h.2 (hL h (by simp)), h1, h2]
    simp only [cells, List.map_append, List.map_map, List.sum_append, Function.comp_def, e1, e2]

lemma list_sum_finset_sum {A κ α : Type*} [AddCommMonoid A] (s : Finset κ) (l : List α) (g : κ → α
    → A) :
    (l.map fun C => ∑ k ∈ s, g k C).sum = ∑ k ∈ s, (l.map (g k)).sum := by
  induction l with
  | nil => simp
  | cons C l ih => simp [ih, Finset.sum_add_distrib]

omit [InnerProductSpace ℝ E] in
lemma interior_biUnion_empty {κ : Type*} (s : Finset κ) (f : κ → Set E) (hc : ∀ k, IsClosed (f k))
    (he : ∀ k, interior (f k) = ∅) : interior (⋃ k ∈ s, f k) = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, interior_union_isClosed_of_interior_empty (hc a) ih, he a]

/-- **The refinement argument.** A set function `D` that is additive under every cut of a convex
polytope by a
plane is additive over every dissection of a convex polytope into finitely many convex polytopes
(pieces cover it and have pairwise disjoint interiors). -/
theorem dissection_additive [FiniteDimensional ℝ E] [Nontrivial E] {A : Type*} [AddCommGroup A]
    (D : Set E → A)
    (hcut : ∀ Q, IsPoly Q → ∀ (c : E) (d : ℝ), c ≠ 0 → D Q = D (Q ∩ hsLe c d) + D (Q ∩ hsGe c d))
    {κ : Type} [Fintype κ] {P : Set E} {p : κ → Set E} (hP : IsPoly P) (hp : ∀ k, IsPoly (p k))
    (hU : (⋃ k, p k) = P)
    (hdisj : Pairwise fun i j => Disjoint (interior (p i)) (interior (p j))) :
    D P = ∑ k, D (p k) := by
  classical
  have hflat : ∀ Q : Set E, IsPoly Q → interior Q = ∅ → D Q = 0 :=
    fun Q hQ hint => flat_of_cut D hcut hQ hint
  have hpk : ∀ k, IsPoly (p k) := hp
  choose hbd ι inst a b hab using hp
  let L0 : List (E × ℝ) := (Finset.univ : Finset κ).toList.flatMap fun k =>
      (@Finset.univ (ι k) (inst k)).toList.map fun i => (a k i, b k i)
  let L : List (E × ℝ) := L0.filter fun h => decide (h.1 ≠ 0)
  have hLne : ∀ h ∈ L, h.1 ≠ 0 := by
    intro h hh; simpa using (List.mem_filter.1 hh).2
  have hLmem : ∀ k i, a k i ≠ 0 → (a k i, b k i) ∈ L := by
    intro k i hne
    refine List.mem_filter.2 ⟨?_, by simpa using hne⟩
    refine List.mem_flatMap.2 ⟨k, by simp, List.mem_map.2 ⟨i, ?_, rfl⟩⟩
    exact Finset.mem_toList.2 (@Finset.mem_univ _ (inst k) i)
  have hsub : ∀ k, p k ⊆ P := fun k => by rw [← hU]; exact subset_iUnion p k
  have key : ∀ C ∈ cells L, D (P ∩ C) = ∑ k, D (p k ∩ C) := by
    intro C hC
    have hdich : ∀ k, C ⊆ p k ∨ interior (p k ∩ C) = ∅ := by
      intro k
      by_cases h : ∀ i, C ⊆ hsLe (a k i) (b k i)
      · left; intro x hx; rw [hab k]; exact fun i => h i hx
      · right
        push Not at h
        obtain ⟨i, hi⟩ := h
        refine interior_inter_eq_empty hi (fun hne => ?_) ?_
        · rcases cells_side L C hC _ (hLmem k i hne) with h1 | h1
          · exact absurd h1 hi
          · exact h1
        · rw [hab k]; exact fun x hx => hx i
    have hpoly : ∀ k, IsPoly (p k ∩ C) := fun k => cells_poly L C hC _ (hpk k)
    by_cases hint : interior (P ∩ C) = ∅
    · rw [hflat _ (cells_poly L C hC _ hP) hint]
      symm; apply Finset.sum_eq_zero; intro k _
      apply hflat _ (hpoly k)
      apply Set.subset_empty_iff.1
      rw [← hint]; exact interior_mono (inter_subset_inter_left _ (hsub k))
    · have hex : ∃ k, C ⊆ p k := by
        by_contra hno
        push Not at hno
        apply hint
        have hPC : P ∩ C = ⋃ k ∈ (Finset.univ : Finset κ), (p k ∩ C) := by
          rw [← hU]; ext x; simp
        rw [hPC]
        exact interior_biUnion_empty _ _ (fun k => (hpoly k).isClosed)
          (fun k => (hdich k).resolve_left (hno k))
      obtain ⟨k0, hk0⟩ := hex
      have hne : (interior (P ∩ C)).Nonempty := Set.nonempty_iff_ne_empty.2 hint
      have huniq : ∀ k, k ≠ k0 → ¬ C ⊆ p k := by
        intro k hk hCk
        obtain ⟨x, hx⟩ := hne
        have hxC : x ∈ interior C := interior_mono inter_subset_right hx
        exact Set.disjoint_left.1 (hdisj hk) (interior_mono hCk hxC) (interior_mono hk0 hxC)
      rw [Finset.sum_eq_single k0]
      · rw [inter_eq_right.2 (hk0.trans (hsub k0)), inter_eq_right.2 hk0]
      · intro k _ hk
        exact hflat _ (hpoly k) ((hdich k).resolve_left (huniq k hk))
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [cells_sum D hcut L hLne P hP]
  have hmap : (cells L).map (fun C => D (P ∩ C)) = (cells L).map (fun C => ∑ k, D (p k ∩ C)) :=
    List.map_congr_left key
  rw [hmap, list_sum_finset_sum]
  apply Finset.sum_congr rfl; intro k _
  exact (cells_sum D hcut L hLne _ (hpk k)).symm

end DehnCanon.Library
