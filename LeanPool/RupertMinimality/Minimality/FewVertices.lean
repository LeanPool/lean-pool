/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Crossing
public import Mathlib.Analysis.Convex.Radon

/-! # Few Vertices -/

@[expose] public section

namespace RupertMinimality

/-!
# Corollary 5.6: every convex polyhedron with at most 5 vertices is Rupert

Proof, without combinatorial types (step 5 of `minimality.md`): replace `V`
by a minimal subset with the same hull
(`exists_hull_minimal`; every point is then outside the hull of the others).
* If some point `E` has the others coplanar: a pyramid (`isRupert_of_pyramid`);
  this covers all `≤ 4`-point sets.
* Otherwise there are exactly 5 points, no 4 coplanar.  Radon's theorem
  (`radon_partition`) splits them into two parts with intersecting hulls; a
  `1 + 4` split contradicts minimality, so it is `2 + 3`: a segment `DE`
  meets a triangle `ABC`, in the relative interior because no 4 points are
  coplanar (`det4`).  Then `isRupert_of_crossing` with the view `E - D`
  (`isRupert_five`).
-/

namespace Minimality

open scoped RealInnerProductSpace
open Module

/-- A minimal subset with the same hull: no point lies in the hull of the
others. -/
theorem exists_hull_minimal (V : Finset ℝ³) :
    ∃ V' ⊆ V, convexHull ℝ (V' : Set ℝ³) = convexHull ℝ (V : Set ℝ³) ∧
      ∀ v ∈ V', v ∉ convexHull ℝ ((V'.erase v : Finset ℝ³) : Set ℝ³) := by
  classical
  set 𝒮 := V.powerset.filter
    (fun S : Finset ℝ³ => convexHull ℝ (S : Set ℝ³) = convexHull ℝ (V : Set ℝ³))
  have hne : 𝒮.Nonempty := ⟨V, Finset.mem_filter.mpr ⟨Finset.mem_powerset_self V, rfl⟩⟩
  obtain ⟨S, hS, hmin⟩ := 𝒮.exists_min_image Finset.card hne
  obtain ⟨hSV, hShull⟩ := Finset.mem_filter.mp hS
  refine ⟨S, Finset.mem_powerset.mp hSV, hShull, fun v hv hvin => ?_⟩
  have heq : convexHull ℝ ((S.erase v : Finset ℝ³) : Set ℝ³) = convexHull ℝ (S : Set ℝ³) := by
    apply le_antisymm (convexHull_mono (by simp [Finset.coe_erase]))
    refine convexHull_min (fun x hx => ?_) (convex_convexHull ℝ _)
    by_cases hxv : x = v
    · rw [hxv]; exact hvin
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxv, hx⟩))
  have hmem : S.erase v ∈ 𝒮 := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr ((Finset.erase_subset v S).trans (Finset.mem_powerset.mp hSV)),
      heq.trans hShull⟩
  have := hmin _ hmem
  rw [Finset.card_erase_of_mem hv] at this
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- At most three points are coplanar. -/
theorem coplanar_of_card_le_three (S : Finset ℝ³) (h : S.card ≤ 3) : Coplanar ℝ (S : Set ℝ³) := by
  classical
  have key : finrank ℝ (vectorSpan ℝ (S : Set ℝ³)) ≤ 2 := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.coe_empty, vectorSpan_empty, finrank_bot]; omega
    · have hc : S.card = (S.card - 1) + 1 := (Nat.sub_add_cancel (Finset.card_pos.mpr hne)).symm
      have := finrank_vectorSpan_image_finset_le ℝ (id : ℝ³ → ℝ³) S hc
      rw [Finset.image_id] at this
      omega
  unfold Coplanar
  rw [← finrank_eq_rank]
  exact_mod_cast key

/-- Three points with nonzero cross product are affinely independent. -/
theorem affineIndependent_of_cross_ne_zero {a b c : ℝ³} (h : cross (b - a) (c - a) ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hcol
  apply h
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (p₀ := a) (by simp)).mp hcol
  obtain ⟨rb, hrb⟩ := hv b (by simp)
  obtain ⟨rc, hrc⟩ := hv c (by simp)
  rw [vadd_eq_add] at hrb hrc
  rw [hrb, hrc]
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- If the segment `DE` meets the line `BC`, the four points are coplanar. -/
theorem det4_eq_zero_of_meet {B C D E : ℝ³} {s γ : ℝ}
    (h : D + s • (E - D) = B + γ • (C - B)) : det4 B C D E = 0 := by
  have h0 := congrArg (fun x : ℝ³ => x 0) h
  have h1 := congrArg (fun x : ℝ³ => x 1) h
  have h2 := congrArg (fun x : ℝ³ => x 2) h
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h0 h1 h2
  simp only [det4, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
    RCLike.inner_apply, conj_trivial]
  simp
  linear_combination
    ((E 1 - B 1) * (C 2 - B 2) - (E 2 - B 2) * (C 1 - B 1) +
      ((C 1 - B 1) * (D 2 - B 2) - (C 2 - B 2) * (D 1 - B 1))) * h0 +
    ((E 2 - B 2) * (C 0 - B 0) - (E 0 - B 0) * (C 2 - B 2) +
      ((C 2 - B 2) * (D 0 - B 0) - (C 0 - B 0) * (D 2 - B 2))) * h1 +
    ((E 0 - B 0) * (C 1 - B 1) - (E 1 - B 1) * (C 0 - B 0) +
      ((C 0 - B 0) * (D 1 - B 1) - (C 1 - B 1) * (D 0 - B 0))) * h2

/-- **Five points in general position** with a segment `DE` meeting the
triangle `ABC` are Rupert. -/
theorem isRupert_five (V : Finset ℝ³) {A B C D E : ℝ³}
    (hVsub : ∀ x ∈ V, x = A ∨ x = B ∨ x = C ∨ x = D ∨ x = E)
    (hA : A ∈ V) (hB : B ∈ V) (hC : C ∈ V) (hD : D ∈ V) (hE : E ∈ V)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hgen : ∀ x ∈ V, ¬ Coplanar ℝ ((V.erase x : Finset ℝ³) : Set ℝ³))
    {s : ℝ} (hX : D + s • (E - D) ∈ convexHull ℝ (({A, B, C} : Finset ℝ³) : Set ℝ³)) :
    IsRupert V := by
  classical
  -- four of the points are never coplanar
  have hcop : ∀ x ∈ V, ∀ p q r t : ℝ³, (∀ y ∈ V, y ≠ x → y = p ∨ y = q ∨ y = r ∨ y = t) →
      det4 p q r t ≠ 0 := by
    intro x hx p q r t hsub h0
    apply hgen x hx
    refine (coplanar_of_det4_eq_zero h0).subset fun y hy => ?_
    obtain ⟨hyx, hyV⟩ := Finset.mem_erase.mp hy
    rcases hsub y hyV hyx with rfl | rfl | rfl | rfl <;> simp
  have hABCD : det4 A B C D ≠ 0 := hcop E hE A B C D (fun y hy hyE => by
    rcases hVsub y hy with rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl (by assumption) | simp only [true_or, or_true])
  set N := cross (B - A) (C - A) with hNdef
  set c := ⟪N, A⟫ with hc
  have hN : N ≠ 0 := fun h0 => hABCD (by simp [det4, ← hNdef, h0])
  have hind : AffineIndependent ℝ ![A, B, C] := affineIndependent_of_cross_ne_zero hN
  have hWN : ∀ w ∈ ({A, B, C} : Finset ℝ³), ⟪N, w⟫ = c := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · have := inner_cross_left (w - A) (C - A)
      rw [← hNdef, inner_sub_right] at this; linarith
    · have := inner_cross_right (B - A) (w - A)
      rw [← hNdef, inner_sub_right] at this; linarith
  -- the crossing point as a convex combination of `A, B, C`
  obtain ⟨μ, hμ0, hμ1, hμX⟩ := Finset.mem_convexHull.mp hX
  rw [Finset.centerMass_eq_of_sum_1 _ _ hμ1] at hμX
  have hA' : A ∉ ({B, C} : Finset ℝ³) := by simp [hAB, hAC]
  have hB' : B ∉ ({C} : Finset ℝ³) := by simp [hBC]
  have hsum3 : ∀ g : ℝ³ → ℝ³, ∑ w ∈ ({A, B, C} : Finset ℝ³), g w = g A + g B + g C := by
    intro g; rw [Finset.sum_insert hA', Finset.sum_insert hB', Finset.sum_singleton, add_assoc]
  have hsum3' : ∀ g : ℝ³ → ℝ, ∑ w ∈ ({A, B, C} : Finset ℝ³), g w = g A + g B + g C := by
    intro g; rw [Finset.sum_insert hA', Finset.sum_insert hB', Finset.sum_singleton, add_assoc]
  rw [hsum3] at hμX
  rw [hsum3'] at hμ1
  simp only [id] at hμX
  have hNX : ⟪N, D + s • (E - D)⟫ = c := by
    rw [← hμX, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, hWN A (by simp), hWN B (by simp), hWN C (by simp)]
    linear_combination c * hμ1
  have hu₀ : ⟪N, E - D⟫ ≠ 0 := by
    intro h0
    apply hABCD
    rw [inner_add_right, real_inner_smul_right, h0, mul_zero, add_zero] at hNX
    simp only [det4, ← hNdef, inner_sub_right, hNX, hc, sub_self]
  -- all three weights are positive
  have hpos : ∀ w ∈ ({A, B, C} : Finset ℝ³), 0 < μ w := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · refine lt_of_le_of_ne (hμ0 _ (by simp)) (fun h0 => ?_)
      apply hcop w hA B C D E (fun y hy hyA => by
        rcases hVsub y hy with rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl (by assumption) | simp only [true_or, or_true])
      apply det4_eq_zero_of_meet (γ := μ C)
      rw [← hμX, ← h0, zero_smul, zero_add, show μ B = 1 - μ C by linarith]
      module
    · refine lt_of_le_of_ne (hμ0 _ (by simp)) (fun h0 => ?_)
      apply hcop w hB A C D E (fun y hy hyB => by
        rcases hVsub y hy with rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl (by assumption) | simp only [true_or, or_true])
      apply det4_eq_zero_of_meet (γ := μ C)
      rw [← hμX, ← h0, zero_smul, add_zero, show μ A = 1 - μ C by linarith]
      module
    · refine lt_of_le_of_ne (hμ0 _ (by simp)) (fun h0 => ?_)
      apply hcop w hC A B D E (fun y hy hyC => by
        rcases hVsub y hy with rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl (by assumption) | simp only [true_or, or_true])
      apply det4_eq_zero_of_meet (γ := μ B)
      rw [← hμX, ← h0, zero_smul, add_zero, show μ A = 1 - μ B by linarith]
      module
  refine isRupert_of_crossing V {A, B, C} (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption)
    N c hWN (by simp) (by simp) (by simp) hind (E - D) hu₀ ?_
  intro v hv hvW
  have hsumμ : ∑ w ∈ ({A, B, C} : Finset ℝ³), μ w = 1 := by rw [hsum3']; exact hμ1
  have hsumX : ∑ w ∈ ({A, B, C} : Finset ℝ³), μ w • w = D + s • (E - D) := by
    rw [hsum3]; exact hμX
  rcases hVsub v hv with rfl | rfl | rfl | rfl | rfl
  · exact absurd (by simp) hvW
  · exact absurd (by simp) hvW
  · exact absurd (by simp) hvW
  · exact ⟨s, μ, hpos, hsumμ, hsumX.symm⟩
  · exact ⟨s - 1, μ, hpos, hsumμ, by rw [hsumX]; module⟩

/-- **Corollary 5.6.** Every convex polyhedron with at most five vertices is
Rupert.  `V` need not consist of vertices only. -/
theorem isRupert_of_card_le_five (V : Finset ℝ³) (hV : V.card ≤ 5)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  obtain ⟨V', hV'V, hhull, hmin⟩ := exists_hull_minimal V
  rw [← hhull] at hint
  apply (isRupert_congr_hull hhull).mp
  by_cases hpyr : ∃ E ∈ V', Coplanar ℝ ((V'.erase E : Finset ℝ³) : Set ℝ³)
  · obtain ⟨E, -, hE⟩ := hpyr
    exact isRupert_of_pyramid V' E hint hE
  push Not at hpyr
  have hne : V'.Nonempty := by
    rcases V'.eq_empty_or_nonempty with h | h
    · rw [h, Finset.coe_empty, convexHull_empty, interior_empty] at hint
      exact absurd hint Set.not_nonempty_empty
    · exact h
  have hcard5 : V'.card = 5 := by
    have h1 := Finset.card_le_card hV'V
    by_contra h5
    obtain ⟨E, hE⟩ := hne
    apply hpyr E hE
    apply coplanar_of_card_le_three
    rw [Finset.card_erase_of_mem hE]; omega
  -- Radon's theorem
  let f : V' → ℝ³ := Subtype.val
  have hnai : ¬ AffineIndependent ℝ f := by
    intro hai
    have := hai.card_le_finrank_succ
    rw [Fintype.card_coe, hcard5] at this
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range f))
    rw [finrank_euclideanSpace, Fintype.card_fin] at h2
    omega
  obtain ⟨I, X, hX1, hX2⟩ := Convex.radon_partition hnai
  set S₁ : Finset ℝ³ := (Finset.univ.filter (· ∈ I)).image Subtype.val with hS₁def
  set S₂ : Finset ℝ³ := (Finset.univ.filter (· ∉ I)).image Subtype.val with hS₂def
  have hS₁ : (S₁ : Set ℝ³) = f '' I := by ext x; simp [S₁, f]
  have hS₂ : (S₂ : Set ℝ³) = f '' Iᶜ := by ext x; simp [S₂, f]
  rw [← hS₁] at hX1
  rw [← hS₂] at hX2
  have hsub₁ : S₁ ⊆ V' := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx; exact y.2
  have hsub₂ : S₂ ⊆ V' := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx; exact y.2
  have hunion : S₁ ∪ S₂ = V' := by
    apply le_antisymm (Finset.union_subset hsub₁ hsub₂)
    intro x hx
    by_cases hI : (⟨x, hx⟩ : V') ∈ I
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, by simp [hI], rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, by simp [hI], rfl⟩)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp h2
    have : z = y := Subtype.ext hzy
    subst this
    exact (Finset.mem_filter.mp hz).2 (Finset.mem_filter.mp hy).2
  have hcardsum : S₁.card + S₂.card = 5 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, hcard5]
  -- neither part is empty or a single point
  have hbig : ∀ T T' : Finset ℝ³, T ∪ T' = V' → Disjoint T T' →
      X ∈ convexHull ℝ (T : Set ℝ³) → X ∈ convexHull ℝ (T' : Set ℝ³) → 2 ≤ T.card := by
    intro T T' hTT' hd hXT hXT'
    by_contra hlt
    push Not at hlt
    rcases Finset.card_le_one_iff_subset_singleton.mp (by omega : T.card ≤ 1) with ⟨x, hx⟩
    rcases T.eq_empty_or_nonempty with h | ⟨y, hy⟩
    · rw [h, Finset.coe_empty, convexHull_empty] at hXT; exact hXT
    · have hyx := Finset.mem_singleton.mp (hx hy)
      subst hyx
      have hT : T = {y} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hy, fun z hz => Finset.mem_singleton.mp (hx hz)⟩
      rw [hT, Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] at hXT
      subst hXT
      have hyV : X ∈ V' := by rw [← hTT']; exact Finset.mem_union_left _ hy
      apply hmin X hyV
      refine convexHull_mono (fun z hz => ?_) hXT'
      have hzV : z ∈ V' := by rw [← hTT']; exact Finset.mem_union_right _ hz
      refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun h => ?_, hzV⟩)
      subst h
      exact Finset.disjoint_left.mp hd hy hz
  have hc₁ := hbig S₁ S₂ hunion hdisj hX1 hX2
  have hc₂ := hbig S₂ S₁ (by rw [Finset.union_comm]; exact hunion) hdisj.symm hX2 hX1
  -- the `2 + 3` split
  have key : ∀ T T' : Finset ℝ³, T.card = 2 → T'.card = 3 → T ∪ T' = V' →
      X ∈ convexHull ℝ (T : Set ℝ³) → X ∈ convexHull ℝ (T' : Set ℝ³) → IsRupert V' := by
    intro T T' h2 h3 hTT' hXT hXT'
    obtain ⟨D, E, -, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨A, B, C, hAB, hAC, hBC, rfl⟩ := Finset.card_eq_three.mp h3
    rw [Finset.coe_pair, convexHull_pair, segment_eq_image'] at hXT
    obtain ⟨θ, -, rfl⟩ := hXT
    have hmem : ∀ x, x ∈ V' ↔ x = D ∨ x = E ∨ x = A ∨ x = B ∨ x = C := fun x => by
      rw [← hTT']; simp; tauto
    refine isRupert_five V' (fun x hx => ?_) ((hmem A).mpr (by simp)) ((hmem B).mpr (by simp))
      ((hmem C).mpr (by simp)) ((hmem D).mpr (by simp)) ((hmem E).mpr (by simp))
      hAB hAC hBC hpyr hXT'
    rcases (hmem x).mp hx with h | h | h | h | h <;> simp [h]
  rcases (by omega : (S₁.card = 2 ∧ S₂.card = 3) ∨ (S₁.card = 3 ∧ S₂.card = 2)) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key S₁ S₂ h1 h2 hunion hX1 hX2
  · exact key S₂ S₁ h2 h1 (by rw [Finset.union_comm]; exact hunion) hX2 hX1

end Minimality

end RupertMinimality
