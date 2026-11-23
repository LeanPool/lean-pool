/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Translation

/-!
# A common center

All direct Euclidean symmetries of the curve have a common fixed point.
-/

@[expose] public section

namespace CurveSymmetry

/-- A direct Euclidean symmetry, in its complex affine form. -/
def DirectSymmetry (S : Set ℂ) (a b : ℂ) : Prop :=
  ‖a‖ = 1 ∧ ∀ z : ℂ, a * z + b ∈ S ↔ z ∈ S

lemma direct_coeff_ne_zero {S : Set ℂ} {a b : ℂ} (h : DirectSymmetry S a b) : a ≠ 0 := by
  intro hz
  have hnorm := h.1
  simp [hz] at hnorm

/-- The two affine compositions differ by a translation, so must agree. -/
lemma direct_symmetries_commute {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty)
    {a b c d : ℂ} (h1 : DirectSymmetry (realLocus P) a b)
    (h2 : DirectSymmetry (realLocus P) c d) : a * d + b = c * b + d := by
  have hk : a * c ≠ 0 := mul_ne_zero (direct_coeff_ne_zero h1) (direct_coeff_ne_zero h2)
  have hc1 : ∀ z : ℂ, a * c * z + (a * d + b) ∈ realLocus P ↔ z ∈ realLocus P := by
    intro z
    rw [show a * c * z + (a * d + b) = a * (c * z + d) + b by ring]
    exact (h1.2 (c * z + d)).trans (h2.2 z)
  have hc2 : ∀ z : ℂ, a * c * z + (c * b + d) ∈ realLocus P ↔ z ∈ realLocus P := by
    intro z
    rw [show a * c * z + (c * b + d) = c * (a * z + b) + d by ring]
    exact (h2.2 (a * z + b)).trans (h1.2 z)
  have ht : ∀ z ∈ realLocus P, z + ((a * d + b) - (c * b + d)) ∈ realLocus P := by
    intro z hz
    let w := (z - (c * b + d)) / (a * c)
    have he : a * c * w + (c * b + d) = z := by
      dsimp [w]
      rw [mul_div_cancel₀ _ hk]
      ring
    have hw : w ∈ realLocus P := (hc2 w).mp (he ▸ hz)
    have hout := (hc1 w).mpr hw
    have he' : a * c * w + (a * d + b) = z + ((a * d + b) - (c * b + d)) := by
      linear_combination he
    rwa [he'] at hout
  exact sub_eq_zero.mp (no_translation_symmetry hP hd hne ht)

/-- All direct Euclidean symmetries have a common fixed point.
If the group is trivial, the origin is selected. -/
theorem direct_symmetries_common_center {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) :
    ∃ z : ℂ, ∀ a b : ℂ, DirectSymmetry (realLocus P) a b → b = (1 - a) * z := by
  by_cases hex : ∃ a b : ℂ, DirectSymmetry (realLocus P) a b ∧ a ≠ 1
  · obtain ⟨a, b, hab, ha⟩ := hex
    refine ⟨b / (1 - a), ?_⟩
    intro c d hcd
    have h := direct_symmetries_commute hP hd hne hab hcd
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
    field_simp
    linear_combination -h
  · refine ⟨0, ?_⟩
    intro a b hab
    have ha : a = 1 := by by_contra h; exact hex ⟨a, b, hab, h⟩
    have hb : b = 0 := no_translation_symmetry hP hd hne (by
      intro z hz
      simpa [ha] using (hab.2 z).mpr hz)
    simp [hb]

end CurveSymmetry
