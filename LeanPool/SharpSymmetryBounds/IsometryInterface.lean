/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.ExtremalClassification
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# Mathlib isometries

The subgroup of Mathlib isometries `ℂ ≃ᵢ ℂ` preserving the curve, made exhaustive by Mazur–Ulam
and the classification of complex linear isometries.
-/

@[expose] public section

namespace CurveSymmetry

/-- The subgroup of actual Mathlib isometries preserving the entire curve. -/
def isometrySetGroup (S : Set ℂ) : Subgroup (ℂ ≃ᵢ ℂ) where
  carrier := {f | ∀ z : ℂ, f z ∈ S ↔ z ∈ S}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg z
    exact (hf (g z)).trans (hg z)
  inv_mem' := by
    intro f hf z
    simpa using (hf (f⁻¹ z)).symm

/-- The subgroup of Mathlib isometries of `ℂ` mapping the real locus of `P` onto itself. -/
abbrev isometrySymmetryGroup (P : BPoly) := isometrySetGroup (realLocus P)

/-- The orientation-preserving isometry `z ↦ a z + b` of `ℂ`, for `‖a‖ = 1`. -/
noncomputable def affineDirectIsometry (a b : ℂ) (ha : ‖a‖ = 1) : ℂ ≃ᵢ ℂ :=
  (rotation ⟨a, by simpa [Submonoid.unitSphere] using ha⟩).toIsometryEquiv.trans
    (IsometryEquiv.addRight b)

@[simp] lemma affineDirectIsometry_apply (a b : ℂ) (ha : ‖a‖ = 1) (z : ℂ) :
    affineDirectIsometry a b ha z = a * z + b := rfl

/-- The orientation-reversing isometry `z ↦ a conj z + b` of `ℂ`, for `‖a‖ = 1`. -/
noncomputable def affineOppositeIsometry (a b : ℂ) (ha : ‖a‖ = 1) : ℂ ≃ᵢ ℂ :=
  Complex.conjLIE.toIsometryEquiv.trans (affineDirectIsometry a b ha)

@[simp] lemma affineOppositeIsometry_apply (a b : ℂ) (ha : ‖a‖ = 1) (z : ℂ) :
    affineOppositeIsometry a b ha z = a * star z + b := rfl

/-- Mazur--Ulam and the complex linear-isometry classification provide exhaustiveness. -/
theorem isometry_affine_forms (f : ℂ ≃ᵢ ℂ) :
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * z + b) ∨
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * star z + b) := by
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex f.toRealLinearIsometryEquiv
  · left
    refine ⟨a, f 0, Circle.norm_coe a, ?_⟩
    intro z
    have he := congrArg (fun L : ℂ ≃ₗᵢ[ℝ] ℂ => L z) ha
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply, rotation_apply] at he
    exact eq_add_of_sub_eq he
  · right
    refine ⟨a, f 0, Circle.norm_coe a, ?_⟩
    intro z
    have he := congrArg (fun L : ℂ ≃ₗᵢ[ℝ] ℂ => L z) ha
    rw [IsometryEquiv.toRealLinearIsometryEquiv_apply] at he
    exact eq_add_of_sub_eq he

lemma direct_parameters_unique {a b c d : ℂ}
    (h : ∀ z : ℂ, a * z + b = c * z + d) : (a, b) = (c, d) := by
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, zero_add] at h0
  simp only [mul_one] at h1
  apply Prod.ext
  · linear_combination h1 - h0
  · exact h0

lemma opposite_parameters_unique {a b c d : ℂ}
    (h : ∀ z : ℂ, a * star z + b = c * star z + d) : (a, b) = (c, d) := by
  apply direct_parameters_unique
  intro z
  simpa using h (star z)

lemma direct_ne_opposite {a b c d : ℂ} (ha : a ≠ 0)
    (h : ∀ z : ℂ, a * z + b = c * star z + d) : False := by
  have h0 := h 0
  have h1 := h 1
  have hI := h Complex.I
  simp only [star_zero, mul_zero, zero_add] at h0
  simp only [star_one, mul_one] at h1
  have hac : a = c := by linear_combination h1 - h0
  have he : a * Complex.I = a * (-Complex.I) := by
    simpa [← hac, h0] using hI
  have hi := congrArg Complex.im (mul_left_cancel₀ ha he)
  norm_num at hi

/-- The Mathlib isometry attached to the parameters of a direct or opposite symmetry. -/
noncomputable def parametersToIsometry (P : BPoly) : EuclideanSymmetries P → isometrySymmetryGroup P
  | Sum.inl u => ⟨affineDirectIsometry u.val.1 u.val.2 u.prop.1, u.prop.2⟩
  | Sum.inr u => ⟨affineOppositeIsometry u.val.1 u.val.2 u.prop.1, u.prop.2⟩

lemma parametersToIsometry_injective (P : BPoly) : Function.Injective (parametersToIsometry P) := by
  intro u v h
  have he : ∀ z : ℂ, (parametersToIsometry P u).val z = (parametersToIsometry P v).val z :=
    fun z => congrArg (fun f : isometrySymmetryGroup P => f.val z) h
  cases u with
  | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Subtype.ext (direct_parameters_unique he))
      | inr v => exact (direct_ne_opposite (direct_coeff_ne_zero u.prop) he).elim
  | inr u =>
      cases v with
      | inl v =>
        exact (direct_ne_opposite (direct_coeff_ne_zero v.prop) (fun z => (he z).symm)).elim
      | inr v => exact congrArg Sum.inr (Subtype.ext (opposite_parameters_unique he))

lemma parametersToIsometry_surjective (P : BPoly) :
    Function.Surjective (parametersToIsometry P) := by
  intro f
  rcases isometry_affine_forms f.val with ⟨a, b, ha, he⟩ | ⟨a, b, ha, he⟩
  · have hs : DirectSymmetry (realLocus P) a b := ⟨ha, by intro z; rw [← he]; exact f.prop z⟩
    refine ⟨Sum.inl ⟨(a, b), hs⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    exact (he z).symm
  · have hs : OppositeSymmetry (realLocus P) a b := ⟨ha, by intro z; rw [← he]; exact f.prop z⟩
    refine ⟨Sum.inr ⟨(a, b), hs⟩, ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    exact (he z).symm

/-- Euclidean-symmetry parameters are equivalent to the isometries preserving the locus. -/
noncomputable def euclideanIsometryEquiv (P : BPoly) :
    EuclideanSymmetries P ≃ isometrySymmetryGroup P :=
  Equiv.ofBijective (parametersToIsometry P)
    ⟨parametersToIsometry_injective P, parametersToIsometry_surjective P⟩

/-- The full bound for the actual subgroup of Mathlib Euclidean isometries. -/
theorem isometry_group_bound {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) (hcircle : NotCircle P) :
    Finite (isometrySymmetryGroup P) ∧ Nat.card (isometrySymmetryGroup P) ≤ 2 * P.totalDegree := by
  obtain ⟨hf, hb⟩ := full_euclidean_bound hP hd hinf hcircle
  let := hf
  refine ⟨Finite.of_equiv _ (euclideanIsometryEquiv P), ?_⟩
  rwa [← Nat.card_congr (euclideanIsometryEquiv P)]

theorem isometry_bound_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ P : BPoly, Irreducible P ∧ P.totalDegree = d ∧ (realLocus P).Infinite ∧ NotCircle P ∧
      Nat.card (isometrySymmetryGroup P) = 2 * d := by
  obtain ⟨P, hP, hdeg, hinf, hnc, hc⟩ := full_bound_sharp d hd
  exact ⟨P, hP, hdeg, hinf, hnc, (Nat.card_congr (euclideanIsometryEquiv P)).symm.trans hc⟩

end CurveSymmetry
