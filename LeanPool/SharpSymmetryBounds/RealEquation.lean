/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Sharpness

/-!
# Real equations

An irreducible equation with infinite real locus can be rescaled to have real coefficients.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

lemma realLocus_C_mul {c : ℂ} (hc : c ≠ 0) (P : BPoly) :
    realLocus (C c * P) = realLocus P := by
  ext z
  change eval _ (C c * P) = 0 ↔ eval _ P = 0
  simp [hc]

lemma C_mul_irreducible {c : ℂ} (hc : c ≠ 0) {P : BPoly} (hP : Irreducible P) :
    Irreducible (C c * P) :=
  (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hc).map C)).mpr hP

lemma exists_nonzero_real_evaluation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ z : ℂ, eval (fun i : Fin 2 => if i = 0 then z else star z) P ≠ 0 := by
  by_contra h
  push Not at h
  have ht := no_translation_symmetry hP hd hinf.nonempty (v := 1) (by
    intro z _
    exact h (z + 1))
  norm_num at ht

/-- An irreducible equation with infinite real locus can be rescaled to have
conjugate-symmetric coefficients. The scalar is constructed, not assumed. -/
theorem exists_real_equation {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ a b : ℕ,
      (C c * P).coeff (exponent b a) = star ((C c * P).coeff (exponent a b)) := by
  obtain ⟨z, hz⟩ := exists_nonzero_real_evaluation hP hd hinf
  let v := eval (fun i : Fin 2 => if i = 0 then z else star z) P
  have hv : v ≠ 0 := hz
  have hsub : realLocus P ⊆ realLocus (conjugateSwap P) := by
    intro w hw
    change eval _ (conjugateSwap P) = 0
    rw [eval_conjugateSwap, hw, star_zero]
  obtain ⟨k, _, hk⟩ := proportional_of_realLocus_subset hP
    (conjugateSwap_ne_zero hP.ne_zero) hinf hsub (conjugateSwap_degree_le P)
  have he := congrArg (eval (fun i : Fin 2 => if i = 0 then z else star z)) hk
  rw [eval_conjugateSwap, map_mul, eval_C] at he
  change star v = k * v at he
  have hscaled : conjugateSwap (C v⁻¹ * P) = C v⁻¹ * P := by
    have hC : conjugateSwap (C v⁻¹) = C (star (v⁻¹)) := by simp [conjugateSwap]
    rw [map_mul, hC, hk, ← mul_assoc, ← C_mul]
    congr 2
    change (starRingEnd ℂ) (v⁻¹) * k = v⁻¹
    rw [map_inv₀]
    change (star v)⁻¹ * k = v⁻¹
    apply (mul_right_cancel₀ hv)
    rw [mul_assoc, ← he, inv_mul_cancel₀ (star_ne_zero.mpr hv), inv_mul_cancel₀ hv]
  refine ⟨v⁻¹, inv_ne_zero hv, ?_⟩
  intro a b
  have h := coeff_conjugateSwap (C v⁻¹ * P) a b
  rwa [hscaled] at h

end CurveSymmetry
