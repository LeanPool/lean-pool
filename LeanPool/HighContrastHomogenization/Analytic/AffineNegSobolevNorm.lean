/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalNorm

/-!
# High-contrast homogenization: Analytic.AffineNegSobolevNorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The negative fractional norm under an invertible affine normalization

The dual norm of `e.physical.negative.norm` is a supremum of normalized
pairings over the smooth compactly supported fields of unit `H^s` norm.  Under
an invertible change of variables the pairing itself is unchanged — the
determinant cancels from a normalized average — and the admissible index family
is transported by pullback, at the cost of the affine distortion factor of the
`H^s` norm square.  Because the norm square is quadratic and the pairing is
linear in the test, the dual norm therefore costs the square root of that
factor.

The same rescaling argument gives the cost of multiplying the values of a field
by a fixed matrix: the matrix moves onto the test field through its transpose,
so the dual norm costs one power of the `ℓ²` operator norm of the transpose.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Rescaling an admissible test -/

/-- A scalar multiple of a local vector test is a local vector test. -/
theorem IsLocalVecTest.const_smul {V : Set (Vec d)} {ψ : Vec d → Vec d}
    (h : IsLocalVecTest V ψ) (c : ℝ) :
    IsLocalVecTest V (fun x => c • ψ x) := by
  have hsub : Function.support (fun x => c • ψ x) ⊆ Function.support ψ := by
    intro x hx hzero
    exact hx (by simp only [hzero, smul_zero])
  exact ⟨h.contDiff.const_smul c, h.hasCompactSupport.mono hsub,
    fun x hx => h.tsupport_subset (closure_mono hsub hx)⟩

/-- The normalized pairing is homogeneous of degree one in the test field. -/
theorem dualPairing_const_smul (V : Set (Vec d)) (F ψ : Vec d → Vec d) {c : ℝ}
    (hc : 0 < c) :
    dualPairing V F (fun x => c • ψ x) =
      ENNReal.ofReal c * dualPairing V F ψ := by
  classical
  have hfun : (fun x => vecDot (F x) (c • ψ x)) =
      fun x => c * vecDot (F x) (ψ x) := by
    funext x
    exact vecDot_smul_right (F x) (ψ x) c
  unfold dualPairing
  rw [hfun]
  by_cases h : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume
  · have hcm : IntegrableOn (fun x => c * vecDot (F x) (ψ x)) V volume :=
      h.const_mul c
    rw [ite_eq_left hcm, ite_eq_left h]
    have hva : volumeAverage V (fun x => c * vecDot (F x) (ψ x)) =
        c * volumeAverage V (fun x => vecDot (F x) (ψ x)) := by
      unfold volumeAverage
      rw [integral_const_mul]
      ring
    rw [hva]
    exact ENNReal.ofReal_mul hc.le
  · have h' : ¬ IntegrableOn (fun x => c * vecDot (F x) (ψ x)) V volume := by
      intro hcon
      exact h (by
        simpa only [IntegrableOn, inv_mul_cancel_left₀ hc.ne'] using hcon.const_mul c⁻¹)
    rw [ite_eq_right h', ite_eq_right h,
      ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hc)]

/-- **The rescaling bound.**  A local vector test whose `H^s` norm square is at
most `K` pairs against a field by at most `√K` times the dual norm. -/
theorem dualPairing_le_negSobolevNorm_of_hsNormSq_le {V : Set (Vec d)} {s : ℝ}
    (F ψ : Vec d → Vec d) {K : ℝ} (hK : 0 < K)
    (htest : IsLocalVecTest V ψ) (hnorm : hsNormSq V s ψ ≤ ENNReal.ofReal K) :
    dualPairing V F ψ ≤
      ENNReal.ofReal (Real.sqrt K) * negSobolevNorm V s F := by
  have hrpos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hφtest : IsLocalVecTest V (fun x => (Real.sqrt K)⁻¹ • ψ x) :=
    htest.const_smul _
  have hφnorm : hsNormSq V s (fun x => (Real.sqrt K)⁻¹ • ψ x) ≤ 1 := by
    rw [hsNormSq_smul]
    refine le_trans (mul_le_mul_right hnorm _) (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (sq_nonneg _), inv_pow, hsq,
      inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one]
  have hmem : dualPairing V F (fun x => (Real.sqrt K)⁻¹ • ψ x) ≤
      negSobolevNorm V s F :=
    le_iSup (f := fun p : {ψ' : Vec d → Vec d //
        IsLocalVecTest V ψ' ∧ hsNormSq V s ψ' ≤ 1} => dualPairing V F p.1)
      ⟨_, hφtest, hφnorm⟩
  have hψ : (fun x => Real.sqrt K • (Real.sqrt K)⁻¹ • ψ x) = ψ := by
    funext x
    rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  calc dualPairing V F ψ
      = dualPairing V F (fun x => Real.sqrt K • (Real.sqrt K)⁻¹ • ψ x) := by
        rw [hψ]
    _ = ENNReal.ofReal (Real.sqrt K) *
          dualPairing V F (fun x => (Real.sqrt K)⁻¹ • ψ x) :=
        dualPairing_const_smul V F _ hrpos
    _ ≤ ENNReal.ofReal (Real.sqrt K) * negSobolevNorm V s F :=
        mul_le_mul_right hmem _

/-! ## The domain transport -/

/-- **The dual fractional norm under an invertible change of variables.**  The
constant is the square root of the affine distortion factor of the inverse
map. -/
theorem negSobolevNorm_matImage_le {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hU0 : volume U ≠ 0) {s N : ℝ}
    (hs : 0 ≤ (d : ℝ) + 2 * s) (hN : 0 ≤ N)
    (hker : ∀ w : Vec d,
      Real.sqrt (vecNormSq w) ≤ N * Real.sqrt (vecNormSq (matVecMul L⁻¹ w)))
    (F : Vec d → Vec d) :
    negSobolevNorm (matImage L U) s F ≤
      ENNReal.ofReal (Real.sqrt (hsAffineFactor L⁻¹ s N)) *
        negSobolevNorm U s (fun y => F (matVecMul L y)) := by
  have hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
  have hKpos : 0 < hsAffineFactor L⁻¹ s N := hsAffineFactor_pos hLinv s N
  have hbound : ∀ ψ : {ψ : Vec d → Vec d //
      IsLocalVecTest (matImage L U) ψ ∧ hsNormSq (matImage L U) s ψ ≤ 1},
      dualPairing (matImage L U) F ψ.1 ≤
        ENNReal.ofReal (Real.sqrt (hsAffineFactor L⁻¹ s N)) *
          negSobolevNorm U s (fun y => F (matVecMul L y)) := by
    rintro ⟨ψ, htest, hnorm⟩
    rw [dualPairing_matImage hL hU]
    refine dualPairing_le_negSobolevNorm_of_hsNormSq_le _ _ hKpos
      (htest.comp_matVecMul hL) ?_
    refine le_trans (hsNormSq_comp_matVecMul_le hL hU hU0 hs hN hker ψ) ?_
    exact le_trans (mul_le_mul_right hnorm _) (le_of_eq (mul_one _))
  exact iSup_le hbound

/-! ## The operator-norm instantiations -/

/-- The dual comparison with the explicit constant built from the determinant of
`L` and the `ℓ²` operator norm of `L`. -/
theorem negSobolevNorm_matImage_le_opNorm {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hU0 : volume U ≠ 0) {s : ℝ}
    (hs : 0 ≤ (d : ℝ) + 2 * s) (F : Vec d → Vec d) :
    negSobolevNorm (matImage L U) s F ≤
      ENNReal.ofReal (Real.sqrt (hsAffineFactor L⁻¹ s ‖L‖)) *
        negSobolevNorm U s (fun y => F (matVecMul L y)) := by
  have hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
  have hker : ∀ w : Vec d,
      Real.sqrt (vecNormSq w) ≤
        ‖L‖ * Real.sqrt (vecNormSq (matVecMul L⁻¹ w)) := by
    intro w
    have h := sqrt_vecNormSq_le_norm_inv_mul hLinv w
    rwa [Matrix.nonsing_inv_nonsing_inv L hL] at h
  exact negSobolevNorm_matImage_le hL hU hU0 hs (norm_nonneg _) hker F

/-! ## The pointwise matrix action on field values -/

end

end HighContrast
end HCPolySupport
