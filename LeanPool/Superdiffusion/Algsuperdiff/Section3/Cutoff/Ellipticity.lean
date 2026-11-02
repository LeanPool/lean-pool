/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.HighMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Ellipticity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Local ellipticity of the genuine cutoff

The lower-infinite cutoff is controlled on each origin cube by the *same*
summable local-control series that licenses its construction.  In particular,
the nonsymmetric coefficient field has lower ellipticity `nu`, but its upper
ellipticity constant also records the realised skew part.  It is never set to
`nu` merely because the symmetric part is `nu I`.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Every entry of the genuine cutoff is bounded by its realised local control
on the matching open origin cube. -/
theorem abs_cutoff_entry_le_cutoffLocalControl (ell m : ℤ)
    (omega : CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) (i j : Fin d) :
    |cutoff m omega x i j| ≤ cutoffLocalControl ell m omega := by
  have hsum : Summable (fun r : ℕ => omega.1 (m - (r : ℤ)) x i j) := by
    refine (summable_cutoffLocalControl ell m omega).of_norm_bounded fun r => ?_
    simpa only [Real.norm_eq_abs] using
      abs_entry_le_localCubeControl ell (omega.1 (m - (r : ℤ))) hx i j
  rw [cutoff_apply_entry]
  calc
    |∑' r : ℕ, omega.1 (m - (r : ℤ)) x i j|
        ≤ ∑' r : ℕ, |omega.1 (m - (r : ℤ)) x i j| :=
      by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' r : ℕ, localCubeControl ell (omega.1 (m - (r : ℤ))) := by
      exact Summable.tsum_le_tsum
        (fun r => abs_entry_le_localCubeControl ell _ hx i j) hsum.norm
        (summable_cutoffLocalControl ell m omega)
    _ = cutoffLocalControl ell m omega := rfl

/-- A pointwise entry bound for the actual coefficient cutoff on an origin
cube.  The `nu` term is the diagonal constant field; the second term is the
realised lower-cutoff control. -/
theorem abs_coefficientCutoff_entry_le (nu : ℝ) (hnu : 0 ≤ nu)
    (ell m : ℤ) (omega : CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) (i j : Fin d) :
    |coefficientCutoff nu m omega x i j| ≤ nu + cutoffLocalControl ell m omega := by
  rw [coefficientCutoff_apply, Matrix.add_apply]
  calc
    |(nu • (1 : Mat d)) i j + cutoff m omega x i j|
        ≤ |(nu • (1 : Mat d)) i j| + |cutoff m omega x i j| := abs_add_le _ _
    _ ≤ nu + cutoffLocalControl ell m omega := by
      gcongr
      · by_cases hij : i = j
        · subst j
          simp [Matrix.smul_apply, abs_of_nonneg hnu]
        · simpa [Matrix.smul_apply, hij] using hnu
      · exact abs_cutoff_entry_le_cutoffLocalControl ell m omega hx i j

/-! ## A finite-dimensional ellipticity producer

This is deliberately local proof infrastructure.  It transports the exact
quadratic-form identity from `Limit.lean` plus a literal entry bound into
CoarseGraining's nonsymmetric `IsEllipticMatrix` predicate.
-/

private theorem vecNormSq_matVecMul_le_frobenius (A : Mat d) (eta : Vec d) :
    vecNormSq (matVecMul A eta) ≤
      (∑ i, ∑ j, (A i j) ^ 2) * vecNormSq eta := by
  have hrow : ∀ i, (matVecMul A eta i) ^ 2 ≤
      (∑ j, (A i j) ^ 2) * vecNormSq eta := by
    intro i
    have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq (fun j => A i j) eta
    have hns : vecNormSq (fun j => A i j) = ∑ j, (A i j) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    have hdot : matVecMul A eta i = vecDot (fun j => A i j) eta := rfl
    rw [hdot, ← hns]
    exact hcs
  calc
    vecNormSq (matVecMul A eta) = ∑ i, (matVecMul A eta i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ i, (∑ j, (A i j) ^ 2) * vecNormSq eta :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ i, ∑ j, (A i j) ^ 2) * vecNormSq eta := by
      rw [Finset.sum_mul]

private theorem isEllipticMatrix_of_coercive_eq_of_bound {A : Mat d} {nu B : ℝ}
    (hnu : 0 < nu) (hnuB : nu ^ 2 ≤ B)
    (hco : ∀ xi : Vec d, vecDot xi (matVecMul A xi) = nu * vecNormSq xi)
    (hbd : ∀ eta : Vec d, vecNormSq (matVecMul A eta) ≤ B * vecNormSq eta) :
    IsEllipticMatrix nu (B / nu) A := by
  have hB : 0 < B := lt_of_lt_of_le (by positivity) hnuB
  have hinj : Function.Injective (fun xi => matVecMul A xi) := by
    intro xi zeta hxi
    have hw : matVecMul A (xi - zeta) = 0 := by
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg,
        sub_eq_zero]
      exact hxi
    have hzero : nu * vecNormSq (xi - zeta) = 0 := by
      rw [← hco (xi - zeta), hw, vecDot_zero_right]
    have hsq : vecNormSq (xi - zeta) = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact False.elim (hnu.ne' h)
      · exact h
    exact sub_eq_zero.mp (vecNormSq_eq_zero hsq)
  have hunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hunit
  have hnuLam : nu ≤ B / nu :=
    (le_div_iff₀ hnu).mpr (by rw [← pow_two]; exact hnuB)
  refine ⟨hnu, hnuLam, ?_, ?_⟩
  · intro xi
    rw [hco xi]
  · intro xi
    set eta := matVecMul A⁻¹ xi with heta
    have hAeta : matVecMul A eta = xi := by
      rw [heta, matVecMul_mul, Matrix.mul_nonsing_inv A hdet]
      exact Matrix.one_mulVec xi
    have hpair : vecDot xi eta = nu * vecNormSq eta := by
      have h1 : vecDot xi eta = vecDot (matVecMul A eta) eta := by rw [hAeta]
      rw [h1, vecDot_comm, hco eta]
    have hnorm : vecNormSq xi ≤ B * vecNormSq eta := by
      have h := hbd eta
      rwa [hAeta] at h
    rw [hpair, inv_div, div_mul_eq_mul_div, div_le_iff₀ hB]
    nlinarith [mul_le_mul_of_nonneg_left hnorm hnu.le]

theorem isEllipticMatrix_of_symmPart_and_entry_bound {A : Mat d}
    {nu C : ℝ} (hnu : 0 < nu) (hsymm : symmPart A = nu • (1 : Mat d))
    (hentry : ∀ i j, |A i j| ≤ C) :
    IsEllipticMatrix nu (((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu) A := by
  refine isEllipticMatrix_of_coercive_eq_of_bound hnu ?_ ?_ (fun eta => ?_)
  · nlinarith [mul_nonneg
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) d))
      (sq_nonneg C)]
  · intro xi
    have hone : matVecMul (1 : Mat d) xi = xi := by
      funext k
      simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [← vecDot_matVecMul_symmPart, hsymm, smul_matVecMul, hone,
      vecDot_smul_right]
    rfl
  · refine le_trans (vecNormSq_matVecMul_le_frobenius A eta) ?_
    refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg eta)
    calc
      (∑ i, ∑ j, (A i j) ^ 2) ≤ ∑ _i : Fin d, ∑ _j : Fin d, C ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        nlinarith [abs_nonneg (A i j), sq_abs (A i j), hentry i j]
      _ = (d : ℝ) * (d : ℝ) * C ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ (d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2 := by nlinarith [sq_nonneg nu]

/-- A local entry bound gives an honest nonsymmetric ellipticity certificate
for the actual coefficient field on any measurable region. -/
theorem isEllipticFieldOn_coefficientCutoff_of_entry_bound (M : ABKModel d)
    (m : ℤ) (omega : CutoffSample d) {U : Set (Vec d)}
    (hU : MeasurableSet U) (C : ℝ)
    (hentry : ∀ x ∈ U, ∀ i j, |coefficientCutoff M.nu m omega x i j| ≤ C) :
    IsEllipticFieldOn M.nu (((d : ℝ) * (d : ℝ) * C ^ 2 + M.nu ^ 2) / M.nu)
      U (coefficientCutoff M.nu m omega) := by
  refine ⟨?_, ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact ((coefficientCutoff M.nu m omega).entry_measurable i j).ite hU measurable_const
  · intro x hx
    exact isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
      (symmPart_coefficientCutoff M.nu m omega x) (hentry x hx)

end

end Algsuperdiff.Section3.Cutoff
