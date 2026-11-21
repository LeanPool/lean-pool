/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsStationarity

/-! # Actual compact Euclidean Hessian energy

The exact identity controlling every second derivative by the Laplacian
is the smooth compact estimate used in local weak H² regularity through
actual mollification. No weak regularity theorem is assumed here.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual Laplacian of a C³ function is C¹. -/
theorem euclideanLaplacian_contDiff_one {f : E → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 (euclideanLaplacian f) := by
  have hd (i : Fin d) : ContDiff ℝ 2 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hdd (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i (coordinateDerivative i f)) := by
    apply contDiff_coordinateDerivative
    convert hd i using 1
    norm_num
  change ContDiff ℝ 1 (fun x => ∑ i : Fin d, coordinateDerivative i (coordinateDerivative i f) x)
  fun_prop

/-- Actual compactly supported C³ functions satisfy the exact Hessian/Laplacian
L² identity. This is a proved elliptic estimate, not a regularity premise. -/
theorem compact_euclidean_hessian_energy_eq_laplacian {f : E → ℝ}
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    (∫ x, ∑ i : Fin d, ∑ j : Fin d, (coordinateDerivative j (coordinateDerivative i f) x) ^ 2) =
      ∫ x, (euclideanLaplacian f x) ^ 2 := by
  let V : E → ℝ := fun _ => 0
  have hV : ContDiff ℝ 2 V := contDiff_const
  have hL : langevinDifferentialOperator V f = euclideanLaplacian f := by
    ext x
    simp [langevinDifferentialOperator, V, gradient_fun_const]
  have hμ : gibbsMeasure volume V = volume := by simp [gibbsMeasure, V]
  have hdom := bochnerIntegrationDomain_of_hasCompactSupport hV hf hfc
  have hB := integrated_bochner_identity hV hf hdom
  rw [hL, hμ] at hB
  have hpot (x : E) : fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) = 0 := by
    simp [V]
  simp_rw [hpot] at hB
  simp only [integral_zero, add_zero] at hB
  have hLapc : HasCompactSupport (euclideanLaplacian f) := by
    rw [← hL]
    exact hasCompactSupport_langevinDifferentialOperator V hfc
  have hE := compact_test_gibbs_energy hV (euclideanLaplacian_contDiff_one hf)
    (hf.of_le (by norm_num)) hLapc
  rw [hL, hμ] at hE
  have hs : (∫ x, inner ℝ (gradient (euclideanLaplacian f) x) (gradient f x)) =
      ∫ x, inner ℝ (gradient f x) (gradient (euclideanLaplacian f) x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => real_inner_comm _ _)
  rw [hs] at hE
  rw [← hB, ← hE]
  simp only [pow_two]

end CutoffRigidity
