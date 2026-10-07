/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedError

/-!
# Quadratic heat energy from weak `L²` data

The weak heat vector is square-integrable whenever its specified second
spatial and time derivative fields are square-integrable.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The squared Euclidean norm of the weak heat vector is integrable
from `L²` second spatial and time derivative data. -/
theorem bu_memLp_heat_sq_integrable
    (S : Set ParabolicPoint)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hD2w : MemLp D2w 2 (volume.restrict S))
    (hDtw : MemLp Dtw 2 (volume.restrict S)) :
    IntegrableOn (fun z =>
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ^ 2)
      S volume := by
  let μ := volume.restrict S
  let L := ucWeakHeatVector D2w Dtw
  have hLm : MemLp L 2 μ := by
    apply MemLp.of_eval
    intro i
    have h0 := (((hD2w.eval i).eval (0 : Fin 3)).eval (0 : Fin 3))
    have h1 := (((hD2w.eval i).eval (1 : Fin 3)).eval (1 : Fin 3))
    have h2 := (((hD2w.eval i).eval (2 : Fin 3)).eval (2 : Fin 3))
    have hsum : MemLp (fun z => ∑ j : Fin 3, D2w z i j j) 2 μ := by
      convert (h0.add h1).add h2 using 1
      funext z
      simp only [Fin.sum_univ_three, Pi.add_apply]
    convert (hDtw.eval i).add hsum using 1
    funext z
    rfl
  have hnormInt : Integrable (fun z => ‖L z‖ ^ 2) μ := by
    simpa only [μ] using hLm.integrable_norm_pow (p := 2) (by norm_num)
  have hEuMeas : AEStronglyMeasurable
      (fun z => vec3EuclideanNorm (L z) ^ 2) μ :=
    (continuous_vec3EuclideanNorm.pow 2).comp_aestronglyMeasurable
      hLm.aestronglyMeasurable
  have hbound (z : ParabolicPoint) :
      vec3EuclideanNorm (L z) ^ 2 ≤ 3 * ‖L z‖ ^ 2 := by
    have h := vec3EuclideanNorm_le_sqrt_three_mul_norm (L z)
    have hs : Real.sqrt 3 ^ 2 = (3 : ℝ) := by norm_num
    have hnn : 0 ≤ vec3EuclideanNorm (L z) := vec3EuclideanNorm_nonneg _
    have hn : 0 ≤ Real.sqrt 3 * ‖L z‖ := by positivity
    nlinarith only [h, hs, hnn, hn, sq_nonneg (‖L z‖)]
  have hEuInt : Integrable (fun z => vec3EuclideanNorm (L z) ^ 2) μ := by
    apply Integrable.mono' (hnormInt.const_mul 3) hEuMeas
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound z
  exact hEuInt

end ESS
