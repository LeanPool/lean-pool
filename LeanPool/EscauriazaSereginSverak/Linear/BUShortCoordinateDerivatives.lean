/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEtaScalarBounds

/-!
# Factor-wise derivatives of height and time functions

The scalar derivatives of a height-dependent cutoff agree with its
spatial derivatives in the normal coordinate.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A scalar function of height has only one spatial derivative. -/
theorem bu_spatialPartial_height
    (g : ℝ → ℝ) (z : ParabolicPoint)
    (hgd : DifferentiableAt ℝ g (z.1 2)) (j : Fin 3) :
    spatialPartial (fun q : ParabolicPoint => g (q.1 2)) j z =
      deriv g (z.1 2) * (if j = 2 then 1 else 0) := by
  let P : Vec3 →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3)
  have hp : HasFDerivAt (fun x : Vec3 => x 2) P z.1 :=
    P.hasFDerivAt
  have hg := hgd.hasDerivAt.hasFDerivAt.comp z.1 hp
  change HasFDerivAt (fun x : Vec3 => g (x 2)) _ z.1 at hg
  unfold spatialPartial
  have hderiv :
      (fderiv ℝ (fun x : Vec3 => g (x 2)) z.1) (basisVec j) =
        deriv g (z.1 2) * (P (basisVec j)) := by
    rw [hg.fderiv]
    change P (basisVec j) • deriv g (z.1 2) = _
    simp [smul_eq_mul, mul_comm]
  rw [hderiv]
  simp only [P, ContinuousLinearMap.proj_apply, basisVec_apply]
  by_cases h : j = 2 <;> simp [h, eq_comm]

/-- The diagonal second spatial derivatives of a height function are
zero except in the normal coordinate. -/
theorem bu_spatialSecondPartial_height_diag
    (g : ℝ → ℝ) (z : ParabolicPoint)
    (hgd : Differentiable ℝ g)
    (hdd : DifferentiableAt ℝ (deriv g) (z.1 2))
    (j : Fin 3) :
    spatialSecondPartial (fun q : ParabolicPoint => g (q.1 2)) j j z =
      if j = 2 then deriv (deriv g) (z.1 2) else 0 := by
  by_cases hj : j = 2
  · subst j
    have hfun :
        (fun q : ParabolicPoint =>
          spatialPartial (fun p : ParabolicPoint => g (p.1 2)) 2 q) =
        (fun q : ParabolicPoint => deriv g (q.1 2)) := by
      funext q
      rw [bu_spatialPartial_height g q (hgd _) 2]
      norm_num
    rw [spatialSecondPartial, hfun,
      bu_spatialPartial_height (deriv g) z hdd 2]
    norm_num
  · have hfun :
        (fun q : ParabolicPoint =>
          spatialPartial (fun p : ParabolicPoint => g (p.1 2)) j q) =
        (fun _ : ParabolicPoint => 0) := by
      funext q
      rw [bu_spatialPartial_height g q (hgd _) j]
      simp [hj]
    rw [spatialSecondPartial, hfun]
    simp [spatialPartial, hj]

/-- A scalar function of time has the expected time partial derivative. -/
theorem bu_timePartial_time
    (g : ℝ → ℝ)
    (z : ParabolicPoint) :
    timePartial (fun q : ParabolicPoint => g q.2) z = deriv g z.2 := by
  unfold timePartial
  rfl

end ESS
