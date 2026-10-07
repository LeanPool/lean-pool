/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortEtaCoordinateBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Product rules for the space and phase cutoffs

The spatial cutoff and normal-phase cutoff are differentiated before
the lower-time factor is added.
-/

public section


open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem bu_spatialPartial_add
    {a b : Vec3 × ℝ → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun q => a q + b q) j z =
      spatialPartial a j z + spatialPartial b j z := by
  have hpair : Differentiable ℝ (fun x : Vec3 => ((x, z.2) : Vec3 × ℝ)) := by
    fun_prop
  have ha' : DifferentiableAt ℝ (fun x : Vec3 => a (x, z.2)) z.1 :=
    (ha.differentiable (by simp) _).comp z.1 (hpair _)
  have hb' : DifferentiableAt ℝ (fun x : Vec3 => b (x, z.2)) z.1 :=
    (hb.differentiable (by simp) _).comp z.1 (hpair _)
  unfold spatialPartial
  change (fderiv ℝ ((fun x : Vec3 => a (x, z.2)) +
    (fun x : Vec3 => b (x, z.2))) z.1) (basisVec j) = _
  rw [fderiv_add ha' hb']
  rfl

/-- The diagonal Hessian of a product has the two cross terms of the
ordinary product rule. -/
theorem bu_spatialSecondPartial_mul_full
    {a b : Vec3 × ℝ → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (j : Fin 3) (z : ParabolicPoint) :
    spatialSecondPartial (fun q => a q * b q) j j z =
      spatialSecondPartial a j j z * b z +
      2 * spatialPartial a j z * spatialPartial b j z +
      a z * spatialSecondPartial b j j z := by
  have hfun :
      (fun q : ParabolicPoint =>
        spatialPartial (fun w => a w * b w) j q) =
      (fun q => spatialPartial a j q * b q +
        a q * spatialPartial b j q) := by
    funext q
    exact CKN.Core.Step3.spatialPartial_mul_full ha hb j q
  unfold spatialSecondPartial
  rw [hfun]
  have ha' : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => spatialPartial a j q) :=
    spatialPartial_contDiff ha j
  have hb' : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => spatialPartial b j q) :=
    spatialPartial_contDiff hb j
  rw [bu_spatialPartial_add (ha'.mul hb) (ha.mul hb') j z]
  calc
    spatialPartial (fun q => spatialPartial a j q * b q) j z +
      spatialPartial (fun q => a q * spatialPartial b j q) j z =
        (spatialPartial (fun q => spatialPartial a j q) j z * b z +
          spatialPartial a j z * spatialPartial b j z) +
        (spatialPartial a j z * spatialPartial b j z +
          a z * spatialPartial (fun q => spatialPartial b j q) j z) := by
          congr 1
          · exact CKN.Core.Step3.spatialPartial_mul_full ha' hb j z
          · exact CKN.Core.Step3.spatialPartial_mul_full ha hb' j z
    _ = _ := by ring

end ESS
