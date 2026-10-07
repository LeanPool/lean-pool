/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedInitialData
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum

/-!
# Classical divergence of the mollified transport field

The smooth convolution of a weakly divergence-free velocity is pointwise
divergence free. This supplies the cancellation in the differentiated energy
estimate.
-/

public section

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The mollified velocity from a Leray-space slice has zero classical
divergence at every spatial point. -/
theorem regUniformMollifiedVelocity_divergence_eq_zero
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hJ : CKN.IsInJ (fun x : Vec3 => u (x, t))) :
    ∀ x : Vec3, ∑ i : Fin 3,
      (fderiv ℝ
        (fun y : Vec3 => regUniformMollifiedVelocity ρ ε hε u (y, t) i) x)
        (CKN.basisVec i) = 0 := by
  let f : Vec3 → Vec3 := fun x => regUniformMollifiedVelocity ρ ε hε u (x, t)
  have hf : f = regUniformMollifiedInitial ρ ε hε
      (fun x : Vec3 => u (x, t)) := rfl
  have hC1 : ∀ i : Fin 3, ContDiff ℝ 1 (fun x : Vec3 => f x i) := by
    have hsmooth := regUniformMollifiedInitial_contDiff ρ ε hε hJ
    rw [hf]
    intro i
    exact (hsmooth.continuousLinearMap_comp
      (ContinuousLinearMap.proj (R := ℝ) i)).of_le
        (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
          WithTop.coe_le_coe.mpr le_top)
  have hdiv : CKN.IsWeakDivFreeL2 f := by
    rw [hf]
    exact CKN.isInJ_weakDivFree (regMollifiedInitial_isInJ ρ ε hε hJ)
  simpa only [f] using
    regUniform_weakDivFree_contDiff_divergence_eq_zero hC1 hdiv

end CKN.Leray

end
