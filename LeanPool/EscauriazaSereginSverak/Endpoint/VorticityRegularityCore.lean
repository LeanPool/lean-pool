/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityStages

/-!
# The regularity of the vorticity on a product box

The time derivative of a solution of a heat equation in divergence form, from the second spatial
derivatives and the derivative of the flux, and the conclusions of `thm:vorticity-regularity` on
the product box `B_{1/2} × (t₀ - 1/4, t₀)`: a continuous bounded representative of the vorticity,
its space-time weak derivatives in `L²`, and the pointwise differential inequality.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak time derivative of a solution of a heat equation in divergence form. -/
theorem vorticityHeat_timeDeriv {W : Set (Vec3 × ℝ)} {w : Vec3 × ℝ → ℝ}
    {g h F Fd : Fin 3 → Vec3 × ℝ → ℝ} (hw : IntegrableOn w W)
    (hh : ∀ j, IntegrableOn (h j) W) (hF : ∀ j, IntegrableOn (F j) W)
    (hFd : ∀ j, IntegrableOn (Fd j) W)
    (heq : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in W, ∑ j : Fin 3, F j y * spatialPartial ψ j y)
    (hdw : ∀ j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, w y * spatialPartial ψ j y = -∫ y in W, g j y * ψ y)
    (hdg : ∀ j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, g j y * spatialPartial ψ j y = -∫ y in W, h j y * ψ y)
    (hdF : ∀ j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, F j y * spatialPartial ψ j y = -∫ y in W, Fd j y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, w y * timePartial ψ y =
        -∫ y in W, (∑ j : Fin 3, h j y + ∑ j : Fin 3, Fd j y) * ψ y := by
  intro ψ hψ hψc hψW
  have iT : IntegrableOn (fun y => w y * timePartial ψ y) W :=
    vorticity_integrableOn_mul_smooth hw (CKN.contDiff_timePartial hψ).continuous
      (CKN.hasCompactSupport_timePartial hψc)
  have iS : ∀ j : Fin 3, IntegrableOn (fun y => w y * spatialSecondPartial ψ j j y) W := fun j =>
    vorticity_integrableOn_mul_smooth hw
      (CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff hψ j) j).continuous
      (CKN.hasCompactSupport_spatialSecondPartial hψc j j)
  have iF : ∀ j : Fin 3, IntegrableOn (fun y => F j y * spatialPartial ψ j y) W := fun j =>
    vorticity_integrableOn_mul_smooth (hF j) (CKN.spatialPartial_contDiff hψ j).continuous
      (CKN.hasCompactSupport_spatialPartial hψc j)
  have iH : ∀ j : Fin 3, IntegrableOn (fun y => h j y * ψ y) W := fun j =>
    vorticity_integrableOn_mul_smooth (hh j) hψ.continuous hψc
  have iFd : ∀ j : Fin 3, IntegrableOn (fun y => Fd j y * ψ y) W := fun j =>
    vorticity_integrableOn_mul_smooth (hFd j) hψ.continuous hψc
  have T1 : ∀ j : Fin 3, ∫ y in W, w y * spatialSecondPartial ψ j j y =
      ∫ y in W, h j y * ψ y := by
    intro j
    have a1 := hdw j _ (CKN.spatialPartial_contDiff hψ j)
      (CKN.hasCompactSupport_spatialPartial hψc j)
      ((CKN.tsupport_spatialPartial_subset j).trans hψW)
    rw [hdg j ψ hψ hψc hψW, neg_neg] at a1
    exact a1
  have L : ∫ y in W, w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
      -(∫ y in W, w y * timePartial ψ y) -
        ∑ j : Fin 3, ∫ y in W, w y * spatialSecondPartial ψ j j y := by
    have hpt : ∀ y, w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -(w y * timePartial ψ y) - ∑ j : Fin 3, w y * spatialSecondPartial ψ j j y :=
      fun y => by rw [mul_sub, mul_neg, Finset.mul_sum]
    refine (integral_congr_ae (Eventually.of_forall hpt)).trans
      ((integral_sub iT.neg (integrable_finsetSum _ fun j _ => iS j)).trans ?_)
    exact congrArg₂ (· - ·) (integral_neg _) (integral_finsetSum _ fun j _ => iS j)
  have R : ∫ y in W, (∑ j : Fin 3, h j y + ∑ j : Fin 3, Fd j y) * ψ y =
      ∑ j : Fin 3, (∫ y in W, h j y * ψ y) + ∑ j : Fin 3, ∫ y in W, Fd j y * ψ y := by
    have hpt : ∀ y, (∑ j : Fin 3, h j y + ∑ j : Fin 3, Fd j y) * ψ y =
        ∑ j : Fin 3, h j y * ψ y + ∑ j : Fin 3, Fd j y * ψ y :=
      fun y => by rw [add_mul, Finset.sum_mul, Finset.sum_mul]
    refine (integral_congr_ae (Eventually.of_forall hpt)).trans
      ((integral_add (integrable_finsetSum _ fun j _ => iH j)
        (integrable_finsetSum _ fun j _ => iFd j)).trans ?_)
    exact congrArg₂ (· + ·) (integral_finsetSum _ fun j _ => iH j)
      (integral_finsetSum _ fun j _ => iFd j)
  have S1 : ∑ j : Fin 3, ∫ y in W, w y * spatialSecondPartial ψ j j y =
      ∑ j : Fin 3, ∫ y in W, h j y * ψ y := Finset.sum_congr rfl fun j _ => T1 j
  have S2 : ∑ j : Fin 3, ∫ y in W, F j y * spatialPartial ψ j y =
      -∑ j : Fin 3, ∫ y in W, Fd j y * ψ y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hdF j ψ hψ hψc hψW
  have H := heq ψ hψ hψc hψW
  rw [L, integral_finsetSum _ fun j _ => iF j] at H
  rw [R]
  linarith only [H, S1, S2]

/-- The absolute value of the negated difference of two sums of two terms. -/
theorem vorticity_abs_neg_sub_le (a b c d : ℝ) :
    |-((a + b) - (c + d))| ≤ |a| + |b| + |c| + |d| :=
  abs_le.2 ⟨by linarith only [le_abs_self a, le_abs_self b, neg_abs_le c, neg_abs_le d],
    by linarith only [neg_abs_le a, neg_abs_le b, le_abs_self c, le_abs_self d]⟩

end ESS
