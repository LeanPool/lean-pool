/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakCalculus

/-!
# Linearity of weak spatial derivatives

Weak spatial derivatives of sums, differences and negatives, used to differentiate the vorticity
flux, a sum of products, in the bootstrap of `thm:vorticity-regularity`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak derivative of a difference. -/
theorem vorticity_weakPartial_sub {W : Set (Vec3 × ℝ)} {f₁ f₂ g₁ g₂ : Vec3 × ℝ → ℝ}
    {j : Fin 3} (hf₁ : IntegrableOn f₁ W) (hf₂ : IntegrableOn f₂ W)
    (hg₁ : IntegrableOn g₁ W) (hg₂ : IntegrableOn g₂ W)
    (h₁ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₁ y * spatialPartial ψ j y = -∫ y in W, g₁ y * ψ y)
    (h₂ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₂ y * spatialPartial ψ j y = -∫ y in W, g₂ y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, (f₁ y - f₂ y) * spatialPartial ψ j y =
        -∫ y in W, (g₁ y - g₂ y) * ψ y := by
  intro ψ hψ hψc hψW
  have hd : Continuous (fun y : Vec3 × ℝ => spatialPartial ψ j y) :=
    (CKN.spatialPartial_contDiff hψ j).continuous
  have hdc : HasCompactSupport (fun y : Vec3 × ℝ => spatialPartial ψ j y) :=
    CKN.hasCompactSupport_spatialPartial hψc j
  have e1 : ∫ y in W, (f₁ y - f₂ y) * spatialPartial ψ j y =
      (∫ y in W, f₁ y * spatialPartial ψ j y) - ∫ y in W, f₂ y * spatialPartial ψ j y := by
    rw [← integral_sub (vorticity_integrableOn_mul_smooth hf₁ hd hdc)
      (vorticity_integrableOn_mul_smooth hf₂ hd hdc)]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have e2 : ∫ y in W, (g₁ y - g₂ y) * ψ y =
      (∫ y in W, g₁ y * ψ y) - ∫ y in W, g₂ y * ψ y := by
    rw [← integral_sub (vorticity_integrableOn_mul_smooth hg₁ hψ.continuous hψc)
      (vorticity_integrableOn_mul_smooth hg₂ hψ.continuous hψc)]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [e1, e2, h₁ ψ hψ hψc hψW, h₂ ψ hψ hψc hψW]
  ring

/-- The weak derivative of a sum. -/
theorem vorticity_weakPartial_add {W : Set (Vec3 × ℝ)} {f₁ f₂ g₁ g₂ : Vec3 × ℝ → ℝ}
    {j : Fin 3} (hf₁ : IntegrableOn f₁ W) (hf₂ : IntegrableOn f₂ W)
    (hg₁ : IntegrableOn g₁ W) (hg₂ : IntegrableOn g₂ W)
    (h₁ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₁ y * spatialPartial ψ j y = -∫ y in W, g₁ y * ψ y)
    (h₂ : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f₂ y * spatialPartial ψ j y = -∫ y in W, g₂ y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, (f₁ y + f₂ y) * spatialPartial ψ j y =
        -∫ y in W, (g₁ y + g₂ y) * ψ y := by
  intro ψ hψ hψc hψW
  have hd : Continuous (fun y : Vec3 × ℝ => spatialPartial ψ j y) :=
    (CKN.spatialPartial_contDiff hψ j).continuous
  have hdc : HasCompactSupport (fun y : Vec3 × ℝ => spatialPartial ψ j y) :=
    CKN.hasCompactSupport_spatialPartial hψc j
  have e1 : ∫ y in W, (f₁ y + f₂ y) * spatialPartial ψ j y =
      (∫ y in W, f₁ y * spatialPartial ψ j y) + ∫ y in W, f₂ y * spatialPartial ψ j y := by
    rw [← integral_add (vorticity_integrableOn_mul_smooth hf₁ hd hdc)
      (vorticity_integrableOn_mul_smooth hf₂ hd hdc)]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have e2 : ∫ y in W, (g₁ y + g₂ y) * ψ y =
      (∫ y in W, g₁ y * ψ y) + ∫ y in W, g₂ y * ψ y := by
    rw [← integral_add (vorticity_integrableOn_mul_smooth hg₁ hψ.continuous hψc)
      (vorticity_integrableOn_mul_smooth hg₂ hψ.continuous hψc)]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [e1, e2, h₁ ψ hψ hψc hψW, h₂ ψ hψ hψc hψW]
  ring

/-- The weak derivative of a negative. -/
theorem vorticity_weakPartial_neg {W : Set (Vec3 × ℝ)} {f g : Vec3 × ℝ → ℝ} {j : Fin 3}
    (h : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * spatialPartial ψ j y = -∫ y in W, g y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, -f y * spatialPartial ψ j y = -∫ y in W, -g y * ψ y := by
  intro ψ hψ hψc hψW
  have e1 : ∫ y in W, -f y * spatialPartial ψ j y = -∫ y in W, f y * spatialPartial ψ j y := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have e2 : ∫ y in W, -g y * ψ y = -∫ y in W, g y * ψ y := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [e1, e2, h ψ hψ hψc hψW]

end ESS
