/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Reduction.AnnulusBoundWholeBallAssembly
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.ClassicalBridge
public import LeanPool.CIVAxisymmetric.Main.SerrinInteriorEstimates

/-!
# The public statement `CIV.Main.regularAnnulus`

This module proves the statement `CIV.regularAnnulus` (`lem:aniso:annulus`). The annulus assembly
`CIV.exists_annulus_bound_wholeBall_conditional_on_serrin` takes two inputs beyond the standing
data: the classical form of the equations, supplied by the weak-to-classical bridge
`CIV.isClassicalSolutionOn_of_suitable`, and Serrin's interior derivative estimate
`CIV.Main.serrinInteriorEstimates`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of the regular-annulus lemma `lem:aniso:annulus`: between any two radii
`R₁ < R₀ < 1` there is an annulus and a final time interval on which the derivatives of `u` of
order at most two are bounded, and on every smaller ball the circulation is bounded. -/
theorem regularAnnulus (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR : 0 ≤ R₁ ∧ R₁ < R₀ ∧ R₀ < 1) :
    ∃ Rm Rp t₀ : ℝ, R₁ < Rm ∧ Rm < Rp ∧ Rp < R₀ ∧ t₀ ∈ Ioo (-1 : ℝ) 0 ∧
      (∃ M : ℝ, ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
        ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
          |multiPartial (fun w => u w i) α (x, t)| ≤ M) ∧
      ∀ Rstar ∈ Ioo Rm Rp, ∃ CΓ : ℝ,
        ∀ x ∈ vec3Ball 0 Rstar, ∀ t ∈ Ioo t₀ 0, |circulation u (x, t)| ≤ CΓ := by
  have hclassical : IsClassicalSolutionOn u p f unitCylinder :=
    isClassicalSolutionOn_of_suitable hsol hu hp hf
  obtain ⟨Rm, Rp, t₀, h1, h2, h3, ht₀, hM, hΓ⟩ :=
    exists_annulus_bound_wholeBall_conditional_on_serrin q u Du p f hsol henergy hu hp hf
      hclassical haxi hfaxi hMf R₁ R₀ hR.1 hR.2.1 hR.2.2
      (fun Rm Rp t₀ Mu hRm hRmRp hRp ht₀ hbdd Rm' Rp' t₀' h1 h2 h3 h4 h5 =>
        serrinInteriorEstimates q u Du p f hsol henergy hu hp hf hMf Rm Rp t₀
          ⟨hRm, hRmRp, hRp⟩ ht₀ Mu hbdd Rm' Rp' t₀' ⟨h1, h2, h3⟩ ⟨h4, h5⟩)
  refine ⟨Rm, Rp, t₀, h1, h2, h3, ht₀, hM, fun Rstar hRstar => ?_⟩
  obtain ⟨CΓ, hCΓ⟩ := hΓ Rstar hRstar
  refine ⟨CΓ, fun x hx t ht => hCΓ x ?_ t ht⟩
  simpa using hx

end Main
end CIV
