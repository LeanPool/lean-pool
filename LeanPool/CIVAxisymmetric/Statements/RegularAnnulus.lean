/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.RegularAnnulus
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Statements.Circulation
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.IsAxisymmetricOn
public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Regular Annulus

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Lemma 3.2 (`lem:aniso:annulus`). -/
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
  exact CIV.Main.regularAnnulus q u Du p f hsol henergy hu hp hf haxi hfaxi hMf R₁ R₀ hR

end CIV
