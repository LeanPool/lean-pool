/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.ClosureLemma
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Statements.BoundedNearOrigin
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.IsAxisymmetricOn
public import LeanPool.CIVAxisymmetric.Statements.MeridionalSmallness
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

/-!
# Closure Lemma

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Lemma 5.1 (`lem:aniso:closure`). -/
theorem closureLemma (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hMf : ForceC2Bounded f)
    (ρ₀ : ℝ) (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) (hsmall : MeridionalSmallness ρ₀ u) :
    BoundedNearOrigin u :=
by exact CIV.Main.closureLemma q u Du p f hsol henergy hu hp hf haxi hfaxi hMf ρ₀ hρ₀ hsmall

end CIV
