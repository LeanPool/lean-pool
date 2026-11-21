/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.Decay
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.ProductH1
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DeltaPCentred
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials

/-!
# Pressure Gradient Base

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The distributional pressure-Laplacian pairing. -/

/-- Distributional pressure Poisson identity on a spatial domain, retaining the force
contribution. -/
def HasPressureDeltaOn {U : Set Vec3} (p : Vec3 → ℝ)
    (u : Vec3 → Vec3) (f : Vec3 → Vec3) : Prop :=
  ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∫ x in U, p x * spatialLaplacian ψ x =
      -(∫ x in U, ∑ i, ∑ j, u x i * u x j * mixedSecond ψ i j x) -
        (∫ x in U, ∑ i, f x i * spatialDeriv ψ i x)

end CKN.Core.Step4
