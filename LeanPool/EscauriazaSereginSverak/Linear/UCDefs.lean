/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussWeights
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantities for Gaussian unique continuation

The cylinder, Gaussian weight, and integral flatness condition are those of
`lem:uc-gaussian`. The flatness predicate records the local all-orders
integral assumption of that lemma.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weak heat operator formed from the specified second and time weak
derivatives. -/
@[expose] def ucWeakHeatVector (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  fun i => Dtw z i + ∑ j : Fin 3, D2w z i j j

/-- Integral vanishing of every order at a boundary point
(`eq:uc-integral-vanishing`). -/
@[expose] def UCIntegralFlatness (x₀ : Vec3) (R T : ℝ)
    (w : ParabolicPoint → Vec3) : Prop :=
  ∀ m : ℕ, ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r < min R (min (Real.sqrt T) r₀) →
      (∫ z in spaceTimeSet (vec3Ball x₀ r) (Ioo 0 (r ^ 2)),
        vec3EuclideanNorm (w z) ^ 2) ≤ C * r ^ m

/-- The unweighted energy over the smaller cylinder used in the Gaussian
box estimate (`lem:uc-gaussian`). -/
@[expose] def ucLocalEnergy (x₀ : Vec3) (R T : ℝ)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3) : ℝ :=
  ∫ z in spaceTimeSet (vec3Ball x₀ (3 * R / 4)) (Ioo 0 (3 * T / 4)),
    vec3EuclideanNorm (w z) ^ 2 + T * spatialGradientSq w Dw z

/-- Gaussian weight in `lem:uc-gaussian`. -/
@[expose] def ucGaussianWeight (a : ℝ) (z : ParabolicPoint) : ℝ :=
  gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
    Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))

/-- The scaled positive-time cylinder. -/
@[expose] def ucCylinder (ρ : ℝ) : Set ParabolicPoint :=
  spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 2)

/-- The plateau on which the spatial and time cutoffs equal one. -/
@[expose] def ucInnerRegion (ρ : ℝ) : Set ParabolicPoint :=
  spaceTimeSet (vec3Ball 0 (ρ / 2)) (Ioo 0 (3 / 2))

/-- The region supporting derivatives of the spatial and final-time cutoffs. -/
@[expose] def ucCutoffRegion (ρ : ℝ) : Set ParabolicPoint :=
  ucCylinder ρ \ ucInnerRegion ρ

/-- Parabolic translation and dilation about a boundary point. -/
@[expose] def ucScaledPoint (x₀ : Vec3) (scale : ℝ) (z : ParabolicPoint) : ParabolicPoint :=
  (x₀ + scale • z.1, scale ^ 2 * z.2)

/-- A field viewed in translated parabolic coordinates. -/
@[expose] def ucScaledField (x₀ : Vec3) (scale : ℝ)
    (w : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z => w (ucScaledPoint x₀ scale z)

/-- The first weak spatial derivative under parabolic dilation. -/
@[expose] def ucScaledDw (x₀ : Vec3) (scale : ℝ)
    (Dw : ParabolicPoint → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Vec3 :=
  fun z i j => scale * Dw (ucScaledPoint x₀ scale z) i j

/-- The second weak spatial derivative under parabolic dilation. -/
@[expose] def ucScaledD2w (x₀ : Vec3) (scale : ℝ)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
  fun z i j k => scale ^ 2 * D2w (ucScaledPoint x₀ scale z) i j k

/-- The time weak derivative under parabolic dilation. -/
@[expose] def ucScaledDtw (x₀ : Vec3) (scale : ℝ)
    (Dtw : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z i => scale ^ 2 * Dtw (ucScaledPoint x₀ scale z) i

end ESS
