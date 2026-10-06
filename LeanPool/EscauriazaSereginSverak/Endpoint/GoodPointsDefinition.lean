/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Good points for the endpoint regularity argument

The domains and energy in this file use the spatial and parabolic conventions
of `def:good-point`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The open space-time cylinder used in `def:good-point`. -/
@[expose] def goodPointPastCylinder (x : Vec3) (t r : ℝ) : Set ParabolicPoint :=
  vec3Ball x r ×ˢ Ioo (t - r ^ 2) t

/-- The open domain and its closed top face used in `def:good-point`. -/
@[expose] def goodPointDomain : Set ParabolicPoint :=
  vec3Ball 0 1 ×ˢ Ioo (-1) 0

@[expose] def goodPointClosedTopDomain : Set ParabolicPoint :=
  vec3Ball 0 1 ×ˢ Ioc (-1) 0

/-- The nonnegative velocity and pressure energy on a past cylinder. The
CKN cylinder includes its top slice, which is null for space-time volume. -/
@[expose] def goodPointEnergy (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (x : Vec3) (t r : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in parabolicCylinder x t r,
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)

/-- A point is good when it has an admissible past cylinder with sufficiently
small normalized velocity and pressure energy. -/
@[expose] def IsGoodPoint (ε₀ : ℝ) (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint) : Prop :=
  z ∈ goodPointClosedTopDomain ∧
    ∃ r : ℝ, 0 < r ∧
      goodPointPastCylinder z.1 z.2 r ⊆ goodPointDomain ∧
      (closure (parabolicCylinder z.1 z.2 r)) ⊆ goodPointClosedTopDomain ∧
      ENNReal.ofReal (r⁻¹ ^ 2) * goodPointEnergy u p z.1 z.2 r <
        ENNReal.ofReal (ε₀ / 8)

/-- The good-point energy is monotone in the cylinder. -/
theorem goodPointEnergy_mono
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {x₁ x₂ : Vec3} {t₁ t₂ r₁ r₂ : ℝ}
    (hsubset : parabolicCylinder x₁ t₁ r₁ ⊆ parabolicCylinder x₂ t₂ r₂) :
    goodPointEnergy u p x₁ t₁ r₁ ≤ goodPointEnergy u p x₂ t₂ r₂ := by
  unfold goodPointEnergy
  exact lintegral_mono_set hsubset

end ESS
