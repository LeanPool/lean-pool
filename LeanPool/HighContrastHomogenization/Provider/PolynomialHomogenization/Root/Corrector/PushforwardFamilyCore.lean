/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardWeakGradient

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardFamilyCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pushforward corrector family: definitions and the corrector equation

The identity-gauge producer reduces the stationary corrector family clause to
`RootNormalizedSupply`, a **change of comparison
matrix**: it asks the certificate for an identity-gauge weak-error row, while
the root's certificate supplies an `abar`-gauge one.  No lemma anywhere
transports between the two.

This module executes the architectural repair.  The physical corrector is
*defined* as the affine pushforward of the normalized-gauge one, so the
certificate-side demand becomes the normalized-gauge datum the converter
already produces.

This module carries the normalized-gauge event and its invariant core, the
pushforward value and gradient families, and the two clauses that need no gauge
algebra: the weak-gradient pair on `Set.univ` and the physical corrector
equation.  The slope-linearity and integer-covariance clauses, the marker and
the hole itself are in `PushforwardGaugeAlgebra` and `PushforwardFamilyClauses`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The normalized-gauge event and its invariant core -/

/-- The samples whose normalized-gauge reading carries the intrinsic datum. -/
@[expose]
def pushforwardEventSet (d : ℕ) [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) : Set (CoeffSpace d) :=
  {a | RootCorrectorEvent d (normalizedSample abar hS a)}

/-- Its invariant core under integer translations of the physical sample. -/
@[expose]
def pushforwardCore (d : ℕ) [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) : Set (CoeffSpace d) :=
  invariantTranslationCore (pushforwardEventSet d abar hS)

theorem pushforwardEvent_of_mem_core [NeZero d] {abar : Mat d}
    {hS : (symmPart abar).PosDef} {a : CoeffSpace d}
    (ha : a ∈ pushforwardCore d abar hS) (z : Fin d → ℤ) :
    RootCorrectorEvent d (normalizedSample abar hS (translateCoeff z a)) :=
  mem_invariantTranslationCore_iff.mp ha z

theorem pushforwardEvent_of_mem_core_self [NeZero d] {abar : Mat d}
    {hS : (symmPart abar).PosDef} {a : CoeffSpace d}
    (ha : a ∈ pushforwardCore d abar hS) :
    RootCorrectorEvent d (normalizedSample abar hS a) := by
  simpa only [translateCoeff_zero] using pushforwardEvent_of_mem_core ha 0

/-! ## Transporting almost-everywhere identities through the gauge -/

/-- The inverse gauge root is quasi-measure-preserving on `Vec d`. -/
theorem quasiMeasurePreserving_matVecMul_gaugeRootInv [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    Measure.QuasiMeasurePreserving (matVecMul (gaugeRoot abar)⁻¹)
      (volume : Measure (Vec d)) volume := by
  refine ⟨(continuous_matVecMul _).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := (gaugeRoot abar)⁻¹) (isUnit_det_gaugeRoot_inv hS).ne_zero
  change Measure.map (Matrix.toLin' (gaugeRoot abar)⁻¹) volume ≪ volume
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

/-! ## The pushforward family -/

/-- The pushforward value family: the affine pushforward of the normalized-gauge
carrier at the pulled-back slope, extended by zero off the invariant core. -/
@[expose]
def pushforwardPhysicalPhi (d : ℕ) [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) : Vec d → CoeffSpace d → Vec d → ℝ :=
  fun e => Set.indicator (pushforwardCore d abar hS) fun b =>
    pushforwardValue abar (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
      (normalizedSample abar hS b))

/-- The pushforward gradient family. -/
@[expose]
def pushforwardPhysicalGradPhi (d : ℕ) [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) : Vec d → CoeffSpace d → Vec d → Vec d :=
  fun e => Set.indicator (pushforwardCore d abar hS) fun b =>
    pushforwardGradient abar (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
      (normalizedSample abar hS b))

theorem pushforwardPhysicalPhi_of_mem [NeZero d] {abar : Mat d}
    {hS : (symmPart abar).PosDef} {a : CoeffSpace d}
    (ha : a ∈ pushforwardCore d abar hS) (e : Vec d) :
    pushforwardPhysicalPhi d abar hS e a =
      pushforwardValue abar (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
        (normalizedSample abar hS a)) :=
  Set.indicator_of_mem ha _

theorem pushforwardPhysicalGradPhi_of_mem [NeZero d] {abar : Mat d}
    {hS : (symmPart abar).PosDef} {a : CoeffSpace d}
    (ha : a ∈ pushforwardCore d abar hS) (e : Vec d) :
    pushforwardPhysicalGradPhi d abar hS e a =
      pushforwardGradient abar (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
        (normalizedSample abar hS a)) :=
  Set.indicator_of_mem ha _

/-! ## The corrector equation -/

/-- The normalized-gauge Liouville membership of the selected carrier at a
pulled-back slope, from the datum's value-growth row. -/
theorem memLiouvilleClass_gaugeCoeff_rootJointCarrier [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (a : CoeffSpace d) (e : Vec d)
    (hevent : RootCorrectorEvent d (normalizedSample abar hS a)) :
    MemLiouvilleClass (gaugeCoeff a abar hS) rootCorrectorGrowth
      (fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
        (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
          (normalizedSample abar hS a)).globalValueRepresentative y)
      (fun y ↦ matVecMul (gaugeRoot abar) e +
        (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
          (normalizedSample abar hS a)).globalGradientRepresentative y) := by
  have hellS : IsAELocallyUniformlyElliptic
      (⇑(normalizedSample abar hS a).1 : CoeffField d) :=
    (normalizedSample abar hS a).2
  obtain ⟨qVal, C, hC, hValTail⟩ :=
    (selectedRootCorrectorData (normalizedSample abar hS a) hevent).valueGrowth
      (matVecMul (gaugeRoot abar) e)
  rw [← rootJointCarrier_of_event (matVecMul (gaugeRoot abar) e) hevent] at hValTail
  have hEquation := (rootJointCarrier_equation hevent
    (matVecMul (gaugeRoot abar) e)).2
  have hLiouSample := memLiouvilleClass_affineAdd_of_cubeGrowth
    (rootJointCarrier d (matVecMul (gaugeRoot abar) e)
      (normalizedSample abar hS a))
    (matVecMul (gaugeRoot abar) e) hEquation qVal C hC hValTail
    rootCorrectorGrowth_pos hellS
  exact (memLiouvilleClass_congr_coefficient (normalizedSample_ae abar hS a)
    hellS (isAELocallyUniformlyElliptic_gaugeCoeff a abar hS)).mp hLiouSample

/-- On the core the pushforward pair is a global weak-gradient pair and solves
the physical corrector equation at every slope. -/
theorem pushforwardPhysical_equation (d : ℕ) [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) {a : CoeffSpace d}
    (ha : a ∈ pushforwardCore d abar hS) (e : Vec d) :
    HasWeakGradientOn Set.univ (pushforwardPhysicalPhi d abar hS e a)
        (pushforwardPhysicalGradPhi d abar hS e a) ∧
      IsWeakSolutionOn (fun y ↦ a.1 y) Set.univ
        (fun y ↦ e + pushforwardPhysicalGradPhi d abar hS e a y) := by
  have hevent := pushforwardEvent_of_mem_core_self ha
  rw [pushforwardPhysicalPhi_of_mem ha e, pushforwardPhysicalGradPhi_of_mem ha e]
  exact ⟨hasWeakGradientOn_univ_pushforward hS _,
    pushforward_isWeakSolutionOn a abar hS _ e
      (memLiouvilleClass_gaugeCoeff_rootJointCarrier hS a e hevent)⟩
end

end Root
end HighContrast
end HCPolySupport
