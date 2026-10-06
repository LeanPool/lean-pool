/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.GaugeSlopeResidue
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardAffineGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffinePullbackCoeffSpace

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The affine pushforward of a normalized-gauge corrector

The physical corrector is *defined* as the affine pushforward, by the
normalized root, of a normalized-gauge corrector carrier.  This module builds
the transport that makes the physical corrector equation a consequence of the
normalized one: the available physical/normalized Liouville equivalence, read in
the `mpr` direction at the pushed-forward pair.

Nothing here selects a family; the carrier is a parameter.  What is proved is
that the *gauge* costs nothing once the construction is placed in the
normalized frame.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The normalized root attached to a homogenized matrix, as a total
definition (positive definiteness is used only by the proofs). -/
@[expose]
def gaugeRoot (abar : Mat d) : Mat d := Selection.normalizedRoot (symmPart abar)

/-- The affine pushforward of a normalized-gauge corrector value. -/
@[expose]
def pushforwardValue (abar : Mat d) (G : NormalizedLocalH1Carrier d) (x : Vec d) : ℝ :=
  G.globalValueRepresentative (matVecMul (gaugeRoot abar)⁻¹ x)

/-- The affine pushforward of a normalized-gauge corrector gradient. -/
@[expose]
def pushforwardGradient (abar : Mat d) (G : NormalizedLocalH1Carrier d) (x : Vec d) :
    Vec d :=
  matVecMul (gaugeRoot abar)⁻¹
    (G.globalGradientRepresentative (matVecMul (gaugeRoot abar)⁻¹ x))

/-! ## Gauge algebra -/

theorem isUnit_det_gaugeRoot [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) : IsUnit (gaugeRoot abar).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp
    (normalizedRoot_posDef_of_posDef hS).isUnit

theorem matTranspose_gaugeRoot [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) :
    matTranspose (gaugeRoot abar) = gaugeRoot abar :=
  matTranspose_normalizedRoot hS

theorem gaugeRoot_inv_apply [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (x : Vec d) :
    matVecMul (gaugeRoot abar)⁻¹ (matVecMul (gaugeRoot abar) x) = x := by
  rw [matVecMul_mul, Matrix.nonsing_inv_mul _ (isUnit_det_gaugeRoot hS)]
  exact matVecMul_one x

theorem gaugeRoot_apply_inv [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (x : Vec d) :
    matVecMul (gaugeRoot abar) (matVecMul (gaugeRoot abar)⁻¹ x) = x := by
  rw [matVecMul_mul, Matrix.mul_nonsing_inv _ (isUnit_det_gaugeRoot hS)]
  exact matVecMul_one x

theorem vecDot_gaugeRoot_comm [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) (e y : Vec d) :
    vecDot e (matVecMul (gaugeRoot abar) y) =
      vecDot (matVecMul (gaugeRoot abar) e) y := by
  have h := vecDot_matVecMul_transpose e y (gaugeRoot abar)
  rwa [matTranspose_gaugeRoot hS] at h

/-! ## The normalized-gauge coefficient -/

/-- The normalized-gauge coefficient field of a sample at a homogenized
matrix. -/
@[expose]
def gaugeCoeff [NeZero d] (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) : CoeffField d :=
  affineCoefficient (gaugeRoot abar) (isUnit_det_gaugeRoot hS)
    ⇑(normalizedCenteredCoeff a abar hS).1

/-- The normalized-gauge coefficient is locally uniformly elliptic, with
constants read off the sample on each ball. -/
theorem isAELocallyUniformlyElliptic_gaugeCoeff [NeZero d] (a : CoeffSpace d)
    (abar : Mat d) (hS : (symmPart abar).PosDef) :
    IsAELocallyUniformlyElliptic (gaugeCoeff a abar hS) :=
  isAELocallyUniformlyElliptic_affineCoefficient (gaugeRoot abar)
    (isUnit_det_gaugeRoot hS) (normalizedCenteredCoeff a abar hS).2

/-- **The normalized sample.**  The sample read in the normalized gauge, as an
element of the coefficient space itself.  This is the object the whole
corrector construction can be run on: `RootCorrectorEvent d (normalizedSample
abar hS a)` is the normalized-gauge datum, and every growth row, intrinsic
slope and identification of that construction applies to it unchanged. -/
@[expose]
def normalizedSample [NeZero d] (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : CoeffSpace d) : CoeffSpace d :=
  affinePullbackCoeffSpace (gaugeRoot abar) (isUnit_det_gaugeRoot hS)
    (normalizedCenteredCoeff a abar hS)

/-- The normalized sample is represented almost everywhere by the
normalized-gauge coefficient field. -/
theorem normalizedSample_ae [NeZero d] (abar : Mat d)
    (hS : (symmPart abar).PosDef) (a : CoeffSpace d) :
    (⇑(normalizedSample abar hS a).1 : CoeffField d) =ᵐ[volume]
      gaugeCoeff a abar hS :=
  affinePullbackCoeffSpace_ae _ _ _

/-! ## The transport -/

/-- **The pushforward transport.**  A normalized-gauge Liouville-class corrector
at the pulled-back slope pushes forward to a physical Liouville-class corrector
at the original slope.  Its weak-solution component is exactly the corrector
equation clause of the stationary corrector family clause. -/
theorem pushforward_memLiouvilleClass [NeZero d]
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (G : NormalizedLocalH1Carrier d) (e : Vec d) {theta : ℝ}
    (hLiou : MemLiouvilleClass (gaugeCoeff a abar hS) theta
      (fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
        G.globalValueRepresentative y)
      (fun y ↦ matVecMul (gaugeRoot abar) e +
        G.globalGradientRepresentative y)) :
    MemLiouvilleClass (fun x ↦ a.1 x) theta
      (fun x ↦ vecDot e x + pushforwardValue abar G x)
      (fun x ↦ e + pushforwardGradient abar G x) := by
  have hb := isAELocallyUniformlyElliptic_gaugeCoeff a abar hS
  have hvalue :
      (fun y ↦ vecDot e (matVecMul (gaugeRoot abar) y) +
          pushforwardValue abar G (matVecMul (gaugeRoot abar) y)) =
        fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
          G.globalValueRepresentative y := by
    funext y
    simp only [pushforwardValue]
    rw [gaugeRoot_inv_apply hS, vecDot_gaugeRoot_comm hS]
  have hgradient :
      (fun y ↦ matVecMul (matTranspose (gaugeRoot abar))
        (e + pushforwardGradient abar G (matVecMul (gaugeRoot abar) y))) =
        fun y ↦ matVecMul (gaugeRoot abar) e +
          G.globalGradientRepresentative y := by
    funext y
    simp only [pushforwardGradient]
    rw [matTranspose_gaugeRoot hS, gaugeRoot_inv_apply hS, matVecMul_add,
      gaugeRoot_apply_inv hS]
  refine (memLiouvilleClass_physical_normalizedPullback_iff a abar hS hb
    (Filter.EventuallyEq.refl _ _) _ _).mpr ?_
  show MemLiouvilleClass (gaugeCoeff a abar hS) theta
      (fun y ↦ vecDot e (matVecMul (gaugeRoot abar) y) +
        pushforwardValue abar G (matVecMul (gaugeRoot abar) y))
      (fun y ↦ matVecMul (matTranspose (gaugeRoot abar))
        (e + pushforwardGradient abar G (matVecMul (gaugeRoot abar) y)))
  rw [hvalue, hgradient]
  exact hLiou

/-- **The corrector equation of the pushforward family.** -/
theorem pushforward_isWeakSolutionOn [NeZero d]
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (G : NormalizedLocalH1Carrier d) (e : Vec d) {theta : ℝ}
    (hLiou : MemLiouvilleClass (gaugeCoeff a abar hS) theta
      (fun y ↦ vecDot (matVecMul (gaugeRoot abar) e) y +
        G.globalValueRepresentative y)
      (fun y ↦ matVecMul (gaugeRoot abar) e +
        G.globalGradientRepresentative y)) :
    IsWeakSolutionOn (fun x ↦ a.1 x) Set.univ
      (fun x ↦ e + pushforwardGradient abar G x) :=
  (pushforward_memLiouvilleClass a abar hS G e hLiou).2.1

end

end Root
end HighContrast
end HCPolySupport
