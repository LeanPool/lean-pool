/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.JointAEEqTransfer

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.PhysicalClassBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A canonical global gradient representative is square integrable on every
integer-scale origin cube, including negative scales. -/
theorem memVectorL2_globalGradient_originCube
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℤ) :
    MemVectorL2 (openCubeSet (originCube d n))
      z.globalGradientRepresentative := by
  let q : ℕ := originCubeCoverGeneration n
  have hsub : openCubeSet (originCube d n) ⊆
      localGradientCube d q := by
    simpa only [q, localGradientCube] using
      openCubeSet_originCube_subset_of_le (le_originCubeCoverGeneration n)
  have hmeasure : volumeMeasureOn (openCubeSet (originCube d n)) ≤
      volumeMeasureOn (localGradientCube d q) :=
    Measure.restrict_mono_set volume hsub
  exact (z.memLp_globalGradientRepresentative q).mono_measure hmeasure

/-- The integer local component is exactly the `L²` class of the canonical
global representative on that cube. -/
theorem correctorGradientOnOriginCube_eq_globalRepresentative
    {d : ℕ} (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (n : ℤ) :
    correctorGradientOnOriginCube Phi e n =
      toHilbertVectorL2OfVecField
        (memVectorL2_globalGradient_originCube (Phi e) n) := by
  let q : ℕ := originCubeCoverGeneration n
  have hnq : n ≤ (q : ℤ) := le_originCubeCoverGeneration n
  unfold correctorGradientOnOriginCube
  rw [LocalGradientCarrier.originCubeComponent_eq_restrict_component
    (Phi e).gradient q hnq]
  apply Lp.ext
  have hmu : volumeMeasureOn (openCubeSet (originCube d n)) ≤
      volumeMeasureOn (localGradientCube d q) :=
    Measure.restrict_mono_set volume (by
      simpa only [q, localGradientCube] using
        openCubeSet_originCube_subset_of_le hnq)
  filter_upwards [
    originCubeL2Restrict_coeFn_ae hnq ((Phi e).gradientComponent q),
    ((Phi e).globalGradientRepresentative_ae_eq_component q).filter_mono
      (ae_mono hmu),
    (coeFn_hilbertVectorL2ToVectorL2
      ((Phi e).gradientComponent q)).filter_mono (ae_mono hmu),
    coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_globalGradient_originCube (Phi e) n)]
      with x hleft hglobal hcomponent hright
  change
    ((originCubeL2Restrict hnq)
      (LocalGradientCarrier.component (Phi e).gradient q) x) =
      (LocalGradientCarrier.component (Phi e).gradient q) x at hleft
  rw [hleft, hright]
  have hvec := congrArg HilbertVec.ofVec (hglobal.trans hcomponent)
  simpa only [HilbertVec.ofVec_toVec] using! hvec.symm

/-- The local negative-one norm of the gradient class reads the canonical raw
global gradient field. -/
theorem localNegOneNorm_correctorGradient_eq_global
    {d : ℕ} (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (n : ℤ) :
    localNegOneNorm (openCubeSet (originCube d n))
        (correctorGradientOnOriginCube Phi e n) =
      negOneNorm (openCubeSet (originCube d n))
        (Phi e).globalGradientRepresentative := by
  rw [correctorGradientOnOriginCube_eq_globalRepresentative]
  exact localNegOneNorm_toHilbertVectorL2OfVecField
    (memVectorL2_globalGradient_originCube (Phi e) n)

/-- The local identity-flux class reads the literal cube-family coefficient
times the canonical full gradient. -/
theorem localNegOneNorm_correctorFlux_eq_global
    {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (n : ℤ) :
    localNegOneNorm (openCubeSet (originCube d n))
        (scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e n) =
      negOneNorm (openCubeSet (originCube d n))
        (fun x ↦ matVecMul ((a.coeffOn (originCube d n)).toCoeffField x)
          (e + (Phi e).globalGradientRepresentative x) - e) := by
  let hmem := memVectorL2_globalGradient_originCube (Phi e) n
  have hgrad : correctorGradientOnOriginCube Phi e n =
      toHilbertVectorL2OfVecField hmem := by
    exact correctorGradientOnOriginCube_eq_globalRepresentative Phi e n
  have hclass := scalarIdentityCorrectorFluxDefectOnOriginCube_toVec_ae
    a Phi e n hmem hgrad
  have hcoeff := Book.Ch03.publicCoeffField_ae_eq_openCubeSet
    (originCube d n) a
  have hraw :
      (fun x ↦
        (scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e n x).toVec)
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
      fun x ↦ matVecMul ((a.coeffOn (originCube d n)).toCoeffField x)
        (e + (Phi e).globalGradientRepresentative x) - e := by
    filter_upwards [hclass, hcoeff] with x hx hax
    rw [hx, hax]
  unfold localNegOneNorm
  exact negOneNorm_eq_of_ae_eq_on hraw

/-- The class-level inverse-scale pair used by the finite-to-limit theorem is
the raw canonical-gradient/canonical-flux pair used by affine transport. -/
theorem triadicScaledNegOne_pair_eq_global
    {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (n : ℤ) :
    triadicScaledNegOneNorm n (correctorGradientOnOriginCube Phi e n) +
        triadicScaledNegOneNorm n
          (scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e n) =
      ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
        (negOneNorm (openCubeSet (originCube d n))
            (Phi e).globalGradientRepresentative +
          negOneNorm (openCubeSet (originCube d n))
            (fun x ↦ matVecMul ((a.coeffOn (originCube d n)).toCoeffField x)
              (e + (Phi e).globalGradientRepresentative x) - e)) := by
  unfold triadicScaledNegOneNorm
  rw [localNegOneNorm_correctorGradient_eq_global,
    localNegOneNorm_correctorFlux_eq_global, mul_add]

end

end HighContrast
end HCPolySupport
