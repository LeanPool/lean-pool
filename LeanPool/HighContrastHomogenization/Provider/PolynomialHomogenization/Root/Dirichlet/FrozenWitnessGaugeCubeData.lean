/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EpsilonFrameWitnessPrice
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessGaugePullback
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.ForceBesovFromHsNormSq
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.TranslatedCubeEnergyPrice
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.AdaptedCellGaugeGeometry
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedWeakTransport
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ConstantMatrixDualIdentityReduction
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ScheduledLocalizationGaugeReduction
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicScalarControls

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessGaugeCubeData

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the analytic inputs, parts (a) and (c): the gauge-cube data of the frozen witness's the analytic
inputs listed four "genuinely absent" analytic identifications.
This module closes two of them and prepares the third.

* **The gauge-cube pullbacks.**  `exists_frozenWitnessGaugeCubePullbacks` moves
  the physical boundary datum `g₀ : H1Function U` and the gauge solution
  `uHat : H1Function (matImage S⁻¹ U)` onto `openCubeSet (originCube d j)`,
  with *literal* value and gradient identities.  No declaration composes
  the matrix pullback with the translation for `H1Function` (only
  `H10Function` has one, `E15:41`); this supplies it, out of
  `exists_h1Function_affinePullback`, `H1Function.restrict` and
  `H1Function.untranslate`, exactly the way
  `exists_observationCoeffFamily_and_forcedEquation` does internally.

* **(a) `hBesov` and `hL2`.**  `forceBesov_and_memVectorL2_at_frozenWitness`
  discharges module two regularity premises for the pulled-back boundary
  gradient, from the hole's own `hsNormSq U s₀ g₀.grad ≠ ⊤` and nothing else.
  These were thought absent; every ingredient is in fact available, and the
  route is: `H1Function.grad_memVectorL2` → `Response.memVectorL2_affinePullback` →
  `memVectorL2_comp_addRight_of_memVectorL2_translateSet` →
  `memVectorL2_constMatrix_mul` for the `L²` leg;
  `hsNormSq_translateSet_add` → `hsNormSq_matImage_le_opNorm` →
  `hsNormSq_matVecMul_ne_top` for the fractional leg; then E14's
  `forceBesovRegularity_of_hsNormSq_ne_top`, whose **only** consumer in the
  repository is this file.

* **(c) `hFrame`.**  `frozenWitnessFrameTransport` is the one-line gauge
  identity that makes `FTrans w := S (g₀.grad (S w))` satisfy last
  premise; `hF` is then the gradient identity of `gObs` read backwards.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The gauge carrier of the frozen witness -/

/-- The gauge image of the frozen witness domain is a translate of the origin
cube of the witness generation. -/
theorem matImage_matSqrtInv_witness_eq_translateSet {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
      openCubeSet (originCube d j)) :
    matImage (matSqrt (symmPart abar))⁻¹ U =
      translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
        (openCubeSet (originCube d j)) := by
  rw [hU]
  exact matImage_inv_affineImage (isUnit_det_matSqrt hS) z _

/-- The frozen witness domain is open. -/
theorem isOpen_witnessDomain {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
      openCubeSet (originCube d j)) :
    IsOpen U := by
  rw [hU]
  exact isOpen_affineImage (isUnit_det_matSqrt hS) z (isOpen_openCubeSet _)

/-! ## The gauge-cube pullbacks -/

/-- **The `H¹` matrix-and-translation composite at the frozen witness.**  The
physical boundary datum and the gauge solution both land on the origin cube of
the witness generation, with literal value and gradient identities. -/
theorem exists_frozenWitnessGaugeCubePullbacks [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
      openCubeSet (originCube d j))
    (g₀ : H1Function U)
    (uHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U)) :
    ∃ gObs uObs : H1Function (openCubeSet (originCube d j)),
      (∀ y : Vec d, gObs.toFun y =
        g₀.toFun (matVecMul (matSqrt (symmPart abar))
          (y + matVecMul (matSqrt (symmPart abar))⁻¹ z))) ∧
      (∀ y : Vec d, gObs.grad y =
        matVecMul (matSqrt (symmPart abar))
          (g₀.grad (matVecMul (matSqrt (symmPart abar))
            (y + matVecMul (matSqrt (symmPart abar))⁻¹ z)))) ∧
      (∀ y : Vec d, uObs.toFun y =
        uHat.toFun (y + matVecMul (matSqrt (symmPart abar))⁻¹ z)) ∧
      (∀ y : Vec d, uObs.grad y =
        uHat.grad (y + matVecMul (matSqrt (symmPart abar))⁻¹ z)) := by
  have hu' : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hUmeas : MeasurableSet U := (isOpen_witnessDomain hS hU).measurableSet
  have hgauge := matImage_matSqrtInv_witness_eq_translateSet hS hU
  obtain ⟨g₀Hat, hgf, hgg⟩ := exists_h1Function_affinePullback hu' hUmeas g₀
  have htOpen : IsOpen (translateSet (matVecMul (matSqrt (symmPart abar))⁻¹ z)
      (openCubeSet (originCube d j))) :=
    isOpen_translateSet (isOpen_openCubeSet _) _
  refine ⟨H1Function.untranslate (matVecMul (matSqrt (symmPart abar))⁻¹ z)
      (g₀Hat.restrict htOpen hgauge.symm.subset),
    H1Function.untranslate (matVecMul (matSqrt (symmPart abar))⁻¹ z)
      (uHat.restrict htOpen hgauge.symm.subset), ?_, ?_, ?_, ?_⟩
  · intro y
    show g₀Hat.toFun (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) = _
    rw [hgf]
  · intro y
    show g₀Hat.grad (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) = _
    rw [hgg, matTranspose_matSqrt_symmPart hS]
  · intro _
    rfl
  · intro _
    rfl

/-! ## (c) The frame identity -/

/-- **the `hFrame` premise, for the canonical choice of `FTrans`.**  Gauging back
and forth is the identity, so the transported field
`FTrans w = S (g₀grad (S w))` restricts to `S ∘ g₀grad` along `S⁻¹`. -/
theorem frozenWitnessFrameTransport {abar : Mat d}
    (hS : (symmPart abar).PosDef) (g0grad : Vec d → Vec d) (w : Vec d) :
    matVecMul (matSqrt (symmPart abar))
        (g0grad (matVecMul (matSqrt (symmPart abar))
          (matVecMul (matSqrt (symmPart abar))⁻¹ w))) =
      matVecMul (matSqrt (symmPart abar)) (g0grad w) := by
  rw [matVecMul_mul, Matrix.mul_nonsing_inv _ (isUnit_det_matSqrt hS),
    matVecMul_one]

/-! ## (a) The two regularity premises -/

/-- **the analytic inputs (a), closed.**  Module the `hBesov` premise and `hL2` for the
pulled-back boundary gradient, from the hole's own binders. -/
theorem forceBesov_and_memVectorL2_at_frozenWitness [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
      openCubeSet (originCube d j))
    (hinner : ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U)
    {s₀ : ℝ} (hs : 0 < s₀) (hs1 : s₀ < 1)
    (g₀ : H1Function U) (hHs : hsNormSq U s₀ g₀.grad ≠ ⊤)
    (G : Vec d → Vec d)
    (hG : ∀ y : Vec d, G y =
      matVecMul (matSqrt (symmPart abar))
        (g₀.grad (matVecMul (matSqrt (symmPart abar))
          (y + matVecMul (matSqrt (symmPart abar))⁻¹ z)))) :
    MemVectorL2 (openCubeSet (originCube d j)) G ∧
      Book.Ch03.ForceBesovRegularity (originCube d j) s₀ G := by
  have hu' : IsUnit (matSqrt (symmPart abar)).det := isUnit_det_matSqrt hS
  have hLinv : IsUnit ((matSqrt (symmPart abar))⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det _ hu'
  have hUmeas : MeasurableSet U := (isOpen_witnessDomain hS hU).measurableSet
  have hgauge := matImage_matSqrtInv_witness_eq_translateSet hS hU
  have hrpos : (0 : ℝ) < 1 / (3 * Real.sqrt (d : ℝ)) := by
    have hd : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have hsq : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd
    positivity
  have hU0 : volume U ≠ 0 := by
    have hpos : 0 < volume (ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ)))) :=
      volume_ellipsoid_pos abar hrpos
    exact (lt_of_lt_of_le hpos (measure_mono hinner)).ne'
  have hGfun : G = fun y : Vec d =>
      matVecMul (matSqrt (symmPart abar))
        (g₀.grad (matVecMul (matSqrt (symmPart abar))
          (y + matVecMul (matSqrt (symmPart abar))⁻¹ z))) := funext hG
  -- the `L²` leg
  have hL2 : MemVectorL2 (openCubeSet (originCube d j)) G := by
    have h2 := Response.memVectorL2_affinePullback hu' hUmeas g₀.grad_memVectorL2
    rw [hgauge] at h2
    have h3 := memVectorL2_comp_addRight_of_memVectorL2_translateSet h2
    have h4 := memVectorL2_constMatrix_mul (matSqrt (symmPart abar)) h3
    rw [hGfun]
    exact h4
  refine ⟨hL2, ?_⟩
  -- the fractional leg
  have hframeInv : ∀ y : Vec d,
      matVecMul (matSqrt (symmPart abar))
          (g₀.grad (matVecMul (matSqrt (symmPart abar))
            (matVecMul (matSqrt (symmPart abar))⁻¹ y))) =
        matVecMul (matSqrt (symmPart abar)) (g₀.grad y) := fun y =>
    frozenWitnessFrameTransport hS g₀.grad y
  have hHsPhys : hsNormSq U s₀
      (fun y => matVecMul (matSqrt (symmPart abar)) (g₀.grad y)) ≠ ⊤ :=
    hsNormSq_matVecMul_ne_top (matSqrt (symmPart abar)) U s₀ hHs
  have hds : (0 : ℝ) ≤ (d : ℝ) + 2 * s₀ := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
    linarith only [hd, hs]
  have hbase := hsNormSq_matImage_le_opNorm (L := (matSqrt (symmPart abar))⁻¹)
    hLinv hUmeas hU0 (s := s₀) hds
    (fun w => matVecMul (matSqrt (symmPart abar))
      (g₀.grad (matVecMul (matSqrt (symmPart abar)) w)))
  rw [Matrix.nonsing_inv_nonsing_inv (matSqrt (symmPart abar)) hu'] at hbase
  have hcomp : (fun y : Vec d =>
        matVecMul (matSqrt (symmPart abar))
          (g₀.grad (matVecMul (matSqrt (symmPart abar))
            (matVecMul (matSqrt (symmPart abar))⁻¹ y)))) =
      fun y : Vec d => matVecMul (matSqrt (symmPart abar)) (g₀.grad y) :=
    funext hframeInv
  rw [hcomp] at hbase
  have hHsGauge : hsNormSq (matImage (matSqrt (symmPart abar))⁻¹ U) s₀
      (fun w => matVecMul (matSqrt (symmPart abar))
        (g₀.grad (matVecMul (matSqrt (symmPart abar)) w))) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHsPhys) hbase
  rw [hgauge] at hHsGauge
  rw [EnergyPrice.hsNormSq_translateSet_add
    (matVecMul (matSqrt (symmPart abar))⁻¹ z) (openCubeSet (originCube d j)) s₀
    (fun w : Vec d => matVecMul (matSqrt (symmPart abar))
      (g₀.grad (matVecMul (matSqrt (symmPart abar)) w)))] at hHsGauge
  have hHsCube : hsNormSq (openCubeSet (originCube d j)) s₀ G ≠ ⊤ := by
    rw [hGfun]
    exact hHsGauge
  exact EnergyPrice.forceBesovRegularity_of_hsNormSq_ne_top (originCube d j)
    hs hs1 G (memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet _ hL2)
    hL2 hHsCube

end

end RowSupply
end HighContrast
end HCPolySupport
