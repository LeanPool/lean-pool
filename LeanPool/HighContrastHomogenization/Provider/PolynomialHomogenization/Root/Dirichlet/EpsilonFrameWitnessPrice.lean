/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EpsilonLambdaFrameReconciliation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ScaledAmplitudeBelowOne
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.PerGOrderGapAudit
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicRowLevelWindowTailComposition

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.EpsilonFrameWitnessPrice

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The frozen-witness energy price at the hole's own microscopic parameter split module twenty-four
hypotheses into a "the certificate destructurings" of
five certificate destructurings and a "the analytic inputs" of four analytic
identifications.  This module closes **the certificate destructurings entirely**, and closes the one
load-bearing analytic input (the λ-versus-ε mismatch), by
composing

* `RowRetainingPrintOrderGoodScale.exists_formulaicScaledResponseWindowTail` — which delivers, in
one call from the row-retaining certificate and
  the hole's own `hx`/`hepsilon`/`hscale`, the whole λ-route package: `N`, `G`,
  `lambda = epsilon * 3 ^ N` with `lambda ∈ Icc 1 3`,
  `aScaled = Quenched.physical_scale_coeff N a`, the amplitude `deltaScaled`,
  the enclosure bracket `3 ^ G ≤ 1 + 3 (ecc √d)`, the **formulaic** shift
  `L = formulaicNormalizedReferenceTailShift d b ρ (2κ) G`, the normalized
  reference `aRef` and its `ScalarIdentityPowerTail` at the response-window
  order;
* the `sqrt_deltaScaled_le_one` premise — the amplitude window `√deltaScaled ≤ 1`;
* the `one_sub_rpow_neg_gap_pos_responseWindow` premise and the two printed-order
  margins — the three scalar premises;
* the `witnessObservation_lambdaScaled_of_epsilon` premise — the ε/λ frame identity.

The certificate-destructuring table points at
`PrintOrderQuantitativeNormalizedReferenceCertificate` itself.  That is the
wrong producer: the raw certificate carries the tail at `printCertificateOrder g`
for the **unscaled** `a`, whereas that module consumes it at `responseWindowOrder g`
for the **scaled** `aScaled`, with the formulaic shift.  that module is the producer
that does both conversions, and it is available.

**Only the analytic inputs remain**, and this theorem exhibits them exactly:
`v`, `hBesov`, `hL2`, `hb`, `hu`, `hF`, `hFrame` are the only hypotheses below
that are not the hole's own binders or a producer's output.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

/-- **The frozen-witness energy price, stated at the hole's `scaledCoeff ε a`.**
Every Group-A hypothesis from the modules named above is discharged inside; the seven Group-B items
(`v`, `hBesov`, `hL2`, `hb`, `hu`, `hF`, `hFrame`) remain as binders, and the
λ-route's microscopic parameter survives only inside `lambdaRouteClaw`, bounded
by the exported `lambda ∈ Icc 1 3`. -/
theorem exists_frozenWitnessEnergyPrice_at_epsilon (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g c kappaRate : ℝ) (abar : Mat d) (a : CoeffSpace d) (x epsilon : ℝ)
        (hgood : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
        (hS : (symmPart abar).PosDef)
        (U : Set (Vec d)) (j : ℤ) (z : Vec d) (rho Rad s₀ : ℝ) (J : ℕ)
        (aFam : Book.Ch03.CoeffFamily d)
        (v : Book.Ch03.DirichletForcedCubeSolution (originCube d j) aFam
          (0 : Vec d → Vec d))
        (aHat : CoeffField d)
        (uHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U))
        (g0grad FTrans : Vec d → Vec d),
        hgood.delta ∈ Set.Ioo (0 : ℝ) 1 →
        g ∈ Set.Ico (0 : ℝ) 1 →
        0 < kappaRate → 1 ≤ x → 0 < epsilon → x ≤ epsilon⁻¹ →
        s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
        2 * Rad ≤ (3 : ℝ) ^ ((J : ℕ) : ℤ) →
        U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
          openCubeSet (originCube d j) →
        U ⊆ ellipsoid abar 1 →
        ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
        HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad →
        ((aFam.coeffOn (originCube d j)).toCoeffField
          =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
          fun y ↦ affineCoefficient (matSqrt (symmPart abar))
            (isUnit_det_matSqrt hS)
            (fun w ↦ scaledCoeff epsilon a w - skewPart abar)
            (y + matVecMul (matSqrt (symmPart abar))⁻¹ z)) →
        Book.Ch03.ForceBesovRegularity (originCube d j) s₀
          (Book.Ch03.dirichletBoundaryGradientField v) →
        MemVectorL2 (openCubeSet (originCube d j))
          (Book.Ch03.dirichletBoundaryGradientField v) →
        (∀ y : Vec d, aHat (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
          (aFam.coeffOn (originCube d j)).toCoeffField y) →
        (∀ y : Vec d,
          uHat.grad (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
            v.toH1.grad y) →
        (∀ y : Vec d,
          FTrans (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
            Book.Ch03.dirichletBoundaryGradientField v y) →
        (∀ w : Vec d,
          FTrans (matVecMul (matSqrt (symmPart abar))⁻¹ w) =
            matVecMul (matSqrt (symmPart abar)) (g0grad w)) →
        ∃ lambda : ℝ, lambda ∈ Set.Icc (1 : ℝ) 3 ∧
          GaugePhysicalEnergyPriceAtWitness
            (matImage (matSqrt (symmPart abar))⁻¹ U) aHat uHat
            (EnergyPrice.gaugeWitnessEnergyPriceW C d s₀
              (witnessRouteCwit d
                (lambdaRouteClaw d (responseWindowOrder g) lambda abar)
                (witnessGeometricFactor d rho (responseWindowOrder g))
                g kappaRate ((J : ℕ) : ℝ) abar) abar)
            (hsNormSq U s₀
              (fun w => matVecMul (matSqrt (symmPart abar)) (g0grad w))) := by
  obtain ⟨C, hC, hprice⟩ := exists_frozenWitnessEnergyPrice_at_printOrder d
  refine ⟨C, hC, ?_⟩
  intro g c kappaRate abar a x epsilon hgood hS U j z rho Rad s₀ J aFam v aHat
    uHat g0grad FTrans hdelta hg hkappa hx hepsilon hscale hs₀ hJbracket hU
    hUsub hinner hsandwich hObsEps hBesov hL2 hb hu hF hFrame
  obtain ⟨N, G, lambda, deltaScaled, aScaled, aRef, L, hlambda, hlambdaRange,
      haScaled, hdeltaScaled, -, hGupper, hLeq, -, haRef, hTail⟩ :=
    hgood.exists_formulaicScaledResponseWindowTail hS hg hkappa hx hepsilon
      hscale
  refine ⟨lambda, hlambdaRange, ?_⟩
  have hg0 : (0 : ℝ) ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hrho : (0 : ℝ) ≤ Certificate.printRowOrder g := by
    rw [Certificate.printRowOrder]
    linarith only [hg0]
  have hgeom := one_sub_rpow_neg_gap_pos_responseWindow hg1
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hsqrtd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hP : 0 < Certificate.shiftedTailAbsorptionPrefactor d
      (responseWindowOrder g) (Certificate.printRowOrder g) G := by
    rw [Certificate.shiftedTailAbsorptionPrefactor]
    exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 6) hd0) hsqrtd)
      (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (one_div_pos.mpr hgeom))
  have hGupperR : (3 : ℝ) ^ ((G : ℕ) : ℝ) ≤
      1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) := by
    rw [Real.rpow_natCast]
    rwa [zpow_natCast] at hGupper
  have hdelta1 : Real.sqrt deltaScaled ≤ 1 :=
    sqrt_deltaScaled_le_one hgood hdelta hkappa hepsilon hscale hlambda
      hlambdaRange hdeltaScaled
  have haRefLocal : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff aScaled abar hS).coeffOn
            (Response.adaptedDomain
              (normalizedRoot_posDef_of_posDef hS) 0)).toCoeffField := by
    intro R
    simpa only [CoeffSpace.coeffOn_toCoeffField] using haRef R
  have hObsLambda := witnessObservation_lambdaScaled_of_epsilon hS hepsilon
    hlambda haScaled hObsEps
  exact hprice abar hS U j z g kappaRate deltaScaled lambda rho Rad s₀ G L J
    aScaled 0 aRef aFam v aHat uHat g0grad FTrans hg hs₀ hkappa hrho hgeom hP
    hLeq hGupperR hJbracket hdelta1 hlambdaRange hU hUsub hinner hsandwich
    haRefLocal hTail hObsLambda hBesov hL2 hb hu hF hFrame

end

end RowSupply
end HighContrast
end HCPolySupport
