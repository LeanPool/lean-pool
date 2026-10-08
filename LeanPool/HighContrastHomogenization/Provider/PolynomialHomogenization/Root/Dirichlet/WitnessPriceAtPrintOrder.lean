/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessPriceAtWitnessRoute
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.LocalCoarseGrainingResponseOrder

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessPriceAtPrintOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The λ-route price at the printed order `s₀`

The orders have to be reconciled: the response-window tail produces the
reference tail at
`responseWindowOrder g = (3+5g)/16`, so the λ-route composition delivers the
observation error at that order, while the frozen clause's boundary energy is at
`s₀ ∈ Ico ((1+g)/4) (1/2)` — and `(3+5g)/16 < (1+g)/4` for every `g < 1`.

**The gap closes with one upstream lemma, and nothing is restated.**  The
multiscale error is *decreasing* in the fractional order
(`Book.Ch03.ABK26.homogenizationErrorOnCube_infinity_two_le_of_lt`, loss exactly
one), and the comparison runs in the favourable direction: the composition is
performed at the *smaller* order `responseWindowOrder g` and its conclusion is
read at the *larger* order `s₀`.  The fold arithmetic —
`frameFoldConstant`, `witnessErrorEccentricityExponent` — is therefore used
unchanged at `responseWindowOrder g` and needs no restatement.

`Cwit` is unchanged: it is still
`lambdaRouteClaw d (responseWindowOrder g) λ abar ·
  ((ρ/(3√d))^(−responseWindowOrder g) · frameFoldConstant) · ecc^q`,
so the whole `s₀`-dependence of the price sits in the energy's own
`gaugeWitnessEnergyPriceW C d s₀ Cwit abar`, exactly where the interface modules
needs it.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The two scalar facts about the two orders -/

/-- The response-window order is positive on the printed `g`-window. -/
theorem responseWindowOrder_pos {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < responseWindowOrder g := by
  have hg0 : (0 : ℝ) ≤ g := hg.1
  rw [responseWindowOrder]
  linarith only [hg0]

/-- **The response-window order is strictly below the whole printed `s₀`
window.**  `(3+5g)/16 < (4+4g)/16 = (1+g)/4 ≤ s₀` for every `g < 1`. -/
theorem responseWindowOrder_lt_printOrder {g s₀ : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hs₀ : s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ)) :
    responseWindowOrder g < s₀ := by
  have hg1 : g < 1 := hg.2
  have hlow : (1 + g) / 4 ≤ s₀ := hs₀.1
  rw [responseWindowOrder]
  linarith only [hg1, hlow]

/-! ## The order lift of the λ-route conclusion -/

/-- **21e.**  The λ-route's observation-error bound, produced at the
response-window order, holds unchanged at every printed order `s₀`. -/
theorem exists_witnessLambdaRouteError_at_printOrder [NeZero d]
    {g kappa deltaScaled lambda s₀ : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hs₀ : s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ))
    (hlambda : lambda ∈ Set.Icc (1 : ℝ) 3)
    (a : CoeffSpace d) {abar : Mat d} (hS : (symmPart abar).PosDef) (t : ℤ)
    {j : ℤ} {z : Vec d} {U : Set (Vec d)}
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    (hUsub : U ⊆ ellipsoid abar 1)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (L : ℕ) (n : ℤ) (hLn : (L : ℤ) ≤ n)
    (hTail : ScalarIdentityPowerTail aRef (responseWindowOrder g)
      (Real.sqrt deltaScaled) kappa ((3 : ℝ) ^ ((L : ℕ) : ℤ)))
    (aObs : Book.Ch03.CoeffFamily d)
    (hObs : (aObs.coeffOn (originCube d j)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff lambda a y - skewPart abar)
        (x + matVecMul (matSqrt (symmPart abar))⁻¹ z)) :
    ∃ M : ℤ, M = max (max n j) 1 ∧ n ≤ M ∧ j ≤ M ∧ (1 : ℤ) ≤ M ∧
      Book.Ch02.HomogenizationErrorOnCube
          (originCube d j) s₀ Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 2) aObs (1 : Mat d) ≤
        lambdaRouteClaw d (responseWindowOrder g) lambda abar *
          ((3 : ℝ) ^ ((responseWindowOrder g - kappa) * (M : ℝ) -
              responseWindowOrder g * (j : ℝ) + kappa * ((L : ℕ) : ℝ)) *
            Real.sqrt deltaScaled) := by
  obtain ⟨M, hMeq, hnM, hjM, hM1, hbound⟩ :=
    exists_witnessLambdaRouteError (kappa := kappa)
      (responseWindowOrder_pos hg)
      (lt_trans (responseWindowOrder_lt_printOrder hg hs₀) hs₀.2)
      hlambda a hS t hU hUsub aRef haRef L n hLn hTail aObs hObs
  refine ⟨M, hMeq, hnM, hjM, hM1, ?_⟩
  refine le_trans ?_ hbound
  exact Book.Ch03.ABK26.homogenizationErrorOnCube_infinity_two_le_of_lt
    (originCube d j) aObs (1 : Mat d) (responseWindowOrder_pos hg)
    (responseWindowOrder_lt_printOrder hg hs₀)

/-! ## The frozen-witness price at the printed order -/

/-- **The frozen-witness energy price at the printed order `s₀`.**  Identical to
`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessPriceAtWitnessRoute`
except that the energy order is
the frozen clause's `s₀`, not the response-window order; `Cwit` is unchanged. -/
theorem exists_frozenWitnessEnergyPrice_at_printOrder (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (abar : Mat d) (hS : (symmPart abar).PosDef)
        (U : Set (Vec d)) (j : ℤ) (z : Vec d)
        (g kappaRate deltaScaled lambda rho Rad s₀ : ℝ) (G L J : ℕ)
        (a : CoeffSpace d) (t : ℤ)
        (aRef aFam : Book.Ch03.CoeffFamily d)
        (v : Book.Ch03.DirichletForcedCubeSolution
          (originCube d j) aFam (0 : Vec d → Vec d))
        (aHat : CoeffField d)
        (uHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U))
        (g0grad FTrans : Vec d → Vec d),
        g ∈ Set.Ico (0 : ℝ) 1 →
        s₀ ∈ Set.Ico ((1 + g) / 4) (1 / 2 : ℝ) →
        0 < kappaRate →
        0 ≤ Certificate.printRowOrder g →
        0 < 1 - (3 : ℝ) ^
          (-(2 * responseWindowOrder g - Certificate.printRowOrder g)) →
        0 < Certificate.shiftedTailAbsorptionPrefactor d
          (responseWindowOrder g) (Certificate.printRowOrder g) G →
        L = Certificate.formulaicNormalizedReferenceTailShift d
          (responseWindowOrder g) (Certificate.printRowOrder g)
            (2 * kappaRate) G →
        (3 : ℝ) ^ ((G : ℕ) : ℝ) ≤
          1 + 3 * (witnessEccentricity (symmPart abar) * Real.sqrt d) →
        2 * Rad ≤ (3 : ℝ) ^ ((J : ℕ) : ℤ) →
        Real.sqrt deltaScaled ≤ 1 →
        lambda ∈ Set.Icc (1 : ℝ) 3 →
        U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
          openCubeSet (originCube d j) →
        U ⊆ ellipsoid abar 1 →
        ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
        HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad →
        (∀ R : TriadicCube d,
          (aRef.coeffOn R).toCoeffField =
            affineCoefficient (Selection.normalizedRoot (symmPart abar))
              ((Matrix.isUnit_iff_isUnit_det _).mp
                (normalizedRoot_posDef_of_posDef hS).isUnit)
              ((normalizedCenteredCoeff a abar hS).coeffOn
                (Response.adaptedDomain
                  (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField) →
        ScalarIdentityPowerTail aRef (responseWindowOrder g)
          (Real.sqrt deltaScaled) kappaRate ((3 : ℝ) ^ ((L : ℕ) : ℤ)) →
        ((aFam.coeffOn (originCube d j)).toCoeffField
          =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
          fun x ↦ affineCoefficient (matSqrt (symmPart abar))
            (isUnit_det_matSqrt hS)
            (fun y ↦ scaledCoeff lambda a y - skewPart abar)
            (x + matVecMul (matSqrt (symmPart abar))⁻¹ z)) →
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
        (∀ x : Vec d,
          FTrans (matVecMul (matSqrt (symmPart abar))⁻¹ x) =
            matVecMul (matSqrt (symmPart abar)) (g0grad x)) →
        GaugePhysicalEnergyPriceAtWitness
          (matImage (matSqrt (symmPart abar))⁻¹ U) aHat uHat
          (EnergyPrice.gaugeWitnessEnergyPriceW C d s₀
            (witnessRouteCwit d
              (lambdaRouteClaw d (responseWindowOrder g) lambda abar)
              (witnessGeometricFactor d rho (responseWindowOrder g))
              g kappaRate ((J : ℕ) : ℝ) abar) abar)
          (hsNormSq U s₀
            (fun x => matVecMul (matSqrt (symmPart abar)) (g0grad x))) := by
  obtain ⟨C, hC, hprice⟩ :=
    EnergyPrice.exists_windowedGaugePhysicalEnergyPriceAtFrozenWitness d
  refine ⟨C, hC, ?_⟩
  intro abar hS U j z g kappaRate deltaScaled lambda rho Rad s₀ G L J a t aRef
    aFam v aHat uHat g0grad FTrans hg hs₀ hkappa hrho hgeom hP hLeq hGupper
    hJbracket hdelta1 hlambda hU hUsub hinner hsandwich haRef hTail hObs hBesov
    hL2 hb hu hF hFrame
  have hb0 : 0 ≤ responseWindowOrder g := (responseWindowOrder_pos hg).le
  obtain ⟨M, hMeq, -, -, hM1, hbound⟩ :=
    exists_witnessLambdaRouteError_at_printOrder (kappa := kappaRate) hg hs₀
      hlambda a hS t hU hUsub aRef haRef L (max (L : ℤ) ((J : ℤ) + 1))
      (le_max_left _ _) hTail aFam hObs
  have hjJ : j ≤ ((J : ℕ) : ℤ) :=
    witnessGeneration_le_bracket hS hU hsandwich hJbracket
  have hMle : M ≤ (L : ℤ) + (J : ℤ) + 2 := by
    rw [hMeq]
    omega
  have hCgeo := rpow_three_neg_order_le_witnessGeometricFactor
    (r := responseWindowOrder g) hS hb0 hU hsandwich
  have h42 := witnessErrorFactor_le_geo_mul_eccentricityPow (abar := abar)
    (g := g) (kappaRate := kappaRate) (deltaScaled := deltaScaled) (G := G)
    (L := L) (J := J) (M := M) (j := j)
    (Cgeo := witnessGeometricFactor d rho (responseWindowOrder g))
    hkappa hrho hgeom hP hLeq hGupper hM1 hMle hCgeo hdelta1
  have hCgeo0 : (0 : ℝ) ≤ witnessGeometricFactor d rho (responseWindowOrder g) :=
    le_trans (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) hCgeo
  have hErr : Book.Ch02.HomogenizationErrorOnCube (originCube d j) s₀
        Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 2) aFam (1 : Mat d) ≤
      witnessRouteCwit d
        (lambdaRouteClaw d (responseWindowOrder g) lambda abar)
        (witnessGeometricFactor d rho (responseWindowOrder g))
        g kappaRate ((J : ℕ) : ℝ) abar := by
    refine hbound.trans ?_
    rw [witnessRouteCwit]
    exact mul_le_mul_of_nonneg_left h42
      (lambdaRouteClaw_nonneg d (responseWindowOrder g) lambda abar)
  refine hprice abar hS U j z s₀
    (witnessRouteCwit d
      (lambdaRouteClaw d (responseWindowOrder g) lambda abar)
      (witnessGeometricFactor d rho (responseWindowOrder g))
      g kappaRate ((J : ℕ) : ℝ) abar)
    aFam v aHat uHat g0grad FTrans
    (lt_of_lt_of_le (responseWindowOrder_pos hg)
      (le_of_lt (responseWindowOrder_lt_printOrder hg hs₀))) hs₀.2
    (witnessRouteCwit_nonneg d
      (lambdaRouteClaw_nonneg d (responseWindowOrder g) lambda abar) hCgeo0
      g kappaRate ((J : ℕ) : ℝ) abar)
    hU hUsub hinner hBesov hL2 hErr hb hu hF hFrame

end

end RowSupply
end HighContrast
end HCPolySupport
