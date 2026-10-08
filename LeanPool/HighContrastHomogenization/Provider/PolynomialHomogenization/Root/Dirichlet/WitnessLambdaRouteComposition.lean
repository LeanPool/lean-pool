/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeEnclosure
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FixedParentResponsePriceAlgebra

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.WitnessLambdaRouteComposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The λ-route composition at the frozen witness

With the witness-cube enclosure of
`HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeEnclosure` in hand,
`observationHomogenizationError_le_referencePowerTail_fixedParent`
applies at the frozen witness, and
`sqrt_observationParent_powerPrice_eq` (`FixedParentResponsePriceAlgebra`)
rewrites its square root into the exact product

```
Claw · 3 ^ ((s − κ) M − s j + κ N) · amplitude,
Claw = √(observationFillingCoefficient d λ abar · geometricDiscount (1−2s) 1 ⁻¹)
```

which is precisely the `hErr` binder shape of
the frozen-witness energy price at the eccentricity-shaped `Cwit`.

The second theorem performs the frozen-witness assembly: it takes exactly
domain surface (`hU`, `hUsub`), the provider's `λ ∈ Icc 1 3` from
the response-window tail, the reference tail, and the observation
identification, and produces
the parent generation together with the `hErr` bound.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-- The law-free half of the λ-route constant: the filling coefficient against
the geometric discount, under a square root. -/
@[expose]
noncomputable def lambdaRouteClaw (d : ℕ) (s epsilon : ℝ) (abar : Mat d) : ℝ :=
  Real.sqrt (observationFillingCoefficient d epsilon abar *
    (Book.Ch02.geometricDiscount (1 - 2 * s) 1)⁻¹)

theorem lambdaRouteClaw_nonneg (d : ℕ) (s epsilon : ℝ) (abar : Mat d) :
    0 ≤ lambdaRouteClaw d s epsilon abar := Real.sqrt_nonneg _

/-- **The λ-route composition at a fixed parent, in the price shape.**  The
all-depth observation error on the target cube is below the λ-route product
`Claw · 3 ^ ((s − κ) M − s K + κ N) · amplitude`. -/
theorem observationHomogenizationError_le_lambdaRoutePrice [NeZero d]
    {s epsilon amplitude kappa : ℝ}
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hepsilon : 0 < epsilon) (hAmplitude : 0 ≤ amplitude)
    (center : Vec d) (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (t : ℤ)
    (aRef : Book.Ch03.CoeffFamily d)
    (haRef : ∀ R : TriadicCube d,
      (aRef.coeffOn R).toCoeffField =
        affineCoefficient (Selection.normalizedRoot (symmPart abar))
          ((Matrix.isUnit_iff_isUnit_det _).mp
            (normalizedRoot_posDef_of_posDef hS).isUnit)
          ((normalizedCenteredCoeff a abar hS).coeffOn
            (Response.adaptedDomain (normalizedRoot_posDef_of_posDef hS) t)).toCoeffField)
    (N K M : ℤ) (hNM : N ≤ M) (hKM : K ≤ M)
    (hTail : ScalarIdentityPowerTail aRef s amplitude kappa ((3 : ℝ) ^ N))
    (aObs : Book.Ch03.CoeffFamily d)
    (hObs : (aObs.coeffOn (originCube d K)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d K))]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff epsilon a y - skewPart abar) (x + center))
    (hEnclose : adaptedCellTranslate (epsilonAffineGrid epsilon abar) K
        (epsilon⁻¹ • matVecMul (matSqrt (symmPart abar)) center +
          adaptedCellCenter (epsilonAffineGrid epsilon abar) K 0) ⊆
      adaptedCell (Selection.normalizedRoot (symmPart abar)) M) :
    Book.Ch02.HomogenizationErrorOnCube
        (originCube d K) s Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 2) aObs (1 : Mat d) ≤
      lambdaRouteClaw d s epsilon abar *
        ((3 : ℝ) ^ ((s - kappa) * (M : ℝ) - s * (K : ℝ) + kappa * (N : ℝ)) *
          amplitude) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hrw : ∀ e : ℝ, Real.rpow (3 : ℝ) e = (3 : ℝ) ^ e := fun _ => rfl
  obtain ⟨-, -, hbound⟩ :=
    observationHomogenizationError_le_referencePowerTail_fixedParent
      hs hsHalf hepsilon hAmplitude center a abar hS t aRef haRef N K M hNM hKM
      hTail aObs hObs hEnclose
  rw [sqrt_observationParent_powerPrice_eq abar hKM hAmplitude hsHalf.le] at hbound
  refine hbound.trans (le_of_eq ?_)
  simp only [hrw]
  have hmul : (3 : ℝ) ^ (s * ((M : ℝ) - (K : ℝ))) *
        (3 : ℝ) ^ (-kappa * ((M : ℝ) - (N : ℝ))) =
      (3 : ℝ) ^ ((s - kappa) * (M : ℝ) - s * (K : ℝ) + kappa * (N : ℝ)) := by
    rw [← Real.rpow_add h3]
    congr 1
    ring
  calc lambdaRouteClaw d s epsilon abar *
          (3 : ℝ) ^ (s * ((M : ℝ) - (K : ℝ))) * amplitude *
          (3 : ℝ) ^ (-kappa * ((M : ℝ) - (N : ℝ)))
      = lambdaRouteClaw d s epsilon abar *
          (((3 : ℝ) ^ (s * ((M : ℝ) - (K : ℝ))) *
            (3 : ℝ) ^ (-kappa * ((M : ℝ) - (N : ℝ)))) * amplitude) := by ring
    _ = lambdaRouteClaw d s epsilon abar *
          ((3 : ℝ) ^ ((s - kappa) * (M : ℝ) - s * (K : ℝ) + kappa * (N : ℝ)) *
            amplitude) := by rw [hmul]

/-- **The frozen-witness λ-route bound.**  Exactly domain surface, the
provider's bracket `λ ∈ Icc 1 3`, the reference tail and the
observation identification produce the parent generation and the `hErr` bound from the modules
named above, with `Claw` the λ-route's own filling constant. -/
theorem exists_witnessLambdaRouteError [NeZero d]
    {s kappa deltaScaled lambda : ℝ}
    (hs : 0 < s) (hsHalf : s < 1 / 2)
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
    (hTail : ScalarIdentityPowerTail aRef s (Real.sqrt deltaScaled) kappa
      ((3 : ℝ) ^ ((L : ℕ) : ℤ)))
    (aObs : Book.Ch03.CoeffFamily d)
    (hObs : (aObs.coeffOn (originCube d j)).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
      fun x ↦ affineCoefficient (matSqrt (symmPart abar))
        (isUnit_det_matSqrt hS)
        (fun y ↦ scaledCoeff lambda a y - skewPart abar)
        (x + matVecMul (matSqrt (symmPart abar))⁻¹ z)) :
    ∃ M : ℤ, M = max (max n j) 1 ∧ n ≤ M ∧ j ≤ M ∧ (1 : ℤ) ≤ M ∧
      Book.Ch02.HomogenizationErrorOnCube
          (originCube d j) s Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 2) aObs (1 : Mat d) ≤
        lambdaRouteClaw d s lambda abar *
          ((3 : ℝ) ^ ((s - kappa) * (M : ℝ) - s * (j : ℝ) +
              kappa * ((L : ℕ) : ℝ)) *
            Real.sqrt deltaScaled) := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda.1
  obtain ⟨M, hMeq, hnM, hjM, hM1, hEnclose⟩ :=
    exists_witnessEnclosingParent hS hlambda hU hUsub n
  refine ⟨M, hMeq, hnM, hjM, hM1, ?_⟩
  have hbound := observationHomogenizationError_le_lambdaRoutePrice
    (kappa := kappa) hs hsHalf hlambdaPos (Real.sqrt_nonneg deltaScaled)
    (matVecMul (matSqrt (symmPart abar))⁻¹ z) a abar hS t aRef haRef
    ((L : ℕ) : ℤ) j M (le_trans hLn hnM) hjM hTail aObs hObs hEnclose
  have hcast : ((((L : ℕ) : ℤ) : ℝ)) = ((L : ℕ) : ℝ) := by push_cast; ring
  rwa [hcast] at hbound

end

end RowSupply
end HighContrast
end HCPolySupport
