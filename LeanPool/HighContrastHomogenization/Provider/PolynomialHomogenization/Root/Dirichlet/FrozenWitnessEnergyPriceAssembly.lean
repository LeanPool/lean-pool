/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessZeroTrace
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.EpsilonFrameWitnessPrice
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.GaugeWeakSolutionAndCellFamily
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessPhysicalRealization

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessEnergyPriceAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The frozen-witness energy price, with the analytic inputs discharged

Modules that module–that module closed, one by one, every item listed as open in
hypothesis surface.  This module composes them: the energy price is
produced from **the clause's own binders alone**, together with two
definitional constraints on the gauge carriers (`haHat`, `huHat`) — which are
binders, not new hypotheses.

The chain, in order:

| step | producer |
|---|---|
| the physical realization `u` of `(uFun, uGrad)` | — |
| the gauge weak solution at `aHat` (row 4′) | — |
| the cube pullbacks `gObs` (of `g₀`) and `uObs` (of `u`) | — |
| `hBesov`, `hL2` for `gObs.grad` | — |
| the observation family, `hb` **and** `hObs` at `scaledCoeff ε a` | — |
| the zero-trace difference | — |
| the Dirichlet forced cube solution `v` | — |
| the ε/λ reconciliation, the certificate destructurings, and the price | — |

`FTrans` is the canonical transported datum
`w ↦ S (g₀.grad (S w))`, and `g0grad := g₀.grad`; the two `FTrans` premises are
gradient identity and the `frozenWitnessFrameTransport` premise.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

/-- **The frozen-witness energy price at the hole's binders.**  No Group-B
hypothesis survives: `v`, `hBesov`, `hL2`, `hb`, `hu`, `hF`, `hFrame` and the
ε-shaped observation identification are all produced inside. -/
theorem exists_frozenWitnessEnergyPrice_atHoleBinders (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g c kappaRate : ℝ) (abar : Mat d) (a : CoeffSpace d) (x epsilon : ℝ)
        (hgood : RowRetainingPrintOrderGoodScale d g c kappaRate abar a x)
        (hS : (symmPart abar).PosDef)
        (U : Set (Vec d)) (j : ℤ) (z : Vec d) (rho Rad s₀ : ℝ) (J : ℕ)
        (g₀ h : H1Function U) (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d)
        (uHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U)),
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
        hsNormSq U s₀ g₀.grad ≠ ⊤ →
        MemAffineH10 U g₀ h →
        MemH1a0 (scaledCoeff epsilon a) U
          (fun y => uFun y - g₀.toFun y) (fun y => uGrad y - g₀.grad y) →
        IsWeakSolutionOn (scaledCoeff epsilon a) U uGrad →
        uHat.grad = (fun y => matVecMul (matSqrt (symmPart abar))
          (uGrad (matVecMul (matSqrt (symmPart abar)) y))) →
        ∃ lambda : ℝ, lambda ∈ Set.Icc (1 : ℝ) 3 ∧
          GaugePhysicalEnergyPriceAtWitness
            (matImage (matSqrt (symmPart abar))⁻¹ U)
            (affineCoefficient (matSqrt (symmPart abar))
              (isUnit_det_matSqrt hS)
              (fun w => scaledCoeff epsilon a w - skewPart abar))
            uHat
            (EnergyPrice.gaugeWitnessEnergyPriceW C d s₀
              (witnessRouteCwit d
                (lambdaRouteClaw d (responseWindowOrder g) lambda abar)
                (witnessGeometricFactor d rho (responseWindowOrder g))
                g kappaRate ((J : ℕ) : ℝ) abar) abar)
            (hsNormSq U s₀
              (fun w => matVecMul (matSqrt (symmPart abar)) (g₀.grad w))) := by
  obtain ⟨C, hC, hprice⟩ := exists_frozenWitnessEnergyPrice_at_epsilon d
  refine ⟨C, hC, ?_⟩
  intro g c kappaRate abar a x epsilon hgood hS U j z rho Rad s₀ J g₀ h uFun
    uGrad uHat hdelta hg hkappa hx hepsilon hscale hs₀ hJbracket hU hUsub
    hinner hsandwich hHs haff hu0 hweak huHat
  -- the physical realization
  obtain ⟨u, huFun, huGrad, -, huPhys⟩ :=
    exists_frozenWitnessPhysicalRealization hS hepsilon hU g₀ h haff uFun uGrad
      hu0 hweak
  have huHat' : uHat.grad = fun y => matVecMul (matSqrt (symmPart abar))
      (u.grad (matVecMul (matSqrt (symmPart abar)) y)) := by
    rw [huGrad]
    exact huHat
  -- row 4′: the gauge weak solution
  have hWeakGauge := exists_frozenWitnessGaugeWeakSolution hS
    (frozenWitness_physicalDomain_isOpenBoundedConvexDomain hS hU) u huPhys
    uHat huHat'
  -- the cube pullbacks
  obtain ⟨gObs, -, hgFun, hgGrad, -, -⟩ :=
    exists_frozenWitnessGaugeCubePullbacks hS hU g₀ uHat
  obtain ⟨uObs, -, huObsFun, huObsGrad, -, -⟩ :=
    exists_frozenWitnessGaugeCubePullbacks hS hU u uHat
  -- the analytic inputs (a)
  have hs0 : 0 < s₀ :=
    lt_of_lt_of_le (by linarith only [hg.1] : (0 : ℝ) < (1 + g) / 4) hs₀.1
  have hs1 : s₀ < 1 := hs₀.2.trans (by norm_num)
  obtain ⟨hL2, hBesov⟩ :=
    forceBesov_and_memVectorL2_at_frozenWitness hS hU hinner hs0 hs1 g₀ hHs
      gObs.grad hgGrad
  -- the analytic inputs (d)
  obtain ⟨aFam, hb, hObsEps⟩ :=
    exists_frozenWitnessCoeffFamilyAtCube hepsilon a hS z j
  -- the analytic inputs (b)
  have hzero := exists_frozenWitnessZeroTraceDifference hS hepsilon hU uFun
    uGrad g₀ hu0 uObs gObs
    (fun y => by rw [huObsFun y, huFun]) hgFun
  obtain ⟨v, hv1, hv2⟩ :=
    exists_frozenWitnessDirichletCubeSolution hS hU hb uHat.grad hWeakGauge
      uObs gObs
      (fun y => by rw [huObsGrad y, huHat']) hzero
  -- the Group-B premises from the modules named above, in its own spelling
  have hBesov' : Book.Ch03.ForceBesovRegularity (originCube d j) s₀
      (Book.Ch03.dirichletBoundaryGradientField v) := by
    rw [hv2]; exact hBesov
  have hL2' : MemVectorL2 (openCubeSet (originCube d j))
      (Book.Ch03.dirichletBoundaryGradientField v) := by
    rw [hv2]; exact hL2
  have hF : ∀ y : Vec d,
      matVecMul (matSqrt (symmPart abar))
          (g₀.grad (matVecMul (matSqrt (symmPart abar))
            (y + matVecMul (matSqrt (symmPart abar))⁻¹ z))) =
        Book.Ch03.dirichletBoundaryGradientField v y := by
    intro y
    rw [hv2, hgGrad y]
  have hu : ∀ y : Vec d,
      uHat.grad (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
        v.toH1.grad y := by
    intro y
    rw [hv1, huObsGrad y, huHat']
  exact hprice g c kappaRate abar a x epsilon hgood hS U j z rho Rad s₀ J aFam v
    (affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
      (fun w => scaledCoeff epsilon a w - skewPart abar))
    uHat g₀.grad
    (fun w => matVecMul (matSqrt (symmPart abar))
      (g₀.grad (matVecMul (matSqrt (symmPart abar)) w)))
    hdelta hg hkappa hx hepsilon hscale hs₀ hJbracket hU hUsub hinner hsandwich
    hObsEps hBesov' hL2' hb hu hF (frozenWitnessFrameTransport hS g₀.grad)

end

end RowSupply
end HighContrast
end HCPolySupport
