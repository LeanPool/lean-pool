/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.RateFactorToHoleShape
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.DirichletHoleConsumption
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessEnergyPriceAssembly
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessClassBRows
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessFluxDefectRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.ObservationFamilyRow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.BoundaryEnergyFiniteness
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.WitnessCubeEnclosure
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.UniformHardyConstantHoist
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.CdualUnconditional

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.DirichletHoleInhabitant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The inhabitant of the restated Dirichlet clause

Every row of's table is now a producer, and this module
assembles them.  The law-free constant is

```
C₀ s₀ ρ Rad := max 0 (frozenHeadC0Factor C d s₀ ρ Rad (1/(3√d)) Cdual
                        (Chardy s₀ ρ Rad).toReal) + 1
```

— strictly positive by construction, and a function of `(s₀, ρ, Rad)` alone;
`C` is the energy's `d`-level constant, `Cdual` the `d`-level duality
constant, and `Chardy` is `(s₀, ρ, Rad)`-level Hardy constant.  The
per-`g` data are

```
Lg   := perGLengthFactor (frozenHeadLgFactor d g κ) κ ,
pEcc := foldedFrameEccentricityExponent g κ + (d + 1 + q) / κ ,
       q := witnessErrorEccentricityExponent g κ .
```

The row-by-row supply, against the hole's own binders:

| binder from the modules named above | producer |
|---|---|
| `hgood`, `hS`, `√δ ≤ 1` | `RootInterface.RootGoodScale.provider_surface` |
| `hscale : x ≤ ε⁻¹` | `RootInterface.scale_le_of_foldedScale_le` |
| `system`, `hU`, `hUnonempty`, `hRad`, `hUhatMeas`, `hUhat0` | — |
| `hGauge` | — |
| `u`, `huGrad` | — |
| `uHat`, `hHat`, `huHat`, `hhHat` | — |
| `aObs`, `hObs` | — |
| `aCell`, `wCell`, `hfamily` | that module (via row 4′) |
| `hEnergy` | — |
| `hBoundaryTop` | — |
| `hHardy` | — |
| `hFdefect` | — |
| `hDual` | the duality constant |
| `hhead` | **that module**, from the modules named above+the `KenergyBound` premise |
| the hole's shape | **that module** + **that module** (double absorptions) |
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

/-- **The restated internal Dirichlet clause is inhabited.** -/
theorem dirichletHole_inhabited (d : ℕ) [NeZero d] :
    DirichletHole d (RootInterface.RootGoodScale d) := by
  classical
  obtain ⟨C, -, hprice⟩ := exists_frozenWitnessEnergyPrice_atHoleBinders d
  obtain ⟨Cdual, hCdual0, hDualAll⟩ :=
    exists_printFaithfulDomainFluxDefectDuality_gaugeWitness d
  obtain ⟨Chardy, hChardy⟩ := exists_uniformHardyConstant d
  refine ⟨fun s₀ rho Rad =>
      max 0 (frozenHeadC0Factor C d s₀ rho Rad (1 / (3 * Real.sqrt (d : ℝ)))
        Cdual ((Chardy s₀ rho Rad).toReal)) + 1, ?_, ?_⟩
  · intro s₀ rho Rad
    have h0 : (0 : ℝ) ≤ max 0 (frozenHeadC0Factor C d s₀ rho Rad
        (1 / (3 * Real.sqrt (d : ℝ))) Cdual ((Chardy s₀ rho Rad).toReal)) :=
      le_max_left _ _
    linarith only [h0]
  intro g hg kappa hkappa hkappaLe
  have hg0 : (0 : ℝ) ≤ g := hg.1
  have hrho0 : (0 : ℝ) ≤ Certificate.printRowOrder g := by
    rw [Certificate.printRowOrder]
    linarith only [hg0]
  have hq0 : 0 ≤ witnessErrorEccentricityExponent g kappa :=
    witnessErrorEccentricityExponent_nonneg hkappa hrho0
  have hp00 : 0 ≤ foldedFrameEccentricityExponent g kappa :=
    foldedFrameEccentricityExponent_nonneg_of_orders hkappa hrho0
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hp0 : (0 : ℝ) ≤ (d : ℝ) + 1 + witnessErrorEccentricityExponent g kappa := by
    linarith only [hdR, hq0]
  refine ⟨perGLengthFactor (frozenHeadLgFactor d g kappa) kappa,
    foldedFrameEccentricityExponent g kappa +
      ((d : ℝ) + 1 + witnessErrorEccentricityExponent g kappa) / kappa,
    one_le_perGLengthFactor _ hkappa, ?_, ?_⟩
  · have hdiv : (0 : ℝ) ≤
        ((d : ℝ) + 1 + witnessErrorEccentricityExponent g kappa) / kappa :=
      div_nonneg hp0 hkappa.le
    linarith only [hp00, hdiv]
  intro abar a x hx hroot s₀ hs₀ rho Rad U hUex hsandwich hUsub hinner
    epsilon hepsilon hscale g₀ _hbdd hHs h hAff hhPhys uFun uGrad hMem hWeakU
  obtain ⟨j, z, hU⟩ := hUex
  obtain ⟨c, hgood, -, hdelta, hS, -, -, -, -, -⟩ := hroot.provider_surface
  -- scalar facts
  have hs0 : 0 < s₀ :=
    lt_of_lt_of_le (by linarith only [hg0] : (0 : ℝ) < (1 + g) / 4) hs₀.1
  have hsHalf : s₀ < 1 / 2 := hs₀.2
  have hrateOrder : kappa ≤ s₀ := le_trans hkappaLe hs₀.1
  have hLg1 : (1 : ℝ) ≤ perGLengthFactor (frozenHeadLgFactor d g kappa) kappa :=
    one_le_perGLengthFactor _ hkappa
  have hscale' : x ≤ epsilon⁻¹ :=
    RootInterface.scale_le_of_foldedScale_le (by linarith only [hx]) hLg1 hscale
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hrhopos : 0 < rho := hsandwich.1
  have hRad0 : (0 : ℝ) ≤ Rad := hsandwich.2.1
  have hRadpos : 0 < Rad := rad_pos_of_hasBallSandwich hsandwich
  have hdelta1 : Real.sqrt hgood.delta ≤ 1 := by
    have h1 := Real.sqrt_le_sqrt hdelta.2.le
    rwa [Real.sqrt_one] at h1
  -- the outer bracket
  obtain ⟨J, hJlow, hJup⟩ :=
    Entry.exists_pow_three_bracket (x := 2 * Rad) (by linarith only [hRad0])
  -- the physical realization, the gauge pullback and the gauge weak solution
  obtain ⟨u, -, huGrad, hAffhu, huPhys⟩ :=
    exists_frozenWitnessPhysicalRealization hS hepsilon hU g₀ h hAff uFun uGrad
      hMem hWeakU
  obtain ⟨uHat, hHat, huHat, hhHat, -⟩ :=
    exists_frozenWitnessGaugePullback hS hU h u hAffhu
  have hWeakGauge := exists_frozenWitnessGaugeWeakSolution hS
    (frozenWitness_physicalDomain_isOpenBoundedConvexDomain hS hU) u huPhys uHat
    huHat
  -- the energy price
  obtain ⟨lambda, hlambdaRange, hEnergy⟩ :=
    hprice g c kappa abar a x epsilon hgood hS U j z rho Rad s₀ J g₀ h uFun uGrad
      uHat hdelta hg hkappa hx hepsilon hscale' hs₀ hJlow hU hUsub hinner
      hsandwich hHs hAff hMem hWeakU (by rw [huHat, huGrad])
  -- the ruled carrier and the Hardy row
  obtain ⟨⟨system⟩, hUconv, hUne, -⟩ :=
    exists_frozenWitnessRuledCarrier hS hU hsandwich
  obtain ⟨hCtop, hCrow⟩ := hChardy s₀ rho Rad hs0 hsHalf
    (matImage (matSqrt (symmPart abar))⁻¹ U) hsandwich
  have hHardy : ∀ G : Vec d → Vec d,
      Integrable G (volume.restrict (matImage (matSqrt (symmPart abar))⁻¹ U)) →
        PrintFaithfulPositiveTestRow system s₀ G (Chardy s₀ rho Rad) :=
    fun G hG => hCrow (matImage (matSqrt (symmPart abar))⁻¹ U) hUconv hsandwich
      system G hG
  -- the remaining rows
  have hFdefect :=
    frozenWitness_fluxDefect_memVectorL2 (a := a) hS hepsilon hU rfl uHat
  obtain ⟨aCell, wCell, hfamily⟩ :=
    exists_frozenWitnessCellFamily (a := a) hS hepsilon system rfl uHat
      hWeakGauge
  obtain ⟨aObs, hObs⟩ :=
    exists_frozenWitnessObservationFamily (a := a) hS hepsilon system rfl uHat
      hWeakGauge
  have hBoundaryTop := hsNormSq_matSqrt_symmPart_ne_top abar hHs
  have hDual := hDualAll hS z j hU rfl hs0 hsHalf (scaledCoeff epsilon a) u h
    uHat hHat huHat hhHat hAffhu huPhys hhPhys rfl hFdefect
  have hGauge := gaugeDomain_subset_normalizedSublevel hS hUsub
  -- the law-free energy bound
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hsqd : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have hCgeo0 : (0 : ℝ) ≤ witnessGeometricFactor d rho (responseWindowOrder g) := by
    rw [witnessGeometricFactor]
    exact Real.rpow_nonneg
      (div_pos hrhopos (by linarith only [hsqd])).le _
  have hA0 : (0 : ℝ) ≤
      lambdaRouteClaw d (responseWindowOrder g) lambda abar *
        (witnessGeometricFactor d rho (responseWindowOrder g) *
          frameFoldConstant d g kappa ((J : ℕ) : ℝ)) :=
    mul_nonneg (lambdaRouteClaw_nonneg d _ _ _)
      (mul_nonneg hCgeo0 (frameFoldConstant_nonneg d g kappa _))
  have hAle := witnessRouteAmplitude_le_classes hS hg hkappa hlambdaRange hinner
    hsandwich hJup
  have hsd : (0 : ℝ) ≤ (d : ℝ) + 2 * s₀ := by linarith only [hdR, hs0]
  have hKle := witnessRouteEnergyPrice_le_collapsed (d := d) (abar := abar) C
    hs0 hkappa hrho0 hsd hA0 hAle
  have hK0 := hEnergy.1
  -- the head
  have hhardyEq : Chardy s₀ rho Rad ≤
      ENNReal.ofReal ((Chardy s₀ rho Rad).toReal) :=
    le_of_eq (ENNReal.ofReal_toReal hCtop).symm
  have hhead : ∀ Jh : ℕ, 2 * Rad ≤ (3 : ℝ) ^ (Jh : ℤ) →
      (3 : ℝ) ^ (Jh : ℤ) ≤ 1 + 3 * (2 * Rad) →
      scheduledRateHead d
          (Real.sqrt (hsAffineFactor (matSqrt (symmPart abar))⁻¹ s₀
            ‖matSqrt (symmPart abar)‖)) Cdual
          ((Real.rpow (3 : ℝ) (responseWindowOrder g) *
              foldedAnchoredFrameConstant d g kappa s₀
                (coarseFluxResponseConstant d) Rad
                (1 / (3 * Real.sqrt (d : ℝ))) hgood.delta ((Jh : ℕ) : ℝ)) ^ 2 *
            EnergyPrice.gaugeWitnessEnergyPriceW C d s₀
              (witnessRouteCwit d
                (lambdaRouteClaw d (responseWindowOrder g) lambda abar)
                (witnessGeometricFactor d rho (responseWindowOrder g))
                g kappa ((J : ℕ) : ℝ) abar) abar)
          (Chardy s₀ rho Rad) ≤
        ENNReal.ofReal (frozenWitnessHeadConstant d g kappa s₀ rho Rad
          (1 / (3 * Real.sqrt (d : ℝ))) Cdual ((Chardy s₀ rho Rad).toReal)
          (collapsedEnergyLawFree C d s₀
              (witnessAmplitudeC0Factor d rho Rad *
                witnessAmplitudeLgFactor d g kappa) *
            (max 1 (witnessEccentricity (symmPart abar))) ^
              ((d : ℝ) + 2 * s₀ +
                2 * witnessErrorEccentricityExponent g kappa)) abar) := by
    intro Jh _ hJhUp
    have hJhR : (3 : ℝ) ^ ((Jh : ℕ) : ℝ) ≤ 1 + 3 * (2 * Rad) := by
      rw [Real.rpow_natCast]
      rwa [zpow_natCast] at hJhUp
    exact frozenWitnessScheduledHead_le hS hg hkappa hs₀ hU hUsub hinner
      hsandwich hRadpos (Nat.cast_nonneg _) hJhR hdelta1 hCdual0
      ENNReal.toReal_nonneg hhardyEq hK0 hKle
  -- the head constant is nonnegative
  have hcnorm : (0 : ℝ) < 1 / (3 * Real.sqrt (d : ℝ)) :=
    div_pos one_pos (by linarith only [hsqd])
  have hHconst0 : (0 : ℝ) ≤ frozenWitnessHeadConstant d g kappa s₀ rho Rad
      (1 / (3 * Real.sqrt (d : ℝ))) Cdual ((Chardy s₀ rho Rad).toReal)
      (collapsedEnergyLawFree C d s₀
          (witnessAmplitudeC0Factor d rho Rad *
            witnessAmplitudeLgFactor d g kappa) *
        (max 1 (witnessEccentricity (symmPart abar))) ^
          ((d : ℝ) + 2 * s₀ +
            2 * witnessErrorEccentricityExponent g kappa)) abar := by
    rw [frozenWitnessHeadConstant]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (gaugeOutputLawFree_nonneg d s₀ rho)
        (eccentricityFoldFactor_pos abar _).le) hCdual0)
      (mul_nonneg (by norm_num) (mul_nonneg ENNReal.toReal_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg
          (fluxC0Factor_nonneg d hs0 Rad _) (fluxLgFactor_nonneg d g kappa))
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))))
  -- the frozen conclusion at the capstone's shape
  have hterm := hgood.explicit_foldedFrozenFrameDirichletBound_of_energy hS hg
    hkappa hx hepsilon hscale' hd1 rfl hUconv.isOpen.measurableSet
    (frozenWitness_gaugeDomain_volume_ne_zero hS hU) system hUconv hUne hRadpos
    hs0 hsHalf hs₀ hrateOrder hGauge u h uHat hHat huHat hhHat rfl aObs aCell
    hObs wCell hfamily hEnergy hBoundaryTop hHardy hFdefect
    hcnorm hinner hsandwich hDual
    (C₀ := fun _ _ _ => frozenWitnessHeadConstant d g kappa s₀ rho Rad
      (1 / (3 * Real.sqrt (d : ℝ))) Cdual ((Chardy s₀ rho Rad).toReal)
      (collapsedEnergyLawFree C d s₀
          (witnessAmplitudeC0Factor d rho Rad *
            witnessAmplitudeLgFactor d g kappa) *
        (max 1 (witnessEccentricity (symmPart abar))) ^
          ((d : ℝ) + 2 * s₀ +
            2 * witnessErrorEccentricityExponent g kappa)) abar)
    hHconst0 hhead uGrad huGrad
  -- the hole's shape
  refine rateFactor_to_holeShape abar hterm ?_ ?_ hkappa hp0 hp00 hepsilon.le
    (by linarith only [hx])
  · refine le_trans (frozenWitnessHeadConstant_le_classes C hs0 hsHalf.le
      hCdual0) ?_
    have hE0 : (0 : ℝ) ≤ (max 1 (witnessEccentricity (symmPart abar))) ^
        ((d : ℝ) + 1 + witnessErrorEccentricityExponent g kappa) :=
      Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
    have hKrest0 : (0 : ℝ) ≤ frozenHeadLgFactor d g kappa :=
      frozenHeadLgFactor_nonneg d g kappa
    have hCle : frozenHeadC0Factor C d s₀ rho Rad (1 / (3 * Real.sqrt (d : ℝ)))
          Cdual ((Chardy s₀ rho Rad).toReal) ≤
        max 0 (frozenHeadC0Factor C d s₀ rho Rad (1 / (3 * Real.sqrt (d : ℝ)))
          Cdual ((Chardy s₀ rho Rad).toReal)) + 1 := by
      have h1 : frozenHeadC0Factor C d s₀ rho Rad (1 / (3 * Real.sqrt (d : ℝ)))
          Cdual ((Chardy s₀ rho Rad).toReal) ≤
          max 0 (frozenHeadC0Factor C d s₀ rho Rad (1 / (3 * Real.sqrt (d : ℝ)))
            Cdual ((Chardy s₀ rho Rad).toReal)) := le_max_right _ _
      linarith only [h1]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCle hE0) hKrest0
  · have h0 : (0 : ℝ) ≤ max 0 (frozenHeadC0Factor C d s₀ rho Rad
        (1 / (3 * Real.sqrt (d : ℝ))) Cdual ((Chardy s₀ rho Rad).toReal)) :=
      le_max_left _ _
    linarith only [h0]

end

end RowSupply
end HighContrast
end HCPolySupport
