/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitObligationsQuadratic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitProducerLoad
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseGoodEnergy

/-!
# SplitObligationsPrincipal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Obligation (1) of `SplitScaleObligations`: the switch energy is sample-integrable

ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.Pz.def`, the switch
display.

## What this module supplies

`Closure.SplitProducerFold.SplitScaleObligations`'s first conjunct: per
mesoscopic cell of the closure mesh,

```
  omega |->  P_z . bfA_{n+h}(z + cu_n) P_z    is integrable under  cutoffSampleLaw M .
```

`LocalizationFluctuationMuMeasCell.integrable_switchCubeEnergy_of_le` reduces
it to a measurable load family and one almost-surely integrable dominator.  The
measurability half is the proved
`Closure.SplitProducerLoad.measurable_principalPz_cutoffSample`.  The dominator
is produced here, from two proved moment layers and nothing else:

* the **pathwise** coarse-quadratic bound
  `Closure.SplitObligationsQuadratic.switchCubeEnergy_le_ellipticityUpper`,
  which replaces the coarse matrix by the realised upper ellipticity constant
  `Lam_omega := Cutoff.coefficientCutoffCubeEllipticityUpper M (n+h) omega R`
  of the cell and the two squared component lengths of the load; and
* the two integrability facts
  `Cutoff.integrable_coefficientCutoffCubeEllipticityUpper_pow` (every finite
  moment of `Lam_omega`, under the genuine cutoff law) and
  `PrincipalResponseGoodEnergy.exists_gamma0_integrable_switchEllipLoad_principalPz_sq`
  (the second moment of the ellipticity load `shom |p_z|^2 + shom^{-1} |q_z|^2`
  of `e.Pz.def`).

The two are combined by plain domination: writing `L` for the ellipticity load,
`|p_z|^2 <= shom^{-1} L` and `|q_z|^2 <= shom L`, and each of `Lam L`,
`Lam^2 L`, `L` is dominated by half a sum of squares whose two summands are
`Lam^2`, `Lam^4`, `L^2` and `1`.  No Holder inequality and no selection occurs.

## Binders

Beyond the typing binders: the parameter block of `e.recurrence.params` in the
shape `Closure.ClosureRegime` supplies (the induction state, `0 < h`, the
`cgamma` threshold through `Cterm (cstar M)^{-1} <= Ec` and `cgamma <=
Ec^{-5}`, and `h <= 6 cstar cgamma^{-1}`), the large-cube gate, the two
direction bounds, and the two weak-solution properties of `e.def.w` for the
corrector families.  No measurability, smallness or selection property of the
families is assumed.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 1--3, `e.Pz.def`,
  `e.recurrence.params`, `e.nablaw.in.L.eight`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## Two elementary measurability facts -/

private theorem measurable_vecNormSq_comp {Omega : Type*} [MeasurableSpace Omega]
    {f : Omega → Vec d} (hf : Measurable f) :
    Measurable fun omega => vecNormSq (f omega) := by
  have hEq : (fun omega => vecNormSq (f omega)) =
      fun omega => ∑ i, f omega i * f omega i := rfl
  rw [hEq]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hf)

private theorem measurable_switchEllipLoad_comp {Omega : Type*} [MeasurableSpace Omega]
    (S : ℝ) {X : Omega → BlockVec d} (hX : Measurable X) :
    Measurable fun omega => switchEllipLoad S (X omega) := by
  have hEq : (fun omega => switchEllipLoad S (X omega)) =
      fun omega => S * vecNormSq (X omega).1 + S⁻¹ * vecNormSq (X omega).2 := rfl
  rw [hEq]
  exact (measurable_const.mul (measurable_vecNormSq_comp hX.fst)).add
    (measurable_const.mul (measurable_vecNormSq_comp hX.snd))

/-! ## Domination by half a sum of squares -/

/-- Two nonnegative square-integrable functions have an integrable product.
Plain arithmetic--geometric-mean domination; no Holder inequality is used. -/
theorem integrable_mul_of_sq_integrable {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A B : Omega → ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega) (hB0 : ∀ omega, 0 ≤ B omega)
    (hAB : AEStronglyMeasurable (fun omega => A omega * B omega) mu)
    (hA : Integrable (fun omega => A omega ^ (2 : ℕ)) mu)
    (hB : Integrable (fun omega => B omega ^ (2 : ℕ)) mu) :
    Integrable (fun omega => A omega * B omega) mu := by
  refine Integrable.mono' ((hA.const_mul ((1 : ℝ) / 2)).add (hB.const_mul ((1 : ℝ) / 2)))
    hAB (Filter.Eventually.of_forall fun omega => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (hA0 omega) (hB0 omega))]
  nlinarith [sq_nonneg (A omega - B omega)]

/-! ## The per-cell integrability, from the ellipticity load's second moment -/

/-- **Obligation (1) at one cell, from the second moment of the ellipticity
load.**

exactly on `hX` (measurability of the load family, a regularity property of the
caller's corrector data) and `hL`, the second moment of `switchEllipLoad` at
the load.  No estimate of the manuscript is used. -/
theorem integrable_switchCubeEnergy_of_integrable_switchEllipLoad_sq
    (M : ABKModel d) (sigma : PositiveScalar) (m : ℤ) (R : TriadicCube d)
    {X : CutoffSample d → BlockVec d} (hX : Measurable X)
    (hL : Integrable
      (fun omega : CutoffSample d => switchEllipLoad ((sigma : ℝ)) (X omega) ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure) :
    Integrable (fun omega : CutoffSample d => switchCubeEnergy M m R (X omega) omega)
      (cutoffSampleLaw M).toMeasure := by
  classical
  have hsig : (0 : ℝ) < (sigma : ℝ) := sigma.2
  have hsinv : (0 : ℝ) < ((sigma : ℝ))⁻¹ := inv_pos.2 hsig
  have hnu : (0 : ℝ) < M.nu := M.nu_pos
  have hnuinv : (0 : ℝ) ≤ M.nu⁻¹ := (inv_pos.2 hnu).le
  set Lam : CutoffSample d → ℝ := fun omega =>
    coefficientCutoffCubeEllipticityUpper M m omega R with hLamdef
  set L : CutoffSample d → ℝ := fun omega => switchEllipLoad ((sigma : ℝ)) (X omega)
    with hLdef
  have hLamMeas : Measurable Lam := measurable_coefficientCutoffCubeEllipticityUpper M m R
  have hLam0 : ∀ omega, 0 ≤ Lam omega := fun omega =>
    coefficientCutoffCubeEllipticityUpper_nonneg M m omega R
  have hLMeas : Measurable L := measurable_switchEllipLoad_comp ((sigma : ℝ)) hX
  have hL0 : ∀ omega, 0 ≤ L omega := fun omega => switchEllipLoad_nonneg hsig (X omega)
  -- every finite moment of the realised upper ellipticity constant
  have hLam2 : Integrable (fun omega : CutoffSample d => Lam omega ^ (2 : ℕ))
      (cutoffSampleLaw M).toMeasure :=
    integrable_coefficientCutoffCubeEllipticityUpper_pow M m R 2
  have hLam4 : Integrable (fun omega : CutoffSample d => Lam omega ^ (4 : ℕ))
      (cutoffSampleLaw M).toMeasure :=
    integrable_coefficientCutoffCubeEllipticityUpper_pow M m R 4
  -- the load's first moment
  have hLint : Integrable L (cutoffSampleLaw M).toMeasure := by
    refine Integrable.mono' ((integrable_const ((1 : ℝ) / 2)).add (hL.const_mul ((1 : ℝ) / 2)))
      hLMeas.aestronglyMeasurable (Filter.Eventually.of_forall fun omega => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (hL0 omega)]
    nlinarith [sq_nonneg (L omega - 1)]
  -- the two mixed moments
  have hLamL : Integrable (fun omega : CutoffSample d => Lam omega * L omega)
      (cutoffSampleLaw M).toMeasure :=
    integrable_mul_of_sq_integrable hLam0 hL0
      ((hLamMeas.mul hLMeas).aestronglyMeasurable) hLam2 hL
  have hLam2L : Integrable (fun omega : CutoffSample d => Lam omega ^ (2 : ℕ) * L omega)
      (cutoffSampleLaw M).toMeasure := by
    have hsq : (fun omega : CutoffSample d => (Lam omega ^ (2 : ℕ)) ^ (2 : ℕ)) =
        fun omega : CutoffSample d => Lam omega ^ (4 : ℕ) := by
      funext omega
      rw [← pow_mul]
    refine integrable_mul_of_sq_integrable (fun omega => by positivity) hL0
      (((hLamMeas.pow_const 2).mul hLMeas).aestronglyMeasurable) ?_ hL
    rw [hsq]
    exact hLam4
  -- the dominator
  have hgint : Integrable (fun omega : CutoffSample d =>
      ((sigma : ℝ))⁻¹ * (Lam omega * L omega) +
        2 * M.nu⁻¹ * ((sigma : ℝ))⁻¹ * (Lam omega ^ (2 : ℕ) * L omega) +
        2 * M.nu⁻¹ * (sigma : ℝ) * L omega) (cutoffSampleLaw M).toMeasure :=
    ((hLamL.const_mul _).add (hLam2L.const_mul _)).add (hLint.const_mul _)
  refine integrable_switchCubeEnergy_of_le M m R hX hgint
    (Filter.Eventually.of_forall fun omega => ?_)
  -- the pathwise domination
  have hLeq : L omega =
      (sigma : ℝ) * vecNormSq (X omega).1 + ((sigma : ℝ))⁻¹ * vecNormSq (X omega).2 := rfl
  have hp0 : (0 : ℝ) ≤ vecNormSq (X omega).1 := vecNormSq_nonneg _
  have hq0 : (0 : ℝ) ≤ vecNormSq (X omega).2 := vecNormSq_nonneg _
  have hinvl : ((sigma : ℝ))⁻¹ * (sigma : ℝ) = 1 := inv_mul_cancel₀ hsig.ne'
  have hinvr : (sigma : ℝ) * ((sigma : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hsig.ne'
  have hp : vecNormSq (X omega).1 ≤ ((sigma : ℝ))⁻¹ * L omega := by
    have hexp : ((sigma : ℝ))⁻¹ * L omega =
        vecNormSq (X omega).1 +
          ((sigma : ℝ))⁻¹ * ((sigma : ℝ))⁻¹ * vecNormSq (X omega).2 := by
      rw [hLeq]
      calc ((sigma : ℝ))⁻¹ *
              ((sigma : ℝ) * vecNormSq (X omega).1 +
                ((sigma : ℝ))⁻¹ * vecNormSq (X omega).2)
          = (((sigma : ℝ))⁻¹ * (sigma : ℝ)) * vecNormSq (X omega).1 +
              ((sigma : ℝ))⁻¹ * ((sigma : ℝ))⁻¹ * vecNormSq (X omega).2 := by ring
        _ = vecNormSq (X omega).1 +
              ((sigma : ℝ))⁻¹ * ((sigma : ℝ))⁻¹ * vecNormSq (X omega).2 := by
            rw [hinvl, one_mul]
    rw [hexp]
    nlinarith [mul_nonneg (mul_nonneg hsinv.le hsinv.le) hq0]
  have hq : vecNormSq (X omega).2 ≤ (sigma : ℝ) * L omega := by
    have hexp : (sigma : ℝ) * L omega =
        (sigma : ℝ) * (sigma : ℝ) * vecNormSq (X omega).1 + vecNormSq (X omega).2 := by
      rw [hLeq]
      calc (sigma : ℝ) *
              ((sigma : ℝ) * vecNormSq (X omega).1 +
                ((sigma : ℝ))⁻¹ * vecNormSq (X omega).2)
          = (sigma : ℝ) * (sigma : ℝ) * vecNormSq (X omega).1 +
              ((sigma : ℝ) * ((sigma : ℝ))⁻¹) * vecNormSq (X omega).2 := by ring
        _ = (sigma : ℝ) * (sigma : ℝ) * vecNormSq (X omega).1 + vecNormSq (X omega).2 := by
            rw [hinvr, one_mul]
    rw [hexp]
    nlinarith [mul_nonneg (mul_nonneg hsig.le hsig.le) hp0]
  have hcoef : (0 : ℝ) ≤ Lam omega + 2 * M.nu⁻¹ * Lam omega ^ (2 : ℕ) := by
    have := hLam0 omega
    positivity
  have h1 := mul_le_mul_of_nonneg_left hp hcoef
  have h2 := mul_le_mul_of_nonneg_left hq
    (by positivity : (0 : ℝ) ≤ 2 * M.nu⁻¹)
  have hbound := switchCubeEnergy_le_ellipticityUpper M m R (X omega) omega
  nlinarith [h1, h2, hbound]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
