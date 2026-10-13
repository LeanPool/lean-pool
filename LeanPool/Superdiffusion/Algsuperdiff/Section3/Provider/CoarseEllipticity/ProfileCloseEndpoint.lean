/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridDominationEndpoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.PayloadSandwich

/-!
# ProfileCloseEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `q = infinity` payload, composed at the `sSup` carrier

`Provider/CoarseEllipticity/GridDominationEndpoint.lean` proves the endpoint's
own dominations: `lambda_{s,infinity}^{-1}` and `Lambda_{s,infinity}` are
*suprema* (`e.coarse.grained.ellipticity.infty`), so any majorant of the
individual weighted grid maxima majorizes them --- with **no** `(2s)^{-1}` and
no fold.  This module supplies the summation half of the endpoint analogue of
what `PayloadSandwich.lean` does at finite `q`: the endpoint weight, its
arithmetic against the finite-`q` grid weight, and the model-free two-term
endpoint summation in the shape the lower payload consumes.

## The recipe, adapted from the finite-`q` sandwich

At finite `q` the sandwich runs: identify CoarseGraining's Chapter 4 grid
maximum with a `gridSupAbs` at an explicit per-cube family, transport it to the
cutoff sample space, split it per cube, lift the lanes by `e.maxy.bound`, and
sum.  The endpoint runs the same five steps at the endpoint's own scales `m -
n`, `n >= 0` --- and it is *simpler* in exactly two places.

* **No gap-`0` fold is inert.**  `gridWeight rho k = 3^{-rho(k+1)}` covers gaps
  `>= 1` only, which is what forces the finite-`q` producers to fold the
  depth-`0` term at a constant `ctop`.  The endpoint index runs over *all* `n
  >= 0`, so the endpoint weight `endpointWeight rho n = 3^{-rho n}` has
  `endpointWeight rho 0 = 1` and the top scale is simply one of the terms.  No
  `ctop`, no `foldedAmp`, no `foldedBlockPole`.
* **The deterministic slot is exactly `Cdet`, with no pole.**  A supremum of
  `Cdet + (lane at gap n)` is at most `Cdet + sup_n (lane)`: the deterministic
  constant is not multiplied by the number of scales.  That is why
  `twoTermFamilySplit_of_endpointMajorant` returns `Ydet <= Cdet` and *not*
  `Cdet (mass rho^{-1})`, and it matches
  `LowerLegProfile.lowerEllipticityProfile_infinity`
  (`lowerEllipticityProfile C gamma s infinity = C`) with nothing left to price.

The collar is still present and still real.  On the lower route,
`e.slstar.multiscale` normalizes the whole payload by `3^{-gamma(m-n)}` on its
left, so the per-cube estimate enters as `|Xc n R| <= 3^{g n} (Cdet + U n R)`.
The upper source comparison instead leaves its deterministic `C` uncollared and
collars only its two random lanes, so an all-collared reading of it is a weaker
derived majorant, not the verbatim printed split.  In either abstract
interface, `rpow_collar_eq_endpointWeight` is the identity `3^{-2sn}
3^{gn} = endpointWeight (2s - g) n`.  Since `endpointWeight (2s-g) n <= 1`,
even a collared deterministic term is bounded by `Cdet`, keeping the endpoint
profile pole-free.

## What is proved here

* the endpoint weight `endpointWeight rho n = 3^{-rho n}` and its arithmetic,
  including the reduction `endpointWeight rho n = 3^{rho} gridWeight rho n`
  which transports every `gridWeight` summability and pole bound of
  `GridWeights`/`BlockPayload` to the endpoint at the cost of one factor
  `3^{rho}`, and the collar identity `rpow_collar_eq_endpointWeight`.
* `endpointTerm_le_tsum` --- a single endpoint term is below the weighted
  series, the elementary step every per-scale estimate passes through.
* `twoTermFamilySplit_of_endpointMajorant` --- the model-free endpoint
  summation, whose deterministic slot is `Cdet` with no pole, in exactly the
  payload shape `LowerLeg.isLowerIntegerFamilyOrlicz_of_familySplit` consumes.

## What is NOT proved here

Nothing in this module touches an observable: the endpoint sandwich at the
`sSup` carrier, the `e.maxy.bound` lift at the endpoint grid, and the composed
producers feeding `LowerLeg.isLowerIntegerFamilyOrlicz_of_familySplit` and
`UpperLeg.isDeterministicShiftTwoTermOneSidedOrlicz_of_split` are not carried
here.  The summation's own `hdom` binder --- the per-cube block estimate at the
endpoint, uniform in the cutoff index `L` --- is an explicit hypothesis, and
nothing below asserts that it is satisfiable.  The small-`m` branch is
untouched.

## References

* ABK26, `e.coarse.grained.ellipticity.infty`, (the endpoint is a supremum);
  `p.cg.ellipticity.bounds`, statement (`e.cg.ellip.lower` label,
  `e.cg.ellip.upper` label), proof (in the upper per-cube comparison, the
  deterministic term is and the two collared random lanes are);
  `p.bfA.multiscalebound`, `e.slstar.multiscale` label and `e.bL.multiscale`
  label; `l.maximums.Gamma.s` label.
* `Provider/CoarseEllipticity/GridDominationEndpoint.lean` (the dominations
  composed here), `.../PayloadSandwich.lean` (the finite-`q` recipe this module
  adapts), `.../LowerLegProfile.lean` (`lowerEllipticityProfile_infinity`),
  `.../ProfileClose.lean` (the finite-`q` pricing).
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {Omega : Type*}
variable {d : ℕ}


noncomputable def endpointWeight (rho : ℝ) (n : ℕ) : ℝ := ((3 : ℝ) ^ (-rho)) ^ n

theorem endpointWeight_pos (rho : ℝ) (n : ℕ) : 0 < endpointWeight rho n :=
  pow_pos (rpow_neg_pos rho) n

theorem endpointWeight_nonneg (rho : ℝ) (n : ℕ) : 0 ≤ endpointWeight rho n :=
  (endpointWeight_pos rho n).le

theorem endpointWeight_zero (rho : ℝ) : endpointWeight rho 0 = 1 := pow_zero _

theorem endpointWeight_le_one {rho : ℝ} (hrho : 0 < rho) (n : ℕ) :
    endpointWeight rho n ≤ 1 :=
  pow_le_one₀ (rpow_neg_nonneg rho) (rpow_neg_lt_one hrho).le

theorem endpointWeight_eq_rpow (rho : ℝ) (n : ℕ) :
    endpointWeight rho n = (3 : ℝ) ^ (-rho * (n : ℝ)) := by
  rw [endpointWeight, ← Real.rpow_natCast ((3 : ℝ) ^ (-rho)) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

theorem rpow_collar_eq_endpointWeight (s g : ℝ) (n : ℕ) :
    (3 : ℝ) ^ (-2 * s * (n : ℝ)) * (3 : ℝ) ^ (g * (n : ℝ))
      = endpointWeight (2 * s - g) n := by
  rw [endpointWeight_eq_rpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring_nf

theorem endpointWeight_eq_const_mul_gridWeight (rho : ℝ) (n : ℕ) :
    endpointWeight rho n = ((3 : ℝ) ^ (-rho))⁻¹ * gridWeight rho n := by
  have hne : ((3 : ℝ) ^ (-rho)) ≠ 0 := ne_of_gt (rpow_neg_pos rho)
  rw [endpointWeight, gridWeight, pow_succ]
  field_simp

theorem summable_endpointWeight_mul {rho : ℝ} {f : ℕ → ℝ}
    (h : Summable fun n : ℕ => gridWeight rho n * f n) :
    Summable fun n : ℕ => endpointWeight rho n * f n := by
  refine (h.mul_left (((3 : ℝ) ^ (-rho))⁻¹)).congr fun n => ?_
  rw [endpointWeight_eq_const_mul_gridWeight]
  ring

theorem tsum_endpointWeight_mul_le {rho S : ℝ} {f : ℕ → ℝ}
    (hS : ∑' n : ℕ, gridWeight rho n * f n ≤ S) :
    ∑' n : ℕ, endpointWeight rho n * f n ≤ ((3 : ℝ) ^ (-rho))⁻¹ * S := by
  have hcnn : (0 : ℝ) ≤ ((3 : ℝ) ^ (-rho))⁻¹ := (inv_pos.2 (rpow_neg_pos rho)).le
  have heq : ∑' n : ℕ, endpointWeight rho n * f n
      = ((3 : ℝ) ^ (-rho))⁻¹ * ∑' n : ℕ, gridWeight rho n * f n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [endpointWeight_eq_const_mul_gridWeight]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hS hcnn

theorem endpointTerm_le_tsum {w : ℕ → ℝ} {V : ℕ → Omega → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hVnonneg : ∀ n omega, 0 ≤ V n omega)
    (hVsum : ∀ omega, Summable fun n : ℕ => w n * V n omega)
    (n : ℕ) (omega : Omega) : w n * V n omega ≤ ∑' j : ℕ, w j * V j omega :=
  (hVsum omega).le_tsum n fun j _ => mul_nonneg (hw j) (hVnonneg j omega)


theorem twoTermFamilySplit_of_endpointMajorant [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : ℤ → Omega → ℝ} {V : ℕ → Omega → ℝ} {w a : ℕ → ℝ} {L0 : ℤ}
    {Cdet Bexp sigmaExp : ℝ}
    (hsigmaExp : 0 < sigmaExp) (hw : ∀ n, 0 < w n)
    (hVnonneg : ∀ n omega, 0 ≤ V n omega) (hVmeas : ∀ n, Measurable (V n))
    (hVsum : ∀ omega, Summable fun n : ℕ => w n * V n omega)
    (ha : ∀ n, 0 < a n) (hasum : Summable fun n : ℕ => w n * a n)
    (hVO : ∀ n, IsBigOWith mu (gammaSigma sigmaExp) (V n) (a n))
    (hBexp : gammaTriangleConst sigmaExp * ∑' n : ℕ, w n * a n ≤ Bexp)
    (hdom : ∀ omega, ∀ L : ℤ, L0 ≤ L →
      X L omega ≤ Cdet + ∑' n : ℕ, w n * V n omega) :
    ∃ Ydet Y : Omega → ℝ,
      (∀ omega, ∀ L : ℤ, L0 ≤ L → X L omega ≤ Ydet omega + Y omega) ∧
      (∀ omega, Ydet omega ≤ Cdet) ∧
      Measurable Y ∧
      IsBigOWith mu (gammaSigma sigmaExp) Y Bexp := by
  refine ⟨fun _ => Cdet, fun omega => ∑' n : ℕ, w n * V n omega, hdom,
    fun _ => le_rfl, ?_, ?_⟩
  · exact measurable_tsum_of_nonneg (fun n => (hVmeas n).const_mul (w n))
      (fun n omega => mul_nonneg (hw n).le (hVnonneg n omega)) hVsum
  · exact isBigOWith_gammaSigma_tsum_weighted hsigmaExp hw hVnonneg hVmeas ha hasum
      hVO hBexp


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
