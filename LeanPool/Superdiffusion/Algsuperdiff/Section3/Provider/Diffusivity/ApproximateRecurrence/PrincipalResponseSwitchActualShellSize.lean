/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube

/-!
# PrincipalResponseSwitchActualShellSize

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the centered-shell size `hshell`, reduced to the centering estimate

Source displays in ABK26:

* `e.good.local.events` (label; display), whose chain is `C_sens sup_{L>=n}
  3^{2m} ||grad(k_L-k_n)||_{W^{1,infinity}(z+cu_m)} <= (1/2)
  C_{e.cg.ellip.lower}^{-1} 3^{-(1/2)(n-m)_+} shom_{n-1} <= 3^{-(1/4)(n-m)_+}
  lambda_{1/8,2}(z+cu_m; a_n)`;
* `e.cg.ellip.lower` (label), the source of the constant `C_{e.cg.ellip.lower}`
  carried here as the explicit parameter `Ccg`;
* the Young remainder of Step 3, whose absorption needs `||h - (h)_{z+cu_n}||^2
  <= Delta^2 shom_{m-h} lambda_{3/8,2}`.

## What this module supplies

The binder `hshell` of `ApproximateRecurrence.PrincipalResponseSwitchTransport`
and of `ApproximateRecurrence.PrincipalResponseSwitchActualPerCube` is reduced
to **one** inequality about the centered shell alone, and the whole probabilistic
and ellipticity content is discharged from the good event.

Precisely, `w1Infinity_sq_le_of_centering_ae` proves: almost surely, on the good
event, and given only

```
hcentre :  ||h - (h)_{z+cu_n}||_{W^{1,infinity}}  <=  K . osc ,
```

where `osc = incrementOscGauge₂` is the manuscript's own gauge
`3^{2n} ||grad(k_m - k_{m-h})||_{W^{1,infinity}(z+cu_n)}`, the required
shell-size bound

```
||h - (h)_{z+cu_n}||^2  <=  Delta^2 . S . lambda_{3/8,2}(z+cu_n; a_{m-h})
```

holds for every `S` above the explicit threshold `shellSizeThreshold`.

Both of the event's inequalities are used, exactly as the manuscript uses them:
the **middle** term (against `shom_{m-h-1}`) supplies one factor of `osc`, and
the **third** term (against `lambda_{1/8,2}`, transferred to the frozen
`lambda_{3/8,2}` by the proved `Provider.BadEvents.lambda_transfer_ae`)
supplies the other.  Their product carries `Delta^3`, and one power of `Delta
<= 1` is discarded to reach the required `Delta^2`.

## The two residuals, stated exactly

* `hcentre` -- **the centering estimate.**  This is elementary at this carrier
  and is *not* an `L^2` Poincare inequality: the shell is `W^{2,infinity}` and
  the localization cube is convex, so `|h(x) - h(y)| <= ||grad h||_{L^infinity}
  |x - y|` on the cube gives `||h - (h)_Q||_{L^infinity} <= ||grad
  h||_{L^infinity} diam(Q)`, and the frozen `w1Infinity = max{ ||grad
  h||_infinity, ||h||_infinity }` is then below a dimensional multiple of the
  gauge `osc`, whose second component is exactly `3^{n} ||grad
  h||_{L^infinity(z+cu_n)}` after the rescaling.  It is **not proved here**: the frozen value gauge is an essential supremum of `matrixNorm`
  and the cube average is CoarseGraining's `cubeAverageMat` at the *unrescaled*
  cube, so a change-of-variables bridge and a mean-value bound at the
  shell-field carrier are still required.  `hcentre` is carried as an explicit
  binder with the constant `K` free, never as an assumed conclusion.
* `hS` -- the threshold `shellSizeThreshold M Ccg K lowScale <= S`.  At the
  manuscript's `S = shom_{m-h}` this is the one-scale comparison
  `shom_{m-h-1} <= 2 Ccg (C_sens/K)^2 shom_{m-h}` of the annealed diffusivity,
  a statement about the *data* of the recurrence, of the same kind as
  `e.cg.ellip.lower`.  It is a hypothesis, not a derived fact.

Neither residual is a predecessor's conclusion and neither smuggles a proof
step.

## Main definitions

* `shellSizeThreshold`: the explicit `S`-threshold
  `K^2 Ccg^{-1} shom_{lowScale-1} / (2 C_sens^2)`.

## Main results

* `rpow_neg_half_scaleGapPos_eq_sq`: `3^{-(1/2)G} = (3^{-(1/4)G})^2`.
* `goodLocalThreshold_eq_sq_discount_mul`: the middle term of
  `e.good.local.events`, in the `Delta^2` form Step 3 uses.
* `w1Infinity_sq_le_of_centering_ae`: the reduction of `hshell`.
* `shell_hypothesis_of_centering_ae`: the same, in the exact binder shape the
  per-cube switch consumes, quantified over the descendants of `Q` at depth
  `j`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz

noncomputable section

variable {d : ℕ}

/-! ## The discount and the middle term of `e.good.local.events` -/

/-- The exponent bookkeeping of `e.good.local.events`: its middle term carries
`3^{-(1/2)(n-m)_+}`, which is the square of the discount
`Delta = 3^{-(1/4)(n-m)_+}` appearing in its third term.

Unconditional: no caller-supplied proposition enters. -/
theorem rpow_neg_half_scaleGapPos_eq_sq (m n : ℤ) :
    (3 : ℝ) ^ (-(1 / 2 : ℝ) * scaleGapPos m n) =
      ((3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos m n)) ^ 2 := by
  rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The middle term of `e.good.local.events` written with the squared discount,
which is the form Step 3's Young absorption consumes.

Unconditional: no caller-supplied proposition enters. -/
theorem goodLocalThreshold_eq_sq_discount_mul (M : ABKModel d) (Ccg : ℝ)
    (m n : ℤ) :
    goodLocalThreshold M Ccg m n =
      (1 / 2 : ℝ) * Ccg⁻¹ *
        ((3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos m n)) ^ 2 *
        ((Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)) := by
  rw [goodLocalThreshold, rpow_neg_half_scaleGapPos_eq_sq]

/-! ## The `S`-threshold -/

/-- The explicit threshold above which the centered-shell size bound holds:
`K^2 Ccg^{-1} shom_{lowScale-1} / (2 C_sens^2)`, with `K` the constant of the
centering estimate and `C_sens = sensitivityConstMax d` the joint sensitivity
constant of `e.good.local.events`.

At the manuscript's own `S = shom_{m-h}` the condition
`shellSizeThreshold <= S` is the one-scale comparison of the annealed
diffusivity described in the module docstring. -/
def shellSizeThreshold (M : ABKModel d) (Ccg K : ℝ) (lowScale : ℤ) : ℝ :=
  K ^ 2 * Ccg⁻¹ *
      ((Algsuperdiff.Section3.Annealed.sigmaBar M (lowScale - 1) : ℝ)) /
    (2 * sensitivityConstMax d ^ 2)

/-! ## The reduction of `hshell` -/

/-- **The centered-shell size bound, reduced to the centering estimate.**

Almost surely on the cutoff sample law: if the sample lies in the manuscript's
own event `cQ_z = cQ(n, m-h, z)` and the centered shell obeys the centering
estimate `hcentre` with constant `K`, then for every `S` above
`shellSizeThreshold` the shell-size bound required by the Young absorption
holds.

Both inequalities of `e.good.local.events` are used: the middle one (against
`shom_{m-h-1}`) and the third one (against `lambda_{1/8,2}`, transferred to the
frozen `lambda_{3/8,2}` almost surely).  Their product carries `Delta^3`, and
one power of `Delta <= 1` is discarded.

: this statement holds only under the propositions supplied by its binders --
`hCcg` (`0 < Ccg`), `hS` (the threshold), the membership in the good event, and
`hcentre`.  It is a provider A, not a source-facing frozen declaration. -/
theorem w1Infinity_sq_le_of_centering_ae [NeZero d] (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (R : TriadicCube d) {lowScale highScale : ℤ}
    (hle : lowScale ≤ highScale) {K S : ℝ}
    (hS : shellSizeThreshold M Ccg K lowScale ≤ S) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      omega ∈ goodLocalEvent M Ccg R lowScale →
        (centeredFreshShellUnitCube M R hle omega).w1Infinity ≤
            K * incrementOscGauge₂ R lowScale highScale omega →
          (centeredFreshShellUnitCube M R hle omega).w1Infinity ^ 2 ≤
            ((3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos R.scale lowScale)) ^ 2 * S *
              Ch02.lambdaSq R (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
  filter_upwards [lambda_transfer_ae M R lowScale] with omega htransfer homega hcentre
  set C : ℝ := sensitivityConstMax d with hCdef
  set Delta : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ) * scaleGapPos R.scale lowScale) with hDdef
  set osc : ℝ := incrementOscGauge₂ R lowScale highScale omega with hoscdef
  set lam : ℝ := Ch02.lambdaSq R (3 / 8) (.finite 2)
    (coefficientCutoffTriadicCoeffFamily M lowScale omega) with hlamdef
  set sig : ℝ := ((Algsuperdiff.Section3.Annealed.sigmaBar M (lowScale - 1) : ℝ))
    with hsigdef
  set w : ℝ := (centeredFreshShellUnitCube M R hle omega).w1Infinity with hwdef
  have hC0 : (0 : ℝ) < C := sensitivityConstMax_pos d
  have hD0 : (0 : ℝ) < Delta := Real.rpow_pos_of_pos (by norm_num) _
  have hD1 : Delta ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by
        have h := scaleGapPos_nonneg R.scale lowScale
        nlinarith)
  have hosc0 : (0 : ℝ) ≤ osc := incrementOscGauge₂_nonneg R lowScale highScale omega
  have hw0 : (0 : ℝ) ≤ w := w1Infinity_nonneg _
  have hsig0 : (0 : ℝ) < sig := (Algsuperdiff.Section3.Annealed.sigmaBar M (lowScale - 1)).2
  have hCcginv : (0 : ℝ) < Ccg⁻¹ := inv_pos.2 hCcg
  -- the middle leg of `e.good.local.events`
  have hmid : C * osc ≤ (1 / 2 : ℝ) * Ccg⁻¹ * Delta ^ 2 * sig := by
    have h := homega.1 highScale hle
    rwa [goodLocalThreshold_eq_sq_discount_mul] at h
  -- the third leg, transferred to the frozen gauge
  have hlam : C * osc ≤ Delta * lam := by
    refine (incrementOscGauge₂_le_of_mem_goodLocalEvent M R homega hle).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hD0.le
    rw [hlamdef, ← unitCubeLambda_unitRescaledCutoffCoeff M R lowScale (3 / 8)
      (.finite 2) omega]
    exact htransfer
  have hlam0 : (0 : ℝ) ≤ lam := by
    have hCo : (0 : ℝ) ≤ C * osc := mul_nonneg hC0.le hosc0
    nlinarith
  set A : ℝ := (1 / 2 : ℝ) * Ccg⁻¹ * Delta ^ 2 * sig with hAdef
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hAdef]
    positivity
  have hCo : (0 : ℝ) ≤ C * osc := mul_nonneg hC0.le hosc0
  -- the product of the two legs
  have hsq : (C * osc) ^ 2 ≤ A * (Delta * lam) := by
    have h := mul_le_mul hmid hlam hCo hA0
    calc (C * osc) ^ 2 = (C * osc) * (C * osc) := by ring
      _ ≤ A * (Delta * lam) := h
  have hwsq : (C * w) ^ 2 ≤ K ^ 2 * (C * osc) ^ 2 := by
    have hw2 : w * w ≤ (K * osc) * (K * osc) := mul_self_le_mul_self hw0 hcentre
    have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
    calc (C * w) ^ 2 = C ^ 2 * (w * w) := by ring
      _ ≤ C ^ 2 * ((K * osc) * (K * osc)) := mul_le_mul_of_nonneg_left hw2 hC2
      _ = K ^ 2 * (C * osc) ^ 2 := by ring
  have hkey : (C * w) ^ 2 ≤ K ^ 2 * (A * (Delta * lam)) :=
    hwsq.trans (mul_le_mul_of_nonneg_left hsq (sq_nonneg K))
  -- discard one power of `Delta`
  have hdrop : K ^ 2 * (A * (Delta * lam)) ≤ K ^ 2 * (A * lam) := by
    have hstep : A * (Delta * lam) ≤ A * lam := by
      have hinner : Delta * lam ≤ lam := by nlinarith
      exact mul_le_mul_of_nonneg_left hinner hA0
    exact mul_le_mul_of_nonneg_left hstep (sq_nonneg K)
  have hthr : w ^ 2 ≤ Delta ^ 2 * shellSizeThreshold M Ccg K lowScale * lam := by
    have hC2 : (0 : ℝ) < C ^ 2 := by positivity
    have hchain : (C * w) ^ 2 ≤ K ^ 2 * (A * lam) := le_trans hkey hdrop
    have hid : Delta ^ 2 * shellSizeThreshold M Ccg K lowScale * lam * C ^ 2 =
        K ^ 2 * (A * lam) := by
      rw [hAdef, shellSizeThreshold, ← hCdef, ← hsigdef]
      field_simp
    have hexp : (C * w) ^ 2 = w ^ 2 * C ^ 2 := by ring
    rw [hexp, ← hid] at hchain
    exact le_of_mul_le_mul_right hchain hC2
  have hmono : Delta ^ 2 * shellSizeThreshold M Ccg K lowScale * lam ≤
      Delta ^ 2 * S * lam := by
    have h1 : Delta ^ 2 * shellSizeThreshold M Ccg K lowScale ≤ Delta ^ 2 * S :=
      mul_le_mul_of_nonneg_left hS (sq_nonneg Delta)
    exact mul_le_mul_of_nonneg_right h1 hlam0
  exact le_trans hthr hmono

/-- **The binder `hshell` of the per-cube switch, produced from the centering
estimate.**

This is `w1Infinity_sq_le_of_centering_ae` in the exact shape the per-cube
switch consumes, quantified over the cubes of a depth-`j` grid.  The
almost-sure quantifier is outside the grid quantifier, which is legitimate
because the grid is finite.

: this statement holds only under the propositions supplied by its binders --
`hCcg`, `hS`, and `hcentre`, the centering estimate for every cube of the grid,
whose status is set out in the module docstring.  It is a provider A, not a
source-facing frozen declaration. -/
theorem shell_hypothesis_of_centering_ae [NeZero d] (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) (j : ℕ) {lowScale highScale : ℤ}
    (hle : lowScale ≤ highScale) {K S : ℝ}
    (hS : shellSizeThreshold M Ccg K lowScale ≤ S) :
    ∀ R ∈ descendantsAtDepth Q j,
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        omega ∈ goodLocalEvent M Ccg R lowScale →
          (centeredFreshShellUnitCube M R hle omega).w1Infinity ≤
              K * incrementOscGauge₂ R lowScale highScale omega →
            (centeredFreshShellUnitCube M R hle omega).w1Infinity ^ 2 ≤
              gridSwitchDiscount Q j lowScale ^ 2 * S *
                Ch02.lambdaSq R (3 / 8) (.finite 2)
                  (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
  intro R hR
  filter_upwards [w1Infinity_sq_le_of_centering_ae M hCcg R hle (K := K) hS
    (highScale := highScale)] with omega hbound homega hcentre
  have h := hbound homega hcentre
  rwa [gridSwitchDiscount_eq_of_mem Q j lowScale hR] at h

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
