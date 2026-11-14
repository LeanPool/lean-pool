/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchPlateau

/-!
# PrincipalResponseSwitchActualDisplay

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: the good-event energy display with a per-cube event, and its actual consumer

Source displays in ABK26:

* `l.approximate.recurrence.formula` (label), Step 3;
* the gauge-switch chain, closing;
* `e.nablaw.in.L.eight` (label), quoted as the ellipticity budget;
* the independence sentence;
* `e.lower.bound.principal.one.pre` (label; display);
* `e.good.local.events` (label), instantiated as `cQ_z := cQ(n, m-h, z)`;
* `e.recurrence.params` (label; display).

## What this module supplies

Two things.

1. **The-generalized display.**  The manuscript's event `cQ_z:= cQ(n, m-h, z)`
   *varies with the cube* `z + cu_n`.  A display whose good event is a single
   fixed set cannot consume the per-cube switch;
   `descendantsAverage_integral_goodEventEnergy_le_annealedCube_family` is the
   same composition with the event carried as a family `Ebad: TriadicCube d ->
   Set Omega`, and with the switch hypothesis taken **almost surely** rather
   than pointwise, which is the form in which the switch is actually available
   (see `ApproximateRecurrence.PrincipalResponseSwitchActualPerCube`).

2. **A consumer with `hswitch` produced.**
   `descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube` is
   that display instantiated at the actual cutoff carrier -- `CutoffSample d`,
   `(Cutoff.cutoffSampleLaw M).toMeasure`, the per-cube bad event
   `principalBadEvent M Ccg . lowScale`, and the three terms
   `switchCubeEnergy`, `switchCubeQuad`, `switchEllipLoad` -- in which the
   switch hypothesis is **not a binder**: it is discharged inside the proof
   from `switchCubeEnergy_indicator_le_ae`.  The `cgamma^6` gate is likewise
   discharged, at the corrected recurrence gap and the manuscript's own
   standing range `cgamma in (0, 1/4]`.

## What the consumer still owes, and to whom

The consumer's remaining binders are exactly the substantive inputs the
manuscript itself quotes from elsewhere, plus the two residuals recorded in
`PrincipalResponseSwitchActualPerCube`:

* `hlam0` -- strict positivity of `lambda_{3/8,2}(z+cu_n; a_{m-h})` on the good
  event;
* `hshell` -- the centered-shell size (see that module's docstring);
* `hellip` -- the ellipticity budget, quoted by the manuscript from
  `e.nablaw.in.L.eight`;
* `hindep` -- the independence replacement;
* `hbudget` -- the numerical smallness in which "increasing `M` in
  `e.cgamma.constraints` if necessary" is made quantitative for the remainder;
* the three integrability families.

`hswitch` is **gone**.

## The `3/2`

The switch factor carried through is the honest `1 + (3/2) Delta` rather than
the printed `1 + Delta`; see the module docstring of
`PrincipalResponseSwitchActualPerCube` for exactly where the printed factor
needs a constant margin that neither the manuscript nor this repository
supplies.

## Main results

* `annealedCubeBlockQuadratic_nonneg_actual`
* `descendantsAverage_integral_goodEventEnergy_le_annealedCube_family`
* `gridSwitchDiscount_eq_rpow_recurrenceGap`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## Nonnegativity of the annealed cube form -/

/-- **The annealed cube quadratic form is nonnegative.**  The proved Loewner
plateau of `ApproximateRecurrence.PrincipalResponseSwitchPlateau` puts the
infinite-volume `bfAhom_L = diag(shom_L, shom_L^{-1})` below the finite-cube
`bfAhom_L(cu_n)`, and the former is a positive diagonal.

Unconditional: no caller-supplied proposition enters. -/
theorem annealedCubeBlockQuadratic_nonneg_actual [NeZero d] (M : ABKModel d)
    (L n : ℤ) (V : BlockVec d) :
    0 ≤ blockVecDot V
      (blockMatVecMul
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n) V) := by
  have hle := blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit M L n V
  have h0 : (0 : ℝ) ≤ blockVecDot V
      (blockMatVecMul
        (Ch02.blockDiag ((Annealed.sigmaBar M L : ℝ) • (1 : Mat d))
          (((Annealed.sigmaBar M L : ℝ))⁻¹ • (1 : Mat d))) V) := by
    rw [blockVecDot_blockDiag_smul_one_vecDot]
    have h1 : (0 : ℝ) ≤ vecDot V.1 V.1 := vecNormSq_nonneg V.1
    have h2 : (0 : ℝ) ≤ vecDot V.2 V.2 := vecNormSq_nonneg V.2
    have h3 : (0 : ℝ) < (Annealed.sigmaBar M L : ℝ) := (Annealed.sigmaBar M L).2
    have h4 : (0 : ℝ) ≤ ((Annealed.sigmaBar M L : ℝ))⁻¹ := (inv_pos.2 h3).le
    positivity
  linarith

/-! ## The-generalized display -/

section Family

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

/-- **`e.lower.bound.principal.one.pre` with the manuscript's own per-cube event.**

ABK26's `cQ_z := cQ(n, m-h, z)` depends on the cube `z + cu_n`, so the good
event enters the display as a **family** `Ebad : TriadicCube d -> Set Omega`,
and no union over the grid is formed.  The switch hypothesis is taken almost
surely, which is the form in which it is available at the cutoff carrier.

At the field index `L` (the manuscript's `m - h`), the cube scale `n`, the
localization cube `Q` and the depth `j`:

```
  avsum_R E[ energy_R 1_{cQ_R} ]
    <= (1 + cgamma^6) avsum_R E[ W_R . bfAhom_L(cu_n) W_R ] + (1/2) cgamma^6 .
```

The nonnegativity of the annealed grid average is **not** assumed: it is
`annealedCubeBlockQuadratic_nonneg_actual`, hence the proved Loewner plateau.

: this statement holds only under the propositions supplied by its binders --
`hdelta0`, `hCs0`, `hswitch`, `hgoodInt`, `hcubeInt`, `hellipInt`, `hindep`,
`hellip`, `hdeltaGate`, `hbudget`, whose provenance is listed in the module
docstring.  It is a provider A, not a source-facing frozen declaration. -/
theorem descendantsAverage_integral_goodEventEnergy_le_annealedCube_family
    [NeZero d] (M : ABKModel d) (L n : ℤ) (Q : TriadicCube d) (j : ℕ)
    (energy cubeQuad ellipLoad : TriadicCube d → Omega → ℝ)
    (W : TriadicCube d → Omega → BlockVec d) (Ebad : TriadicCube d → Set Omega)
    {delta Cs Cell : ℝ} (hdelta0 : 0 ≤ delta) (hCs0 : 0 ≤ Cs)
    (hswitch : ∀ R ∈ descendantsAtDepth Q j, ∀ᵐ omega ∂mu,
      energy R omega * (Ebad R)ᶜ.indicator (fun _ => (1 : ℝ)) omega ≤
        (1 + delta) * cubeQuad R omega + Cs * delta * ellipLoad R omega)
    (hgoodInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega =>
        energy R omega * (Ebad R)ᶜ.indicator (fun _ => (1 : ℝ)) omega) mu)
    (hcubeInt : ∀ R ∈ descendantsAtDepth Q j, Integrable (cubeQuad R) mu)
    (hellipInt : ∀ R ∈ descendantsAtDepth Q j, Integrable (ellipLoad R) mu)
    (hindep : ∀ R ∈ descendantsAtDepth Q j,
      ∫ omega, cubeQuad R omega ∂mu =
        ∫ omega, blockVecDot (W R omega)
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
            (W R omega)) ∂mu)
    (hellip : descendantsAverage Q j
      (fun R => ∫ omega, ellipLoad R omega ∂mu) ≤ Cell)
    (hdeltaGate : delta ≤ M.gamma ^ (6 : ℕ))
    (hbudget : Cs * delta * Cell ≤ M.gamma ^ (6 : ℕ) / 2) :
    descendantsAverage Q j
        (fun R => ∫ omega,
          energy R omega * (Ebad R)ᶜ.indicator (fun _ => (1 : ℝ)) omega ∂mu) ≤
      (1 + M.gamma ^ (6 : ℕ)) *
          descendantsAverage Q j (fun R => ∫ omega, blockVecDot (W R omega)
            (blockMatVecMul
              (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
              (W R omega)) ∂mu) +
        M.gamma ^ (6 : ℕ) / 2 := by
  classical
  set A : TriadicCube d → ℝ := fun R => ∫ omega, blockVecDot (W R omega)
    (blockMatVecMul
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M L) n)
      (W R omega)) ∂mu with hA
  have hA0 : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ A R := by
    intro R _
    exact MeasureTheory.integral_nonneg fun omega =>
      annealedCubeBlockQuadratic_nonneg_actual M L n (W R omega)
  have hAavg0 : 0 ≤ descendantsAverage Q j A :=
    descendantsAverage_nonneg Q j A hA0
  have hstep : ∀ R ∈ descendantsAtDepth Q j,
      (∫ omega, energy R omega * (Ebad R)ᶜ.indicator (fun _ => (1 : ℝ)) omega ∂mu) ≤
        (1 + delta) * A R + Cs * delta * ∫ omega, ellipLoad R omega ∂mu := by
    intro R hR
    have hbound : Integrable (fun omega =>
        (1 + delta) * cubeQuad R omega + Cs * delta * ellipLoad R omega) mu :=
      ((hcubeInt R hR).const_mul (1 + delta)).add
        ((hellipInt R hR).const_mul (Cs * delta))
    have hmono := MeasureTheory.integral_mono_ae (hgoodInt R hR) hbound (hswitch R hR)
    rw [MeasureTheory.integral_add ((hcubeInt R hR).const_mul (1 + delta))
      ((hellipInt R hR).const_mul (Cs * delta)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hindep R hR] at hmono
    exact hmono
  have hgrid := descendantsAverage_le_descendantsAverage Q j hstep
  rw [descendantsAverage_add Q j (fun R => (1 + delta) * A R)
    (fun R => Cs * delta * ∫ omega, ellipLoad R omega ∂mu),
    descendantsAverage_mul_left Q j (1 + delta) A,
    descendantsAverage_mul_left Q j (Cs * delta)
      (fun R => ∫ omega, ellipLoad R omega ∂mu)] at hgrid
  have hfac : (1 + delta) * descendantsAverage Q j A ≤
      (1 + M.gamma ^ (6 : ℕ)) * descendantsAverage Q j A :=
    mul_le_mul_of_nonneg_right (by linarith) hAavg0
  have hrem : Cs * delta *
      descendantsAverage Q j (fun R => ∫ omega, ellipLoad R omega ∂mu) ≤
      M.gamma ^ (6 : ℕ) / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left hellip (mul_nonneg hCs0 hdelta0)) hbudget
  linarith

end Family

/-! ## The manuscript's own gap, and the `cgamma^6` gate on the display -/

/-- At the manuscript's own mesoscale `n = m - h - a ceil|log_3 gamma|`
(`e.recurrence.params`, label, at the free multiplier) the grid switch discount
is exactly `3^{-(m-h-n)/4} = 3^{-(recurrenceGap a gamma)/4}`.

: this statement holds only under the proposition supplied by its binder
`hscale`, the identification of the grid scale with the manuscript's mesoscale.
It is a provider A, not a source-facing frozen declaration. -/
theorem gridSwitchDiscount_eq_rpow_recurrenceGap (Q : TriadicCube d) (j : ℕ)
    (a : ℕ) (gamma : ℝ) (m h : ℤ)
    (hscale : (Q.scale : ℤ) - (j : ℤ) = recurrenceMesoScale a gamma m h) :
    gridSwitchDiscount Q j (m - h) =
      (3 : ℝ) ^ (-((recurrenceGap a gamma : ℝ) / 4)) := by
  have hle : (Q.scale : ℤ) - (j : ℤ) ≤ m - h := by
    rw [hscale, recurrenceMesoScale]
    have : (0 : ℤ) ≤ (recurrenceGap a gamma : ℤ) := Int.natCast_nonneg _
    omega
  have hgap : scaleGapPos ((Q.scale : ℤ) - (j : ℤ)) (m - h) =
      (recurrenceGap a gamma : ℝ) := by
    rw [scaleGapPos_of_le hle, hscale, recurrenceMesoScale]
    push_cast
    ring
  rw [gridSwitchDiscount, hgap]
  congr 1
  ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
