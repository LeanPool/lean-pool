/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseCentre
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseEllipBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.JResponseApplication

/-!
# PrincipalResponseLamWire

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
inventories below are informal descriptions only.

# The lower-ellipticity gauge on the good event, and the per-cube display with
# the shell size and the ellipticity budget both supplied

Source displays in ABK26:

* `l.approximate.recurrence.formula` (label), Step 3;
* the gauge-switch chain, whose Young remainder is absorbed;
* `e.lower.bound.principal.one.pre` (label; display);
* The ellipticity budget quoted from `e.nablaw.in.L.eight` (label; display);
* `e.good.local.events` (label; display), instantiated as `cQ_z:= cQ(n, m-h,
  z)`;
* `e.cg.ellip.lower` (label), the source of the constant `Ccg`;
* `e.recurrence.params` (label; display);
* `e.Pz.def` (label; display) and `e.def.w` (label).

## What this module supplies

Two things.

1. **The lower-ellipticity gauge is positive, with nothing assumed.**
   `lambdaSq_coefficientCutoffTriadicCoeffFamily_pos` is `0 <
   lambda_{3/8,2}(z+cu_n; a_{m-h})` at every sample, for every cube and every
   scale.  The good event is *not* used: CoarseGraining's `Ch02.lambdaSq_pos`
   is positive for every coefficient family at every admissible exponent pair,
   and `3/8 > 0`, `q = 2 >= 1` are admissible.  The binder that
   `ApproximateRecurrence.PrincipalResponseSwitchActualPerCube` and
   `ApproximateRecurrence.PrincipalResponseSwitchActualDisplay` call `hlam0`
   asks for exactly this proposition restricted to the samples of the good
   event, so it is supplied here in a strictly stronger unconditional form.

2. **The composed per-cube display.**  The final theorem of this module,
`exists_constant_principalEnergy_bound_of_centering`,
   is the display at the manuscript's own load `P_z` of `e.Pz.def`, in which
   none of `hswitch`, `hshell`, `hellip`, `hellipInt`, `hlam0` is a binder:
   * `hswitch` was already discharged inside
     `ApproximateRecurrence.PrincipalResponseSwitchActualDisplay`;
   * `hlam0` is discharged from item 1;
   * `hshell` is discharged from
     `ApproximateRecurrence.PrincipalResponseCentre.shell_hypothesis_of_centeringConst_ae`
     at `K = centeringConst d = d^3`;
   * `hellip` is discharged from
`exists_const_descendantsAverage_integral_switchEllipLoad_principalPz_le`;
   * `hellipInt` is discharged from the pointwise `X <= 1/2 + X^2/2` together
     with the two per-cube data conditions `hmeasR` and `hintR`, exactly as in
     `ApproximateRecurrence.PrincipalResponseEllipBudget`.

## The almost-sure quantifier, and why the chain is rebuilt here

`shell_hypothesis_of_centeringConst_ae` delivers the shell-size bound **almost
surely** on the cutoff sample law, because the transfer between the measurable
representative of `lambda_{1/8,2}` carried by `goodLocalEvent` and the frozen
`lambda_{3/8,2}` (`Provider.BadEvents.lambda_transfer_ae`) is almost sure and
no pointwise information about the representative exists.  The proved
`switchCubeEnergy_indicator_le_ae` and the proved display consumer take that
bound *pointwise* on the good event, so they cannot consume it.

The two intermediate steps of this module are therefore the same two proved
statements with the shell-size binder weakened from pointwise to almost sure
and with `hlam0` removed; both are `private`, both use only public proved
inputs (`blockVecDot_coarseBlockMatrix_le_switch_absorbed_cube`,
`responseSensitivityConst_mul_gradientW1Infinity_centeredFreshShell_le_ae`,
`centeredFreshShellUnitCube_shift`, `freshShellCubeAverage_skew`,
`three_halves_switch_excess_le_gamma_pow_six_of_model`,
`gridSwitchDiscount_eq_rpow_recurrenceGap` and the-generalized display
`descendantsAverage_integral_goodEventEnergy_le_annealedCube_family`), and
neither weakens the conclusion.  No proved file is edited.

## The manuscript's `S`, and what survives of the threshold

The manuscript's weight in the ellipticity load is `S = shom_{m-h}`, and that
is the weight used here: `shellSizeThreshold M Ccg (centeringConst d) (m-h) <=
shom_{m-h}` is the residual data condition that
`ApproximateRecurrence.PrincipalResponseSwitchActualShellSize` records.  It is
**not** carried raw.  Written out it is

```
  d^6 Ccg^{-1} shom_{m-h-1} / (2 C_sens^2)  <=  shom_{m-h} ,
```

and `shellSizeThreshold_centeringConst_le_sigmaBar` reduces it, using the
proved one-scale comparison `shom_{j} <= 4 shom_{i}` for `j <= i <= m0`
(`Provider.Multiscale.sigmaBar_le_four_mul_sigmaBar`, which reads the frozen
induction state `Algsuperdiff.Frozen.Section3.inductionState` already carried
by the consumer) at `j = m-h-1`, `i = m-h`, to the single scale-free inequality

```
  2 d^6  <=  Ccg . C_sens^2 .
```

That inequality is the one surviving data condition of the composition.  It
involves no sample, no scale and no corrector: it is a numerical lower bound on
the constant `C_{e.cg.ellip.lower}` in terms of the dimension and the joint
sensitivity constant `C_sens = sensitivityConstMax d` of `l.J.sensitivity`.  It
is a statement about the data of the recurrence of the same kind as
`e.cg.ellip.lower` itself, it is a hypothesis and never a derived fact, and it
is not a step of the manuscript's proof.  Nothing else about `Ccg` is assumed:
`0 < Ccg` is *derived* from it, because `d >= 1` already makes the left side at
least `2` while `C_sens^2 > 0`.

## The complete census of the final theorem's binders

Parameter gates and typing data: `hd` (`2 <= d`); `M.gamma <= gamma0`; the
frozen induction state; `0 < hgap`, `m - hgap <= m0`, `hgap <= 6 cstar
cgamma^{-1}` (/7183), `10^10 cgamma^{-1} <= K - m` (`e.recurrence.params`); the
two direction bounds `|e|, |e'| <= 1`; `recurrenceGapMultiplierFloor <= a` and
the mesoscale identification; `m - hgap <= highScale`; the free integers `n`,
`highScale`; the free reals `Ccg`; the two corrector families `wD`, `wN`
together with `hwD`, `hwN`, which say that they solve the two problems of
`e.def.w`; the free family `W`.

Data conditions: `hccg` (the threshold residue described above); `hmeasR` and
`hintR` (per-cube measurability of the load and integrability of its square,
the two data conditions of the budget); `hgoodInt` and `hcubeInt` (the two
remaining integrability families).

Residuals of the manuscript's own text: `hindep`, the independence replacement;
`hbudget`, the numerical smallness in which "increasing `M` in
`e.cgamma.constraints` if necessary" is made quantitative.

**Deferred obligations, named.**  The earlier sentence here -- "No binder of
the final theorem is a step of the manuscript's proof" -- was false as written
and is withdrawn.  The exact position is:

* `hindep` is the *conclusion* of the independence sentence, not a premise of
  it: it asserts the equality, cube by cube, of the expectation of the
  gauge-conjugated coarse quadratic form with the annealed quadratic form at a
  free family `W`.  It is a deferred proof obligation of this module, it is
  carried as a caller-supplied hypothesis, and it is discharged nowhere in this
  module or in any module of its import cone.
* `hbudget` is a numerical step of the manuscript's own argument ("increasing
  `M` in `e.cgamma.constraints` if necessary") rather than a source premise.
  It is a binder here only; it is discharged one module downstream, in
  `ApproximateRecurrence.PrincipalResponseBudgetWire`, by shrinking this
  theorem's own existential threshold `gamma0`.
* the four measurability and integrability data conditions `hmeasR`, `hintR`,
  `hgoodInt`, `hcubeInt` are conditional A obligations of this provider helper.
  They are not premises of the pinned source statement and are not discharged
  here.

Every other binder is parameter data, typing data, a standing gate of
`e.recurrence.params` //7183, the numerical gate `2 d^6 <= Ccg C_sens^2`, a
direction bound, or the `e.def.w` solution property of the two corrector
families.

## The `3/2`

The switch factor carried through is the honest `1 + (3/2) Delta` rather than
the printed `1 + Delta`, declared by
`ApproximateRecurrence.PrincipalResponseSwitchActualPerCube`; it enters only
through `hbudget`, unchanged.

## Main results

* `lambdaSq_coefficientCutoffTriadicCoeffFamily_pos`
* `shellSizeThreshold_centeringConst_le_sigmaBar`
*
`exists_constant_principalEnergy_bound_of_centering`

## References

* ABK26, (Step 3 of `l.approximate.recurrence.formula`, label);
  `e.lower.bound.principal.one.pre` (label; display); quoting
  `e.nablaw.in.L.eight` (label); `e.good.local.events` (label; display);
  `e.cg.ellip.lower` (label); `e.recurrence.params` (label; display);
  `e.Pz.def` (label); `e.def.w` (label).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The lower-ellipticity gauge is positive, unconditionally -/

/-- **`hlam0`, in a strictly stronger unconditional form.**

The frozen lower multiscale ellipticity `lambda_{3/8,2}(z+cu_n; a_r)` of the
cutoff coefficient family is strictly positive at every sample, for every cube
and every cutoff scale.

Unconditional: no caller-supplied proposition enters.  The binder `hlam0` of
`ApproximateRecurrence.PrincipalResponseSwitchActualPerCube` is the restriction
of this statement to the samples of the good event, so it is supplied by
`fun _ _ omega _ => lambdaSq_coefficientCutoffTriadicCoeffFamily_pos M R r omega`. -/
theorem lambdaSq_coefficientCutoffTriadicCoeffFamily_pos [NeZero d]
    (M : ABKModel d) (R : TriadicCube d) (r : ℤ) (omega : CutoffSample d) :
    0 < Ch02.lambdaSq R (3 / 8) (.finite 2)
      (coefficientCutoffTriadicCoeffFamily M r omega) :=
  Ch02.lambdaSq_pos R _ (by norm_num) (by norm_num)

/-! ## The per-cube switch with the shell size taken almost surely -/

/-- The closing line, cube by cube and almost surely, with the shell-size input
weakened to the almost-sure form in which
`ApproximateRecurrence.PrincipalResponseCentre` supplies it, and with `hlam0`
discharged from `lambdaSq_coefficientCutoffTriadicCoeffFamily_pos`.

This is the proved `switchCubeEnergy_indicator_le_ae` with one binder removed
and one binder weakened; the conclusion is unchanged. -/
theorem switchCubeEnergy_indicator_le_ae_of_shell_ae (dimension : 2 ≤ d)
    [NeZero d] (M : ABKModel d) (Ccg : ℝ) (Q : TriadicCube d) (j : ℕ)
    {lowScale highScale : ℤ} (hle : lowScale ≤ highScale)
    (P : TriadicCube d → CutoffSample d → BlockVec d) {S : ℝ} (hS0 : 0 < S)
    (hshell : ∀ R ∈ descendantsAtDepth Q j,
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        omega ∈ goodLocalEvent M Ccg R lowScale →
          (centeredFreshShellUnitCube M R hle omega).w1Infinity ^ 2 ≤
            gridSwitchDiscount Q j lowScale ^ 2 * S *
              Ch02.lambdaSq R (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M lowScale omega)) :
    ∀ R ∈ descendantsAtDepth Q j,
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        switchCubeEnergy M highScale R (P R omega) omega *
            (principalBadEvent M Ccg R lowScale)ᶜ.indicator
              (fun _ => (1 : ℝ)) omega ≤
          (1 + (3 / 2 : ℝ) * gridSwitchDiscount Q j lowScale) *
              switchCubeQuad M lowScale highScale R (P R omega) omega +
            principalSwitchLoadConst d *
                ((3 / 2 : ℝ) * gridSwitchDiscount Q j lowScale) *
              switchEllipLoad S (P R omega) := by
  classical
  intro R hR
  filter_upwards
    [responseSensitivityConst_mul_gradientW1Infinity_centeredFreshShell_le_ae
      M Ccg R hle (highScale := highScale), hshell R hR] with omega hgate hsh
  have hquad0 : (0 : ℝ) ≤ switchCubeQuad M lowScale highScale R (P R omega) omega :=
    switchCubeQuad_nonneg M lowScale highScale R (P R omega) omega
  have hload0 : (0 : ℝ) ≤ switchEllipLoad S (P R omega) :=
    switchEllipLoad_nonneg hS0 (P R omega)
  have hCload : 0 < principalSwitchLoadConst d := principalSwitchLoadConst_pos dimension
  have hD0 : 0 < gridSwitchDiscount Q j lowScale := gridSwitchDiscount_pos Q j lowScale
  by_cases hmem : omega ∈ goodLocalEvent M Ccg R lowScale
  · have hmem' : omega ∈ (principalBadEvent M Ccg R lowScale)ᶜ := by
      rwa [compl_principalBadEvent]
    rw [Set.indicator_of_mem hmem', mul_one]
    have hgrad : responseSensitivityConst d *
        (centeredFreshShellUnitCube M R hle omega).gradientW1Infinity ≤
        gridSwitchDiscount Q j lowScale *
          Ch02.lambdaSq R (3 / 8) (.finite 2)
            (coefficientCutoffTriadicCoeffFamily M lowScale omega) := by
      have h := hgate hmem
      rwa [gridSwitchDiscount_eq_of_mem Q j lowScale hR] at h
    exact blockVecDot_coarseBlockMatrix_le_switch_absorbed_cube dimension M R
      lowScale highScale omega (centeredFreshShellUnitCube M R hle omega)
      (freshShellCubeAverage_skew R omega.1 lowScale highScale)
      (centeredFreshShellUnitCube_shift M R hle omega)
      hD0 (gridSwitchDiscount_le_one Q j lowScale) hS0
      (lambdaSq_coefficientCutoffTriadicCoeffFamily_pos M R lowScale omega) hgrad
      (hsh hmem) (P R omega)
  · have hmem' : omega ∉ (principalBadEvent M Ccg R lowScale)ᶜ := by
      rwa [compl_principalBadEvent]
    rw [Set.indicator_of_notMem hmem', mul_zero]
    have h1 : (0 : ℝ) ≤ (1 + (3 / 2 : ℝ) * gridSwitchDiscount Q j lowScale) *
        switchCubeQuad M lowScale highScale R (P R omega) omega :=
      mul_nonneg (by linarith) hquad0
    have h2 : (0 : ℝ) ≤ principalSwitchLoadConst d *
        ((3 / 2 : ℝ) * gridSwitchDiscount Q j lowScale) *
          switchEllipLoad S (P R omega) :=
      mul_nonneg (mul_nonneg hCload.le (by linarith)) hload0
    linarith

/-! ## The display consumer with the shell size taken almost surely -/

/-- The display at the actual cutoff carrier, with `hswitch` and `hlam0` gone and
the shell size taken in the almost-sure form.

This is the proved
`descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube` with one
binder removed and one binder weakened; the conclusion is unchanged. -/
private theorem descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_shell_ae
    (dimension : 2 ≤ d) [NeZero d] (M : ABKModel d) (Ccg : ℝ)
    (Q : TriadicCube d) (j : ℕ) (a : ℕ) (m hgap : ℤ) (n : ℤ)
    (ha : recurrenceGapMultiplierFloor ≤ a)
    (hscale : (Q.scale : ℤ) - (j : ℤ) = recurrenceMesoScale a M.gamma m hgap)
    {highScale : ℤ} (hle : m - hgap ≤ highScale)
    (P : TriadicCube d → CutoffSample d → BlockVec d) {S Cell : ℝ} (hS0 : 0 < S)
    (hshell : ∀ R ∈ descendantsAtDepth Q j,
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        omega ∈ goodLocalEvent M Ccg R (m - hgap) →
          (centeredFreshShellUnitCube M R hle omega).w1Infinity ^ 2 ≤
            gridSwitchDiscount Q j (m - hgap) ^ 2 * S *
              Ch02.lambdaSq R (3 / 8) (.finite 2)
                (coefficientCutoffTriadicCoeffFamily M (m - hgap) omega))
    (hgoodInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega : CutoffSample d =>
        switchCubeEnergy M highScale R (P R omega) omega *
          (principalBadEvent M Ccg R (m - hgap))ᶜ.indicator (fun _ => (1 : ℝ)) omega)
        (Cutoff.cutoffSampleLaw M).toMeasure)
    (hcubeInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega : CutoffSample d =>
        switchCubeQuad M (m - hgap) highScale R (P R omega) omega)
        (Cutoff.cutoffSampleLaw M).toMeasure)
    (hellipInt : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega : CutoffSample d => switchEllipLoad S (P R omega))
        (Cutoff.cutoffSampleLaw M).toMeasure)
    (W : TriadicCube d → CutoffSample d → BlockVec d)
    (hindep : ∀ R ∈ descendantsAtDepth Q j,
      (∫ omega : CutoffSample d,
          switchCubeQuad M (m - hgap) highScale R (P R omega) omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫ omega : CutoffSample d, blockVecDot (W R omega)
          (blockMatVecMul
            (Ch04.annealedBlockMatrixAtScale
              (Cutoff.coefficientCutoffLaw M (m - hgap)) n) (W R omega))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    (hellip : descendantsAverage Q j
      (fun R => ∫ omega : CutoffSample d, switchEllipLoad S (P R omega)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ Cell)
    (hbudget : principalSwitchLoadConst d *
      ((3 / 2 : ℝ) * gridSwitchDiscount Q j (m - hgap)) * Cell ≤
        M.gamma ^ (6 : ℕ) / 2) :
    descendantsAverage Q j
        (fun R => ∫ omega : CutoffSample d,
          switchCubeEnergy M highScale R (P R omega) omega *
            (principalBadEvent M Ccg R (m - hgap))ᶜ.indicator
              (fun _ => (1 : ℝ)) omega
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (1 + M.gamma ^ (6 : ℕ)) *
          descendantsAverage Q j (fun R => ∫ omega : CutoffSample d,
            blockVecDot (W R omega)
              (blockMatVecMul
                (Ch04.annealedBlockMatrixAtScale
                  (Cutoff.coefficientCutoffLaw M (m - hgap)) n) (W R omega))
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
        M.gamma ^ (6 : ℕ) / 2 := by
  have hD0 : 0 < gridSwitchDiscount Q j (m - hgap) :=
    gridSwitchDiscount_pos Q j (m - hgap)
  have hdeltaGate : (3 / 2 : ℝ) * gridSwitchDiscount Q j (m - hgap) ≤
      M.gamma ^ (6 : ℕ) := by
    rw [gridSwitchDiscount_eq_rpow_recurrenceGap Q j a M.gamma m hgap hscale]
    exact three_halves_switch_excess_le_gamma_pow_six_of_model M ha
  exact descendantsAverage_integral_goodEventEnergy_le_annealedCube_family
    M (m - hgap) n Q j
    (fun R omega => switchCubeEnergy M highScale R (P R omega) omega)
    (fun R omega => switchCubeQuad M (m - hgap) highScale R (P R omega) omega)
    (fun R omega => switchEllipLoad S (P R omega)) W
    (fun R => principalBadEvent M Ccg R (m - hgap))
    (by positivity) (principalSwitchLoadConst_pos dimension).le
    (switchCubeEnergy_indicator_le_ae_of_shell_ae dimension M Ccg Q j hle P hS0
      hshell)
    hgoodInt hcubeInt hellipInt hindep hellip hdeltaGate hbudget

/-! ## The shell-size threshold at the manuscript's own `S = shom_{m-h}` -/

/-- The scale-free gate on `Ccg` forces `Ccg` to be positive, because `d >= 1`
makes the left side at least `2`. -/
private theorem ccg_pos_of_gate [NeZero d] {Ccg : ℝ}
    (hccg : 2 * (d : ℝ) ^ 6 ≤ Ccg * sensitivityConstMax d ^ 2) : 0 < Ccg := by
  have hCsq : (0 : ℝ) < sensitivityConstMax d ^ 2 :=
    pow_pos (sensitivityConstMax_pos d) 2
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hd6 : (1 : ℝ) ≤ (d : ℝ) ^ 6 := one_le_pow₀ hd1
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg (neg_nonneg.2 hcon) hCsq.le]

/-- **The threshold comparison of
`ApproximateRecurrence.PrincipalResponseSwitchActualShellSize`, at the
manuscript's own `S = shom_{m-h}` and at `K = centeringConst d`.**

Written out, `shellSizeThreshold M Ccg (centeringConst d) lowScale <=
shom_{lowScale}` is

```
  d^6 Ccg^{-1} shom_{lowScale-1} / (2 C_sens^2)  <=  shom_{lowScale} ,
```

and the proved one-scale comparison `shom_j <= 4 shom_i` for `j <= i <= m0`
reduces it to the scale-free `2 d^6 <= Ccg C_sens^2`.

: this statement holds only under the propositions supplied by its binders --
`hstate`, the frozen induction state; `hlow`, the reading-scale gate `lowScale
<= m0`; and `hccg`, the numerical lower bound on the constant of
`e.cg.ellip.lower` (label).  It is a provider A, not a source-facing frozen
declaration. -/
theorem shellSizeThreshold_centeringConst_le_sigmaBar [NeZero d] (M : ABKModel d)
    {m0 : ℤ} {Eind : {E : ℝ // 1 ≤ E}}
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M m0 Eind)
    {lowScale : ℤ} (hlow : lowScale ≤ m0) {Ccg : ℝ}
    (hccg : 2 * (d : ℝ) ^ 6 ≤ Ccg * sensitivityConstMax d ^ 2) :
    shellSizeThreshold M Ccg (centeringConst d) lowScale ≤
      (Annealed.sigmaBar M lowScale : ℝ) := by
  have hCsq : (0 : ℝ) < sensitivityConstMax d ^ 2 :=
    pow_pos (sensitivityConstMax_pos d) 2
  have hCcg0 : 0 < Ccg := ccg_pos_of_gate hccg
  have hinvpos : (0 : ℝ) ≤ Ccg⁻¹ := (inv_pos.2 hCcg0).le
  have hsigpos : (0 : ℝ) < (Annealed.sigmaBar M lowScale : ℝ) :=
    (Annealed.sigmaBar M lowScale).2
  have hsig : (Annealed.sigmaBar M (lowScale - 1) : ℝ) ≤
      4 * (Annealed.sigmaBar M lowScale : ℝ) :=
    Provider.Multiscale.sigmaBar_le_four_mul_sigmaBar M hstate (by omega) hlow
  have hstep : 2 * (d : ℝ) ^ 6 * Ccg⁻¹ ≤ sensitivityConstMax d ^ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hCcg0]
    linarith
  rw [shellSizeThreshold, centeringConst,
    div_le_iff₀ (by linarith : (0 : ℝ) < 2 * sensitivityConstMax d ^ 2)]
  calc ((d : ℝ) ^ 3) ^ 2 * Ccg⁻¹ * (Annealed.sigmaBar M (lowScale - 1) : ℝ)
      ≤ ((d : ℝ) ^ 3) ^ 2 * Ccg⁻¹ * (4 * (Annealed.sigmaBar M lowScale : ℝ)) :=
        mul_le_mul_of_nonneg_left hsig (mul_nonneg (by positivity) hinvpos)
    _ = 2 * (2 * (d : ℝ) ^ 6 * Ccg⁻¹) * (Annealed.sigmaBar M lowScale : ℝ) := by
        ring
    _ ≤ 2 * sensitivityConstMax d ^ 2 * (Annealed.sigmaBar M lowScale : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hsigpos.le
    _ = (Annealed.sigmaBar M lowScale : ℝ) * (2 * sensitivityConstMax d ^ 2) := by
        ring

/-! ## The composed consumer -/

/-- **The good-event energy display at the actual cutoff carrier, with the switch,
the lower-ellipticity gauge, the centered-shell size and the ellipticity budget
all supplied.**

Every object is the manuscript's own: the grid is the triadic descendants of
`cu_K` at a free depth `j`, the sample carrier is `Cutoff.CutoffSample d` under
`(Cutoff.cutoffSampleLaw M).toMeasure`, the event is the per-cube `cQ_z = cQ(n,
m-h, z)` through `principalBadEvent M Ccg. (m-h)`, the load is `P_z` of
`e.Pz.def` built from a sample family of solutions of `e.def.w`, and the weight
is `S = shom_{m-h}`.

None of `hswitch`, `hlam0`, `hshell`, `hellip`, `hellipInt` is a binder; the
module docstring names the producer of each and gives the complete census of the
binders that remain.

* `hd` -- the paper-wide `2 <= d`;
* `M.gamma <= gamma0`, and the induction state
  `Algsuperdiff.Frozen.Section3.inductionState M m0 Eind`;
* `0 < hgap`, `m - hgap <= m0`, `hgap <= 6 cstar cgamma^{-1}` (/7183) and
  `10^10 cgamma^{-1} <= K - m` (`e.recurrence.params`);
* the two direction bounds `vecNorm e <= 1`, `vecNorm e' <= 1`;
* `2 d^6 <= Ccg C_sens^2` -- the one surviving data condition, a numerical
  lower bound on the constant of `e.cg.ellip.lower` (label) described in the
  module docstring; `0 < Ccg` is derived from it;
* `hle : m - hgap <= highScale`, the scale ordering of the switch;
* the two solution families `hwD`, `hwN` of `e.def.w`;
* `hmeasR`, `hintR` -- the two per-cube data conditions of the budget;
* `hgoodInt`, `hcubeInt` -- the two remaining integrability families;
* `hindep` -- the independence replacement;
* `hbudget` -- the numerical smallness in which "increasing `M` in
  `e.cgamma.constraints` if necessary" is made quantitative, at the produced
  constant `Cell`.

It is a provider A, not a source-facing frozen declaration; it does not derive
`e.lower.bound.principal.one.pre` or any sub-step of
`l.approximate.recurrence.formula`.

Reaches exactly the one frozen theorem
`Algsuperdiff.Frozen.External.calderon_zygmund`, a **proved** external. -/
theorem exists_constant_principalEnergy_bound_of_centering
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cell : ℝ, 0 < Cell ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
            ∀ (m K : ℤ) (hgap : ℕ), 0 < hgap → m - (hgap : ℤ) ≤ m0 →
              (hgap : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
              (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
              ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
                Book.Ch02.vecNorm e' ≤ 1 →
                ∀ (j a : ℕ), recurrenceGapMultiplierFloor ≤ a →
                  ((originCube d K).scale : ℤ) - (j : ℤ) =
                    recurrenceMesoScale a M.gamma m (hgap : ℤ) →
                  ∀ Ccg : ℝ,
                    2 * (d : ℝ) ^ 6 ≤ Ccg * sensitivityConstMax d ^ 2 →
                  ∀ (n highScale : ℤ), m - (hgap : ℤ) ≤ highScale →
                  ∀ (wD : Cutoff.CutoffSample d →
                      H10Function (openCubeSet (originCube d K)))
                    (wN : Cutoff.CutoffSample d →
                      H1MeanZeroFunction (openCubeSet (originCube d K))),
                    (∀ z : Cutoff.CutoffSample d,
                      IsZeroTraceDirichletRhsWeakSolution
                        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                        (openCubeSet (originCube d K)) (wD z)
                        (fun x => -Corrector.streamForcing
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ z.val
                          (m - (hgap : ℤ)) m e x)) →
                    (∀ z : Cutoff.CutoffSample d,
                      IsMeanZeroNeumannRhsWeakSolution
                        (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                        (openCubeSet (originCube d K)) (wN z)
                        (fun x => -Corrector.streamForcing
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ z.val
                          (m - (hgap : ℤ)) m e' x)) →
                    (∀ R ∈ descendantsAtDepth (originCube d K) j,
                      Measurable (fun z : Cutoff.CutoffSample d =>
                        switchEllipLoad
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
                          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                            z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)))) →
                    (∀ R ∈ descendantsAtDepth (originCube d K) j,
                      Integrable (fun z : Cutoff.CutoffSample d =>
                        switchEllipLoad
                            ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
                            (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                              z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) ^
                          (2 : ℕ))
                        (Cutoff.cutoffSampleLaw M).toMeasure) →
                    (∀ R ∈ descendantsAtDepth (originCube d K) j,
                      Integrable (fun omega : Cutoff.CutoffSample d =>
                        switchCubeEnergy M highScale R
                            (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                              omega.val (m - (hgap : ℤ)) m e e' R (wD omega)
                              (wN omega)) omega *
                          (principalBadEvent M Ccg R (m - (hgap : ℤ)))ᶜ.indicator
                            (fun _ => (1 : ℝ)) omega)
                        (Cutoff.cutoffSampleLaw M).toMeasure) →
                    (∀ R ∈ descendantsAtDepth (originCube d K) j,
                      Integrable (fun omega : Cutoff.CutoffSample d =>
                        switchCubeQuad M (m - (hgap : ℤ)) highScale R
                          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                            omega.val (m - (hgap : ℤ)) m e e' R (wD omega)
                            (wN omega)) omega)
                        (Cutoff.cutoffSampleLaw M).toMeasure) →
                    ∀ W : TriadicCube d → Cutoff.CutoffSample d → BlockVec d,
                      (∀ R ∈ descendantsAtDepth (originCube d K) j,
                        (∫ omega : Cutoff.CutoffSample d,
                            switchCubeQuad M (m - (hgap : ℤ)) highScale R
                              (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                                omega.val (m - (hgap : ℤ)) m e e' R (wD omega)
                                (wN omega)) omega
                            ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
                          ∫ omega : Cutoff.CutoffSample d, blockVecDot (W R omega)
                            (blockMatVecMul
                              (Book.Ch04.annealedBlockMatrixAtScale
                                (Cutoff.coefficientCutoffLaw M (m - (hgap : ℤ))) n)
                              (W R omega))
                            ∂(Cutoff.cutoffSampleLaw M).toMeasure) →
                      principalSwitchLoadConst d *
                          ((3 / 2 : ℝ) *
                            gridSwitchDiscount (originCube d K) j
                              (m - (hgap : ℤ))) * Cell ≤
                        M.gamma ^ (6 : ℕ) / 2 →
                      descendantsAverage (originCube d K) j
                          (fun R => ∫ omega : Cutoff.CutoffSample d,
                            switchCubeEnergy M highScale R
                                (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                                  omega.val (m - (hgap : ℤ)) m e e' R (wD omega)
                                  (wN omega)) omega *
                              (principalBadEvent M Ccg R
                                (m - (hgap : ℤ)))ᶜ.indicator (fun _ => (1 : ℝ)) omega
                            ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                        (1 + M.gamma ^ (6 : ℕ)) *
                            descendantsAverage (originCube d K) j
                              (fun R => ∫ omega : Cutoff.CutoffSample d,
                                blockVecDot (W R omega)
                                  (blockMatVecMul
                                    (Book.Ch04.annealedBlockMatrixAtScale
                                      (Cutoff.coefficientCutoffLaw M
                                        (m - (hgap : ℤ))) n) (W R omega))
                                ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
                          M.gamma ^ (6 : ℕ) / 2 := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cell, hCellpos, gamma0, hg0pos, hg0quarter, hprod⟩ :=
    exists_const_descendantsAverage_integral_switchEllipLoad_principalPz_le d hd
  refine ⟨Cell, hCellpos, gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' j a ha hscale
    Ccg hccg n highScale hle wD wN hwD hwN hmeasR hintR hgoodInt hcubeInt W hindep
    hbudget
  have hellipInt : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Integrable (fun z : Cutoff.CutoffSample d =>
        switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
            (m - (hgap : ℤ)) m e e' R (wD z) (wN z)))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    intro R hR
    refine ((integrable_const ((1 : ℝ) / 2)).add
      ((hintR R hR).const_mul ((1 : ℝ) / 2))).mono'
      (hmeasR R hR).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 : (0 : ℝ) ≤ switchEllipLoad
        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
          (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) :=
      switchEllipLoad_nonneg (Annealed.sigmaBar M (m - (hgap : ℤ))).2 _
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg h0]
    nlinarith [sq_nonneg (switchEllipLoad
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
      (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
        (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) - 1)]
  have hshell := shell_hypothesis_of_centeringConst_ae M (ccg_pos_of_gate hccg)
    (originCube d K) j hle
    (shellSizeThreshold_centeringConst_le_sigmaBar M hstate hm hccg)
  exact descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_shell_ae
    hd M Ccg (originCube d K) j a m (hgap : ℤ) n ha hscale hle
    (fun R z => principalPz (Annealed.sigmaBar M (m - (hgap : ℤ))) z.val
      (m - (hgap : ℤ)) m e e' R (wD z) (wN z))
    (Annealed.sigmaBar M (m - (hgap : ℤ))).2 hshell hgoodInt hcubeInt hellipInt W
    hindep
    (hprod M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' j wD wN hwD
      hwN hmeasR hintR)
    hbudget

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
