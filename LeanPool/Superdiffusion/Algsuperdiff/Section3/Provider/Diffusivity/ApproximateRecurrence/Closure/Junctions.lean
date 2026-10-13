/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumCarrierLaw
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.StepSixClosure
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseComposeAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLoadMeas
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualPerCube

/-!
# Junctions

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two junctions of the closure node, and the assembly skeletons

The two-sided closure of `l.approximate.recurrence.formula` needs three
things beyond the arithmetic of `Closure.StepSixClosure`:

1. the **principal comparison**, proved:
   `PrincipalResponseTerminal.exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`;
2. the **gauge endpoints** of Steps 4 and 5 (`e.lower.bound.pre1`, and
   `e.lower.bound.pre2`), whose fresh-shell energy display is produced by the
   lane `shellsum-limit` (Corrector territory);
3. the **basic split with its localization remainder**
   (`e.lower.bound.basic.split`, and `e.lower.bound.localization.terms`)
   together with the passage `P . bfAhom_m P = lim_K E[P . bfA_m(cu_K) P]`,
   whose `cgamma^10` endpoint is produced by the lane `gamma10-final`.

Items 2 and 3 are **in flight**.  This module therefore does two things:

* it proves the assembly skeletons: given those propositions, the printed
  displays follow.  When the producers land, each premise is discharged by a
  single `exact`.

The proved terminal itself is deliberately **not imported**: this module uses
only the carriers it is stated about (`switchCubeEnergy`, `principalPz`,
`gaugedPrincipalLoadShell`, `principalResponseSwitchBudget`), so importing the
terminal would add elaboration weight without adding content.  The consumer
that discharges `PrincipalSwitchEndpoint` imports both.

**These are the only caller-supplied mathematical propositions in this lane.**
They are marked `private` where they are assembly skeletons; the named endpoint
`Prop`s themselves are public only so that a producer can state that it proves
one.  Nothing here realizes a source node, and nothing here is a public node
claim.

## The gauge junctions carry the FINITE-`K` corrector energies

An earlier revision of this module stated the two gauge junctions with the
manuscript's **limit** drift constant `shom_n^{-2} cstar (log 3) sum_{k in Ioc
n (n+h)} 3^{2 cgamma k}` at a single fixed localization cube `cu_K`.  That form
is *undischargeable*, and this is the failure recorded: after the gauge
collapse (`ApproximateRecurrence.ClosureGaugeCollapse`), Step 4's right-hand
side is `1 + E || grad w_N^{(K)} ||^2_{L2(cu_K)}` whose energy **decreases** to
the drift, so at finite `K` it is `>=` the drift and never `<=` it; Step 5's is
`1 - E || grad w_D^{(K)} ||^2_{L2(cu_K)} + ...` whose energy **increases** to
the drift, so at finite `K` it is `<=` the drift and again on the wrong side.
The manuscript itself only ever asserts the two displays under a `limsup_K`,
and its own inner step is the finite-`K` Jensen inequality.

That prescription is carried out here:

* `Step4GaugeEndpoint` and `Step5GaugeEndpoint` are restated at the **finite-`K`
  corrector energies** `neumannCubeEnergy` and `dirichletCubeEnergy`, i.e. at
  exactly the manuscript's inner display;
* the drift comparison moves into the assembly skeletons as a **limit passage**:
  the two `shom`-ratio displays `RecurrenceUpperDisplay`, `RecurrenceLowerDisplay`
  are `K`-independent, so the skeletons consume the whole *family* of finite-`K`
  junctions together with the convergence of the corrector energy to the drift,
  and pass `K -> infinity` with vanishing slack.

The convergence input is proved, as
`Provider.Corrector.ShellSumEnergyDisplay.tendsto_integral_cutoffSample_cubeAverage_display`
at gauge `c = shom_n^{-1}` and unit direction: its limit is `shellDrift M n h`
by `shellDrift_eq_shellSum`, its Neumann half is the Step-4 input and its
Dirichlet half the Step-5 input.  The sharp sandwich halves behind it are
`Provider.Corrector.NeumannUpperBound` and
`Provider.Corrector.DirichletLowerBound`.

## The corrector families are indexed by the increment path

The proved terminal's load `gaugedPrincipalLoadShell` indexes the corrector
families by the *shell sequence* `ShellSeq d`, while `e.def.w` and the energy
display index them by the *increment path* `C(Vec d, Mat d)` --- which is the
honest reading, the forcing depending on the sample only through `k_{n+h} -
k_n`.  The junctions below take the producers' indexing and compose with
`Provider.Corrector.shellSumValuePath`; the composition is named
`alongIncrementPath` so that the bridge is explicit at every use.

## The carriers

Instantiating the terminal at `m := n + h`, `hgap := h` therefore leaves one
integer rewrite, `n + h - h = n`, before the `exact`; that rewrite is the only
difference between the terminal's conclusion and `PrincipalSwitchEndpoint`.

## Constants

`closureConstant` is the absolute constant that folds the switch cross term `(1
+ shellIncrementCap) * delta` and the two additive remainders `cgamma^6`,
`cgamma^10` under the printed budget `C E^2 |log cgamma|^2 cgamma`.

## References

* ABK26, `l.approximate.recurrence.formula`, Steps 4--6.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open Algsuperdiff.Section3.Observable
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The two carriers of the terminal, re-indexed by `(n, h)` -/

/-- The left-hand side of the proved principal-response terminal, at the recurrence
pair `(n, n+h)`: the depth-`j` descendant average of the annealed localized
principal energy. -/
def principalEnergyAverage (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))) : ℝ :=
  descendantsAverage (originCube d Kc) j
    (fun R => ∫ omega : CutoffSample d,
      switchCubeEnergy M (n + (h : ℤ)) R
        (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
          (wD omega.val) (wN omega.val)) omega
      ∂(cutoffSampleLaw M).toMeasure)

/-- The right-hand side of the proved principal-response terminal, at the
recurrence pair `(n, n+h)`: the depth-`j` descendant average of the annealed
gauged load quadratic against `bfAhom_n`.  This is the left-hand side of both
`e.lower.bound.pre1` and `e.lower.bound.pre2`. -/
def gaugeEnergyAverage (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))) : ℝ :=
  descendantsAverage (originCube d Kc) j
    (fun R => ∫ omega : CutoffSample d,
      blockVecDot
        (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e e'
          wD wN omega.val)
        (blockMatVecMul
          (Ch02.blockDiag ((Annealed.sigmaBar M n : ℝ) • (1 : Mat d))
            (((Annealed.sigmaBar M n : ℝ))⁻¹ • (1 : Mat d)))
          (gaugedPrincipalLoadShell (Annealed.sigmaBar M n) R n (n + (h : ℤ)) e e'
            wD wN omega.val))
      ∂(cutoffSampleLaw M).toMeasure)

/-! ## The shell sum, in the two index conventions -/

/-- The manuscript writes the shell sum as `sum_{k = m-h+1}^m`; the in-flight
fresh-shell display carries it as a sum over `Finset.Ioc (m-h) m`.  At the
recurrence pair the two are the same finite set. -/
theorem sum_Ioc_eq_sum_Icc (gamma : ℝ) (n : ℤ) (h : ℕ) :
    ∑ k ∈ Finset.Ioc n (n + (h : ℤ)), (3 : ℝ) ^ (2 * gamma * (k : ℝ)) =
      ∑ k ∈ Finset.Icc (n + 1) (n + (h : ℤ)), (3 : ℝ) ^ (2 * gamma * (k : ℝ)) := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- The fresh-shell display's right-hand constant is `shellDrift`. -/
theorem shellDrift_eq_shellSum (M : ABKModel d) (n : ℤ) (h : ℕ) :
    shellDrift M n h =
      (((Annealed.sigmaBar M n : ℝ)) ^ 2)⁻¹ *
        (Disorder.cstar M * Real.log 3 *
          ∑ k ∈ Finset.Ioc n (n + (h : ℤ)), (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
  rw [sum_Ioc_eq_sum_Icc]
  unfold shellDrift
  ring

/-! ## The indexing bridge and the finite-`K` corrector energies -/

/-- **The indexing bridge.**

The producers of the gauge junctions (`e.def.w` and the fresh-shell energy
display) deliver the corrector families indexed by the increment path `k_{n+h}
- k_n`; the proved terminal's load `gaugedPrincipalLoadShell` indexes them by
the shell sequence.  This is the composition, written once so that the bridge
is visible at every use. -/
def alongIncrementPath {alpha : Type*} (n : ℤ) (h : ℕ)
    (w : C(Vec d, Mat d) → alpha) : ShellSeq d → alpha :=
  fun omega =>
    w (Algsuperdiff.Section3.Provider.Corrector.shellSumValuePath n (n + (h : ℤ)) omega)

/-- **The finite-`K` Neumann corrector energy
`E[ || grad w_N^{(K)} ||^2_{L2(cu_K)} ]`**, at the recurrence consumer's carrier.

This is, verbatim, the left-hand side of the Neumann half of
`Provider.Corrector.ShellSumEnergyDisplay.tendsto_integral_cutoffSample_cubeAverage_display`,
whose limit as `K -> infinity` is the drift `shellDrift M n h` at gauge
`c = shom_n^{-1}` and unit direction. -/
def neumannCubeEnergy (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ)
    (wN : C(Vec d, Mat d) →
      H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ)))) : ℝ :=
  ∫ omega : CutoffSample d,
      cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot
          ((alongIncrementPath n h wN omega.val).toH1Function.grad x)
          ((alongIncrementPath n h wN omega.val).toH1Function.grad x))
    ∂(cutoffSampleLaw M).toMeasure

/-- **The finite-`K` Dirichlet corrector energy
`E[ || grad w_D^{(K)} ||^2_{L2(cu_K)} ]`**, at the recurrence consumer's carrier.

This is the left-hand side of the Dirichlet half of the same proved display,
and its limit is again `shellDrift M n h`. -/
def dirichletCubeEnergy (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ)))) : ℝ :=
  ∫ omega : CutoffSample d,
      cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot
          ((alongIncrementPath n h wD omega.val).toH1Function.grad x)
          ((alongIncrementPath n h wD omega.val).toH1Function.grad x))
    ∂(cutoffSampleLaw M).toMeasure

/-! ## The named junction premises

Each definition below is a proposition **supplied by a named producer**.  None is
proved here; each is consumed as a binder by the assembly skeletons at the end
of this module. -/

/-- The manuscript's Step-4 display is asserted under a `limsup_K`; its right-hand
side is the *limit* constant `shom_n^{-2} cstar (log 3) sum_{k in Ioc n (n+h)}
3^{2 cgamma k}`.  Per that form cannot be a junction premise --- the consumer
is an inequality between two numbers at one grid, and the finite-`K` Neumann
energy lies on the wrong side of the limit.  What the manuscript actually
*proves* before passing to the limit is the inner Jensen display

```
  avsum_z | Ahom^{1/2} G_{-(h)_z} Ahom^{-1/2} P_z |^2
    = |e'|^2 + avsum_z |(grad w_N^{(K)})_z|^2
    <= |e'|^2 + || grad w_N^{(K)} ||^2_{L2(cu_K)} ,
```

and that is what is stated here, at `|e'| = 1`, in expectation, and at the
terminal's carrier.  The passage to the drift is done by the assembly skeletons
below, from the proved convergence.

: `Closure.JunctionDischargeStepFour`, composing

* the gauge collapse `ApproximateRecurrence.ClosureGaugeCollapse.blockVecDot_gaugedPrincipalLoadShell_blockDiag`;
* the zero-direction vanishing
  `Provider.Diffusivity.Corrector.FreshShellSumZeroDirection.grad_ae_eq_zero_of_isZeroTraceDirichletRhsWeakSolution_streamForcing_zero`
  (the `e = 0` branch of Step 6, where the Dirichlet corrector's forcing
  vanishes identically, so `w_D = 0` and `(grad w_D)_R = 0`);
* the cube-average/`matVecMul` interchange
  `cubeAverageVec R (streamForcing c omega n m e') = c . (h)_R e'`, which is
  what cancels the shell term of `e.Pz.def` against the gauge shear;
* the descendant-tiling Jensen step
  `avsum_R |(grad w)_R|^2 <= avg_{cu_K} |grad w|^2`. -/
def Step4GaugeEndpoint (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (j : ℕ)
    (e' : Vec d)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (wN : C(Vec d, Mat d) →
      H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ)))) : Prop :=
  gaugeEnergyAverage M n h (K : ℤ) j 0 e'
      (alongIncrementPath n h wD) (alongIncrementPath n h wN) ≤
    1 + neumannCubeEnergy M n h K wN

/-- Mirroring Junction 1: the manuscript's `limsup_K` display is replaced by the
finite-`K` inequality it is deduced from.  The manuscript's own chain is

```
  avsum_z E| ... |^2
    = |e|^2 + avsum_z E[ |(grad w_D^{(K)})_z|^2
        + shom^{-2}|(h)_z (grad w_D^{(K)})_z|^2
        - 2 shom^{-1} e . (h)_z (grad w_D^{(K)})_z ]
    <= |e|^2 + shom^{-2} E|| h grad w_D^{(K)} ||^2_{L2(cu_K)}
        - E|| grad w_D^{(K)} ||^2_{L2(cu_K)} + cgamma^15 ,
```

whose first positive term is bounded by `Fend h^2 shom_n^{-4} 3^{4 cgamma(n+h)}`
via `Closure.shellProduct_le_quadratic_error`, and whose negative term is the
finite-`K` Dirichlet energy of `dirichletCubeEnergy`.  The drift only appears
after `K -> infinity`, which the skeletons below perform.

: `Closure.JunctionDischargeStepFive`, composing the gauge collapse read at `e'
= 0`
(`ClosureGaugeCollapse.blockVecDot_gaugedPrincipalLoadShell_blockDiag_flux`),
the zero-direction vanishing of the Neumann leg
(`FreshShellSumZeroDirection.grad_ae_eq_zero_of_isMeanZeroNeumannRhsWeakSolution_streamForcing_zero`),
the Hoelder product `Closure.shellProduct_le_quadratic_error` (on
`l.km.kn.Lp` and `e.nablaw.in.L.eight`), and the proved `cgamma^15` oscillation
endpoint
(`LocalizationOscillationEndpoint.exists_gamma0_freshShellDirichlet_meshOscillation_le_gamma_pow_fifteen`).

`Fend` is the endpoint's own constant for the quadratic `h`-error; it is left
free here and enters the printed display only through `max`.  The directional
factor `|e|^2` restored is `1`, this being the `|e| = 1` branch.  The Neumann
direction is `0`: the `e' = 0` branch of Step 6, where the Neumann forcing
vanishes, so `w_N = 0` and the flux slot of `gaugedPrincipalLoadShell`
collapses to the manuscript's bare `e`, the shell term `shom_n^{-1} h e'` being
`0` as well. -/
def Step5GaugeEndpoint (M : ABKModel d) (n : ℤ) (h : ℕ) (K : ℕ) (j : ℕ)
    (e : Vec d) (Fend : ℝ)
    (wD : C(Vec d, Mat d) → H10Function (openCubeSet (originCube d (K : ℤ))))
    (wN : C(Vec d, Mat d) →
      H1MeanZeroFunction (openCubeSet (originCube d (K : ℤ)))) : Prop :=
  gaugeEnergyAverage M n h (K : ℤ) j e 0
      (alongIncrementPath n h wD) (alongIncrementPath n h wN) ≤
    1 - dirichletCubeEnergy M n h K wD
      + Fend * ((h : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ)) ^ 4)⁻¹ *
          (3 : ℝ) ^ (4 * M.gamma * ((n + (h : ℤ) : ℤ) : ℝ))
      + M.gamma ^ (15 : ℕ)

/-- **Junction 3 --- the basic split, its localization remainder, and the annealed
limit passage.**

, jointly:

* the proved structural split
  `LocalizationRecurrenceMesh.exists_localizationRecurrenceMeshSplit_le_descendantsAverage_expanded`;
* lane `gamma10-final` --- the `cgamma^10` fluctuation endpoint
  (`e.lower.bound.localization.terms`) at the same `descendantsAverage`
  carrier;
* the annealed identification `P . bfAhom_m P = lim_K E[P . bfA_m(cu_K) P]`,
  available from `Annealed.sigmaBar_characterization`, which is the root
  assembly's step rather than an endpoint.

The premise is stated as a single inequality because that is how the three enter
Step 6: the doubled form at the annealed limit is dominated by the localized
principal average plus the `cgamma^10` localization remainder. -/
def AnnealedSplitEndpoint (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ)
    (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))) : Prop :=
  blockVecDot (recurrenceP (Annealed.sigmaBar M n) e e')
      (blockMatVecMul (annealedLimitBlock (Annealed.sigmaBar M (n + (h : ℤ))))
        (recurrenceP (Annealed.sigmaBar M n) e e')) ≤
    principalEnergyAverage M n h Kc j e e' wD wN + M.gamma ^ (10 : ℕ)

/-- **Junction 4 --- the proved principal comparison, at this indexing.**

: already proved, as
`PrincipalResponseTerminal.exists_const_descendantsAverage_integral_principalEnergy_le_annealedLimit`;
this is only its re-indexing from `(m - h, m)` to `(n, n + h)`, at the witness
pair `wD, wN` that the terminal itself produces.

This `Prop` itself does not reach it, and a discharge of it from the terminal
inherits the reach but no incomplete-proof axiom.  See the module header's
Disclosure section. -/
def PrincipalSwitchEndpoint (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ)
    (Ec : {E : ℝ // 1 ≤ E}) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc))) : Prop :=
  principalEnergyAverage M n h Kc j e e' wD wN ≤
    (1 + 3 * principalResponseSwitchBudget M Ec 64) *
        gaugeEnergyAverage M n h Kc j e e' wD wN + M.gamma ^ (6 : ℕ)

/-! ## The absorbing constant -/

/-- The absolute constant of the closure: it folds the switch cross term and the
three additive remainders `cgamma^6`, `cgamma^10`, `cgamma^15` under the printed
budget.  It depends on nothing --- not on the dimension, the model, the scales or
the parameters. -/
def closureConstant : ℝ :=
  (1 + shellIncrementCap) * 3 * principalResponseBudgetConst * 3 ^ (128 : ℕ) + 4

/-- The printed switch budget, unfolded. -/
theorem principalResponseSwitchBudget_eq (M : ABKModel d)
    (Ec : {E : ℝ // 1 ≤ E}) :
    principalResponseSwitchBudget M Ec 64 =
      principalResponseBudgetConst * 3 ^ (128 : ℕ) *
        ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma) := by
  unfold principalResponseSwitchBudget
  norm_num

/-- **The absorption.**

On the manuscript's own smallness `cgamma <= exp (-1)` (which
`e.cgamma.constraints` implies, `E >= 1` giving `cgamma <= E^{-5} <= 1` and the
enlarged `M` giving the rest), the switch cross term together with the `cgamma^6`
and `cgamma^10` remainders is below the printed budget at the absolute constant
`closureConstant`. -/
theorem gamma_le_one_of_le_exp_neg_one {gamma : ℝ} (hgamma : gamma ≤ Real.exp (-1)) :
    gamma ≤ 1 := by
  have h := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
  rw [Real.exp_zero] at h
  linarith [hgamma, h]

theorem switch_and_remainders_le_flatError (M : ABKModel d)
    (Ec : {E : ℝ // 1 ≤ E}) (hgamma : M.gamma ≤ Real.exp (-1)) :
    (1 + shellIncrementCap) * (3 * principalResponseSwitchBudget M Ec 64) +
        (M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ)) + 2 * M.gamma ^ (15 : ℕ) ≤
      recurrenceFlatError M closureConstant (Ec : ℝ) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgamma1 : M.gamma ≤ 1 := gamma_le_one_of_le_exp_neg_one hgamma
  have hE1 : (1 : ℝ) ≤ (Ec : ℝ) := Ec.2
  -- `|log cgamma| >= 1`
  have hlog : Real.log M.gamma ≤ -1 := by
    have h := Real.log_le_log hgamma0 hgamma
    rwa [Real.log_exp] at h
  have hlogsq : (1 : ℝ) ≤ Real.log M.gamma ^ 2 := by
    nlinarith [hlog, sq_nonneg (Real.log M.gamma + 1)]
  have hEsq : (1 : ℝ) ≤ (Ec : ℝ) ^ 2 := by nlinarith [hE1]
  have hfac : (1 : ℝ) ≤ (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 := by
    nlinarith [hEsq, hlogsq]
  -- the three remainders
  have hpow : ∀ k : ℕ, 1 ≤ k → M.gamma ^ k ≤ M.gamma := by
    intro k hk
    calc M.gamma ^ k ≤ M.gamma ^ 1 :=
          pow_le_pow_of_le_one hgamma0.le hgamma1 hk
      _ = M.gamma := pow_one _
  have hbase : M.gamma ≤ (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma := by
    have h := mul_le_mul_of_nonneg_right hfac hgamma0.le
    rwa [one_mul] at h
  have hrem : M.gamma ^ (6 : ℕ) + M.gamma ^ (10 : ℕ) + 2 * M.gamma ^ (15 : ℕ) ≤
      4 * ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma) := by
    have h6 := hpow 6 (by norm_num)
    have h10 := hpow 10 (by norm_num)
    have h15 := hpow 15 (by norm_num)
    linarith [h6, h10, h15, hbase]
  -- the switch term
  rw [principalResponseSwitchBudget_eq]
  unfold recurrenceFlatError closureConstant
  have hexpand : ((1 + shellIncrementCap) * 3 * principalResponseBudgetConst *
        3 ^ (128 : ℕ) + 4) * (Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma =
      (1 + shellIncrementCap) * (3 * (principalResponseBudgetConst * 3 ^ (128 : ℕ) *
          ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma))) +
        4 * ((Ec : ℝ) ^ 2 * Real.log M.gamma ^ 2 * M.gamma) := by ring
  rw [hexpand]
  linarith [hrem]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
