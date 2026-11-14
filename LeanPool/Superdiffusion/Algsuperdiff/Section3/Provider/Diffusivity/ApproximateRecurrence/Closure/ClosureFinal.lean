/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureFinalArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.ClosureFinalMeasurability

/-!
# ClosureFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two-sided closure, reduced to its named endpoints

`Closure.ClosureAssembly` carries the node as far as *conditional* displays: two
statements of the form "given the four junctions at the chosen corrector
families, plus two typing binders and three parameter-regime facts, the printed
display holds".  This module removes everything from that list that is not a
mathematical endpoint of the manuscript:

* the two `AEStronglyMeasurable` typing binders `hDm`, `hNm` are discharged by
  `Closure.ClosureFinalMeasurability`;
* the three parameter-regime facts `hgamma`, `hcap`, `hsmall` are *derived* from
  the contract's own antecedents by `Closure.ClosureFinalArithmetic` and
  `Closure.shellDrift_le_cap`, at an enlarged absolute constant;
* Junction 4 is discharged at the chosen families by
  `Closure.eventually_principalSwitchEndpoint_closureFamilies`;
* the induction state is moved from the contract's scale `m0 - 1` to the
  producers' scale `n + h - 1` by `Closure.inductionState_mono`;
* the degenerate shell `h = 0` is discharged by
  `Closure.recurrenceUpperDisplay_zero` and `Closure.recurrenceLowerDisplay_zero`;
* the two displays' constants (`closureConstant` and `max closureConstant (2 F)`)
  are merged into one by `Closure.recurrenceUpperDisplay_mono` and
  `Closure.recurrenceLowerDisplay_mono`;
* the direction of the displays is chosen here (`closureUnitVec`), the printed
  lines being statements about `shom` ratios alone.

What is left is exactly three named endpoints, `ClosureSplitInput`,
`ClosureStep4Input` and `ClosureStep5Input` below, each stated **at the closure's
own corrector families** and in the shape its named producer delivers.

Each of the three carries, as its own leading antecedent, the manuscript's
standing dimension hypothesis `2 <= d` --- exactly the shape
`Closure.NodeContract.TwoSidedClosure` itself has.
`twoSidedClosure_of_endpoints` introduces `hd` before consuming any input.

## The three inputs, and their status

| input | content | producer |
|---|---|---|
| `ClosureSplitInput` | the finite-grid half of Steps 1--3 at the `cgamma^10` endpoint, in the exact
antecedent shape of
`Closure.AnnealedLimitJunction.annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le` | **IN**,
lane `gamma10-*` |
| `ClosureStep4Input` | Junction 1, `e.lower.bound.pre1` at the closure families |
`Closure.JunctionDischargeStepFour.step4GaugeEndpoint_of_correctors`, whose four remaining binders
are analytic side conditions of the display |
| `ClosureStep5Input` | Junction 2, `e.lower.bound.pre2` at the closure families, with the produced
`Fend` | `Closure.JunctionDischargeStepFiveDisplay.step5GaugeEndpoint_of_correctors_gauge` (per-cube
gauge), whose `hosc` binder is supplied by `Closure.Step5DefectGauge`'s re-sited full-mesh producer
|

Nothing else is assumed.  In particular no smallness, no normalization and no
bound of the manuscript is carried as a hypothesis of
`twoSidedClosure_of_endpoints`: the three inputs are the manuscript's own Step-1--3,
Step-4 and Step-5 conclusions, and everything the assembly needs besides them is
proved.

## References

* ABK26, `l.approximate.recurrence.formula`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## A unit direction

Both printed lines of `e.what.do.we.have` are statements about the ratio
`shom_{n+h} shom_n^{-1}` alone; the direction enters only through the junctions,
which hold at every unit direction.  The closure therefore *chooses* one. -/

/-- The first coordinate direction, a unit vector of `Vec d` whenever `d /= 0`. -/
def closureUnitVec (d : ℕ) [NeZero d] : Vec d :=
  Pi.single (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ : Fin d) (1 : ℝ)

theorem vecNormSq_closureUnitVec (d : ℕ) [NeZero d] :
    vecNormSq (closureUnitVec d) = 1 := by
  classical
  have hi : (0 : ℕ) < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hfun : ∀ i : Fin d, closureUnitVec d i * closureUnitVec d i =
      if i = (⟨0, hi⟩ : Fin d) then (1 : ℝ) else 0 := by
    intro i
    simp only [closureUnitVec, Pi.single_apply]
    split <;> simp
  change ∑ i, closureUnitVec d i * closureUnitVec d i = 1
  rw [Finset.sum_congr rfl fun i _ => hfun i]
  rw [Finset.sum_eq_single (⟨0, hi⟩ : Fin d)]
  · simp
  · intro b _ hb
    simp only [ite_eq_right hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## The regime under which the three inputs are read

Each input is read exactly where the manuscript reads Steps 1--5: inside
`l.approximate.recurrence.formula`'s standing hypotheses.  `ClosureRegime`
records that antecedent block once, in the shape the proved principal-response
producer `Closure.eventually_principalSwitchEndpoint_closureFamilies` already
uses, so that an input is never asked for outside the regime in which the
manuscript proves it. -/

/-- The manuscript's standing hypotheses at one admissible pair `(n, n+h)` and
one threshold `C`. -/
def ClosureRegime {d : ℕ} (C : ℝ) (M : ABKModel d) (n : ℤ) (h : ℕ)
    (Ec : {E : ℝ // 1 ≤ E}) : Prop :=
  Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec ∧
    0 < h ∧
    C * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) ∧
    M.gamma ≤ (Ec : ℝ) ^ (-5 : ℤ) ∧
    (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ ∧
    shellDrift M n h ≤ shellIncrementCap

/-! ## The three inputs -/

/-- **Input 1 (Steps 1--3, the `cgamma^10` endpoint).**

The finite-grid half of `e.lower.bound.basic.split` together with
`e.lower.bound.localization.terms`, stated verbatim in the antecedent shape of
`Closure.AnnealedLimitJunction.annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le`
and at the closure's own corrector families, for all sufficiently large
localization cubes.  Both gauge branches are required: the upper display reads
it at `(e, e') = (0, e)`, the lower display at `(e, 0)`.  The producer names
its own threshold `Csplit`, exactly as the proved principal-response terminal
does. -/
def ClosureSplitInput (d : ℕ) [NeZero d] : Prop :=
  2 ≤ d →
  ∃ Csplit : ℝ, 0 < Csplit ∧
    ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e : Vec d),
      vecNormSq e = 1 → ClosureRegime Csplit M n h Ec →
      (∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega : CutoffSample d,
              blockVecDot (recurrenceP (Annealed.sigmaBar M n) 0 e)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d (K : ℤ)))
                    ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                      (originCube d (K : ℤ))))
                  (recurrenceP (Annealed.sigmaBar M n) 0 e))
              ∂(cutoffSampleLaw M).toMeasure ≤
            principalEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) 0 e
                (alongIncrementPath n h
                  (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K))
                (alongIncrementPath n h
                  (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)) +
              M.gamma ^ (10 : ℕ)) ∧
        (∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega : CutoffSample d,
              blockVecDot (recurrenceP (Annealed.sigmaBar M n) e 0)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d (K : ℤ)))
                    ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                      (originCube d (K : ℤ))))
                  (recurrenceP (Annealed.sigmaBar M n) e 0))
              ∂(cutoffSampleLaw M).toMeasure ≤
            principalEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e 0
                (alongIncrementPath n h
                  (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
                (alongIncrementPath n h
                  (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K)) +
              M.gamma ^ (10 : ℕ))

/-- **Input 2 (Step 4).**  `Closure.Step4GaugeEndpoint` at the closure's own
corrector families, in the manuscript's regime, for all sufficiently large
localization cubes. -/
def ClosureStep4Input (d : ℕ) [NeZero d] : Prop :=
  2 ≤ d →
  ∃ C4 : ℝ, 0 < C4 ∧
    ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e : Vec d),
      vecNormSq e = 1 → ClosureRegime C4 M n h Ec →
      ∀ᶠ K : ℕ in Filter.atTop,
        Step4GaugeEndpoint M n h K (closureMeshDepth M n h K) e
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K)
          (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)

/-- **Input 3 (Step 5).**  `Closure.Step5GaugeEndpoint` at the closure's own
corrector families, in the manuscript's regime, with the produced constant
`Fend` uniform in the model, for all sufficiently large localization cubes. -/
def ClosureStep5Input (d : ℕ) [NeZero d] : Prop :=
  2 ≤ d →
  ∃ C5 Fend : ℝ, 0 < C5 ∧ 0 ≤ Fend ∧
    ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e : Vec d),
      vecNormSq e = 1 → ClosureRegime C5 M n h Ec →
      ∀ᶠ K : ℕ in Filter.atTop,
        Step5GaugeEndpoint M n h K (closureMeshDepth M n h K) e Fend
          (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)
          (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K)

/-! ## Junction 3 at the closure families, from the finite-grid input -/

theorem eventually_annealedSplitEndpoint_of_splitInput [NeZero d] {Csplit : ℝ}
    (hsplit : ∀ (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) (e : Vec d),
      vecNormSq e = 1 → ClosureRegime Csplit M n h Ec →
      (∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega : CutoffSample d,
              blockVecDot (recurrenceP (Annealed.sigmaBar M n) 0 e)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d (K : ℤ)))
                    ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                      (originCube d (K : ℤ))))
                  (recurrenceP (Annealed.sigmaBar M n) 0 e))
              ∂(cutoffSampleLaw M).toMeasure ≤
            principalEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) 0 e
                (alongIncrementPath n h
                  (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K))
                (alongIncrementPath n h
                  (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K)) +
              M.gamma ^ (10 : ℕ)) ∧
        (∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega : CutoffSample d,
              blockVecDot (recurrenceP (Annealed.sigmaBar M n) e 0)
                (blockMatVecMul
                  (Ch02.coarseBlockMatrix (Ch02.cubeDomain (originCube d (K : ℤ)))
                    ((coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega).coeffOn
                      (originCube d (K : ℤ))))
                  (recurrenceP (Annealed.sigmaBar M n) e 0))
              ∂(cutoffSampleLaw M).toMeasure ≤
            principalEnergyAverage M n h (K : ℤ) (closureMeshDepth M n h K) e 0
                (alongIncrementPath n h
                  (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
                (alongIncrementPath n h
                  (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K)) +
              M.gamma ^ (10 : ℕ)))
    (M : ABKModel d) (n : ℤ) (h : ℕ) (Ec : {E : ℝ // 1 ≤ E}) {e : Vec d}
    (he : vecNormSq e = 1) (hreg : ClosureRegime Csplit M n h Ec) :
    (∀ᶠ K : ℕ in Filter.atTop,
        AnnealedSplitEndpoint M n h (K : ℤ) (closureMeshDepth M n h K) 0 e
          (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K))
          (alongIncrementPath n h
            (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))) ∧
      (∀ᶠ K : ℕ in Filter.atTop,
        AnnealedSplitEndpoint M n h (K : ℤ) (closureMeshDepth M n h K) e 0
          (alongIncrementPath n h
            (closureDirichletFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ e K))
          (alongIncrementPath n h
            (closureNeumannFamily ((Annealed.sigmaBar M n : ℝ))⁻¹ 0 K))) := by
  obtain ⟨hup, hlo⟩ := hsplit M n h Ec e he hreg
  constructor
  · filter_upwards [hup] with K hK
    exact annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le M n h (K : ℤ)
      (closureMeshDepth M n h K) (K : ℤ) 0 e _ _ hK
  · filter_upwards [hlo] with K hK
    exact annealedSplitEndpoint_of_integral_ch02CoarseBlockMatrix_le M n h (K : ℤ)
      (closureMeshDepth M n h K) (K : ℤ) e 0 _ _ hK

/-! ## The contract -/

/-- **The two-sided closure of `l.approximate.recurrence.formula`, from its three
named endpoints.**

Everything the assembly needs besides the three inputs is proved: the two
`AEStronglyMeasurable` typing binders, the three parameter-regime facts,
Junction 4, the induction-state transport, the degenerate shell `h = 0` and the
merge of the two displays' constants.

The switch endpoint enters through
`Closure.eventually_principalSwitchEndpoint_closureFamilies`. -/
theorem twoSidedClosure_of_endpoints (d : ℕ) [NeZero d]
    (hsplit : ClosureSplitInput d) (hstep4 : ClosureStep4Input d)
    (hstep5 : ClosureStep5Input d) : TwoSidedClosure d := by
  intro hd
  obtain ⟨Cup, hCup0, hupper⟩ := exists_const_recurrenceUpperDisplay_of_inflight d hd
  obtain ⟨Clo, hClo0, hlower⟩ := exists_const_recurrenceLowerDisplay_of_inflight d hd
  obtain ⟨Csplit, hCsplit0, hsplit'⟩ := hsplit hd
  obtain ⟨C4, hC40, hstep4'⟩ := hstep4 hd
  obtain ⟨C5, Fend, hC50, hFend, hstep5'⟩ := hstep5 hd
  set C : ℝ := max (max (max Cup Clo) (max Csplit (max C4 C5)))
    (max closureRegimeConst (max closureConstant (2 * Fend))) with hCdef
  have hCup : Cup ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hClo : Clo ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hCsplit : Csplit ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hC4 : C4 ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_left _ _)
  have hC5 : C5 ≤ C :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_left _ _)
  have hCreg : closureRegimeConst ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCcl : closureConstant ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hCF : max closureConstant (2 * Fend) ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hC0 : 0 < C := lt_of_lt_of_le closureRegimeConst_pos hCreg
  refine ⟨C, hC0, ?_⟩
  intro M m0 Ec _hm0 hstate hCE hgammaE n h hh _hmss hnle
  have hcstar0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcinv0 : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.2 hcstar0
  rcases Nat.eq_zero_or_pos h with hzero | hpos
  · subst hzero
    exact ⟨recurrenceUpperDisplay_zero M hC0.le n, recurrenceLowerDisplay_zero M hC0.le n⟩
  have hnm1 : n ≤ m0 - 1 := by
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hpos
    omega
  have hcap : shellDrift M n h ≤ shellIncrementCap :=
    shellDrift_le_cap M hstate hnm1 hh
  -- the standing regime facts, derived from the contract's own antecedents
  have hgamma : M.gamma ≤ Real.exp (-1) :=
    gamma_le_exp_neg_one_of_regime M hCreg hCE hgammaE
  have hsmall : 3 * principalResponseSwitchBudget M Ec 64 ≤ 1 :=
    three_mul_switchBudget_le_one_of_regime M hCreg hCE hgammaE
  -- the induction state at the producers' scale
  have hstate' : Algsuperdiff.Frozen.Section3.inductionState M (n + (h : ℤ) - 1) Ec :=
    inductionState_mono (by omega) hstate
  -- the largeness thresholds the five producers ask for
  have hthresh : ∀ C' : ℝ, C' ≤ C → C' * (Disorder.cstar M)⁻¹ ≤ (Ec : ℝ) := fun C' hC' =>
    le_trans (mul_le_mul_of_nonneg_right hC' hcinv0.le) hCE
  have hreg : ∀ C' : ℝ, C' ≤ C → ClosureRegime C' M n h Ec := fun C' hC' =>
    ⟨hstate', hpos, hthresh C' hC', hgammaE, hh, hcap⟩
  -- the chosen direction
  have he : vecNormSq (closureUnitVec d) = 1 := vecNormSq_closureUnitVec d
  obtain ⟨hsplitUp, hsplitLo⟩ :=
    eventually_annealedSplitEndpoint_of_splitInput hsplit' M n h Ec he (hreg Csplit hCsplit)
  refine ⟨?_, ?_⟩
  · refine recurrenceUpperDisplay_mono M hCcl ?_
    exact hupper M n h Ec (closureUnitVec d) he hstate' hpos (hthresh Cup hCup) hgammaE hh
      hgamma hcap hsplitUp
      (hstep4' M n h Ec (closureUnitVec d) he (hreg C4 hC4))
      (aestronglyMeasurable_cubeAverage_closureDirichletFamily M n h (closureUnitVec d))
      (aestronglyMeasurable_cubeAverage_closureNeumannFamily M n h (closureUnitVec d))
  · refine recurrenceLowerDisplay_mono M hCF ?_
    exact hlower M n h Ec (closureUnitVec d) Fend he hFend hstate' hpos (hthresh Clo hClo)
      hgammaE hh hgamma hsmall hsplitLo
      (hstep5' M n h Ec (closureUnitVec d) he (hreg C5 hC5))
      (aestronglyMeasurable_cubeAverage_closureDirichletFamily M n h (closureUnitVec d))
      (aestronglyMeasurable_cubeAverage_closureNeumannFamily M n h (closureUnitVec d))

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
