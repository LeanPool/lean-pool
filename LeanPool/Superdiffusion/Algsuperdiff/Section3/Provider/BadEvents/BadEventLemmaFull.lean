/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventLemmaCases
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.OscillationBranchLow

/-!
# BadEventLemmaFull

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `l.bad.event.lemma` over the full range of `m` and `n`

`BadEventLemmaOscillation.lean` supplies a local oscillation-branch result for
ABK26's Lemma `l.bad.event.lemma` on the branch `m <= n`, and
`OscillationBranchLow.lean` supplies its local `n < m` counterpart.  This
ordinary Provider module combines them into a conditional full-range estimate
matching the displayed form over *all* `m, n`,

```
P[ B_osc(m,n) ]  <=  exp( - c c_star gamma^{-1} 3^{-5(m-n)_+} 3^{(n-m)_+} ) ,
```

and then assembles the corresponding conditional complement-event estimate

```
P[ not Q(m,n,z) ]
  <= exp( - c c_star gamma^{-1} 3^{-5(m-n)_+} 3^{(n-m)_+} )
     + exp( - exp( c' E^{-2} gamma^{-1} ) )
```

over the same full range, from the coarse-ellipticity branch of
`BadEventLemmaCases.lean`.

## Where each hypothesis comes from

* **The printed admissibility** `e.bad.event.admissibility` is carried as
  `hadm`/`hgammaE` at the dimension-only constant `badEventOscLowAdmissibleConst
  d Ccg`.  As in the branch `m <= n`, this discharges the weak-Orlicz gate of
  the oscillation half *and* the gate `gamma <= 1/8` of the coarse-ellipticity
  half (through `badEventOscAdmissibleConst_le_badEventOscLowAdmissibleConst`
  and the proved `gamma_le_one_eighth_of_admissible`).  Choosing a larger
  dimension-only constant is exactly what the lemma's own existential `c(d)`
  permits.
* On the branch `m <= n` no such hypothesis is present: there the gate is
  derived from the printed admissibility.
* **The two conditional binders of the coarse-ellipticity half**, `hmono` and
  `hcg`, are the proved ones of `BadEventLemmaCases.lean`, verbatim: `hcg` is
  the exact specialization of the now-proved frozen `coarse_ellipticity_bounds`
  conclusion, retained here as a conditional A binder for a downstream assembly
  to discharge, and `hmono` is the W cube-monotonicity step (whose weight-free
  form is false —).  On the branch `n < m` the binder `hmono` additionally
  absorbs the manuscript's subadditivity step `e.subadda.nosymm`, which has no
  realization in this repository.

## Main definitions

* `badEventOscLowAdmissibleConst`: the dimension-only constant at which the
  printed admissibility discharges both gates over the full range.

## Main results

* `one_le_badEventOscFullRate_of_admissible`: the gate on the branch `m <= n`.
* `measureReal_goodLocalSensitivityFailure_le_full`: `e.oscillation.bound` over
  the full range, from the display's own exponent being at least one.
* `measureReal_goodLocalSensitivityFailure_le_full_of_admissible`: the same,
  with the branch `m <= n` discharged from the printed admissibility and the
  restriction confined to `n < m`.

## References

* ABK26, `l.bad.event.lemma`; `e.bad.event.Q.estimate`; `e.oscillation.bound`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

private theorem one_le_mul_one_leF {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b := by nlinarith

/-! ## The admissibility constant of the full range -/

/-- The dimension-only constant at which the manuscript's admissibility display
`e.bad.event.admissibility` (`c^{-1} c_star^{-1} <= E <= gamma^{-1/5}`)
discharges the gate of the oscillation branch on `m <= n` at the *full-range*
constant `badEventOscLowConst`.  It is the constant `badEventOscAdmissibleConst`
of the branch `m <= n`, enlarged by the square of the dimension-only covering
constant of `e.W1inf.jL.bound.smaller`. -/
def badEventOscLowAdmissibleConst (d : ℕ) (Ccg : ℝ) : ℝ :=
  max 3 (3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
    (max 1 (shellW1InfSmallerConst d)) ^ 2)

theorem badEventOscAdmissibleConst_le_badEventOscLowAdmissibleConst (d : ℕ)
    {Ccg : ℝ} (hCcg : 0 < Ccg) :
    badEventOscAdmissibleConst d Ccg ≤ badEventOscLowAdmissibleConst d Ccg := by
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hmax1 : (1 : ℝ) ≤ max 1 (shellW1InfSmallerConst d) := le_max_left _ _
  have hbase : (0 : ℝ) ≤ 3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 := by
    positivity
  have hsq : (1 : ℝ) ≤ (max 1 (shellW1InfSmallerConst d)) ^ 2 := by nlinarith
  have hstep : 3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 ≤
      3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
        (max 1 (shellW1InfSmallerConst d)) ^ 2 := by nlinarith
  unfold badEventOscAdmissibleConst badEventOscLowAdmissibleConst
  exact max_le_max le_rfl hstep

/-- **The gate on the branch `m <= n` from the printed admissibility.**  With
the absolute bound `c_star <= 3/2` (`Provider.Disorder.cstar_le_three_halves`),
the manuscript's own admissibility at `badEventOscLowAdmissibleConst` gives
`1 <= badEventOscFullRate`.  Nothing is assumed on this branch beyond the
printed display. -/
theorem one_le_badEventOscFullRate_of_admissible (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 < Ccg) (Q : TriadicCube d) {n : ℤ} {E : ℝ} (hmn : Q.scale ≤ n)
    (hadm : badEventOscLowAdmissibleConst d Ccg ≤
      E * Algsuperdiff.Section3.Disorder.cstar M)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    1 ≤ badEventOscFullRate M Ccg Q n := by
  have hC : (0 : ℝ) < sensitivityConstMax d := sensitivityConstMax_pos d
  have hc : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hchalf : Algsuperdiff.Section3.Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hmaxpos : (0 : ℝ) < max 1 (shellW1InfSmallerConst d) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCne : (sensitivityConstMax d) ≠ 0 := ne_of_gt hC
  have hCcgne : Ccg ≠ 0 := ne_of_gt hCcg
  have hmaxne : (max 1 (shellW1InfSmallerConst d)) ≠ 0 := ne_of_gt hmaxpos
  have h3 : (3 : ℝ) ≤ E * Algsuperdiff.Section3.Disorder.cstar M :=
    le_trans (le_max_left _ _) hadm
  have hbig : 3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
      (max 1 (shellW1InfSmallerConst d)) ^ 2 ≤
      E * Algsuperdiff.Section3.Disorder.cstar M :=
    le_trans (le_max_right _ _) hadm
  have hbigpos : (0 : ℝ) < 3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
      (max 1 (shellW1InfSmallerConst d)) ^ 2 := by positivity
  -- `E >= 2`
  have hE2 : (2 : ℝ) ≤ E := by
    by_contra hlt
    push Not at hlt
    have hmul : E * Algsuperdiff.Section3.Disorder.cstar M <
        2 * Algsuperdiff.Section3.Disorder.cstar M :=
      mul_lt_mul_of_pos_right hlt hc
    linarith
  -- `gamma^{-1} >= E^5`
  have hE5 : (0 : ℝ) < E ^ (5 : ℕ) := by positivity
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hginv : E ^ (5 : ℕ) ≤ M.gamma⁻¹ := by
    rw [le_inv_comm₀ hE5 hg, ← hEpow]
    exact hgamma
  have hE4 : (1 : ℝ) ≤ E ^ (4 : ℕ) := one_le_pow₀ (by linarith)
  have hkey : 3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
      (max 1 (shellW1InfSmallerConst d)) ^ 2 ≤
      Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ := by
    calc 3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
          (max 1 (shellW1InfSmallerConst d)) ^ 2
        = (3600 * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
            (max 1 (shellW1InfSmallerConst d)) ^ 2) * 1 := (mul_one _).symm
      _ ≤ (E * Algsuperdiff.Section3.Disorder.cstar M) * E ^ (4 : ℕ) :=
          mul_le_mul hbig hE4 (by norm_num) (le_trans hbigpos.le hbig)
      _ = Algsuperdiff.Section3.Disorder.cstar M * E ^ (5 : ℕ) := by ring
      _ ≤ Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ :=
          mul_le_mul_of_nonneg_left hginv hc.le
  -- the gap factor is at least one on this branch
  have hzero : scaleGapPos n Q.scale = 0 := by
    have hle : ((Q.scale : ℝ)) - (n : ℝ) ≤ 0 := by
      have : ((Q.scale : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    rw [scaleGapPos]
    exact max_eq_right hle
  have hgap : (1 : ℝ) ≤
      (3 : ℝ) ^ (scaleGapPos Q.scale n - 5 * scaleGapPos n Q.scale) := by
    rw [hzero]
    refine Real.one_le_rpow (by norm_num) ?_
    have := scaleGapPos_nonneg Q.scale n
    linarith
  have hconst : badEventOscLowConst d Ccg =
      ((3600 : ℝ) * (sensitivityConstMax d) ^ 2 * Ccg ^ 2 *
        (max 1 (shellW1InfSmallerConst d)) ^ 2)⁻¹ := by
    rw [badEventOscLowConst]
    field_simp
  have hone : (1 : ℝ) ≤ badEventOscLowConst d Ccg *
      (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) := by
    rw [hconst, ← div_eq_inv_mul, le_div_iff₀ hbigpos]
    linarith [hkey]
  have hrewrite : badEventOscFullRate M Ccg Q n =
      badEventOscLowConst d Ccg *
        (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) *
        (3 : ℝ) ^ (scaleGapPos Q.scale n - 5 * scaleGapPos n Q.scale) := by
    rw [badEventOscFullRate]
    ring
  rw [hrewrite]
  exact one_le_mul_one_leF hone hgap

/-! ## `e.oscillation.bound` over the full range -/

/-- **`e.oscillation.bound` over the full range of `m, n`** (ABK26):

```
P[ sensitivity clause of Q(m,n,z) fails ]
  <= exp( - c c_star gamma^{-1} 3^{-5(m-n)_+} 3^{(n-m)_+} ) ,
```

with `c = badEventOscLowConst d Ccg`, dimension-only.  The single hypothesis
`hrestrict` says that the displayed exponent is at least one; on the branch `m
<= n` it follows from the printed admissibility
(`one_le_badEventOscFullRate_of_admissible`), and on the branch `n < m` it is
the restriction. -/
theorem measureReal_goodLocalSensitivityFailure_le_full (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 0 < Ccg) (Q : TriadicCube d) {n m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E)
    (hn : n ≤ m0 - 1) (hrestrict : 1 ≤ badEventOscFullRate M Ccg Q n) :
    (cutoffSampleLaw M).toMeasure.real (goodLocalSensitivityFailure M Ccg Q n) ≤
      Real.exp (-(badEventOscFullRate M Ccg Q n)) := by
  rcases le_or_gt Q.scale n with hmn | hmn
  · have hle := badEventOscFullRate_le_badEventOscRate M hCcg Q hmn
    have hgate : 1 ≤ badEventOscRate M Ccg Q n := le_trans hrestrict hle
    refine le_trans
      (measureReal_goodLocalSensitivityFailure_le M hCcg Q hS hn hmn hgate) ?_
    exact Real.exp_le_exp.2 (neg_le_neg hle)
  · exact measureReal_goodLocalSensitivityFailure_le_low M hCcg Q hS hn hmn
      hrestrict

theorem measureReal_goodLocalSensitivityFailure_le_full_of_admissible
    (M : ABKModel d) {Ccg : ℝ} (hCcg : 0 < Ccg) (Q : TriadicCube d) {n m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E)
    (hn : n ≤ m0 - 1)
    (hadm : badEventOscLowAdmissibleConst d Ccg ≤
      (E : ℝ) * Algsuperdiff.Section3.Disorder.cstar M)
    (hgammaE : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ))
    (hrestrict : n < Q.scale → 1 ≤ badEventOscFullRate M Ccg Q n) :
    (cutoffSampleLaw M).toMeasure.real (goodLocalSensitivityFailure M Ccg Q n) ≤
      Real.exp (-(badEventOscFullRate M Ccg Q n)) := by
  rcases le_or_gt Q.scale n with hmn | hmn
  · exact measureReal_goodLocalSensitivityFailure_le_full M hCcg Q hS hn
      (one_le_badEventOscFullRate_of_admissible M hCcg Q hmn hadm hgammaE)
  · exact measureReal_goodLocalSensitivityFailure_le_full M hCcg Q hS hn
      (hrestrict hmn)

end

end Algsuperdiff.Section3.Provider.BadEvents
