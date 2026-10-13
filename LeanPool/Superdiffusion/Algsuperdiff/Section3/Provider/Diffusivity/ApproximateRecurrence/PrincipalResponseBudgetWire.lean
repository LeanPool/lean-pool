/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLamWire

/-!
# PrincipalResponseBudgetWire

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
inventories below are informal descriptions only.

# The Young-remainder smallness, supplied rather than assumed

Sources in ABK26:

* The sentence "Therefore, by independence of `bfA_{m-h}` and
  `G_{-(h)_{z+cu_n}} P_z` (the latter is a function of `k_m - k_{m-h}`),
  increasing `M` in `\eqref{e.cgamma.constraints}` if necessary,";
* `e.cgamma.constraints` (label; display), which reads `cgamma <= E^{-5}` and
  `E >= M cstar^{-1}` "for a constant `M = M(d) < infty` to be determined
  below";
* `e.recurrence.params` (label; display);
* `e.lower.bound.principal.one.pre` (label; display), the display the consumer
  produces.

## What this module supplies

One bridge and one consumer.

1. `principalSwitchLoadConst_mul_gridSwitchDiscount_mul_le_half_gamma_pow_six`
   turns the numerical smallness

   ```
     C_load(d) . (3/2) . Cell . cgamma  <=  1/2
   ```

   into the exact proposition that
   `ApproximateRecurrence.PrincipalResponseLamWire` binds as `hbudget`,

   ```
     C_load(d) . ( (3/2) Delta ) . Cell  <=  cgamma^6 / 2 ,
     Delta = gridSwitchDiscount cu_K j (m-h) ,
   ```

   at the manuscript's own mesoscale `n = m - h - a ceil|log_3 cgamma|`.

2. `exists_gamma0_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_centeringConst`
   is the direct successor and consumer of `PrincipalResponseLamWire`'s
   `exists_const_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_centeringConst`,
   with `hbudget` **gone** and every other binder unchanged, in the same order,
   with the same types.  Nothing replaces it: no binder is added, and the two
   binders `W` and `hindep` that the consumer also carries are left exactly as
   they were.

   The smallness is discharged by shrinking the theorem's own already-existential
   threshold `gamma0`.  `PrincipalResponseLamWire` produces a pair
   `(Cell, gamma0)`; this module keeps that `Cell` and returns the smaller
   threshold

   ```
     min gamma0 ( (1/2) / ( C_load(d) . (3/2) . Cell ) ) ,
   ```

   which is positive, still at most `1/4`, and at most `gamma0`.

   The implication runs in one direction only, and this is the direction:
   **every model satisfying the new, smaller threshold `M.gamma <= min gamma0
   ((1/2) / (C_load(d). (3/2). Cell))` also satisfies the old threshold
   `M.gamma <= gamma0`.**  Hence `PrincipalResponseLamWire`'s theorem is
   available at every model this theorem quantifies over, and at those models
   the smallness holds by construction.  The converse is false, and the cost is
   recorded rather than hidden: the statement produced here is applied at
   *fewer* models than the statement it re-states, not at the same ones.  An
   earlier version of this paragraph asserted that the produced statement "is
   applied at every model it was applied at before"; that reversed the
   implication and is withdrawn.

   This is the manuscript's own device and no other: `e.cgamma.constraints`
   bounds `cgamma` by `E^{-5}` with `E >= M cstar^{-1}`, so "increasing `M` if
   necessary" *is* a threshold on `cgamma` depending on the dimension and on
   the already-produced constants.  The dependence here is exactly that: `d`
   and `Cell`, both fixed before the threshold is chosen.

## Why the constant `Cell` disappears from the statement

In `PrincipalResponseLamWire`'s consumer, `Cell` occurs in `hbudget` and nowhere
else.  Once `hbudget` is discharged, `Cell` occurs nowhere in the statement, so
the leading `∃ Cell : ℝ, 0 < Cell ∧ _` is an existential over a variable its
body does not mention and is dropped.  Dropping it is a logical equivalence, not
a strengthening or a weakening.

## What this module is *not*

It is not a bridge from the proved Section 3.4 **Budget** chain
(`...PrincipalResponseBudget{,Moment,Scales,Descent}`).  That chain bounds a
different quantity, the annealed probe defect

```
  cubeAnnealedProbeDefect M L n Ev  <=  C 3^{2K} E^2 |log cgamma|^2 cgamma
```

(`cubeAnnealedProbeDefect_le_logSq_budget`), which is the input of the proved
`...PrincipalResponseSwitch.annealedCubeBlockQuadratic_le_annealedLimitBlockQuadratic`
and does not occur in `hbudget`.  The `hbudget` binder is a
scale-and-sample-free numerical inequality among `C_load(d)`, the grid switch
discount `Delta` and the grid ellipticity budget constant `Cell`.  The two are
different displays of the manuscript and are not interchanged here.

## The `3/2`

The switch factor carried through is the honest `1 + (3/2) Delta` rather than
the printed `1 + Delta`, declared by
`ApproximateRecurrence.PrincipalResponseSwitchActualPerCube`.  It enters the
bridge unchanged, as the literal factor `(3/2)`.

## Main results

* `principalSwitchLoadConst_mul_gridSwitchDiscount_mul_le_half_gamma_pow_six`
* `exists_gamma0_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_centeringConst`

## References

* ABK26, (the sentence quoted above); `e.cgamma.constraints` (label; display);
  `e.recurrence.params` (label; display); `e.lower.bound.principal.one.pre`
  (label; display).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The bridge: the smallness at the grid switch discount -/

/-- **The Young-remainder smallness, at the manuscript's own mesoscale.**

```
  C_load(d) . (3/2) . Cell . cgamma  <=  1/2 .
```

This is the manuscript's "increasing `M` in `e.cgamma.constraints` if
necessary" made numerical: `e.cgamma.constraints` (label) bounds `cgamma` by
`E^{-5}` with `E >= M cstar^{-1}`, so a lower bound on `M` is a threshold on
`cgamma`.

The step is `Delta <= cgamma^7` at `a >= 28`
(`ApproximateRecurrence.LocalizationParams`
`rpow_three_neg_recurrenceGap_div_four_le_rpow_seven`), which leaves one spare
power of `cgamma` for the constants.

It is a provider A, not a source-facing frozen declaration. -/
private theorem principalSwitchLoadConst_mul_gridSwitchDiscount_mul_le_half_gamma_pow_six
    (dimension : 2 ≤ d) (M : ABKModel d) (Q : TriadicCube d) (j a : ℕ)
    (m h : ℤ) (ha : recurrenceGapMultiplierFloor ≤ a)
    (hscale : (Q.scale : ℤ) - (j : ℤ) = recurrenceMesoScale a M.gamma m h)
    {Cell : ℝ} (hCell0 : 0 ≤ Cell)
    (hsmall : principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell * M.gamma ≤ 1 / 2) :
    principalSwitchLoadConst d *
        ((3 / 2 : ℝ) * gridSwitchDiscount Q j (m - h)) * Cell ≤
      M.gamma ^ (6 : ℕ) / 2 := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgamma1 : M.gamma ≤ 1 :=
    le_trans M.shellPrefix.gamma_le_quarter (by norm_num)
  have hCs : (0 : ℝ) < principalSwitchLoadConst d :=
    principalSwitchLoadConst_pos dimension
  have hCs0 : (0 : ℝ) ≤ principalSwitchLoadConst d * (3 / 2 : ℝ) := by linarith
  have hseven :=
    rpow_three_neg_recurrenceGap_div_four_le_rpow_seven a hgamma0 hgamma1 ha
  have hpow : M.gamma ^ (7 : ℝ) = M.gamma ^ (6 : ℕ) * M.gamma := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hpow] at hseven
  rw [gridSwitchDiscount_eq_rpow_recurrenceGap Q j a M.gamma m h hscale]
  have hmul : principalSwitchLoadConst d * (3 / 2 : ℝ) *
        (3 : ℝ) ^ (-((recurrenceGap a M.gamma : ℝ) / 4)) * Cell ≤
      principalSwitchLoadConst d * (3 / 2 : ℝ) *
        (M.gamma ^ (6 : ℕ) * M.gamma) * Cell :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hseven hCs0) hCell0
  have hfin : principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell * M.gamma *
        M.gamma ^ (6 : ℕ) ≤ 1 / 2 * M.gamma ^ (6 : ℕ) :=
    mul_le_mul_of_nonneg_right hsmall (by positivity)
  calc principalSwitchLoadConst d *
        ((3 / 2 : ℝ) * (3 : ℝ) ^ (-((recurrenceGap a M.gamma : ℝ) / 4))) * Cell
      = principalSwitchLoadConst d * (3 / 2 : ℝ) *
          (3 : ℝ) ^ (-((recurrenceGap a M.gamma : ℝ) / 4)) * Cell := by ring
    _ ≤ principalSwitchLoadConst d * (3 / 2 : ℝ) *
          (M.gamma ^ (6 : ℕ) * M.gamma) * Cell := hmul
    _ = principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell * M.gamma *
          M.gamma ^ (6 : ℕ) := by ring
    _ ≤ 1 / 2 * M.gamma ^ (6 : ℕ) := hfin
    _ = M.gamma ^ (6 : ℕ) / 2 := by ring

/-! ## The consumer that no longer binds `hbudget` -/

/-- **The good-event energy display at the actual cutoff carrier, with the
Young-remainder smallness supplied.**

This is
`ApproximateRecurrence.PrincipalResponseLamWire.exists_const_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_centeringConst`
with its binder `hbudget` removed and nothing put in its place.  Every other
binder is unchanged, in the same order and at the same type; the two binders
`W` and `hindep` in particular are untouched.  Because `Cell` occurred only in
`hbudget`, the leading existential `∃ Cell : ℝ, 0 < Cell ∧ _` no longer mentions
its own variable and is dropped; that is a logical equivalence.

The threshold produced here is the one produced there, intersected with `(1/2)
/ (C_load(d). (3/2). Cell)`.  Shrinking an existential threshold is the
manuscript's own "increasing `M` in `e.cgamma.constraints` if necessary" (
with `e.cgamma.constraints` at label): the returned threshold depends only on
the dimension and on the constant `Cell` that `PrincipalResponseLamWire` had
already produced before any model is named.

: this statement holds only under the propositions supplied by its binders,
which are those of the consumer it re-states, minus `hbudget`:

* `hd` -- the paper-wide `2 <= d`;
* `M.gamma <= gamma0`, and the induction state
  `Algsuperdiff.Frozen.Section3.inductionState M m0 Eind`;
* `0 < hgap`, `m - hgap <= m0`, `hgap <= 6 cstar cgamma^{-1}` (/7183) and
  `10^10 cgamma^{-1} <= K - m` (`e.recurrence.params`);
* the two direction bounds `vecNorm e <= 1`, `vecNorm e' <= 1`;
* `2 d^6 <= Ccg C_sens^2`, the numerical lower bound on the constant of
  `e.cg.ellip.lower` (label) described in `PrincipalResponseLamWire`;
* `hle : m - hgap <= highScale`, the scale ordering of the switch;
* the two solution families `hwD`, `hwN` of `e.def.w` (label);
* `hmeasR`, `hintR`, `hgoodInt`, `hcubeInt` -- the four measurability and
  integrability data conditions;
* `hindep` -- the independence replacement, at the free family `W`.

**Deferred obligations, named.**  The earlier sentence here -- "No binder is a
step of the manuscript's proof" -- was false as written and is withdrawn.  Five
of the binders above are deferred obligations of this provider helper rather
than premises of the pinned source statement:

* `hindep` is the *conclusion* of the independence sentence, not a premise of
  it, carried here at a free family `W`.  It is discharged nowhere in this
  module or in any module of its import cone.
* `hmeasR`, `hintR`, `hgoodInt`, `hcubeInt` are conditional A obligations: the
  sample measurability of the ellipticity load, the integrability of its
  square, and the two per-cube integrability families.  None of them is
  discharged here.

`hbudget` -- itself a numerical step of the manuscript's argument rather than a
source premise -- is the one obligation this module does discharge, and it is
accordingly no longer a binder.  Every remaining binder is parameter data,
typing data, a standing scale gate, a direction bound, the numerical gate
`2 d^6 <= Ccg C_sens^2`, or the `e.def.w` solution property of the two
corrector families.

It is a provider A, not a source-facing frozen declaration; it does not derive
`e.lower.bound.principal.one.pre` or any sub-step of
`l.approximate.recurrence.formula` (label).

Reaches exactly the one frozen theorem
`Algsuperdiff.Frozen.External.calderon_zygmund`, a **proved** external,
inherited from the consumer it re-states. -/
theorem exists_gamma0_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_centeringConst
    (d : ℕ) (hd : 2 ≤ d) :
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
  obtain ⟨Cell, hCellpos, gamma0, hg0pos, hg0quarter, hmain⟩ :=
    exists_const_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube_of_centeringConst
      d hd
  have hCs : (0 : ℝ) < principalSwitchLoadConst d :=
    principalSwitchLoadConst_pos hd
  have hBpos : (0 : ℝ) < principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell :=
    mul_pos (by linarith) hCellpos
  refine ⟨min gamma0
    (1 / 2 / (principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell)),
    lt_min hg0pos (by positivity), le_trans (min_le_left _ _) hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' j a ha
    hscale Ccg hccg n highScale hle wD wN hwD hwN hmeasR hintR hgoodInt hcubeInt
    W hindep
  have hsmall : principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell * M.gamma ≤
      1 / 2 := by
    have hthr : M.gamma ≤
        1 / 2 / (principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell) :=
      le_trans hMgamma (min_le_right _ _)
    rw [le_div_iff₀ hBpos] at hthr
    calc principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell * M.gamma
        = M.gamma * (principalSwitchLoadConst d * (3 / 2 : ℝ) * Cell) := by ring
      _ ≤ 1 / 2 := hthr
  exact hmain M (le_trans hMgamma (min_le_left _ _)) m0 Eind hstate m K hgap hhpos
    hm hh hK e e' he he' j a ha hscale Ccg hccg n highScale hle wD wN hwD hwN
    hmeasR hintR hgoodInt hcubeInt W hindep
    (principalSwitchLoadConst_mul_gridSwitchDiscount_mul_le_half_gamma_pow_six hd M
      (originCube d K) j a m (hgap : ℤ) ha hscale hCellpos.le hsmall)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
