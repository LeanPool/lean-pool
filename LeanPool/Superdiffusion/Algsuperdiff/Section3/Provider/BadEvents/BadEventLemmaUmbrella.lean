/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventLemmaFull
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.EllipticityBranchLow

/-!
# BadEventLemmaUmbrella

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The umbrella of `l.bad.event.lemma`, re-assembled through both ellipticity branches

`BadEventLemmaFull.measureReal_compl_goodLocalEvent_le_full_of_coarseBounds`
assembles ABK26's `e.bad.event.Q.estimate` over the full range of `m, n`, but
it routes **both** branches of the coarse-ellipticity half through
`BadEventLemmaCases.measureReal_coarseEllipticityFailure_le_of_coarseBounds`,
which is the branch `n ≥ m`.  On the other branch that is a degeneracy, not a
generalization:

```
n < m = Q.scale   ⟹   scaleGapPos Q.scale n = 0
                  ⟹   3^{(1/4) scaleGapPos Q.scale n} = 1 ,
```

The umbrella is therefore vacuous on `n < m`.  The collapse itself is
machine-checked here (`three_rpow_scaleGapPos_eq_one_of_lt`), so the diagnosis
is not commentary.

This module supplies the missing import edge and re-assembles the umbrella so
that **each branch is served by its own conditional Provider A**.

## The shape of the re-assembly, and why the constant is re-based

`EllipticityBranchLow` delivers its branch at the re-based constant `2 Ccg`
(the gap constant `G(1/8,1/16,2) ≤ 2` of the transfer), i.e. it bounds
`coarseEllipticityFailure M (2 Ccg) Q n`.  The umbrella below is therefore
stated at the good local event `Q(m,n,z)` read at `2 Ccg`, on **both**
branches.  On `n ≥ m` the re-basing costs nothing beyond monotonicity of the
failure event in the constant (`coarseEllipticityFailure_two_mul_subset`,
proved here), so the proved `n ≥ m` branch is consumed at its own constant
`Ccg` and its own binder shape, verbatim.

The two branches deliver different double exponents --- `Ccg^{-1}/4` on `n ≥ m`,
`Ccg^{-1}/8` on `n < m` (the gate's own budget) --- and the umbrella is stated at
the weaker of the two, `Ccg^{-1}/8`, exactly as `EllipticityBranchLow`'s header
predicts.  The `n ≥ m` branch alone remains available at `Ccg^{-1}/4` from
`BadEventLemmaCases`; nothing is lost, and nothing here re-derives either tail.

## The four disclosed conditional binders (no graph status)

Each is **guarded by the branch that needs it**, which is the whole content of
the re-assembly:

* `hmono`, under `Q.scale ≤ n` --- the W cube-monotonicity step.  Under the
  guard the weight `3^{(1/4)(n-m)_+}` is genuine, so the binder is not the
  refuted weight-free statement.  On `n < Q.scale` it is **not assumed at
  all**.
* `hcgHigh`, under `Q.scale ≤ n` --- the conclusion of the frozen
  `Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds` at the centered
  observable, `sigma = 1/2`, `s = 1/8`, `q = 2`, verbatim the binder of
  `BadEventLemmaCases.lean`.
* `hcgLow`, under `n < Q.scale` --- the same frozen conclusion at every
  translate `R ∈ descendantsAtScale Q n` and at the exponent `t = 1/16`,
  verbatim the binder of `EllipticityBranchLow.lean`.

`hrestrict` is the restriction, already guarded by `n < Q.scale` in
`BadEventLemmaFull`, forwarded unchanged.

## The `1 ≤ Ccg` normalization, named precisely

Both branches need `1 ≤ Ccg`, and the frozen `coarse_ellipticity_bounds`
supplies only a positive constant.  The binding constraint is the **low**
branch: its per-translate tail is read at the level `Ccg /
exp(-Ccg^{-1}E^{-2}gamma^{-1})`, which must be `≥ 1` for the weak-Orlicz tail
to apply, and that is exactly `1 ≤ Ccg`
(`EllipticityBranchLow.measureReal_translateCoarseEllipticityTail_le`).  The
high branch needs only `1 ≤ 2 Ccg`.  So the re-assembly **inherits** `1 ≤ Ccg`
unchanged from the two proved branches and adds nothing; it is discharged only
after the frozen theorem is proved with its own choice of constant, exactly as
`BadEventLemmaCases.lean` records.  No step here is blocked by the gap, and no
step here weakens it.

For the record, the gap looks closable in one lemma, which is **not** built
here (it belongs in `Section3/Probability/LowerFamily.lean`, not in a bad-event
umbrella, and it changes how the frozen conclusion is consumed): re-basing the
frozen constant to `max 1 Ccg` needs `IsLowerIntegerFamilyOrlicz` monotone
upward in the deterministic profile `b` (immediate from its `dominates` clause,
`X L ω ≤ b + Y ω`) and in the Orlicz scale `A` (CoarseGraining's proved
`IndependentSums.IsBigOWith.mono_scale`), together with monotonicity of
`lowerEllipticityProfile Ccg gamma s 2 = Ccg s (2s-gamma)^{-1}` in `Ccg`.
Until that lemma exists, `1 ≤ Ccg` stays a binder here, as it already is
upstream.

## What is *not* proved

* **No discharge of `hmono`.**  The centered-cube discharge sketched in
  `BadEventLemmaCases.lean` (`ErrorComparison.lambdaSq_originCube_eighth_le`) is
  a statement about the literal `Ch02.lambdaSq`, not about the inverse
  observables the binder is written against; converting it needs a positivity
  and inversion step that is not performed here.
* **No claim about the printed `B_osc`.**  The oscillation half below is the
  proved `goodLocalSensitivityFailure`, i.e. by definition the complement of
  the event's own first clause (`compl_goodLocalSensitivity_eq`).  The census's
  on the oscillation bound of `l.bad.event.lemma` (the proved event may be a proper
  subset of the printed `B_osc`) is **not** relied on in either direction:
  nothing here asserts that the two events coincide.
* **No sharpening.**  `Ccg^{-1}/8`, `2 Ccg` and `badEventOscLowConst` are the
  proved constants; nothing is optimized.

## Main results

* `coarseEllipticityFailure_two_mul_subset`.
* `measureReal_coarseEllipticityFailure_two_mul_le_of_coarseBounds`: the branch
  `n ≥ m` at the re-based constant and the reconciled exponent.
* `measureReal_compl_goodLocalEvent_le_full_reassembled`: the umbrella over the
  full range, each branch served by its own conditional Provider A.

## References

* ABK26, `l.bad.event.lemma`; `e.bad.event.Q.estimate`;
  `e.bad.event.admissibility`; the decomposition; the case `n ≥ m`; the case
  `n < m`; the recombined display; `e.oscillation.bound`.
  `p.cg.ellipticity.bounds`.  Label-line pins throughout.
* `Provider/BadEvents/BadEventLemmaCases.lean`,
  `Provider/BadEvents/BadEventLemmaFull.lean`,
  `Provider/BadEvents/EllipticityBranchLow.lean`,
  `Provider/BadEvents/GoodLocalEllipticity.lean`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Monotonicity of the failure event in its constant -/

/-- The coarse-ellipticity failure event is antitone in the constant: raising the
threshold shrinks the event.  This is what lets the proved `n ≥ m` branch,
proved at `Ccg`, be read at the re-based constant `2 Ccg`. -/
theorem coarseEllipticityFailure_two_mul_subset (M : ABKModel d) {Ccg : ℝ}
    (hCcg : 0 ≤ Ccg) (Q : TriadicCube d) (n : ℤ) :
    coarseEllipticityFailure M (2 * Ccg) Q n ⊆ coarseEllipticityFailure M Ccg Q n := by
  intro omega homega
  have h3 : (0 : ℝ) < (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hstep : 2 * (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) * Ccg ≤
      2 * (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) * (2 * Ccg) := by
    nlinarith
  exact lt_of_le_of_lt hstep homega

/-! ## The branch `n ≥ m`, at the re-based constant and the reconciled exponent -/

/-- **The case `n ≥ m` of the coarse-ellipticity branch**, read at the re-based
constant `2 Ccg` and at the exponent `Ccg^{-1}/8` at which the two branches
meet:

```
P[ lambda^{-1}_{1/8,2}(z+square_m; a_n) sigmabar_{n-1} > 2 . 3^{(1/4)(n-m)_+} (2 Ccg) ]
  <= exp( - exp( (1/8) Ccg^{-1} E^{-2} gamma^{-1} ) ) .
```

Both weakenings are theorems: the event shrinks when the constant is doubled
(`coarseEllipticityFailure_two_mul_subset`), and `exp((1/8)X) ≤ exp((1/4)X)` for
`X ≥ 0`.  The binders are those of
`BadEventLemmaCases.measureReal_coarseEllipticityFailure_le_of_coarseBounds`,
verbatim and at the un-re-based `Ccg`. -/
theorem measureReal_coarseEllipticityFailure_two_mul_le_of_coarseBounds (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 1 ≤ Ccg) (Q : TriadicCube d) {n : ℤ} {E : ℝ}
    (hgamma : M.gamma ≤ 1 / 8)
    (hmono : ∀ omega : CutoffSample d,
      cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
        (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) *
          Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n n (1 / 8)
            (by norm_num) exponentTwo omega)
    (hcg : Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
      (Cutoff.cutoffSampleLaw M).toMeasure
      (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
      (fun L : ℤ => fun omega =>
        Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n L (1 / 8)
            (by norm_num) exponentTwo omega *
          (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
      (n - 1)
      (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 8)
        exponentTwo)
      (Real.exp (-(Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹)))) :
    (cutoffSampleLaw M).toMeasure.real (coarseEllipticityFailure M (2 * Ccg) Q n) ≤
      Real.exp (-Real.exp ((1 / 8 : ℝ) * (Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))) := by
  have hCcg0 : (0 : ℝ) < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hXnn : (0 : ℝ) ≤ Ccg⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹ := by
    have h1 : (0 : ℝ) ≤ Ccg⁻¹ := (inv_pos.2 hCcg0).le
    have h3 : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.2 hg).le
    positivity
  have hsub : (cutoffSampleLaw M).toMeasure.real
      (coarseEllipticityFailure M (2 * Ccg) Q n) ≤
      (cutoffSampleLaw M).toMeasure.real (coarseEllipticityFailure M Ccg Q n) :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (coarseEllipticityFailure_two_mul_subset M hCcg0.le Q n))
  refine le_trans hsub
    (le_trans (measureReal_coarseEllipticityFailure_le_of_coarseBounds M hCcg Q hgamma
      hmono hcg) ?_)
  refine Real.exp_le_exp.2 (neg_le_neg (Real.exp_le_exp.2 ?_))
  linarith

/-! ## The umbrella over the full range, each branch on its own conditional A -/

/-- **`l.bad.event.lemma` over the full range of `m, n`, re-assembled** (ABK26,
`e.bad.event.Q.estimate`), at the re-based constant `2 Ccg`:

```
P[ not Q(m,n,z) ]
  <= exp( - c c_star gamma^{-1} 3^{-5(m-n)_+} 3^{(n-m)_+} )
     + exp( - exp( (1/8) Ccg^{-1} E^{-2} gamma^{-1} ) ) ,
```

with `c = badEventOscLowConst d (2 Ccg)`, dimension-only.

Unlike
`BadEventLemmaFull.measureReal_compl_goodLocalEvent_le_full_of_coarseBounds`,
the coarse-ellipticity half is served on `n < Q.scale` by
`EllipticityBranchLow.measureReal_coarseEllipticityFailure_le_printed_of_gap`
rather than by the `n ≥ m` branch, whose `hmono` binder degenerates there to a
refuted statement (`three_rpow_scaleGapPos_eq_one_of_lt`).  Accordingly `hmono`
and the centered `hcg` are hypothesised only under `Q.scale ≤ n`, and the
translate `hcg` and the entropy gate only under `n < Q.scale`.

The two `hcg` binders have the shape of specializations of the proved
`p.cg.ellipticity.bounds`, but this statement does not itself perform their
translated-carrier discharge; `hgap` and `hrestrict` restrict the two
branches. -/
theorem measureReal_compl_goodLocalEvent_le_full_reassembled (M : ABKModel d)
    {Ccg : ℝ} (hCcg : 1 ≤ Ccg) (Q : TriadicCube d) {n m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E)
    (hn : n ≤ m0 - 1)
    (hadm : badEventOscLowAdmissibleConst d (2 * Ccg) ≤
      (E : ℝ) * Algsuperdiff.Section3.Disorder.cstar M)
    (hgammaE : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ))
    (hrestrict : n < Q.scale → 1 ≤ badEventOscFullRate M (2 * Ccg) Q n)
    (hmono : Q.scale ≤ n → ∀ omega : CutoffSample d,
      cubeLowerEllipticityInv M Q n (1 / 8) (by norm_num) exponentTwo omega ≤
        (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos Q.scale n) *
          Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n n (1 / 8)
            (by norm_num) exponentTwo omega)
    (hcgHigh : Q.scale ≤ n →
      Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
        (fun L : ℤ => fun omega =>
          Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv M n L (1 / 8)
              (by norm_num) exponentTwo omega *
            (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
        (n - 1)
        (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 8)
          exponentTwo)
        (Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))))
    (hcgLow : n < Q.scale → ∀ R ∈ descendantsAtScale Q n,
      Algsuperdiff.Section3.Probability.IsLowerIntegerFamilyOrlicz
        (Cutoff.cutoffSampleLaw M).toMeasure
        (HCPolySupport.IndependentSums.gammaSigma ((1 - 1 / 2) / 2))
        (fun L : ℤ => fun omega =>
          cubeLowerEllipticityInv M R L (1 / 16) (by norm_num) exponentTwo omega *
            (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ))
        (n - 1)
        (Algsuperdiff.Section3.lowerEllipticityProfile Ccg M.gamma (1 / 16)
          exponentTwo)
        (Real.exp (-(Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))))
    (hgap : n < Q.scale →
      (d : ℝ) * ((Q.scale : ℝ) - (n : ℝ)) * Real.log 3 +
          Real.exp ((1 / 8 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
        Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) :
    (cutoffSampleLaw M).toMeasure.real (goodLocalEvent M (2 * Ccg) Q n)ᶜ ≤
      Real.exp (-(badEventOscFullRate M (2 * Ccg) Q n)) +
        Real.exp (-Real.exp ((1 / 8 : ℝ) *
          (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  have hCcg0 : (0 : ℝ) < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  have hCcg20 : (0 : ℝ) < 2 * Ccg := by linarith
  have hadm' : badEventOscAdmissibleConst d (2 * Ccg) ≤
      (E : ℝ) * Algsuperdiff.Section3.Disorder.cstar M :=
    le_trans (badEventOscAdmissibleConst_le_badEventOscLowAdmissibleConst d hCcg20)
      hadm
  refine le_trans (measureReal_compl_goodLocalEvent_le M hCcg20 Q n) ?_
  refine add_le_add ?_ ?_
  · exact measureReal_goodLocalSensitivityFailure_le_full_of_admissible M hCcg20 Q
      hS hn hadm hgammaE hrestrict
  · rcases le_or_gt Q.scale n with hmn | hmn
    · exact measureReal_coarseEllipticityFailure_two_mul_le_of_coarseBounds M hCcg Q
        (gamma_le_one_eighth_of_admissible M hadm' hgammaE) (hmono hmn) (hcgHigh hmn)
    · exact measureReal_coarseEllipticityFailure_le_printed_of_gap M hCcg Q hmn
        (gamma_le_one_sixteenth_of_admissible M hadm' hgammaE) (hcgLow hmn) (hgap hmn)

end

end Algsuperdiff.Section3.Provider.BadEvents
