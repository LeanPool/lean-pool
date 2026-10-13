/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.UnionAggregation
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.UnionSubadditivity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.Maximum

/-!
# UnionCompletion

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Completion of the Section 3.5 cutoff union

This module performs the last two steps of the cutoff-union argument of ABK26
(proof of `p.homogenization.step`): the passage from one fixed direction to
*all* directions, and the final fold of constants into the shape of the Section
3.5 conclusion.

The proved endpoint `exists_unionGridAverageCommonEnvelope`
(`Provider/Homogenization/UnionAggregation.lean`) aggregates the grid displays
over the infinite cutoff family at **one** unit direction.  The proved
pointwise reduction `ae_forall_cutoffResponseJ_le_directionNet`
(`Provider/Homogenization/UnionDirectionNet.lean`) reduces an arbitrary unit
direction to the `d` coordinate directions at the cost `2 ^ d * d`.  What was
missing between them is a countable family carrying all `d` coordinate
directions *at once*, and the arithmetic that turns the two amplitudes into the
printed `epsilon E^2 gamma` and `epsilon exp(-2 E^{-3} gamma^{-1})`.

## The direction wiring, and the route chosen

The two admissible routes are: re-index the family by `ℕ × Fin d`, or replace
each member by the finite sum over the `d` directions through the finite
`Gamma_sigma` triangle.  **The route taken here is the re-indexing by `ℕ × Fin
d`**, realized *without* a `Denumerable` transport and *without* re-deriving
the aggregation: the proved one-direction endpoint is consumed `d` times, once
at each `Pi.single i (1 : ℝ)`, and the `d` resulting common-event bounds are
merged by the new abstract combinator
`isCommonEventTwoTermBigOWith_prod_of_fintype`, whose two envelopes are the
finite `Finset.sup'` of the given ones.

This keeps `Probability.IsCommonEventTwoTermBigOWith` exact --- one pair of
measurable envelopes, one event of probability one, two separate one-sided
tails, lanes never merged --- and the amplitudes `C(d)`-clean: the only price
is one factor `(3 max(1, log d))^{1/sigma}` per lane, supplied by the proved
finite-maximum estimate `Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty`,
which is a constant depending on `d` alone and is absorbed into the module's
`Cunion`.  The alternative finite-sum route was not taken because it would pay
a `gammaTriangleConst` per direction *inside* the countable aggregation and
would require rebuilding the per-member two-term display.

## The fold

`exists_gridDecay_mul_le` (`UnionAggregation.lean`) chooses the separation `k2`
so that the grid gain `3 ^ (-d k2 / 2)` beats `epsilon / 2` after the direction
cost; `k2` is then enlarged by one so that the printed corridor condition `1 <=
k1 + k2` holds.  `epsilon` is split in half between the two fluctuation lanes
and the deterministic mean.  Because the direction net multiplies the *mean* as
well, the iteration is run at the shrunken tolerance `epsilon / (2 ^ d * d)`,
which is the second of the two absorption places recorded in the direction-net
module.  The deterministic mean is absorbed by
`isCommonEventTwoTermBigOWith_add_const` and the amplitudes are relaxed to the
printed ones by `isCommonEventTwoTermBigOWith_mono_scale`.  The printed budget
`k = k1 + k2 <= C(d) |log epsilon|` is discharged in `union_budget_bound`,
against `|log epsilon| >= log 2 >= 1/2`, which is where `epsilon <= 1/2` is
used.

The constant `Chom` produced here is `max 64 (max (Citer * 2^d d) (Citer + 1 +
2 Q))` with `Q` built from `log(2 ^ d d)`, `log Cunion` and `log 2`; it is
chosen before the model, the scale, the tolerance and the direction, and it
unfolds to `d`, `Cunion` and the iteration's own constant only.  All three
occurrences of `Chom` in the Section 3.5 statement point the same way:
enlarging it strengthens the smallness binder, shrinks the index set, and
relaxes `1 <= Chom`.

## What fixes `k1`

ABK26 sets `k1 := ceil(alpha^{-1} log_3(4 epsilon^{-1} C))` where `alpha(d)` and
`C(d)` are the exponent and constant of the iterated recurrence `e.iter.post`.
Neither `alpha` nor that `C` exists in this repository --- they are outputs of
the separate node `p.homogenization.step#iterate` --- so `k1` is **not** derived
here.  It is bound existentially, together with its budget, inside the
single conditional A obligation below, in exactly the shape the iteration
delivers.

## Scope facts, inherited and disclosed

* The direction cost is `2 ^ d * d` rather than the printed `d`: the
  coordinate net replaces the sign vertices.  Both are `C(d)`.
* The cutoff family deliberately omits the printed `n <= m - 1`: at `k2 = j =
  0` its observation scale is `n = m`.  This strengthening is inherited from
  the proved two-lane transport.
* The two-sided `IsBigO` of the consumed envelope engine where the printed
  statement is one-sided,
  the `(3 ^ d + 1) ^ d` colour stride, the CoarseGraining `gammaTriangleConst`
  centering constant, and the numerals `1/16` and `1/8` are all inherited
  from the consumed statements, not introduced here.

The data are `M : ABKModel d`, together with `d`, `m`, `E`, `k1`, `k2`,
`epsilon`, `Chom`, the abstract carriers of the two combinators, and the
`meanBound` slot of the domination lemma.  The only numerals fixed by hand are
the two numerals already fixed by the proved transport.

## References

* ABK26, Proposition `p.homogenization.step`, proof; in particular the choices
  `k1`, `k2`, `k = k1 + k2` and `n = L + k1`, the post-iteration display
  `e.iter.post.new`, the union bound `e.union.bound.fluct`, the subadditivity
  and final absorption, and the budget.
* ABK26, Appendix.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

/-! ## Two further pieces of the common-event two-term A -/

section Abstract

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A common-event two-term bound scales by a positive constant: both
amplitudes are multiplied by it, and the two envelopes are multiplied by it as
well, so the single domination event is unchanged. -/
theorem isCommonEventTwoTermBigOWith_const_mul {I : Type*}
    {Psi1 Psi2 : ℝ → ℝ} {X : I → Omega → ℝ} {A1 A2 c : ℝ} (hc : 0 < c)
    (hX : Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2 X A1 A2) :
    Probability.IsCommonEventTwoTermBigOWith mu Psi1 Psi2
      (fun i omega => c * X i omega) (c * A1) (c * A2) := by
  obtain ⟨Y, Z, hPsi1, hPsi2, hA1, hA2, hXm, hYm, hZm, hdom, hYt, hZt⟩ := hX
  refine ⟨fun omega => c * Y omega, fun omega => c * Z omega, hPsi1, hPsi2,
    mul_pos hc hA1, mul_pos hc hA2, fun i => (hXm i).const_mul c,
    hYm.const_mul c, hZm.const_mul c, ?_, hYt.const_mul hc.le,
    hZt.const_mul hc.le⟩
  filter_upwards [hdom] with omega homega
  intro i
  linarith [mul_le_mul_of_nonneg_left (homega i) hc.le]

/-- **Merging finitely many common-event two-term bounds.**

Given one common-event two-term bound for each member of a finite nonempty
family, at one common pair of amplitudes, the whole product family carries a
single common-event two-term bound.  The two envelopes are the finite maxima of
the given ones, and the amplitudes pay the finite-maximum weak-Orlicz cost
`(3 max(1, log N))^{1/sigma}` of `Provider/Orlicz/Maximum.lean`.

Only one further null set is spent, namely the finite intersection of the
given domination events; the index of the inner family stays inside the
event. -/
theorem isCommonEventTwoTermBigOWith_prod_of_fintype {I J : Type*}
    [IsFiniteMeasure mu] [Fintype J] [Nonempty J] {sigmaOne sigmaTwo : ℝ}
    (hsigmaOne : 0 < sigmaOne) (hsigmaTwo : 0 < sigmaTwo)
    {W : J → I → Omega → ℝ} {A1 A2 : ℝ}
    (hW : ∀ b : J, Probability.IsCommonEventTwoTermBigOWith mu
      (gammaSigma sigmaOne) (gammaSigma sigmaTwo) (W b) A1 A2) :
    Probability.IsCommonEventTwoTermBigOWith mu
      (gammaSigma sigmaOne) (gammaSigma sigmaTwo)
      (fun p : I × J => W p.2 p.1)
      ((3 * max 1 (Real.log (Fintype.card J : ℝ))) ^ sigmaOne⁻¹ * A1)
      ((3 * max 1 (Real.log (Fintype.card J : ℝ))) ^ sigmaTwo⁻¹ * A2) := by
  classical
  choose Y Z hwit using hW
  have hA1 : 0 < A1 := (hwit (Classical.arbitrary J)).2.2.1
  have hA2 : 0 < A2 := (hwit (Classical.arbitrary J)).2.2.2.1
  have hWm : ∀ b : J, ∀ i : I, Measurable (W b i) :=
    fun b => (hwit b).2.2.2.2.1
  have hYm : ∀ b : J, Measurable (Y b) := fun b => (hwit b).2.2.2.2.2.1
  have hZm : ∀ b : J, Measurable (Z b) := fun b => (hwit b).2.2.2.2.2.2.1
  have hdom : ∀ b : J, ∀ᵐ omega ∂mu, ∀ i : I, W b i omega ≤ Y b omega + Z b omega :=
    fun b => (hwit b).2.2.2.2.2.2.2.1
  have hYt : ∀ b : J, IsBigOWith mu (gammaSigma sigmaOne) (Y b) A1 :=
    fun b => (hwit b).2.2.2.2.2.2.2.2.1
  have hZt : ∀ b : J, IsBigOWith mu (gammaSigma sigmaTwo) (Z b) A2 :=
    fun b => (hwit b).2.2.2.2.2.2.2.2.2
  have hne : (Finset.univ : Finset J).Nonempty := Finset.univ_nonempty
  have hcard : ((Finset.univ : Finset J).card : ℝ) = (Fintype.card J : ℝ) := by
    rw [Finset.card_univ]
  have hbase : (1 : ℝ) ≤ 3 * max 1 (Real.log (Fintype.card J : ℝ)) := by
    have : (1 : ℝ) ≤ max 1 (Real.log (Fintype.card J : ℝ)) := le_max_left _ _
    linarith
  have hpow1 : (0 : ℝ) < (3 * max 1 (Real.log (Fintype.card J : ℝ))) ^ sigmaOne⁻¹ :=
    Real.rpow_pos_of_pos (by linarith) _
  have hpow2 : (0 : ℝ) < (3 * max 1 (Real.log (Fintype.card J : ℝ))) ^ sigmaTwo⁻¹ :=
    Real.rpow_pos_of_pos (by linarith) _
  have hYsup : Measurable fun omega => (Finset.univ : Finset J).sup' hne
      fun b => Y b omega := by
    have hmeas : Measurable ((Finset.univ : Finset J).sup' hne Y) :=
      Finset.measurable_sup' hne fun b _ => hYm b
    have heq : (fun omega => (Finset.univ : Finset J).sup' hne fun b => Y b omega) =
        (Finset.univ : Finset J).sup' hne Y := by
      funext omega
      rw [Finset.sup'_apply]
    rw [heq]
    exact hmeas
  have hZsup : Measurable fun omega => (Finset.univ : Finset J).sup' hne
      fun b => Z b omega := by
    have hmeas : Measurable ((Finset.univ : Finset J).sup' hne Z) :=
      Finset.measurable_sup' hne fun b _ => hZm b
    have heq : (fun omega => (Finset.univ : Finset J).sup' hne fun b => Z b omega) =
        (Finset.univ : Finset J).sup' hne Z := by
      funext omega
      rw [Finset.sup'_apply]
    rw [heq]
    exact hmeas
  have hYtail := Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (μ := mu) (Finset.univ : Finset J) hne (X := Y) (A := A1) (σ := sigmaOne)
    hsigmaOne hA1.le fun b _ => hYt b
  have hZtail := Provider.Orlicz.isBigOWith_gammaSigma_finset_sup'_of_nonempty
    (μ := mu) (Finset.univ : Finset J) hne (X := Z) (A := A2) (σ := sigmaTwo)
    hsigmaTwo hA2.le fun b _ => hZt b
  rw [hcard] at hYtail hZtail
  refine ⟨fun omega => (Finset.univ : Finset J).sup' hne fun b => Y b omega,
    fun omega => (Finset.univ : Finset J).sup' hne fun b => Z b omega,
    (hwit (Classical.arbitrary J)).1, (hwit (Classical.arbitrary J)).2.1,
    mul_pos hpow1 hA1, mul_pos hpow2 hA2,
    fun p => hWm p.2 p.1, hYsup, hZsup, ?_, hYtail, hZtail⟩
  have hall : ∀ᵐ omega ∂mu, ∀ b : J, ∀ i : I,
      W b i omega ≤ Y b omega + Z b omega := (MeasureTheory.ae_all_iff).2 hdom
  filter_upwards [hall] with omega homega
  intro p
  refine (homega p.2 p.1).trans (add_le_add ?_ ?_)
  · exact Finset.le_sup' (fun b => Y b omega) (Finset.mem_univ p.2)
  · exact Finset.le_sup' (fun b => Z b omega) (Finset.mem_univ p.2)

end Abstract

/-! ## The union family carrying all `d` coordinate directions -/

section AllDirections

/-- **The Section 3.5 cutoff-union display, at all `d` coordinate directions
at once.**

The proved endpoint `exists_unionGridAverageCommonEnvelope` holds one unit
direction fixed.  Applying it at each of the `d` coordinate directions and
merging the `d` resulting common-event bounds by
`isCommonEventTwoTermBigOWith_prod_of_fintype` re-indexes the family by `ℕ ×
Fin d`, at the cost of one factor `(3 max(1, log d))^{1/sigma}` on each lane,
which is a constant depending only on `d` and is absorbed into `Cunion`.

Nothing in the proved endpoint is re-derived: it is consumed `d` times. -/
theorem exists_unionGridAverageAllDirectionsCommonEnvelope (d : ℕ) :
    ∃ Cunion : ℝ, 0 < Cunion ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 →
        ∀ k1 k2 : ℕ, 1 ≤ k1 + k2 →
          Probability.IsCommonEventTwoTermBigOWith
            (cutoffSampleLaw M).toMeasure (gammaSigma 1) (gammaSigma (1 / 4))
            (fun p : ℕ × Fin d =>
              unionGridAverage M m k1 k2 p.1 (Pi.single p.2 (1 : ℝ)))
            (Cunion * ((E : ℝ) ^ 2 * M.gamma) * gridDecay d k2)
            (Cunion *
              Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) * gridDecay d k2) := by
  classical
  obtain ⟨C0, hC0pos, hC0⟩ := exists_unionGridAverageCommonEnvelope d
  have hbase : (1 : ℝ) ≤ 3 * max 1 (Real.log (d : ℝ)) := by
    have : (1 : ℝ) ≤ max 1 (Real.log (d : ℝ)) := le_max_left _ _
    linarith
  have hnet : (0 : ℝ) < (3 * max 1 (Real.log (d : ℝ))) ^ (4 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  refine ⟨(3 * max 1 (Real.log (d : ℝ))) ^ (4 : ℝ) * C0,
    mul_pos hnet hC0pos, ?_⟩
  intro M m E hLower hWindow k1 k2 hsep
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmerge := isCommonEventTwoTermBigOWith_prod_of_fintype
    (mu := (cutoffSampleLaw M).toMeasure) (I := ℕ) (J := Fin d)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 4)
    (W := fun b : Fin d => fun j : ℕ =>
      unionGridAverage M m k1 k2 j (Pi.single b (1 : ℝ)))
    (fun b => hC0 M m E hLower hWindow k1 k2 hsep (Pi.single b (1 : ℝ))
      (vecNorm_single_one b))
  rw [Fintype.card_fin] at hmerge
  have hgammann : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hgd : (0 : ℝ) ≤ gridDecay d k2 := (gridDecay_pos d k2).le
  have hone : (3 * max 1 (Real.log (d : ℝ))) ^ (1 : ℝ) ≤
      (3 * max 1 (Real.log (d : ℝ))) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  refine isCommonEventTwoTermBigOWith_mono_scale hmerge ?_ ?_
  · have hinv : ((1 : ℝ))⁻¹ = (1 : ℝ) := by norm_num
    rw [hinv]
    have hX : (0 : ℝ) ≤ C0 * ((E : ℝ) ^ 2 * M.gamma) * gridDecay d k2 :=
      mul_nonneg (mul_nonneg hC0pos.le (mul_nonneg (sq_nonneg _) hgammann)) hgd
    calc (3 * max 1 (Real.log (d : ℝ))) ^ (1 : ℝ) *
          (C0 * ((E : ℝ) ^ 2 * M.gamma) * gridDecay d k2)
        ≤ (3 * max 1 (Real.log (d : ℝ))) ^ (4 : ℝ) *
            (C0 * ((E : ℝ) ^ 2 * M.gamma) * gridDecay d k2) :=
          mul_le_mul_of_nonneg_right hone hX
      _ = (3 * max 1 (Real.log (d : ℝ))) ^ (4 : ℝ) * C0 *
            ((E : ℝ) ^ 2 * M.gamma) * gridDecay d k2 := by ring
  · have hinv : ((1 / 4 : ℝ))⁻¹ = (4 : ℝ) := by norm_num
    rw [hinv]
    exact le_of_eq (by ring)

end AllDirections

/-! ## The pointwise domination of the Section 3.5 response family -/

section Domination

variable {d : ℕ}

/-- **The composed pointwise domination.**

On one probability-one event, simultaneously for every admissible cutoff scale
`L` and *every* Euclidean unit direction, the Section 3.5 response at the
parent cube `square_m` is bounded by `2 ^ d * d` times one member of the
all-directions union family, shifted by `2 ^ d * d` times the mean bound.

The budget hypothesis `hbudget` is what converts the printed separation `L <= m
- k` with `k = k1 + k2` into the frozen statement's own restriction `L <= m -
Chom |log epsilon|`.

Two null sets are spent beyond those of the consumed statements: the direction
net's single event, and the countable intersection over `ℤ × Fin d` of the
recentred subadditivity events.  The uncountable direction quantifier stays
inside the event. -/
theorem ae_forall_cutoffResponseJ_le_unionGridAverageAllDirections
    (M : ABKModel d) (m : ℤ) (k1 k2 : ℕ) (hsep : 1 ≤ k1 + k2)
    (Chom epsilon meanBound : ℝ)
    (hbudget : ((k1 : ℝ) + (k2 : ℝ)) ≤ Chom * |Real.log epsilon|)
    (hmean : ∀ L : ℤ, L ≤ m - 1 → L + (k1 : ℤ) ≤ m → ∀ b : Fin d,
      ∫ omega, Observable.cutoffResponseJ M (L + k1) L (Pi.single b (1 : ℝ)) omega
          ∂(cutoffSampleLaw M).toMeasure ≤ meanBound) :
    ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ i : {p : ℤ × {v : Vec d // Ch02.vecNorm v = 1} //
          (p.1 : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon|},
        ∃ p : ℕ × Fin d,
          Observable.cutoffResponseJ M m i.1.1 i.1.2.1 omega ≤
            2 ^ d * (d : ℝ) *
                unionGridAverage M m k1 k2 p.1 (Pi.single p.2 (1 : ℝ)) omega +
              2 ^ d * (d : ℝ) * meanBound := by
  classical
  have hsub : ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
      ∀ (L : ℤ) (b : Fin d), L + k1 ≤ m →
        Observable.cutoffResponseJ M m L (Pi.single b (1 : ℝ)) omega ≤
          |((cubeFinset (d := d) (m - (L + k1)).toNat).card : ℝ)⁻¹ *
              ∑ u ∈ cubeFinset (d := d) (m - (L + k1)).toNat,
                siteCenteredResponseJ M L (L + k1) u (Pi.single b (1 : ℝ)) omega| +
            ∫ omega', Observable.cutoffResponseJ M (L + k1) L
                (Pi.single b (1 : ℝ)) omega'
              ∂(cutoffSampleLaw M).toMeasure := by
    rw [MeasureTheory.ae_all_iff]
    intro L
    rw [MeasureTheory.ae_all_iff]
    intro b
    by_cases hle : L + k1 ≤ m
    · filter_upwards
        [ae_cutoffResponseJ_le_abs_gridAverage_siteCenteredResponseJ_add_integral
          M m (L + k1) L hle (Pi.single b (1 : ℝ))] with omega homega
      exact fun _ => homega
    · exact Filter.Eventually.of_forall fun _ hcon => absurd hcon hle
  filter_upwards [ae_forall_cutoffResponseJ_le_directionNet M m, hsub]
    with omega hdir hsubomega
  intro i
  have hLreal : ((i.1.1 : ℤ) : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon| := i.2
  have hLcast : ((i.1.1 : ℤ) : ℝ) ≤ ((m - (k1 : ℤ) - (k2 : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith
  have hLint : i.1.1 ≤ m - (k1 : ℤ) - (k2 : ℤ) := by exact_mod_cast hLcast
  have hnn : (0 : ℤ) ≤ m - (k1 : ℤ) - (k2 : ℤ) - i.1.1 := by omega
  have hsepint : (1 : ℤ) ≤ (k1 : ℤ) + (k2 : ℤ) := by exact_mod_cast hsep
  have hjcast : (((m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat : ℕ) : ℤ) =
      m - (k1 : ℤ) - (k2 : ℤ) - i.1.1 := Int.toNat_of_nonneg hnn
  obtain ⟨b, hb⟩ := hdir i.1.1 i.1.2.1 i.1.2.2
  refine ⟨((m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat, b), ?_⟩
  have hgrid : unionGridAverage M m k1 k2
        (m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat (Pi.single b (1 : ℝ)) omega =
      |((cubeFinset (d := d) (m - (i.1.1 + k1)).toNat).card : ℝ)⁻¹ *
        ∑ u ∈ cubeFinset (d := d) (m - (i.1.1 + k1)).toNat,
          siteCenteredResponseJ M i.1.1 (i.1.1 + k1) u
            (Pi.single b (1 : ℝ)) omega| := by
    have h1 : unionCutoffScale m k1 k2
        (m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat = i.1.1 := by
      simp only [unionCutoffScale]
      omega
    have h2 : unionObservationScale m k2
        (m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat = i.1.1 + k1 := by
      simp only [unionObservationScale]
      omega
    have h3 : (m - (i.1.1 + k1)).toNat =
        k2 + (m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat := by omega
    simp only [unionGridAverage, h1, h2, h3]
  have hle : i.1.1 + (k1 : ℤ) ≤ m := by omega
  have hLm1 : i.1.1 ≤ m - 1 := by omega
  have hcoeff : (0 : ℝ) ≤ 2 ^ d * (d : ℝ) := by positivity
  have hmid : Observable.cutoffResponseJ M m i.1.1 (Pi.single b (1 : ℝ)) omega ≤
      unionGridAverage M m k1 k2
        (m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat (Pi.single b (1 : ℝ)) omega +
        meanBound := by
    rw [hgrid]
    have h := hsubomega i.1.1 b hle
    have hm := hmean i.1.1 hLm1 hle b
    linarith
  calc Observable.cutoffResponseJ M m i.1.1 i.1.2.1 omega
      ≤ 2 ^ d * (d : ℝ) *
          Observable.cutoffResponseJ M m i.1.1 (Pi.single b (1 : ℝ)) omega := hb
    _ ≤ 2 ^ d * (d : ℝ) *
          (unionGridAverage M m k1 k2
            (m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat (Pi.single b (1 : ℝ)) omega +
            meanBound) := mul_le_mul_of_nonneg_left hmid hcoeff
    _ = 2 ^ d * (d : ℝ) *
          unionGridAverage M m k1 k2
            (m - (k1 : ℤ) - (k2 : ℤ) - i.1.1).toNat
            (Pi.single b (1 : ℝ)) omega +
          2 ^ d * (d : ℝ) * meanBound := by ring

end Domination


/-! ## The constant fold -/

section Fold

/-- Below one half the logarithm has absolute value at least `log 2`. -/
private theorem log_two_le_abs_log {epsilon : ℝ}
    (heps : epsilon ∈ Set.Ioc 0 (1 / 2)) :
    Real.log 2 ≤ |Real.log epsilon| := by
  have hhalf : Real.log epsilon ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log heps.1 heps.2
  have hval : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hval] at hhalf
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- The base-three logarithm exceeds one, which is what makes the geometric
separation of `exists_gridDecay_mul_le` cost at most one unit of
`|log epsilon|` per dimension. -/
private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  linarith [Real.exp_one_lt_d9]

/-- The manuscript smallness binder `gamma <= Chom^{-1} E^{-2} epsilon`, read at
`Chom >= 64`, `E >= 1` and `epsilon <= 1/2`, already forces `gamma <= 1/128`. -/
private theorem gamma_le_of_smallness {Chom Escale epsilon gamma : ℝ}
    (hChom : 64 ≤ Chom) (hE : 1 ≤ Escale)
    (heps : epsilon ∈ Set.Ioc 0 (1 / 2))
    (hgamma : gamma ≤ Chom⁻¹ * (Escale⁻¹) ^ 2 * epsilon) : gamma ≤ 1 / 128 := by
  have hChompos : (0 : ℝ) < Chom := by linarith
  have hChominv : Chom⁻¹ ≤ 1 / 64 :=
    (inv_anti₀ (by norm_num : (0 : ℝ) < 64) hChom).trans (by norm_num)
  have hEpos : (0 : ℝ) < Escale := by linarith
  have hEinv : Escale⁻¹ ≤ 1 := by
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hE
  have hEinvnn : (0 : ℝ) ≤ Escale⁻¹ := le_of_lt (inv_pos.2 hEpos)
  have hEsq : (Escale⁻¹) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hEinvnn hEinv 2
  have hstep : Chom⁻¹ * (Escale⁻¹) ^ 2 * epsilon ≤ 1 / 64 * 1 * (1 / 2) :=
    mul_le_mul (mul_le_mul hChominv hEsq (sq_nonneg _) (by norm_num)) heps.2
      heps.1.le (by norm_num)
  linarith

/-- Transfer of the smallness binder to the tolerance at which the iteration is
run.  Shrinking the tolerance by the direction cost is paid for by enlarging
`Chom` by the same factor. -/
private theorem gamma_le_iterate_smallness {Chom Citer Dcost Escale epsilon gamma : ℝ}
    (hCiter : 1 ≤ Citer) (hD : 1 ≤ Dcost) (hCD : Citer * Dcost ≤ Chom)
    (hepspos : 0 < epsilon)
    (hgamma : gamma ≤ Chom⁻¹ * (Escale⁻¹) ^ 2 * epsilon) :
    gamma ≤ Citer⁻¹ * (Escale⁻¹) ^ 2 * (epsilon / Dcost) := by
  have hCDpos : (0 : ℝ) < Citer * Dcost := mul_pos (by linarith) (by linarith)
  have hinvle : Chom⁻¹ ≤ (Citer * Dcost)⁻¹ := inv_anti₀ hCDpos hCD
  have hfac : (0 : ℝ) ≤ (Escale⁻¹) ^ 2 * epsilon :=
    mul_nonneg (sq_nonneg _) hepspos.le
  have hmono : Chom⁻¹ * (Escale⁻¹) ^ 2 * epsilon ≤
      (Citer * Dcost)⁻¹ * (Escale⁻¹) ^ 2 * epsilon := by
    calc Chom⁻¹ * (Escale⁻¹) ^ 2 * epsilon
        = Chom⁻¹ * ((Escale⁻¹) ^ 2 * epsilon) := by ring
      _ ≤ (Citer * Dcost)⁻¹ * ((Escale⁻¹) ^ 2 * epsilon) :=
          mul_le_mul_of_nonneg_right hinvle hfac
      _ = (Citer * Dcost)⁻¹ * (Escale⁻¹) ^ 2 * epsilon := by ring
  have hsplit : (Citer * Dcost)⁻¹ * (Escale⁻¹) ^ 2 * epsilon =
      Citer⁻¹ * (Escale⁻¹) ^ 2 * (epsilon / Dcost) := by
    rw [mul_inv, div_eq_mul_inv]
    ring
  linarith [hsplit ▸ hmono]

/-- **The printed logarithmic budget** `k = k1 + k2 <= C(d) |log epsilon|` of
ABK26, at the two separations actually produced: `k1` by the finite-corridor
iteration, run at the shrunken tolerance `epsilon / Dcost`, and `k2` by
`exists_gridDecay_mul_le`, enlarged by one so that the corridor condition `1 <=
k1 + k2` holds.

The additive constants are absorbed against `|log epsilon| >= log 2 >= 1/2`,
which is where `epsilon <= 1/2` is used. -/
private theorem union_budget_bound {d : ℕ} (hd2 : 2 ≤ d)
    {Citer Dcost c1 epsilon : ℝ} (hCiter : 1 ≤ Citer) (hD : 1 ≤ Dcost)
    (hc1 : 1 ≤ c1) (heps : epsilon ∈ Set.Ioc 0 (1 / 2)) {k1 k2zero : ℕ}
    (hk1 : (k1 : ℝ) ≤ Citer * |Real.log (epsilon / Dcost)|)
    (hk2 : (k2zero : ℝ) ≤
      1 + |2 * Real.log (c1 / (epsilon / 2)) / ((d : ℝ) * Real.log 3)|) :
    ((k1 : ℝ) + ((k2zero + 1 : ℕ) : ℝ)) ≤
      (Citer + 1 +
          2 * (Citer * Real.log Dcost + 2 + Real.log c1 + Real.log 2)) *
        |Real.log epsilon| := by
  have hepspos : (0 : ℝ) < epsilon := heps.1
  have hDpos : (0 : ℝ) < Dcost := by linarith
  have hc1pos : (0 : ℝ) < c1 := by linarith
  have hlognonpos : Real.log epsilon ≤ 0 :=
    Real.log_nonpos hepspos.le (by linarith [heps.2])
  have habs : |Real.log epsilon| = -Real.log epsilon := abs_of_nonpos hlognonpos
  have hlogD : (0 : ℝ) ≤ Real.log Dcost := Real.log_nonneg hD
  have hlogc1 : (0 : ℝ) ≤ Real.log c1 := Real.log_nonneg hc1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hPnn : (0 : ℝ) ≤ |Real.log epsilon| := abs_nonneg _
  have hPhalf : (1 : ℝ) / 2 ≤ |Real.log epsilon| := by
    linarith [log_two_le_abs_log heps, Real.log_two_gt_d9]
  have hk1' : (k1 : ℝ) ≤ Citer * (|Real.log epsilon| + Real.log Dcost) := by
    have hlogdiv : Real.log (epsilon / Dcost) =
        Real.log epsilon - Real.log Dcost :=
      Real.log_div (ne_of_gt hepspos) (ne_of_gt hDpos)
    have habs2 : |Real.log (epsilon / Dcost)| =
        |Real.log epsilon| + Real.log Dcost := by
      rw [hlogdiv, abs_of_nonpos (by linarith), habs]
      ring
    rw [habs2] at hk1
    exact hk1
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hden : (2 : ℝ) ≤ (d : ℝ) * Real.log 3 := by
    calc (2 : ℝ) = 2 * 1 := (mul_one 2).symm
      _ ≤ (d : ℝ) * Real.log 3 :=
          mul_le_mul hdreal one_lt_log_three.le zero_le_one (by linarith)
  have hdenpos : (0 : ℝ) < (d : ℝ) * Real.log 3 := by linarith
  have hlogquot : Real.log (c1 / (epsilon / 2)) =
      Real.log c1 + Real.log 2 + |Real.log epsilon| := by
    rw [Real.log_div (ne_of_gt hc1pos) (by positivity),
      Real.log_div (ne_of_gt hepspos) (by norm_num), habs]
    ring
  have hSnn : (0 : ℝ) ≤ Real.log c1 + Real.log 2 + |Real.log epsilon| := by
    linarith
  have hXnn : (0 : ℝ) ≤
      2 * Real.log (c1 / (epsilon / 2)) / ((d : ℝ) * Real.log 3) := by
    rw [hlogquot]
    exact div_nonneg (by linarith) hdenpos.le
  have hXle : 2 * Real.log (c1 / (epsilon / 2)) / ((d : ℝ) * Real.log 3) ≤
      Real.log c1 + Real.log 2 + |Real.log epsilon| := by
    rw [hlogquot, div_le_iff₀ hdenpos]
    calc 2 * (Real.log c1 + Real.log 2 + |Real.log epsilon|)
        = (Real.log c1 + Real.log 2 + |Real.log epsilon|) * 2 := by ring
      _ ≤ (Real.log c1 + Real.log 2 + |Real.log epsilon|) * ((d : ℝ) * Real.log 3) :=
          mul_le_mul_of_nonneg_left hden hSnn
  rw [abs_of_nonneg hXnn] at hk2
  have hk2' : ((k2zero + 1 : ℕ) : ℝ) ≤
      2 + (Real.log c1 + Real.log 2 + |Real.log epsilon|) := by
    push_cast
    linarith
  have hQ : (0 : ℝ) ≤ Citer * Real.log Dcost + 2 + Real.log c1 + Real.log 2 := by
    linarith only [hlogc1, hlog2, mul_nonneg (by linarith : (0 : ℝ) ≤ Citer) hlogD]
  have hkey : (0 : ℝ) ≤
      (Citer * Real.log Dcost + 2 + Real.log c1 + Real.log 2) *
        (2 * |Real.log epsilon| - 1) := mul_nonneg hQ (by linarith)
  linarith only [hk1', hk2', hkey]

/-- **The Section 3.5 cutoff-union conclusion, conditional on the iterate mean
bound.**

The fold is the last paragraph of the printed proof.  The separation `k2` is
chosen by `exists_gridDecay_mul_le` so that the grid gain `3 ^ (-d k2 / 2)`
beats one half of `epsilon`; `epsilon` is split evenly between the two
fluctuation lanes and the deterministic mean; the mean is absorbed by
`isCommonEventTwoTermBigOWith_add_const` and the amplitudes are relaxed by
`isCommonEventTwoTermBigOWith_mono_scale`.  The direction cost `2 ^ d d` of the
net multiplies the mean as well, which is why the iteration is run at
`epsilon / (2 ^ d d)`; both increments stay inside the printed budget
`k1 + k2 <= Chom |log epsilon|`, which is discharged here by
`union_budget_bound`.

The window evaluation `1/16 in [8 gamma, 1]` required by the proved transport
is *derived*, not assumed: the frozen smallness binder `gamma <= Chom^{-1}
E^{-2} epsilon` with `Chom >= 64`, `E >= 1` and `epsilon <= 1/2` gives `gamma
<= 1/128`.  The manuscript's own route (a lower bound on `E` from `15
c_star^{-1} <= E` together with an upper bound on `c_star`, whence `8 gamma <
1/16`) is available here — the proved `Provider.Disorder.cstar_le_three_halves`
gives `E >= 10` and `8 gamma <= 8 * 10^{-10} < 1/16`; only the literal
`c_star <= 1` is absent.  The derivation from the smallness
binder is taken instead because it needs no new import; the two regime binders
`15 c_star^{-1} <= E` and `gamma <= E^{-10}` are passed unchanged to `hIter`,
which is where the printed proof uses them.

This is a Provider result and carries no source-node status by itself. -/
theorem exists_isCommonEventTwoTermBigOWith_cutoffResponseJ_of_iterateMeanBound
    (d : ℕ)
    (hIter : ∃ Citer : ℝ, 1 ≤ Citer ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Citer⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∃ k1 : ℕ, (k1 : ℝ) ≤ Citer * |Real.log epsilon| ∧
            ∀ n L : ℤ, L ≤ m - 1 → L + k1 ≤ n → n ≤ m →
              ∀ e : Vec d, Ch02.vecNorm e = 1 →
                ∫ omega, Observable.cutoffResponseJ M n L e omega
                    ∂(cutoffSampleLaw M).toMeasure ≤
                  2⁻¹ * epsilon * (E : ℝ) ^ 2 * M.gamma) :
    ∃ Chom : ℝ, 1 ≤ Chom ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Chom⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          Probability.IsCommonEventTwoTermBigOWith
            (cutoffSampleLaw M).toMeasure (gammaSigma 1) (gammaSigma (1 / 4))
            (fun i : {p : ℤ × {e : Vec d // Ch02.vecNorm e = 1} //
                (p.1 : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon|} =>
              Observable.cutoffResponseJ M m i.1.1 i.1.2.1)
            (epsilon * (E : ℝ) ^ 2 * M.gamma)
            (epsilon * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))) := by
  classical
  obtain ⟨Citer, hCiter1, hiter⟩ := hIter
  obtain ⟨C0, hC0pos, henv⟩ := exists_unionGridAverageAllDirectionsCommonEnvelope d
  refine ⟨max 64 (max (Citer * (2 ^ d * (d : ℝ)))
      (Citer + 1 + 2 * (Citer * Real.log (2 ^ d * (d : ℝ)) + 2 +
        Real.log (max 1 (2 ^ d * (d : ℝ) * C0)) + Real.log 2))),
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  set Chom : ℝ := max 64 (max (Citer * (2 ^ d * (d : ℝ)))
      (Citer + 1 + 2 * (Citer * Real.log (2 ^ d * (d : ℝ)) + 2 +
        Real.log (max 1 (2 ^ d * (d : ℝ) * C0)) + Real.log 2))) with hChomDef
  intro M m E hE hgamma10 hLower epsilon heps hgammaEps
  have hd2 : 2 ≤ d := M.shellPrefix.dimension
  have hd : 0 < d := by omega
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have htwod : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hDpos : (0 : ℝ) < 2 ^ d * (d : ℝ) := by positivity
  have hD1 : (1 : ℝ) ≤ 2 ^ d * (d : ℝ) := by
    have hmul : (1 : ℝ) * 1 ≤ 2 ^ d * (d : ℝ) :=
      mul_le_mul htwod (by linarith) (by norm_num) (by linarith)
    linarith
  have hc1one : (1 : ℝ) ≤ max 1 (2 ^ d * (d : ℝ) * C0) := le_max_left _ _
  have hc1pos : (0 : ℝ) < max 1 (2 ^ d * (d : ℝ) * C0) := by linarith
  have hChom64 : (64 : ℝ) ≤ Chom := by
    rw [hChomDef]; exact le_max_left _ _
  have hChomCD : Citer * (2 ^ d * (d : ℝ)) ≤ Chom := by
    rw [hChomDef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hChomQ : Citer + 1 + 2 * (Citer * Real.log (2 ^ d * (d : ℝ)) + 2 +
      Real.log (max 1 (2 ^ d * (d : ℝ) * C0)) + Real.log 2) ≤ Chom := by
    rw [hChomDef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hEone : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hgammapos : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hepspos : (0 : ℝ) < epsilon := heps.1
  -- the window evaluation, derived from the smallness binder
  have hWindow : (1 / 16 : ℝ) ∈ Set.Icc (8 * M.gamma) 1 :=
    Set.mem_Icc.2
      ⟨by linarith [gamma_le_of_smallness hChom64 hEone heps hgammaEps],
        by norm_num⟩
  -- the iteration, run at the tolerance shrunk by the direction cost
  have hshrunkpos : (0 : ℝ) < epsilon / (2 ^ d * (d : ℝ)) := div_pos hepspos hDpos
  have hshrunkle : epsilon / (2 ^ d * (d : ℝ)) ≤ 1 / 2 :=
    le_trans (div_le_self hepspos.le hD1) heps.2
  obtain ⟨k1, hk1, hmeanAll⟩ := hiter M m E hE hgamma10 hLower
    (epsilon / (2 ^ d * (d : ℝ))) (Set.mem_Ioc.2 ⟨hshrunkpos, hshrunkle⟩)
    (gamma_le_iterate_smallness hCiter1 hD1 hChomCD hepspos hgammaEps)
  -- the separation k2
  obtain ⟨k2zero, hgain, hk2⟩ := exists_gridDecay_mul_le hd
    (c := max 1 (2 ^ d * (d : ℝ) * C0)) (epsilon := epsilon / 2) hc1pos
    (by linarith)
  have hsep : 1 ≤ k1 + (k2zero + 1) := by omega
  have hbudget : ((k1 : ℝ) + ((k2zero + 1 : ℕ) : ℝ)) ≤
      Chom * |Real.log epsilon| := by
    have hPnn : (0 : ℝ) ≤ |Real.log epsilon| := abs_nonneg _
    exact le_trans (union_budget_bound hd2 hCiter1 hD1 hc1one heps hk1 hk2)
      (mul_le_mul_of_nonneg_right hChomQ hPnn)
  -- the envelope, scaled by the direction cost and shifted by the mean
  have hscaled := isCommonEventTwoTermBigOWith_const_mul (c := 2 ^ d * (d : ℝ))
    hDpos (henv M m E hLower hWindow k1 (k2zero + 1) hsep)
  have hmeannn : (0 : ℝ) ≤ 2 ^ d * (d : ℝ) *
      (2⁻¹ * (epsilon / (2 ^ d * (d : ℝ))) * (E : ℝ) ^ 2 * M.gamma) :=
    mul_nonneg hDpos.le
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hshrunkpos.le)
        (sq_nonneg _)) hgammapos.le)
  have hdom := ae_forall_cutoffResponseJ_le_unionGridAverageAllDirections
    M m k1 (k2zero + 1) hsep Chom epsilon
    (2⁻¹ * (epsilon / (2 ^ d * (d : ℝ))) * (E : ℝ) ^ 2 * M.gamma) hbudget
    (fun L hL hLk b => hmeanAll (L + k1) L hL le_rfl hLk (Pi.single b (1 : ℝ))
      (vecNorm_single_one b))
  have htransfer := isCommonEventTwoTermBigOWith_of_ae_forall_exists_le
    (isCommonEventTwoTermBigOWith_add_const hscaled hmeannn)
    (fun i : {p : ℤ × {e : Vec d // Ch02.vecNorm e = 1} //
        (p.1 : ℝ) ≤ (m : ℝ) - Chom * |Real.log epsilon|} =>
      Observable.measurable_cutoffResponseJ M m i.1.1 i.1.2.1) hdom
  -- the amplitude fold
  have hgainStep : 2 ^ d * (d : ℝ) * C0 * gridDecay d (k2zero + 1) ≤
      epsilon / 2 := by
    have hgdpos : (0 : ℝ) < gridDecay d k2zero := gridDecay_pos d k2zero
    have hstep : gridDecay d (k2zero + 1) ≤ gridDecay d k2zero :=
      calc gridDecay d (k2zero + 1) = gridDecay d k2zero * gridDecay d 1 :=
            gridDecay_add d k2zero 1
        _ ≤ gridDecay d k2zero * 1 :=
            mul_le_mul_of_nonneg_left (gridDecay_le_one d 1) hgdpos.le
        _ = gridDecay d k2zero := mul_one _
    have hle : 2 ^ d * (d : ℝ) * C0 ≤ max 1 (2 ^ d * (d : ℝ) * C0) :=
      le_max_right _ _
    have hgdnn : (0 : ℝ) ≤ gridDecay d (k2zero + 1) := (gridDecay_pos _ _).le
    calc 2 ^ d * (d : ℝ) * C0 * gridDecay d (k2zero + 1)
        ≤ max 1 (2 ^ d * (d : ℝ) * C0) * gridDecay d (k2zero + 1) :=
          mul_le_mul_of_nonneg_right hle hgdnn
      _ ≤ max 1 (2 ^ d * (d : ℝ) * C0) * gridDecay d k2zero :=
          mul_le_mul_of_nonneg_left hstep hc1pos.le
      _ ≤ epsilon / 2 := hgain
  have hDne : ((2 : ℝ) ^ d * (d : ℝ)) ≠ 0 := ne_of_gt hDpos
  have hDmul : 2 ^ d * (d : ℝ) * (epsilon / (2 ^ d * (d : ℝ))) = epsilon := by
    field_simp
  refine isCommonEventTwoTermBigOWith_mono_scale htransfer ?_ ?_
  · have hEgamma : (0 : ℝ) ≤ (E : ℝ) ^ 2 * M.gamma :=
      mul_nonneg (sq_nonneg _) hgammapos.le
    have hmeanEq : 2 ^ d * (d : ℝ) *
        (2⁻¹ * (epsilon / (2 ^ d * (d : ℝ))) * (E : ℝ) ^ 2 * M.gamma) =
        2⁻¹ * epsilon * ((E : ℝ) ^ 2 * M.gamma) := by
      rw [show 2 ^ d * (d : ℝ) *
            (2⁻¹ * (epsilon / (2 ^ d * (d : ℝ))) * (E : ℝ) ^ 2 * M.gamma) =
          2⁻¹ * (2 ^ d * (d : ℝ) * (epsilon / (2 ^ d * (d : ℝ)))) *
            ((E : ℝ) ^ 2 * M.gamma) from by ring, hDmul]
    have hfluct : 2 ^ d * (d : ℝ) *
        (C0 * ((E : ℝ) ^ 2 * M.gamma) * gridDecay d (k2zero + 1)) ≤
        epsilon / 2 * ((E : ℝ) ^ 2 * M.gamma) := by
      rw [show 2 ^ d * (d : ℝ) *
            (C0 * ((E : ℝ) ^ 2 * M.gamma) * gridDecay d (k2zero + 1)) =
          2 ^ d * (d : ℝ) * C0 * gridDecay d (k2zero + 1) *
            ((E : ℝ) ^ 2 * M.gamma) from by ring]
      exact mul_le_mul_of_nonneg_right hgainStep hEgamma
    rw [hmeanEq]
    linarith
  · have hexppos : (0 : ℝ) < Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) :=
      Real.exp_pos _
    rw [show 2 ^ d * (d : ℝ) *
          (C0 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) *
            gridDecay d (k2zero + 1)) =
        2 ^ d * (d : ℝ) * C0 * gridDecay d (k2zero + 1) *
          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) from by ring]
    calc 2 ^ d * (d : ℝ) * C0 * gridDecay d (k2zero + 1) *
          Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹))
        ≤ epsilon / 2 * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) :=
          mul_le_mul_of_nonneg_right hgainStep hexppos.le
      _ ≤ epsilon * Real.exp (-(2 * ((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)) :=
          mul_le_mul_of_nonneg_right (by linarith) hexppos.le

end Fold

end

end Algsuperdiff.Section3.Provider.Homogenization
