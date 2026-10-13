/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.BadEventEstimate
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.BadEventScaleShiftBridge

/-!
# BadEventFrozenApplication

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-cube bad-event tail at the dimension floor, from the frozen estimate

This module consumes `Algsuperdiff.Frozen.Section3.bad_event_estimate` and
delivers the per-cube tail at a constant that clears the dimension floor
`(d : ℝ) ^ 6`, which is what the Section 3.4 good-event display needs.  It is
the consuming half of the scale-shift bridge whose geometric core is
`Provider.Diffusivity.ApproximateRecurrence.BadEventScaleShiftBridge`.

## The mechanism

The frozen export publishes only `1 ≤ Ccg`, and `goodLocalEvent` is not monotone
in that constant.  The bridge trades the constant against the *cube scale*: with
`k := badEventScaleShiftExp d = 6 d`,

```
good (2 Ccg, cu_m, n) ∩ good (2 Ccg, cu_{m + 2k}, n) ⊆ good (2 · 3^k · Ccg, cu_m, n)
```

(`goodLocalEvent_inter_subset_scaleShift_le`), and `3 ^ k ≥ (d : ℝ) ^ 6`
(`dim_pow_six_le_three_pow_scaleShiftExp`).  The frozen export is applied twice
at the *same* translate `triadicCubeShift R`, once at the cube scale `R.scale`
and once at the enlarged scale `R.scale + 2 k`, and the union bound produces the
factor `2` that the consumer absorbs through its Hoelder `3/8` power.

## The two guarded rate gates

The first application sits in the `¬ (n < m)` regime, so both of its guarded
gates are vacuous.  The second one need not: the Section 3.4 grid is indexed by
a *free* recurrence multiplier `a ≤ 32`, and at `a = 0` the cube scale equals the
field scale, leaving no headroom at all.  The two gates are therefore discharged
**on their own terms**, using only `R.scale ≤ n`, which caps the enlarged gap at
`m - n ≤ 2 k`:

* the rate gate `3 ^ (5 (m - n)) ≤ c · cstar · gamma⁻¹` follows from the
  admissibility premise `c⁻¹ cstar⁻¹ ≤ E ≤ gamma⁻¹` once the exported `c` is the
  dimension-only shrink `c₀ · 3 ^ (-12 k)`;
* the ellipticity gate
  `d (m - n) log 3 + exp (X / 8) ≤ exp (X / 4)`, `X := Ccg⁻¹ E⁻² gamma⁻¹`,
  follows from `u ^ 2 + exp u ≤ exp (2 u)` at `u = X / 8` once `X` is above the
  dimension-only threshold `Kgate := 40 (d + k + 1) Ccg`, which is exported as a
  binder and discharged by the consumer from its own window premise.

Both gates are *derived*, never assumed of the source: `Kgate` is an exported
existential witness, and the consumer discharges `Kgate ≤ E⁻² gamma⁻¹` from the
window premise `gamma / 2 + exp (-(C⁻¹ E⁻² gamma⁻¹)) ≤ gamma` at its own
enlarged constant `C`.

## References

* ABK26, `l.bad.event.lemma`; `e.good.local.events`.
* The gate `R.scale + 2 k ≤ n` that §5.3 proposes is *not* available at the
  consumer, whose public statement quantifies the recurrence multiplier freely;
  the two gates are discharged non-vacuously instead, and no public statement
  changes.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
open MeasureTheory

noncomputable section

/-! ## One elementary exponential inequality -/

/-- `u ^ 2 + exp u ≤ exp (2 u)` on `0 ≤ u`, from `1 + u ≤ exp u` applied twice.
This is the whole content of the frozen ellipticity gate once the gap is capped
by the scale shift. -/
private theorem sq_add_exp_le_exp_two_mul {u : ℝ} (hu : 0 ≤ u) :
    u * u + Real.exp u ≤ Real.exp (2 * u) := by
  have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
  have h2 : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have h3 : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [two_mul, Real.exp_add]
  rw [h3]
  nlinarith [h1, h2, hu]

/-- `x g log 3 ≤ 4 x y` when `0 ≤ g ≤ 2 y`: the deterministic side of the frozen
ellipticity gate, over abstract reals. -/
private theorem mul_gap_mul_log_three_le {x g y : ℝ} (hx : 0 ≤ x) (hg0 : 0 ≤ g)
    (hg : g ≤ 2 * y) : x * g * Real.log 3 ≤ x * (2 * y) * 2 := by
  have hlog : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hB : (0 : ℝ) ≤ x * g := mul_nonneg hx hg0
  have hC : x * g * Real.log 3 ≤ x * g * 2 := mul_le_mul_of_nonneg_left hlog hB
  have hA : x * g ≤ x * (2 * y) := mul_le_mul_of_nonneg_left hg hx
  linarith

/-- `4 x y ≤ (5 (x + y + 1)) ^ 2` on nonnegative reals, by `(x - y) ^ 2 ≥ 0`. -/
private theorem four_mul_le_sq_five_mul_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * (2 * y) * 2 ≤ (5 * (x + y + 1)) * (5 * (x + y + 1)) := by
  nlinarith [sq_nonneg (x - y), hx, hy]

/-! ## The frozen application -/

private theorem badEventFrozenApplication_comparisonBounds1 :
    ∀ (d : ℕ) (c0 : ℝ) (_ : (0 : ℝ) < c0) (k : ℕ) (M : ABKModel d) (E : { E : ℝ // (1 : ℝ) ≤ E })
      (R : TriadicCube d) (n : ℤ) (_ : (0 : ℝ) < Disorder.cstar M) (_ : (0 : ℝ) < M.gamma)
      (_ : (0 : ℝ) < M.gamma⁻¹) (_ : (1 : ℝ) ≤ (↑E : ℝ)) (_ : c0 * ((3 : ℝ) ^ ((12 : ℕ) * k))⁻¹ ≤ c0)
      (_ : (↑(R.scale + (2 : ℤ) * (↑k : ℤ)) : ℝ) = (↑R.scale : ℝ) + (2 : ℝ) * (↑k : ℝ))
      (_ : (↑R.scale : ℝ) ≤ (↑n : ℝ)),
      Real.exp (-(c0 * Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ ((↑n : ℝ) - (↑R.scale : ℝ)))) +
            Real.exp (-Real.exp (c0 * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ≤
          Real.exp
              (-(c0 * ((3 : ℝ) ^ ((12 : ℕ) * k))⁻¹ * Disorder.cstar M * M.gamma⁻¹ *
                  (3 : ℝ) ^ ((↑n : ℝ) - (↑R.scale : ℝ)))) +
            Real.exp (-Real.exp (c0 * ((3 : ℝ) ^ ((12 : ℕ) * k))⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ∧
        Real.exp
              (-(c0 * Disorder.cstar M * M.gamma⁻¹ * (3 : ℝ) ^ ((-5 : ℝ) * scaleGapPos n (R.scale + (2 : ℤ) * (↑k : ℤ))) *
                  (3 : ℝ) ^ scaleGapPos (R.scale + (2 : ℤ) * (↑k : ℤ)) n)) +
            Real.exp (-Real.exp (c0 * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) ≤
          Real.exp
              (-(c0 * ((3 : ℝ) ^ ((12 : ℕ) * k))⁻¹ * Disorder.cstar M * M.gamma⁻¹ *
                  (3 : ℝ) ^ ((↑n : ℝ) - (↑R.scale : ℝ)))) +
            Real.exp (-Real.exp (c0 * ((3 : ℝ) ^ ((12 : ℕ) * k))⁻¹ * (↑E : ℝ)⁻¹ ^ (2 : ℕ) * M.gamma⁻¹)) := by
  intro d c0 hc0 k M E R n hcstar0 _ hginv0 _ hcle hm2cast _
  have h3A : (0 : ℝ) < (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hX0 : (0 : ℝ) ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by positivity
  -- the second exponential is common to both applications
  have hexp2 : Real.exp (-Real.exp (c0 * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-Real.exp (c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := by
    refine Real.exp_le_exp.2 (neg_le_neg (Real.exp_le_exp.2 ?_))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcle (sq_nonneg ((E : ℝ)⁻¹))) hginv0.le
  -- the first application
  have hcmp1 : c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * Algsuperdiff.Section3.Disorder.cstar M *
        M.gamma⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)) ≤
      c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)) := by
    refine mul_le_mul_of_nonneg_right ?_ h3A.le
    refine mul_le_mul_of_nonneg_right ?_ hginv0.le
    exact mul_le_mul_of_nonneg_right hcle hcstar0.le
  have hT1 : Real.exp (-(c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)))) +
        Real.exp (-Real.exp (c0 * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-(c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * Algsuperdiff.Section3.Disorder.cstar M *
          M.gamma⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)))) +
        Real.exp (-Real.exp (c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    add_le_add (Real.exp_le_exp.2 (neg_le_neg hcmp1)) hexp2
  -- the second application, uniformly in the position of `n`
  have hgapineq : (n : ℝ) - (R.scale : ℝ) + -(12 * (k : ℝ)) ≤
      -5 * scaleGapPos n (R.scale + 2 * (k : ℤ)) +
        scaleGapPos (R.scale + 2 * (k : ℤ)) n := by
    simp only [scaleGapPos, hm2cast]
    rcases le_or_gt ((R.scale : ℝ) + 2 * (k : ℝ)) (n : ℝ) with hle | hlt
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      linarith
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
      linarith
  have hnp : (3 : ℝ) ^ (-(12 * (k : ℝ))) = ((3 : ℝ) ^ (12 * k))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    rw [← Real.rpow_natCast 3 (12 * k)]
    congr 1
    push_cast
    ring
  have hconv : ((3 : ℝ) ^ (12 * k))⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)) =
      (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ) + -(12 * (k : ℝ))) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), hnp]
    ring
  have hexpge : ((3 : ℝ) ^ (12 * k))⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)) ≤
      (3 : ℝ) ^ (-5 * scaleGapPos n (R.scale + 2 * (k : ℤ))) *
        (3 : ℝ) ^ (scaleGapPos (R.scale + 2 * (k : ℤ)) n) := by
    rw [hconv, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hgapineq
  have hbase0 : (0 : ℝ) ≤ c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ :=
    (mul_pos (mul_pos hc0 hcstar0) hginv0).le
  have hcmp2 : c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * Algsuperdiff.Section3.Disorder.cstar M *
        M.gamma⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)) ≤
      c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (-5 * scaleGapPos n (R.scale + 2 * (k : ℤ))) *
          (3 : ℝ) ^ (scaleGapPos (R.scale + 2 * (k : ℤ)) n) := by
    calc c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * Algsuperdiff.Section3.Disorder.cstar M *
          M.gamma⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ))
        = (c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) *
            (((3 : ℝ) ^ (12 * k))⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ))) := by ring
      _ ≤ (c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) *
            ((3 : ℝ) ^ (-5 * scaleGapPos n (R.scale + 2 * (k : ℤ))) *
              (3 : ℝ) ^ (scaleGapPos (R.scale + 2 * (k : ℤ)) n)) :=
          mul_le_mul_of_nonneg_left hexpge hbase0
      _ = c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (-5 * scaleGapPos n (R.scale + 2 * (k : ℤ))) *
            (3 : ℝ) ^ (scaleGapPos (R.scale + 2 * (k : ℤ)) n) := by ring
  have hT2 : Real.exp (-(c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (-5 * scaleGapPos n (R.scale + 2 * (k : ℤ))) *
            (3 : ℝ) ^ (scaleGapPos (R.scale + 2 * (k : ℤ)) n))) +
        Real.exp (-Real.exp (c0 * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-(c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * Algsuperdiff.Section3.Disorder.cstar M *
          M.gamma⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)))) +
        Real.exp (-Real.exp (c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
    add_le_add (Real.exp_le_exp.2 (neg_le_neg hcmp2)) hexp2
  exact ⟨hT1, hT2⟩

/-- **The per-cube bad-event tail at a floor-normalized constant, derived from
the frozen `Algsuperdiff.Frozen.Section3.bad_event_estimate`.**

The frozen export is applied twice at the same translate `triadicCubeShift R`,
once at the cube scale `R.scale` and once at the enlarged scale
`R.scale + 2 * badEventScaleShiftExp d`; the scale-shift inclusion turns the two
events into the single event at the enlarged constant `2 * 3 ^ k * Ccg`, whose
floor `(d : ℝ) ^ 6` is cleared by `dim_pow_six_le_three_pow_scaleShiftExp`, and
the union bound produces the factor `2`.

The exported `Kgate` is a dimension-only lower threshold on `E⁻² gamma⁻¹`: it is
what discharges the frozen ellipticity gate at the enlarged scale, and the
consumer derives it from its own window premise.

: this statement holds only under the propositions supplied by its binders.  It
is a provider A, not a source-facing frozen declaration. -/
theorem exists_badEventEstimate_perCube_dimFloor_ofFrozen (d : ℕ) :
    ∃ Cbase c Kgate : ℝ, 1 ≤ Cbase ∧ (d : ℝ) ^ 6 ≤ Cbase ∧ 0 < c ∧ 0 < Kgate ∧
      ∀ (M : ABKModel d) (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        c⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        Kgate ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ →
        ∀ (R : TriadicCube d) (n : ℤ), n ≤ m0 - 1 → R.scale ≤ n →
          (cutoffSampleLaw M).toMeasure.real (goodLocalEvent M (2 * Cbase) R n)ᶜ ≤
            2 * (Real.exp (-(c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
                    (3 : ℝ) ^ (-5 * scaleGapPos n R.scale) *
                    (3 : ℝ) ^ scaleGapPos R.scale n)) +
                  Real.exp (-Real.exp (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  classical
  obtain ⟨Ccg, c0, -, hCcg, hc0, hbody⟩ := Algsuperdiff.Frozen.Section3.bad_event_estimate d
  obtain ⟨k, hk6⟩ : ∃ k : ℕ, (d : ℝ) ^ 6 ≤ (3 : ℝ) ^ k :=
    ⟨badEventScaleShiftExp d, dim_pow_six_le_three_pow_scaleShiftExp d⟩
  have hCcg0 : (0 : ℝ) < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  have hCcgne : Ccg ≠ 0 := ne_of_gt hCcg0
  have hc0ne : c0 ≠ 0 := ne_of_gt hc0
  have hk1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have h12pos : (0 : ℝ) < (3 : ℝ) ^ (12 * k) := pow_pos (by norm_num) _
  have h12ne : ((3 : ℝ) ^ (12 * k)) ≠ 0 := ne_of_gt h12pos
  have h121 : (1 : ℝ) ≤ (3 : ℝ) ^ (12 * k) := one_le_pow₀ (by norm_num)
  refine ⟨(3 : ℝ) ^ k * Ccg, c0 * ((3 : ℝ) ^ (12 * k))⁻¹,
    40 * ((d : ℝ) + (k : ℝ) + 1) * Ccg, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · exact mul_pos hc0 (inv_pos.2 h12pos)
  · have hpos : (0 : ℝ) < 40 * ((d : ℝ) + (k : ℝ) + 1) := by positivity
    exact mul_pos hpos hCcg0
  intro M m0 E hS hadm hEgamma hKgate R n hn hRn
  have hcstar0 : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hginv0 : (0 : ℝ) < M.gamma⁻¹ := inv_pos.2 hgamma0
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.2
  have hE0 : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  -- the exported constant is a dimension-only shrink of the frozen one
  have hcle : c0 * ((3 : ℝ) ^ (12 * k))⁻¹ ≤ c0 := by
    have hinv : ((3 : ℝ) ^ (12 * k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h121
    nlinarith
  have hc'0 : (0 : ℝ) < c0 * ((3 : ℝ) ^ (12 * k))⁻¹ := mul_pos hc0 (inv_pos.2 h12pos)
  have hadm0 : c0⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) := by
    have h : c0⁻¹ ≤ (c0 * ((3 : ℝ) ^ (12 * k))⁻¹)⁻¹ := by
      rw [inv_le_inv₀ hc0 hc'0]
      exact hcle
    exact le_trans (mul_le_mul_of_nonneg_right h (inv_pos.2 hcstar0).le) hadm
  -- the admissibility premise, read as a lower bound on `cstar gamma⁻¹`
  have hpow5 : (0 : ℝ) < (E : ℝ) ^ (5 : ℕ) := pow_pos hE0 5
  have hgz : M.gamma ≤ ((E : ℝ) ^ (5 : ℕ))⁻¹ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.gamma_le_inv_pow_five hE1 hgamma0 hEgamma
  have hEle : (E : ℝ) ≤ M.gamma⁻¹ := by
    have h1 : (E : ℝ) ^ (5 : ℕ) ≤ M.gamma⁻¹ := by
      rw [le_inv_comm₀ hpow5 hgamma0]
      exact hgz
    have h2 : (E : ℝ) ≤ (E : ℝ) ^ (5 : ℕ) := by
      calc (E : ℝ) = (E : ℝ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (E : ℝ) ^ (5 : ℕ) := pow_le_pow_right₀ hE1 (by norm_num)
    linarith
  have hkey : (3 : ℝ) ^ (12 * k) ≤
      c0 * (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) := by
    have hinv : (c0 * ((3 : ℝ) ^ (12 * k))⁻¹)⁻¹ = (3 : ℝ) ^ (12 * k) * c0⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm]
    rw [hinv] at hadm
    have h1 : (3 : ℝ) ^ (12 * k) * c0⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤
        M.gamma⁻¹ := le_trans hadm hEle
    have h2 := mul_le_mul_of_nonneg_right h1 hcstar0.le
    have h3 : (3 : ℝ) ^ (12 * k) * c0⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
        Algsuperdiff.Section3.Disorder.cstar M = (3 : ℝ) ^ (12 * k) * c0⁻¹ := by
      field_simp
    rw [h3] at h2
    have h4 := mul_le_mul_of_nonneg_left h2 hc0.le
    have h5 : c0 * ((3 : ℝ) ^ (12 * k) * c0⁻¹) = (3 : ℝ) ^ (12 * k) := by
      field_simp
    calc (3 : ℝ) ^ (12 * k) = c0 * ((3 : ℝ) ^ (12 * k) * c0⁻¹) := h5.symm
      _ ≤ c0 * (M.gamma⁻¹ * Algsuperdiff.Section3.Disorder.cstar M) := h4
      _ = c0 * (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) := by ring
  -- the enlarged scale, and the cap on its gap
  have hm2cast : ((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) = (R.scale : ℝ) + 2 * (k : ℝ) := by
    push_cast
    ring
  have hRncast : ((R.scale : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hRn
  -- the frozen rate gate at the enlarged scale
  have hG1 : n < R.scale + 2 * (k : ℤ) →
      (3 : ℝ) ^ (5 * scaleGapPos n (R.scale + 2 * (k : ℤ))) ≤
        c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ := by
    intro hlt
    have hgap : scaleGapPos n (R.scale + 2 * (k : ℤ)) =
        ((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) - (n : ℝ) := scaleGapPos_of_le hlt.le
    have hub : ((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) - (n : ℝ) ≤ 2 * (k : ℝ) := by
      rw [hm2cast]
      linarith
    have hcast : (3 : ℝ) ^ (12 * (k : ℝ)) = (3 : ℝ) ^ (12 * k) := by
      rw [← Real.rpow_natCast 3 (12 * k)]
      congr 1
      push_cast
      ring
    rw [hgap]
    calc (3 : ℝ) ^ (5 * (((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) - (n : ℝ)))
        ≤ (3 : ℝ) ^ (12 * (k : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (3 : ℝ) ^ (12 * k) := hcast
      _ ≤ c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ := by
          rw [mul_assoc]
          exact hkey
  -- the frozen ellipticity gate at the enlarged scale
  have hG2 : n < R.scale + 2 * (k : ℤ) →
      (d : ℝ) * (((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) - (n : ℝ)) * Real.log 3 +
            Real.exp ((1 / 8 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
          Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := by
    intro hlt
    have hXge : 40 * ((d : ℝ) + (k : ℝ) + 1) ≤ Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hKgate (inv_pos.2 hCcg0).le
      calc 40 * ((d : ℝ) + (k : ℝ) + 1)
          = Ccg⁻¹ * (40 * ((d : ℝ) + (k : ℝ) + 1) * Ccg) := by
            field_simp
        _ ≤ Ccg⁻¹ * (((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) := h
        _ = Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ := by ring
    have hu5 : 5 * ((d : ℝ) + (k : ℝ) + 1) ≤
        (1 / 8 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) := by linarith
    have hu0 : (0 : ℝ) ≤ (1 / 8 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) := by
      linarith
    have hsq := sq_add_exp_le_exp_two_mul hu0
    have h2u : 2 * ((1 / 8 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) =
        (1 / 4 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) := by ring
    rw [h2u] at hsq
    have hgap0 : (0 : ℝ) ≤ ((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) - (n : ℝ) := by
      have : (n : ℝ) ≤ ((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) := by exact_mod_cast hlt.le
      linarith
    have hgapub : ((R.scale + 2 * (k : ℤ) : ℤ) : ℝ) - (n : ℝ) ≤ 2 * (k : ℝ) := by
      rw [hm2cast]
      linarith
    have hstep1 := mul_gap_mul_log_three_le hd0 hgap0 hgapub
    have h4dk := four_mul_le_sq_five_mul_add hd0 hk0
    have hmul : (5 * ((d : ℝ) + (k : ℝ) + 1)) * (5 * ((d : ℝ) + (k : ℝ) + 1)) ≤
        ((1 / 8 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) *
          ((1 / 8 : ℝ) * (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) :=
      mul_le_mul hu5 hu5 (by positivity) (by linarith)
    linarith [hsq, hstep1, h4dk, hmul]
  -- the two frozen applications, at the same translate
  have hb1 := hbody M m0 E hS hadm0 hEgamma R.scale n hn
    (fun hlt => absurd hlt (not_lt.2 hRn)) (fun hlt => absurd hlt (not_lt.2 hRn))
    (triadicCubeShift R)
  have hb2 := hbody M m0 E hS hadm0 hEgamma (R.scale + 2 * (k : ℤ)) n hn hG1 hG2
    (triadicCubeShift R)
  have hev1 : Algsuperdiff.Frozen.Section3.goodLocalEventAt M (2 * Ccg) R.scale n
      (triadicCubeShift R) = goodLocalEvent M (2 * Ccg) R n :=
    goodLocalEventAt_triadicCubeShift M (2 * Ccg) R n
  rw [hev1] at hb1
  -- the scale-shift inclusion, pulled back by the common translate
  have hincl : goodLocalEvent M (2 * Ccg) R n ∩
      Algsuperdiff.Frozen.Section3.goodLocalEventAt M (2 * Ccg)
        (R.scale + 2 * (k : ℤ)) n (triadicCubeShift R) ⊆
      goodLocalEvent M (2 * ((3 : ℝ) ^ k * Ccg)) R n := by
    rintro omega ⟨h1, h2⟩
    have hcore := goodLocalEvent_inter_subset_scaleShift_le M hCcg0 R.scale n k hRn
    have hmem : translateCutoffSample (triadicCubeShift R) omega ∈
        goodLocalEvent M (2 * Ccg) (originCube d R.scale) n ∩
          goodLocalEvent M (2 * Ccg) (originCube d (R.scale + 2 * (k : ℤ))) n := by
      refine ⟨?_, h2⟩
      rw [← hev1] at h1
      exact h1
    have hout := hcore hmem
    have hev3 : Algsuperdiff.Frozen.Section3.goodLocalEventAt M
        (2 * (3 : ℝ) ^ k * Ccg) R.scale n (triadicCubeShift R) =
        goodLocalEvent M (2 * (3 : ℝ) ^ k * Ccg) R n :=
      goodLocalEventAt_triadicCubeShift M _ R n
    have hmem3 : omega ∈ goodLocalEvent M (2 * (3 : ℝ) ^ k * Ccg) R n := by
      rw [← hev3]
      exact hout
    have hassoc : 2 * ((3 : ℝ) ^ k * Ccg) = 2 * (3 : ℝ) ^ k * Ccg := by ring
    rw [hassoc]
    exact hmem3
  -- the union bound
  have hunion : (goodLocalEvent M (2 * ((3 : ℝ) ^ k * Ccg)) R n)ᶜ ⊆
      (goodLocalEvent M (2 * Ccg) R n)ᶜ ∪
        (Algsuperdiff.Frozen.Section3.goodLocalEventAt M (2 * Ccg)
          (R.scale + 2 * (k : ℤ)) n (triadicCubeShift R))ᶜ := by
    intro omega homega
    by_contra hcon
    refine homega (hincl ⟨?_, ?_⟩)
    · by_contra h1
      exact hcon (Or.inl h1)
    · by_contra h2
      exact hcon (Or.inr h2)
  have hmeasure : (cutoffSampleLaw M).toMeasure.real
      (goodLocalEvent M (2 * ((3 : ℝ) ^ k * Ccg)) R n)ᶜ ≤
      (cutoffSampleLaw M).toMeasure.real (goodLocalEvent M (2 * Ccg) R n)ᶜ +
        (cutoffSampleLaw M).toMeasure.real
          (Algsuperdiff.Frozen.Section3.goodLocalEventAt M (2 * Ccg)
            (R.scale + 2 * (k : ℤ)) n (triadicCubeShift R))ᶜ := by
    refine le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hunion)) ?_
    exact MeasureTheory.measureReal_union_le _ _
  -- the two scale gaps of the target
  have hg1 : scaleGapPos n R.scale = 0 := by
    simp only [scaleGapPos]
    exact max_eq_right (by linarith)
  have hg2 : scaleGapPos R.scale n = (n : ℝ) - (R.scale : ℝ) := scaleGapPos_of_le hRn
  simp only [hg1, hg2, mul_zero, Real.rpow_zero, mul_one] at hb1 ⊢
  obtain ⟨hT1, hT2⟩ :=
    (show (Real.exp (-(c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)))) +
        Real.exp (-Real.exp (c0 * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-(c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * Algsuperdiff.Section3.Disorder.cstar M *
          M.gamma⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)))) +
        Real.exp (-Real.exp (c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) ∧
          (Real.exp (-(c0 * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (-5 * scaleGapPos n (R.scale + 2 * (k : ℤ))) *
            (3 : ℝ) ^ (scaleGapPos (R.scale + 2 * (k : ℤ)) n))) +
        Real.exp (-Real.exp (c0 * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
      Real.exp (-(c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * Algsuperdiff.Section3.Disorder.cstar M *
          M.gamma⁻¹ * (3 : ℝ) ^ ((n : ℝ) - (R.scale : ℝ)))) +
        Real.exp (-Real.exp (c0 * ((3 : ℝ) ^ (12 * k))⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) from
      @badEventFrozenApplication_comparisonBounds1 (d) (c0) (hc0) (k) (M) (E) (R) (n) (hcstar0)
        (hgamma0) (hginv0) (hE1) (hcle) (hm2cast) (hRncast))
  linarith [hmeasure, le_trans hb1 hT1, le_trans hb2 hT2]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
