/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg


/-!
# Sobolev ladder at the full step

`EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le` raises the exponent from `p` to `p'` with
`1/p' = 1/p - 1/d`. Iterating it `s` times lands on `1/p - s/d`, which is the exponent Guo's
Sobolev embedding writes as `p^{∗⋯∗}` (Guo, *Partial Differential Equations*, Theorem IV.2.3).
This file runs that iteration from `p = 2`, at the full step and to a bounded depth.

## Rung condition

A rung is available while the reciprocal below it stays positive, and `2 * s ≤ d` is what keeps
it so: at the top rung the reciprocal is `1/2 - s/d ≥ 0`, and at every rung below it exceeds
`1/d`. So `⌊d/2⌋` rungs run, against the `d - 1` a half-step ladder needs, and both reach `L^{2d}`.

The top rung is where the two dimensional parities separate. For `d` even the reciprocal at
`s = d/2` is exactly `0`, so the rung reaches every finite exponent and attains none of them;
for `d` odd it is `1/(2d)`, and that one is attained. Neither case is special in the proof,
since the statement asks only that the target reciprocal be at least `1/2 - s/d`, and
`EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_of_le` is what lets a rung be fed from an
exponent above the one it consumes. That is the same mechanism
`EllipticPdes.Embedding.exists_eLpNorm_four_le` uses in dimension two.

## Bounded depth

The family is closed under differentiation only as far as `dep` records. An index `i` sits at
depth `dep i`, differentiating adds at most one, and `m` is the total supply. Running `s` rungs
on `F i` consumes `s` of the orders above `dep i`, so the conclusion is stated for those `i` with
`dep i + s ≤ m`. A family closed at every order is the case `dep = 0`.

## Main declarations

* `EllipticPdes.Embedding.memLp_of_gradClosed_fullStep`: the ladder, at rung `s` and any exponent
  the rung reaches.
* `EllipticPdes.Embedding.memLp_two_mul_of_gradClosed_fullStep`: the ladder run to `L^{2d}`, which
  passes `d` in every dimension and is what `EllipticPdes.Embedding.morrey_ball` consumes.

## References

Guo, *Partial Differential Equations*, Theorem IV.2.3.
Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1 and §5.6.3.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-! ### Reciprocal arithmetic

Three facts about reciprocals, kept apart so that the induction's own context stays small.
-/

private theorem inv_antitone_fullStep {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha h
  nlinarith [mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', inv_pos.mpr ha, inv_pos.mpr hb]

private theorem le_of_inv_le_inv_fullStep {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a⁻¹ ≤ b⁻¹) :
    b ≤ a := by
  nlinarith [mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', inv_pos.mpr ha, inv_pos.mpr hb]

private theorem coe_toNNReal_inv_fullStep {t : ℝ} (ht : 0 < t) :
    ((Real.toNNReal t⁻¹ : ℝ≥0) : ℝ) = t⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)

/-! ### Ladder -/

/-- **Sobolev bootstrap at the full step to bounded depth.** Let `F` assign a function to each
index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`, and let
`dep` record how far an index sits above the root, so that differentiating adds at most one. If
every index of depth at most `m` lies in `L²` there and every index of depth below `m` has its
weak gradient in the family, then at step `s` with `2 * s ≤ d` every index of depth at most
`m - s` lies in `Lq` on `Metric.ball c r`, for any exponent `q ≥ 2` whose reciprocal is at least
`1/2 - s/d`.

The induction is on the step. Each one splits the gap `r < R` at its midpoint, applies the
hypothesis at step `s` on the outer half to the index and to its derivatives, and takes one
Gagliardo-Nirenberg-Sobolev step on the inner half. The depth bookkeeping is what replaces
closure at every order: a derivative sits one level higher, so a step fewer is available to it,
and that is what the recursive call is given. -/
theorem memLp_of_gradClosed_fullStep (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, 2 * s ≤ d → (2 : ℝ≥0) ≤ q →
      2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
      ∀ i, dep i + s ≤ m → MemLp (F i) q (volume.restrict (Metric.ball c r)) := by
  intro s
  induction s with
  | zero =>
    intro q r R _ hq2 hqs hr hrR _ hmem i hi
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at this
      linarith
    -- At the bottom rung the exponent is `2` itself, since `1/q ≥ 1/2` caps it there.
    have hq2' : q ≤ 2 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_ofNat]
      refine le_of_inv_le_inv_fullStep (by norm_num) hq0 ?_
      simpa using hqs
    have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hqE : (q : ℝ≥0∞) ≤ 2 := by exact_mod_cast hq2'
    exact ((hmem i (by omega)).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).mono_exponent hqE
  | succ s ih =>
    intro q r R hsd hq2 hqs hr hrR hgrad hmem i hi
    -- The rung above the top one is unavailable, so the dimension is at least `2 s + 2`.
    have hd2n : 2 ≤ d := by omega
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2n
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hdinv : (d : ℝ)⁻¹ ≤ 2⁻¹ := by
      have := inv_antitone_fullStep (a := (2 : ℝ)) (by norm_num) hd2
      simpa using this
    have hdinv0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
    have hqinv0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have h2q : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at h2q
      exact inv_pos.mpr (by linarith)
    have hqinv : (q : ℝ)⁻¹ ≤ 2⁻¹ := by
      have h2q : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at h2q
      have := inv_antitone_fullStep (a := (2 : ℝ)) (by norm_num) h2q
      simpa using this
    push_cast at hqs
    -- The midpoint of the gap, so that the rung shrinks the ball without leaving `r`.
    set r' : ℝ := (r + R) / 2 with hr'_def
    have hrr' : r < r' := by rw [hr'_def]; linarith
    have hr'R : r' < R := by rw [hr'_def]; linarith
    have hr' : (0 : ℝ) < r' := lt_trans hr hrr'
    -- The exponent of the rung below, `1/Q = 1/2 - s/d`.
    set t : ℝ := 2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ with ht_def
    -- `2 s + 2 ≤ d` puts the reciprocal below the top rung at or above `1/d`.
    have ht0 : 0 < t := by
      have hs : 2 * (s : ℝ) + 2 ≤ (d : ℝ) := by exact_mod_cast hsd
      have hmul : 2 * (s : ℝ) * (d : ℝ)⁻¹ + 2 * (d : ℝ)⁻¹ ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hs hdinv0.le
        rw [mul_inv_cancel₀ hdpos.ne'] at this
        nlinarith
      rw [ht_def]; nlinarith
    have ht2 : t ≤ 2⁻¹ := by
      have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
      rw [ht_def]; linarith
    set Q : ℝ≥0 := Real.toNNReal t⁻¹ with hQ_def
    have hQcoe : ((Q : ℝ≥0) : ℝ) = t⁻¹ := by rw [hQ_def]; exact coe_toNNReal_inv_fullStep ht0
    have hQ0 : (0 : ℝ) < (Q : ℝ) := by rw [hQcoe]; exact inv_pos.mpr ht0
    have hQinv : ((Q : ℝ≥0) : ℝ)⁻¹ = t := by rw [hQcoe, inv_inv]
    have hQ2 : (2 : ℝ≥0) ≤ Q := by
      rw [← NNReal.coe_le_coe, NNReal.coe_ofNat, hQcoe]
      have := inv_antitone_fullStep ht0 ht2
      simpa using this
    -- The exponent the inequality is applied at, `1/p = 1/q + 1/d`.
    set u : ℝ := (q : ℝ)⁻¹ + (d : ℝ)⁻¹ with hu_def
    have hu0 : 0 < u := by rw [hu_def]; linarith
    have hu1 : u ≤ 1 := by rw [hu_def]; linarith
    set p : ℝ≥0 := Real.toNNReal u⁻¹ with hp_def
    have hpcoe : ((p : ℝ≥0) : ℝ) = u⁻¹ := by rw [hp_def]; exact coe_toNNReal_inv_fullStep hu0
    have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hpcoe]; exact inv_pos.mpr hu0
    have hpinv : ((p : ℝ≥0) : ℝ)⁻¹ = u := by rw [hpcoe, inv_inv]
    have hp1 : (1 : ℝ≥0) ≤ p := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one, hpcoe]
      have := inv_antitone_fullStep hu0 hu1
      simpa using this
    -- The full step is exactly what the target reciprocal at rung `s + 1` pays for.
    have htu : t ≤ u := by rw [ht_def, hu_def]; linarith
    have hpQ : p ≤ Q := by
      rw [← NNReal.coe_le_coe]
      refine le_of_inv_le_inv_fullStep hQ0 hp0 ?_
      rw [hQinv, hpinv]; exact htu
    have hpp' : ((q : ℝ≥0) : ℝ)⁻¹ = ((p : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
      rw [hpinv, hu_def]; ring
    -- The rung below, on the outer half, for the index and for its derivatives.
    have hQmem : ∀ j, dep j + s ≤ m → MemLp (F j) Q (volume.restrict (Metric.ball c r')) :=
      ih (by omega) hQ2 (le_of_eq hQinv.symm) hr' hr'R hgrad hmem
    obtain ⟨_K, hK⟩ :=
      exists_eLpNorm_sobolevConj_le_of_le (p := p) (q := Q) (p' := q) hd c hp1 hpQ hpp' hr hrr'
    exact (hK (F i) (fun k => F (nxt i k)) (hQmem i (by omega))
      (fun k => hQmem (nxt i k) (by have := hdep i k; omega))
      ((hgrad i (by omega)).mono (Metric.ball_subset_ball hr'R.le))).1

/-- **Full-step ladder run to the top.** An index of depth at most `m - ⌊d/2⌋` in a family
closed under weak differentiation as far as `m`, with every member of depth at most `m` in `L²`
on `Metric.ball c R`, lies in `L^{2d}` on any smaller concentric ball. Since `2d > d`, this is
the exponent `EllipticPdes.Embedding.morrey_ball` asks for, in every dimension.

The rung count is `⌊d/2⌋`, and the reciprocal it lands on is `1/2 - ⌊d/2⌋/d`, which is `0` when
`d` is even and `1/(2d)` when `d` is odd. Both are at most `1/(2d)`, which is why one statement
serves the two parities. -/
theorem memLp_two_mul_of_gradClosed_fullStep (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R)))
    (i : ι) (hi : dep i + d / 2 ≤ m) :
    MemLp (F i) (2 * (d : ℝ≥0)) (volume.restrict (Metric.ball c r)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdinv0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
  have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- The landing exponent, `2 d`, and its reciprocal.
  have hcoe : ((2 * (d : ℝ≥0) : ℝ≥0) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
  have h2d2 : (2 : ℝ≥0) ≤ 2 * (d : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, hcoe, NNReal.coe_ofNat]
    nlinarith
  -- `d - 2 ⌊d/2⌋ ≤ 1` is what puts the landing reciprocal at or below `1/(2 d)`.
  have hmod : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by
    have : d ≤ 2 * (d / 2) + 1 := by omega
    exact_mod_cast this
  have hland : 2⁻¹ - ((d / 2 : ℕ) : ℝ) * (d : ℝ)⁻¹ ≤ ((2 * (d : ℝ≥0) : ℝ≥0) : ℝ)⁻¹ := by
    rw [hcoe, mul_inv]
    have hcancel : (d : ℝ) * (d : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hdpos.ne'
    have := mul_le_mul_of_nonneg_right hmod hdinv0.le
    rw [hcancel] at this
    nlinarith
  exact memLp_of_gradClosed_fullStep hd c hdep (d / 2) (by omega) h2d2 hland hr hrR hgrad hmem i hi


/-! ### The ladder with its constant -/

/-- **Full-step ladder with a constant.** One constant, depending on the dimension, the rung
count, the exponent and the two radii alone, takes a uniform `L²` bound on the family over the
outer ball to an `L^q` bound on the inner one, at every index the rungs reach.

`memLp_of_gradClosed_fullStep` is this with the constant discarded. Guo's
`‖u‖_{L^q} ≤ C‖u‖_{W^{k,p}}` at `p = 2` is this estimate: the bound is by the `L²` data alone,
uniformly over the members the rungs consume. -/
theorem exists_const_eLpNorm_le_of_gradClosed_fullStep (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) (ι : Type*) :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, 2 * s ≤ d → (2 : ℝ≥0) ≤ q →
      2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      ∃ K : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
        {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
        (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
        (∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
        ∀ M : ℝ≥0, (∀ j, dep j ≤ m →
            eLpNorm (F j) 2 (volume.restrict (Metric.ball c R)) ≤ M) →
        ∀ i, dep i + s ≤ m →
          eLpNorm (F i) q (volume.restrict (Metric.ball c r)) ≤ (K : ℝ≥0∞) * M := by
  intro s
  induction s with
  | zero =>
    intro q r R _ hq2 hqs hr hrR
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at this
      linarith
    have hq2' : q ≤ 2 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_ofNat]
      refine le_of_inv_le_inv_fullStep (by norm_num) hq0 ?_
      simpa using hqs
    have hqE : (q : ℝ≥0∞) ≤ 2 := by exact_mod_cast hq2'
    -- The exponent drop uses one power of the ball's measure.
    have he : (0 : ℝ) ≤ 1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal := by
      have h2 : (q : ℝ≥0∞).toReal ≤ (2 : ℝ≥0∞).toReal := ENNReal.toReal_mono (by simp) hqE
      have hqR : (q : ℝ≥0∞).toReal = (q : ℝ) := by simp
      rw [sub_nonneg]
      refine one_div_le_one_div_of_le ?_ h2
      rw [hqR]; exact hq0
    have hVfin : volume (Metric.ball c r) ≠ ⊤ := measure_ball_lt_top.ne
    refine ⟨(volume (Metric.ball c r)
      ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toNNReal, ?_⟩
    intro F nxt dep m _hdep _hgrad hmem M hM i hi
    have hcoe : ((volume (Metric.ball c r)
        ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toNNReal : ℝ≥0∞)
        = volume (Metric.ball c r) ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
      ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg he hVfin)
    have hmeas : AEStronglyMeasurable (F i) (volume.restrict (Metric.ball c r)) :=
      ((hmem i (by omega)).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).aestronglyMeasurable
    have h2r : eLpNorm (F i) 2 (volume.restrict (Metric.ball c r)) ≤ M := by
      refine le_trans (eLpNorm_mono_measure _
        (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)) ?_
      exact hM i (by omega)
    calc eLpNorm (F i) q (volume.restrict (Metric.ball c r))
        ≤ eLpNorm (F i) 2 (volume.restrict (Metric.ball c r))
            * (volume.restrict (Metric.ball c r)) Set.univ
              ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqE hmeas
      _ ≤ (M : ℝ≥0∞) * volume (Metric.ball c r)
            ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
          rw [Measure.restrict_apply_univ]
          gcongr
      _ = _ := by rw [hcoe, mul_comm]
  | succ s ih =>
    intro q r R hsd hq2 hqs hr hrR
    have hd2n : 2 ≤ d := by omega
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2n
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hdinv : (d : ℝ)⁻¹ ≤ 2⁻¹ := by
      have := inv_antitone_fullStep (a := (2 : ℝ)) (by norm_num) hd2
      simpa using this
    have hdinv0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
    have hqinv0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have h2q : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at h2q
      exact inv_pos.mpr (by linarith)
    have hqinv : (q : ℝ)⁻¹ ≤ 2⁻¹ := by
      have h2q : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at h2q
      have := inv_antitone_fullStep (a := (2 : ℝ)) (by norm_num) h2q
      simpa using this
    push_cast at hqs
    -- The midpoint of the gap, so that the rung shrinks the ball without leaving `r`.
    set r' : ℝ := (r + R) / 2 with hr'_def
    have hrr' : r < r' := by rw [hr'_def]; linarith
    have hr'R : r' < R := by rw [hr'_def]; linarith
    have hr' : (0 : ℝ) < r' := lt_trans hr hrr'
    -- The exponent of the rung below, `1/Q = 1/2 - s/d`.
    set t : ℝ := 2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ with ht_def
    -- `2 s + 2 ≤ d` puts the reciprocal below the top rung at or above `1/d`.
    have ht0 : 0 < t := by
      have hs : 2 * (s : ℝ) + 2 ≤ (d : ℝ) := by exact_mod_cast hsd
      have hmul : 2 * (s : ℝ) * (d : ℝ)⁻¹ + 2 * (d : ℝ)⁻¹ ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hs hdinv0.le
        rw [mul_inv_cancel₀ hdpos.ne'] at this
        nlinarith
      rw [ht_def]; nlinarith
    have ht2 : t ≤ 2⁻¹ := by
      have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
      rw [ht_def]; linarith
    set Q : ℝ≥0 := Real.toNNReal t⁻¹ with hQ_def
    have hQcoe : ((Q : ℝ≥0) : ℝ) = t⁻¹ := by rw [hQ_def]; exact coe_toNNReal_inv_fullStep ht0
    have hQ0 : (0 : ℝ) < (Q : ℝ) := by rw [hQcoe]; exact inv_pos.mpr ht0
    have hQinv : ((Q : ℝ≥0) : ℝ)⁻¹ = t := by rw [hQcoe, inv_inv]
    have hQ2 : (2 : ℝ≥0) ≤ Q := by
      rw [← NNReal.coe_le_coe, NNReal.coe_ofNat, hQcoe]
      have := inv_antitone_fullStep ht0 ht2
      simpa using this
    -- The exponent the inequality is applied at, `1/p = 1/q + 1/d`.
    set u : ℝ := (q : ℝ)⁻¹ + (d : ℝ)⁻¹ with hu_def
    have hu0 : 0 < u := by rw [hu_def]; linarith
    have hu1 : u ≤ 1 := by rw [hu_def]; linarith
    set p : ℝ≥0 := Real.toNNReal u⁻¹ with hp_def
    have hpcoe : ((p : ℝ≥0) : ℝ) = u⁻¹ := by rw [hp_def]; exact coe_toNNReal_inv_fullStep hu0
    have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hpcoe]; exact inv_pos.mpr hu0
    have hpinv : ((p : ℝ≥0) : ℝ)⁻¹ = u := by rw [hpcoe, inv_inv]
    have hp1 : (1 : ℝ≥0) ≤ p := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one, hpcoe]
      have := inv_antitone_fullStep hu0 hu1
      simpa using this
    -- The full step is exactly what the target reciprocal at rung `s + 1` pays for.
    have htu : t ≤ u := by rw [ht_def, hu_def]; linarith
    have hpQ : p ≤ Q := by
      rw [← NNReal.coe_le_coe]
      refine le_of_inv_le_inv_fullStep hQ0 hp0 ?_
      rw [hQinv, hpinv]; exact htu
    have hpp' : ((q : ℝ≥0) : ℝ)⁻¹ = ((p : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
      rw [hpinv, hu_def]; ring
    -- The rung below, quantified before the family, and the rung itself.
    obtain ⟨Kih, hKih⟩ := ih (by omega) hQ2 (le_of_eq hQinv.symm) hr' hr'R
    obtain ⟨Krung, hK⟩ :=
      exists_eLpNorm_sobolevConj_le_of_le (p := p) (q := Q) (p' := q) hd c hp1 hpQ hpp' hr hrr'
    refine ⟨Krung * (1 + d) * Kih, ?_⟩
    intro F nxt dep m hdep hgrad hmem M hM i hi
    have hQmem : ∀ j, dep j + s ≤ m → MemLp (F j) Q (volume.restrict (Metric.ball c r')) :=
      memLp_of_gradClosed_fullStep hd c hdep s (by omega) hQ2 (le_of_eq hQinv.symm) hr' hr'R
        hgrad hmem
    have hQb : ∀ j, dep j + s ≤ m →
        eLpNorm (F j) Q (volume.restrict (Metric.ball c r')) ≤ (Kih : ℝ≥0∞) * M :=
      fun j hj => hKih hdep hgrad hmem M hM j hj
    have hrung := (hK (F i) (fun k => F (nxt i k)) (hQmem i (by omega))
      (fun k => hQmem (nxt i k) (by have := hdep i k; omega))
      ((hgrad i (by omega)).mono (Metric.ball_subset_ball hr'R.le))).2
    calc eLpNorm (F i) q (volume.restrict (Metric.ball c r))
        ≤ (Krung : ℝ≥0∞) * (eLpNorm (F i) Q (volume.restrict (Metric.ball c r'))
            + ∑ k, eLpNorm (F (nxt i k)) Q (volume.restrict (Metric.ball c r'))) := hrung
      _ ≤ (Krung : ℝ≥0∞) * ((Kih : ℝ≥0∞) * M + ∑ _k : Fin d, (Kih : ℝ≥0∞) * M) := by
          gcongr with k _
          · exact hQb i (by omega)
          · exact hQb (nxt i k) (by have := hdep i k; omega)
      _ = ((Krung * (1 + d) * Kih : ℝ≥0) : ℝ≥0∞) * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

end EllipticPdes.Embedding
