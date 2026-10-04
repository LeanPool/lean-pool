/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Embedding.GagliardoNirenberg


/-!
# Iterating the Sobolev ladder

One Gagliardo-Nirenberg-Sobolev step raises the exponent from `p` to `p'` with
`1/p' = 1/p - 1/d`, and `EllipticPdes.Embedding.morrey_ball` asks for `p' > d`. Starting from the
`L²` data an `H²` estimate delivers, a single step reaches `p' > d` only in dimensions one to
three, which is where `EllipticPdes.Embedding.exists_eLpNorm_six_le` and
`EllipticPdes.Embedding.exists_eLpNorm_four_le` stop.

Iterating the step reaches every dimension, at the price of consuming a weak derivative per
rung. The family that pays for it is one closed under differentiation: an index type `ι`, a
function `F i` for each index, and a successor `nxt i k` naming the `k`-th weak derivative of `F
i`. A solution with weak derivatives of every order has such a family, indexed by lists of
directions, and closure is what lets a single induction climb without bookkeeping of orders.

## Rungs

Each rung improves the reciprocal exponent by `1/(2d)` rather than the full `1/d` the inequality
allows. The half-step is deliberate. Starting at `1/2` and taking `d - 1` rungs of `1/(2d)` lands
at `1/(2d)`, so the exponent reached is `2d`, comfortably past `d`, while every intermediate
reciprocal `1/2 - s/(2d)` stays strictly positive for `s < d`. Full steps would land on `1/p' = 0`
in even dimensions and on `p' = d` exactly one rung earlier, both degenerate.

A rung consumes two exponents: the data sits at `q_s` with `1/q_s = 1/2 - s/(2d)`, the inequality
is applied at `p` with `1/p = 1/q_{s+1} + 1/d`, and `p ≤ q_s` follows from the half-step, so
`EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_of_le` takes the drop from `q_s` to `p` on
the ball's finite measure. That `p` may sit below `2`, which is why the ladder is stated against
the exponent-lowering form of the bootstrap rather than the sharp one.

Each rung also shrinks the ball. The induction hands the shrinking back to its own hypothesis, so
the statement is between one fixed pair of radii `r < R` however many rungs it runs.

## Main declarations

* `EllipticPdes.Embedding.memLp_of_gradClosed`: the ladder, at rung `s` and any exponent the rung
  reaches.
* `EllipticPdes.Embedding.memLp_two_mul_of_gradClosed`: the ladder run to the top, landing at
  `2d > d`, which is what `EllipticPdes.Embedding.morrey_ball` consumes.

## References

Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1 and §5.6.3.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-! ### Ladder -/

/-- **Sobolev ladder on a family closed under differentiation.** Let `F` assign a function to
each index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`, and let
every `F i` lie in `L²` there. Then at rung `s < d` every `F i` lies in `Lq` on `Metric.ball c r`,
for any exponent `q ≥ 2` whose reciprocal is at least `1/2 - s/(2d)`.

The induction is on the rung. Each step splits the gap `r < R` at its midpoint, applies the
hypothesis at rung `s` on the outer half to the whole family at once, and takes one
Gagliardo-Nirenberg-Sobolev step on the inner half. Closure is what makes the second half work:
the gradient of `F i` is again a member of the family, so the hypothesis supplies its `Lq` bound
with no separate induction on the order of differentiation. -/
theorem memLp_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι} :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, s < d → (2 : ℝ≥0) ≤ q →
      2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ / 2 ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      (∀ i, HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
      ∀ i, MemLp (F i) q (volume.restrict (Metric.ball c r)) := by
  intro s
  induction s with
  | zero =>
    intro q r R _ hq2 hqs hr hrR _ hmem i
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at this
      linarith
    -- At the bottom rung the exponent is `2` itself, since `1/q ≥ 1/2` caps it there.
    have hq2' : q ≤ 2 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_ofNat]
      refine (inv_le_inv₀ (by norm_num) hq0).mp ?_
      simpa using hqs
    have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hqE : (q : ℝ≥0∞) ≤ 2 := by exact_mod_cast hq2'
    exact ((hmem i).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).mono_exponent hqE
  | succ s ih =>
    intro q r R hsd hq2 hqs hr hrR hgrad hmem i
    -- The dimension is at least two, since the rung `s + 1` sits strictly below it.
    have hd2n : 2 ≤ d := le_trans (Nat.le_add_left 2 s) (Nat.succ_le_of_lt hsd)
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2n
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hdinv : (d : ℝ)⁻¹ ≤ 2⁻¹ := by
      have := inv_anti₀ (b := (2 : ℝ)) (by norm_num) hd2
      simpa using this
    have hdinv0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
    have hqinv0 : (0 : ℝ) < (q : ℝ)⁻¹ := by
      have h2q : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at h2q
      exact inv_pos.mpr (by linarith)
    have hqinv : (q : ℝ)⁻¹ ≤ 2⁻¹ := by
      have h2q : ((2 : ℝ≥0) : ℝ) ≤ (q : ℝ) := NNReal.coe_le_coe.mpr hq2
      simp only [NNReal.coe_ofNat] at h2q
      have := inv_anti₀ (b := (2 : ℝ)) (by norm_num) h2q
      simpa using this
    push_cast at hqs
    -- The midpoint of the gap, so that the rung shrinks the ball without leaving `r`.
    set r' : ℝ := (r + R) / 2 with hr'_def
    have hrr' : r < r' := by rw [hr'_def]; linarith
    have hr'R : r' < R := by rw [hr'_def]; linarith
    have hr' : (0 : ℝ) < r' := lt_trans hr hrr'
    -- The exponent of the rung below, `1/Q = 1/2 - s/(2d)`.
    set t : ℝ := 2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ / 2 with ht_def
    have ht0 : 0 < t := by
      have hs : (s : ℝ) < (d : ℝ) := by exact_mod_cast Nat.lt_of_succ_lt hsd
      have hmul : (s : ℝ) * (d : ℝ)⁻¹ < 1 := by
        rw [← mul_inv_cancel₀ hdpos.ne']
        exact mul_lt_mul_of_pos_right hs hdinv0
      rw [ht_def]; linarith
    have ht2 : t ≤ 2⁻¹ := by
      have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
      rw [ht_def]; linarith
    set Q : ℝ≥0 := Real.toNNReal t⁻¹ with hQ_def
    have hQcoe : ((Q : ℝ≥0) : ℝ) = t⁻¹ := by
      rw [hQ_def]
      exact Real.coe_toNNReal _ (inv_nonneg.mpr ht0.le)
    have hQ0 : (0 : ℝ) < (Q : ℝ) := by rw [hQcoe]; exact inv_pos.mpr ht0
    have hQinv : ((Q : ℝ≥0) : ℝ)⁻¹ = t := by rw [hQcoe, inv_inv]
    have hQ2 : (2 : ℝ≥0) ≤ Q := by
      rw [← NNReal.coe_le_coe, NNReal.coe_ofNat, hQcoe]
      have := inv_anti₀ ht0 ht2
      simpa using this
    -- The exponent the inequality is applied at, `1/p = 1/q + 1/d`.
    set u : ℝ := (q : ℝ)⁻¹ + (d : ℝ)⁻¹ with hu_def
    have hu0 : 0 < u := by rw [hu_def]; linarith
    have hu1 : u ≤ 1 := by rw [hu_def]; linarith
    set p : ℝ≥0 := Real.toNNReal u⁻¹ with hp_def
    have hpcoe : ((p : ℝ≥0) : ℝ) = u⁻¹ := by
      rw [hp_def]
      exact Real.coe_toNNReal _ (inv_nonneg.mpr hu0.le)
    have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hpcoe]; exact inv_pos.mpr hu0
    have hpinv : ((p : ℝ≥0) : ℝ)⁻¹ = u := by rw [hpcoe, inv_inv]
    have hp1 : (1 : ℝ≥0) ≤ p := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one, hpcoe]
      have := inv_anti₀ hu0 hu1
      simpa using this
    -- The half-step is what keeps the applied exponent below the rung's own.
    have htu : t ≤ u := by rw [ht_def, hu_def]; linarith
    have hpQ : p ≤ Q := by
      rw [← NNReal.coe_le_coe]
      refine (inv_le_inv₀ hQ0 hp0).mp ?_
      rw [hQinv, hpinv]; exact htu
    have hpp' : ((q : ℝ≥0) : ℝ)⁻¹ = ((p : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
      rw [hpinv, hu_def]; ring
    -- The rung below, on the outer half, for the whole family at once.
    have hQmem : ∀ j, MemLp (F j) Q (volume.restrict (Metric.ball c r')) :=
      ih (Nat.lt_of_succ_lt hsd) hQ2 (le_of_eq hQinv.symm) hr' hr'R hgrad hmem
    obtain ⟨_K, hK⟩ :=
      exists_eLpNorm_sobolevConj_le_of_le (p := p) (q := Q) (p' := q) hd c hp1 hpQ hpp' hr hrr'
    exact (hK (F i) (fun k => F (nxt i k)) (hQmem i) (fun k => hQmem (nxt i k))
      ((hgrad i).mono (Metric.ball_subset_ball hr'R.le))).1

/-- **Ladder run to the top.** A family closed under differentiation, in `L²` on
`Metric.ball c R`, lies in `L^{2d}` on any smaller concentric ball. Since `2d > d`, this is the
exponent `EllipticPdes.Embedding.morrey_ball` asks for, in every dimension.

The rung count is `d - 1`, and the reciprocal it lands on is `1/2 - (d-1)/(2d) = 1/(2d)`. -/
theorem memLp_two_mul_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hgrad : ∀ i, HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, MemLp (F i) 2 (volume.restrict (Metric.ball c R))) (i : ι) :
    MemLp (F i) (2 * (d : ℝ≥0)) (volume.restrict (Metric.ball c r)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  refine memLp_of_gradClosed hd c (d - 1) (Nat.sub_lt hd Nat.one_pos) ?_ ?_ hr hrR hgrad hmem i
  · rw [← NNReal.coe_le_coe, NNReal.coe_ofNat]
    push_cast
    linarith
  · rw [hsub]
    push_cast
    rw [show ((2 : ℝ) * (d : ℝ))⁻¹ = (d : ℝ)⁻¹ / 2 by field_simp]
    linarith [mul_inv_cancel₀ hdpos.ne']

end EllipticPdes.Embedding
