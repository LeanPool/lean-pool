/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.SobolevLadderFullStep


/-!
# Sobolev ladder at a general base exponent

`EllipticPdes.Embedding.memLp_of_gradClosed_fullStep` iterates the rung from `p` to `p'` with
`1/p' = 1/p - 1/d` starting at `p = 2`. This file runs the same iteration from any
`p₀ ∈ [1, ∞)`, which is the first case of Guo, *Partial Differential Equations*,
Theorem IV.2.3 at the exponent that statement quantifies over.

## Two regimes of a rung

The step from rung `s` to rung `s + 1` applies the inequality at the exponent `p` with
`1/p = 1/q + 1/d`, where `q` is the target. That `p` is admissible when `1/q + 1/d ≤ 1`, and at
`p₀ = 2` the hypotheses already give it: `q ≥ 2` and `d ≥ 2` put both summands at or below
`1/2`. Below `p₀ = 2` the target may sit under the conjugate exponent `d/(d-1)`, and there the
step runs the other way: one rung from `p₀` overshoots the target, and the exponent is lowered
onto it by the finiteness of the ball's measure.

## Dimension one

The base exponent `p₀ = 1` in dimension one asks the rung for the conjugate of `1`, whose
reciprocal is `1 - 1 = 0`. The rung produces a finite exponent and cannot express that, so the
statement takes `1 < d`. In dimension one the rung condition `p₀ * s ≤ d` leaves only `s = 0`,
where the conclusion is the hypothesis with its exponent lowered.

## Main declarations

* `EllipticPdes.Embedding.memLp_of_gradClosed_general`: the ladder at a general base exponent.
* `EllipticPdes.Embedding.memLp_of_gradClosed_general_ideal`: the same at the exponent
  `1/p₀ - s/d` names, which is the exponent of Theorem IV.2.3 case (i).

## References

Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (i), and §5.6.1
Theorem 1 for the single rung.
Guo, *Partial Differential Equations*, Theorem IV.2.3 case (i).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-! ### Reciprocal arithmetic -/

private theorem inv_anti_gen {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha h
  nlinarith [mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', inv_pos.mpr ha, inv_pos.mpr hb]

private theorem le_of_inv_le_inv_gen {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a⁻¹ ≤ b⁻¹) :
    b ≤ a := by
  nlinarith [mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', inv_pos.mpr ha, inv_pos.mpr hb]

private theorem coe_toNNReal_inv_gen {t : ℝ} (ht : 0 < t) :
    ((Real.toNNReal t⁻¹ : ℝ≥0) : ℝ) = t⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.mpr ht.le)

/-! ### The ladder -/

/-- **Sobolev ladder from a general base exponent.** Let `F` assign a function to each index
of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Metric.ball c R`, and let `dep`
record how far an index sits above the root. If every index of depth at most `m` lies in
`L^{p₀}` there and every index of depth below `m` has its weak gradient in the family, then at
rung `s` with `p₀ s ≤ d` every index of depth at most `m - s` lies in `L^q` on
`Metric.ball c r`, for any `q ≥ p₀` whose reciprocal is at least `1/p₀ - s/d`. -/
theorem memLp_of_gradClosed_general (hd : 1 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) :
    ∀ (s : ℕ) {q : ℝ≥0} {r R : ℝ}, (p₀ : ℝ) * s ≤ (d : ℝ) → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ → 0 < r → r < R →
      (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict (Metric.ball c R))) →
      ∀ i, dep i + s ≤ m → MemLp (F i) q (volume.restrict (Metric.ball c r)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdinv0 : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.mpr hdpos
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  have hp₀inv : (p₀ : ℝ)⁻¹ ≤ 1 := by
    have := inv_anti_gen (a := (1 : ℝ)) one_pos hp₀1
    simpa using this
  intro s
  induction s with
  | zero =>
    intro q r R _ hpq hqs hr hrR _ hmem i hi
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hp₀0 (by exact_mod_cast hpq)
    have hqp : q ≤ p₀ := by
      rw [← NNReal.coe_le_coe]
      refine le_of_inv_le_inv_gen hp₀0 hq0 ?_
      simpa using hqs
    have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hqE : (q : ℝ≥0∞) ≤ (p₀ : ℝ≥0∞) := by exact_mod_cast hqp
    exact ((hmem i (by omega)).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).mono_exponent hqE
  | succ s ih =>
    intro q r R hsd hpq hqs hr hrR hgrad hmem i hi
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hp₀0 (by exact_mod_cast hpq)
    have hqinv0 : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr hq0
    have hqinv : (q : ℝ)⁻¹ ≤ (p₀ : ℝ)⁻¹ := inv_anti_gen hp₀0 (by exact_mod_cast hpq)
    have hsdR : (p₀ : ℝ) * ((s : ℝ) + 1) ≤ (d : ℝ) := by push_cast at hsd; linarith
    have hsdprev : (p₀ : ℝ) * (s : ℝ) ≤ (d : ℝ) := by nlinarith
    push_cast at hqs
    -- The midpoint of the gap, so that the rung shrinks the ball without leaving `r`.
    set r' : ℝ := (r + R) / 2 with hr'_def
    have hrr' : r < r' := by rw [hr'_def]; linarith
    have hr'R : r' < R := by rw [hr'_def]; linarith
    have hr' : (0 : ℝ) < r' := lt_trans hr hrr'
    -- The reciprocal at rung `s`, and the exponent naming it.
    set t : ℝ := (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ with ht_def
    have ht0 : 0 < t := by
      have hstep : (s : ℝ) * (d : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ (p₀ : ℝ)⁻¹ := by
        have hmul := mul_le_mul_of_nonneg_right hsdR (mul_pos hdinv0 (inv_pos.mpr hp₀0)).le
        have hc1 : (d : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (p₀ : ℝ)⁻¹ := by
          field_simp
        have hc2 : (p₀ : ℝ) * ((s : ℝ) + 1) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹)
            = ((s : ℝ) + 1) * (d : ℝ)⁻¹ := by field_simp
        rw [hc1, hc2] at hmul
        linarith
      rw [ht_def]; linarith
    have ht_le : t ≤ (p₀ : ℝ)⁻¹ := by
      have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
      rw [ht_def]; linarith
    set Q : ℝ≥0 := Real.toNNReal t⁻¹ with hQ_def
    have hQcoe : ((Q : ℝ≥0) : ℝ) = t⁻¹ := by rw [hQ_def]; exact coe_toNNReal_inv_gen ht0
    have hQ0 : (0 : ℝ) < (Q : ℝ) := by rw [hQcoe]; exact inv_pos.mpr ht0
    have hQinv : ((Q : ℝ≥0) : ℝ)⁻¹ = t := by rw [hQcoe, inv_inv]
    have hp₀Q : p₀ ≤ Q := by
      rw [← NNReal.coe_le_coe, hQcoe]
      have := inv_anti_gen ht0 ht_le
      simpa using this
    have hQmem : ∀ j, dep j + s ≤ m → MemLp (F j) Q (volume.restrict (Metric.ball c r')) :=
      ih hsdprev hp₀Q (le_of_eq hQinv.symm) hr' hr'R hgrad hmem
    by_cases hu1 : (q : ℝ)⁻¹ + (d : ℝ)⁻¹ ≤ 1
    · -- The target is at or above the conjugate exponent, so the rung runs onto it.
      set u : ℝ := (q : ℝ)⁻¹ + (d : ℝ)⁻¹ with hu_def
      have hu0 : 0 < u := by rw [hu_def]; linarith
      set p : ℝ≥0 := Real.toNNReal u⁻¹ with hp_def
      have hpcoe : ((p : ℝ≥0) : ℝ) = u⁻¹ := by rw [hp_def]; exact coe_toNNReal_inv_gen hu0
      have hp0 : (0 : ℝ) < (p : ℝ) := by rw [hpcoe]; exact inv_pos.mpr hu0
      have hpinv : ((p : ℝ≥0) : ℝ)⁻¹ = u := by rw [hpcoe, inv_inv]
      have hp1 : (1 : ℝ≥0) ≤ p := by
        rw [← NNReal.coe_le_coe, NNReal.coe_one, hpcoe]
        have := inv_anti_gen hu0 hu1
        simpa using this
      have htu : t ≤ u := by rw [ht_def, hu_def]; linarith
      have hpQ : p ≤ Q := by
        rw [← NNReal.coe_le_coe]
        refine le_of_inv_le_inv_gen hQ0 hp0 ?_
        rw [hQinv, hpinv]; exact htu
      have hpp' : ((q : ℝ≥0) : ℝ)⁻¹ = ((p : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
        rw [hpinv, hu_def]; ring
      obtain ⟨_K, hK⟩ :=
        exists_eLpNorm_sobolevConj_le_of_le (p := p) (q := Q) (p' := q) (by omega) c hp1 hpQ
          hpp' hr hrr'
      exact (hK (F i) (fun k => F (nxt i k)) (hQmem i (by omega))
        (fun k => hQmem (nxt i k) (by have := hdep i k; omega))
        ((hgrad i (by omega)).mono (Metric.ball_subset_ball hr'R.le))).1
    · -- The target sits below the conjugate exponent, so one rung overshoots it.
      have hu1' : 1 < (q : ℝ)⁻¹ + (d : ℝ)⁻¹ := lt_of_not_ge hu1
      have hqd : 1 - (d : ℝ)⁻¹ < (q : ℝ)⁻¹ := by linarith
      set t₁ : ℝ := (p₀ : ℝ)⁻¹ - (d : ℝ)⁻¹ with ht₁_def
      have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
      have ht₁0 : 0 < t₁ := by
        by_contra hcon
        have hcon' : t₁ ≤ 0 := le_of_not_gt hcon
        have hple : (d : ℝ)⁻¹ ≥ (p₀ : ℝ)⁻¹ := by rw [ht₁_def] at hcon'; linarith
        have hdp : (d : ℝ) ≤ (p₀ : ℝ) := le_of_inv_le_inv_gen hp₀0 hdpos hple
        have hqge : (p₀ : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
        have hqinv' : (q : ℝ)⁻¹ ≤ (d : ℝ)⁻¹ :=
          inv_anti_gen hdpos (le_trans hdp hqge)
        have : (1 : ℝ) < 2 * (d : ℝ)⁻¹ := by linarith
        have hdd : (d : ℝ)⁻¹ ≤ 2⁻¹ := by
          have := inv_anti_gen (a := (2 : ℝ)) (by norm_num) hd2R
          simpa using this
        linarith
      have ht₁_le : t₁ ≤ (p₀ : ℝ)⁻¹ := by rw [ht₁_def]; linarith
      set P : ℝ≥0 := Real.toNNReal t₁⁻¹ with hP_def
      have hPcoe : ((P : ℝ≥0) : ℝ) = t₁⁻¹ := by rw [hP_def]; exact coe_toNNReal_inv_gen ht₁0
      have hP0 : (0 : ℝ) < (P : ℝ) := by rw [hPcoe]; exact inv_pos.mpr ht₁0
      have hPinv : ((P : ℝ≥0) : ℝ)⁻¹ = t₁ := by rw [hPcoe, inv_inv]
      have hp₀P : ((P : ℝ≥0) : ℝ)⁻¹ = ((p₀ : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
        rw [hPinv, ht₁_def]
      -- One rung from `p₀` on the outer half, then the exponent is lowered onto `q`.
      obtain ⟨_K, hK⟩ :=
        exists_eLpNorm_sobolevConj_le (p := p₀) (p' := P) (by omega) c hp₀ hp₀P hr hrr'
      have hmem' : ∀ j, dep j ≤ m → MemLp (F j) p₀ (volume.restrict (Metric.ball c r')) :=
        fun j hj => (hmem j hj).mono_measure
          (Measure.restrict_mono (Metric.ball_subset_ball hr'R.le) le_rfl)
      have hPmem : MemLp (F i) P (volume.restrict (Metric.ball c r)) :=
        (hK (F i) (fun k => F (nxt i k)) (hmem' i (by omega))
          (fun k => hmem' (nxt i k) (by have := hdep i k; omega))
          ((hgrad i (by omega)).mono (Metric.ball_subset_ball hr'R.le))).1
      have hqP : q ≤ P := by
        rw [← NNReal.coe_le_coe]
        refine le_of_inv_le_inv_gen hP0 hq0 ?_
        rw [hPinv, ht₁_def]
        have hs0 : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
        linarith
      have : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
      exact hPmem.mono_exponent (by exact_mod_cast hqP)

/-! ### The exponent of case (i) -/

/-- **Ladder at the exponent case (i) names.** Under the strict rung condition
`p₀ s < d`, which is the `k < n/p` of Evans §5.6.3 Theorem 6, the reciprocal `1/p₀ - s/d` is
positive and names a finite exponent; the ladder lands on it. -/
theorem memLp_of_gradClosed_general_ideal (hd : 1 < d) (c : EuclideanSpace ℝ (Fin d))
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) (s : ℕ) {r R : ℝ}
    (hsd : (p₀ : ℝ) * s < (d : ℝ)) (hr : 0 < r) (hrR : r < R)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict (Metric.ball c R)))
    (i : ι) (hi : dep i + s ≤ m) :
    MemLp (F i) (Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹)
      (volume.restrict (Metric.ball c r)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hp₀1 : (1 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast hp₀
  have hp₀0 : (0 : ℝ) < (p₀ : ℝ) := by linarith
  set t : ℝ := (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ with ht_def
  -- The strict rung condition is exactly positivity of the landing reciprocal.
  have ht0 : 0 < t := by
    have hmul := mul_lt_mul_of_pos_right hsd
      (mul_pos (inv_pos.mpr hdpos) (inv_pos.mpr hp₀0))
    have hc1 : (d : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (p₀ : ℝ)⁻¹ := by field_simp
    have hc2 : (p₀ : ℝ) * (s : ℝ) * ((d : ℝ)⁻¹ * (p₀ : ℝ)⁻¹) = (s : ℝ) * (d : ℝ)⁻¹ := by
      field_simp
    rw [hc1, hc2] at hmul
    rw [ht_def]; linarith
  have ht_le : t ≤ (p₀ : ℝ)⁻¹ := by
    have : 0 ≤ (s : ℝ) * (d : ℝ)⁻¹ := by positivity
    rw [ht_def]; linarith
  have hqcoe : ((Real.toNNReal t⁻¹ : ℝ≥0) : ℝ) = t⁻¹ := coe_toNNReal_inv_gen ht0
  have hqinv : ((Real.toNNReal t⁻¹ : ℝ≥0) : ℝ)⁻¹ = t := by rw [hqcoe, inv_inv]
  have hp₀q : p₀ ≤ Real.toNNReal t⁻¹ := by
    rw [← NNReal.coe_le_coe, hqcoe]
    have := inv_anti_gen ht0 ht_le
    simpa using this
  exact memLp_of_gradClosed_general hd c hp₀ hdep s (le_of_lt hsd) hp₀q
    (le_of_eq hqinv.symm) hr hrR hgrad hmem i hi

end EllipticPdes.Embedding
