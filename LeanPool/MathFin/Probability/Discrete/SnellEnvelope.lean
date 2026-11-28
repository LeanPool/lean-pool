/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Probability.Martingale.Basic

/-!
# The Snell envelope on a filtered probability space

The discrete-time Snell envelope of an adapted integrable reward `Z` is the backward recursion
`U_i = max(Z_i, 𝔼[U_{i+1} | 𝓕_i])` from the horizon `N`; early exercise is allowed at the times
of an exercise set `X` (at the other times the recursion is the bare continuation value
`𝔼[U_{i+1} | 𝓕_i]`), so `X = univ` is the American envelope and a finite `X` the Bermudan one.
This is the library's general envelope: the American-put stopping rules
(`Models/BlackScholes/American/Stopping/`) are its `X = univ` instances, and the binomial tree's
pathwise envelope `snell` (`Models/Binomial/SnellEnvelope.lean`), computed with the node-average
conditional expectation, agrees with it almost surely (`snell_ae_eq_snellEnvelope`,
`Models/Binomial/PathMeasure.lean`).

* `snellEnvelopeAux P 𝓕 X Z n i` — the recursion with `n` steps left from time `i`.
* `snellEnvelope P 𝓕 X Z N i` — the envelope for the horizon `N`, frozen at `Z N` past it.
* `snellEnvelope_supermartingale` — it is a supermartingale.
* `snellEnvelope_le_supermartingale` — it is the smallest one dominating the reward at the
  exercise times and at the horizon.
* `snellEnvelopeAux_const_mul` — it is positively homogeneous in the reward.

## Main definitions

* `snellEnvelopeAux`: the Snell recursion with `n` steps left from time `i`, taking
  `max (Z i) 𝔼[· | 𝓕 i]` at exercise times in `X` and the bare conditional expectation elsewhere.
* `snellEnvelope`: the Snell envelope of a reward `Z` for horizon `N` and exercise set `X`
  (`X = univ` is the American envelope, a finite `X` the Bermudan one).

## Main results

* `snellEnvelope_succ_of_mem`, `snellEnvelope_succ_of_notMem`: the backward recursion, with and
  without exercise, for `i < N`.
* `snellEnvelope_dominates`: the envelope dominates the reward at exercise times and past the
  horizon.
* `snellEnvelope_supermartingale`: the envelope is a supermartingale.
* `snellEnvelope_le_supermartingale`: minimality, the envelope lies a.s. below any supermartingale
  dominating the reward a.s. at the exercise times up to the horizon.
* `snellEnvelope_integrable`, `snellEnvelope_stronglyAdapted`: integrability and adaptedness.

## Tags

Snell envelope, optimal stopping, American option, Bermudan option, early exercise,
backward recursion, smallest supermartingale, MSC 60G40, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {X : Set ℕ} {Z : ℕ → Ω → ℝ}

open scoped Classical in
/-- The Snell recursion with `n` steps left from time `i`, exercise allowed at the times in `X`:
it is `Z i` for `n = 0`; for `n + 1` it is the continuation value
`P[snellEnvelopeAux P 𝓕 X Z n (i + 1) | 𝓕 i]`, maxed with `Z i` when `i ∈ X`. -/
noncomputable def snellEnvelopeAux (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (X : Set ℕ) (Z : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0, i => Z i
  | n + 1, i => fun ω ↦
    if i ∈ X then max (Z i ω) (P[snellEnvelopeAux P 𝓕 X Z n (i + 1) | 𝓕 i] ω)
    else P[snellEnvelopeAux P 𝓕 X Z n (i + 1) | 𝓕 i] ω

/-- The **Snell envelope** of `Z` for the horizon `N`, exercise times `X`: the recursion run for
the `N - i` remaining steps from `min i N`, so it is frozen at `Z N` past the horizon. -/
noncomputable def snellEnvelope (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (X : Set ℕ) (Z : ℕ → Ω → ℝ) (N i : ℕ) : Ω → ℝ :=
  snellEnvelopeAux P 𝓕 X Z (N - i) (min i N)

theorem snellEnvelopeAux_succ_of_mem {n i : ℕ} (hi : i ∈ X) :
    snellEnvelopeAux P 𝓕 X Z (n + 1) i =
      fun ω ↦ max (Z i ω) (P[snellEnvelopeAux P 𝓕 X Z n (i + 1) | 𝓕 i] ω) := by
  rw [snellEnvelopeAux]
  exact funext fun ω ↦ ite_eq_left hi

theorem snellEnvelopeAux_succ_of_notMem {n i : ℕ} (hi : i ∉ X) :
    snellEnvelopeAux P 𝓕 X Z (n + 1) i = P[snellEnvelopeAux P 𝓕 X Z n (i + 1) | 𝓕 i] := by
  rw [snellEnvelopeAux]
  exact funext fun ω ↦ ite_eq_right hi

theorem snellEnvelopeAux_measurable (hZ : Adapted 𝓕 Z) (n i : ℕ) :
    Measurable[𝓕 i] (snellEnvelopeAux P 𝓕 X Z n i) := by
  cases n with
  | zero => exact hZ i
  | succ n =>
    by_cases hi : i ∈ X
    · rw [snellEnvelopeAux_succ_of_mem hi]
      exact (hZ i).max stronglyMeasurable_condExp.measurable
    · rw [snellEnvelopeAux_succ_of_notMem hi]
      exact stronglyMeasurable_condExp.measurable

theorem snellEnvelopeAux_integrable (hZ : ∀ i, Integrable (Z i) P) (n i : ℕ) :
    Integrable (snellEnvelopeAux P 𝓕 X Z n i) P := by
  cases n with
  | zero => exact hZ i
  | succ n =>
    by_cases hi : i ∈ X
    · rw [snellEnvelopeAux_succ_of_mem hi]
      exact (hZ i).sup integrable_condExp
    · rw [snellEnvelopeAux_succ_of_notMem hi]
      exact integrable_condExp

/-- At the horizon and at the exercise times the envelope dominates the reward. -/
theorem snellEnvelopeAux_dominates {n i : ℕ} (h : n = 0 ∨ i ∈ X) (ω : Ω) :
    Z i ω ≤ snellEnvelopeAux P 𝓕 X Z n i ω := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    rw [snellEnvelopeAux_succ_of_mem (h.resolve_left n.succ_ne_zero)]
    exact le_max_left _ _

/-- The continuation value is at most the envelope: the supermartingale step. -/
theorem snellEnvelopeAux_condExp_le (n i : ℕ) (ω : Ω) :
    P[snellEnvelopeAux P 𝓕 X Z n (i + 1) | 𝓕 i] ω ≤ snellEnvelopeAux P 𝓕 X Z (n + 1) i ω := by
  by_cases hi : i ∈ X
  · rw [snellEnvelopeAux_succ_of_mem hi]
    exact le_max_right _ _
  · rw [snellEnvelopeAux_succ_of_notMem hi]

theorem snellEnvelope_after_horizon {N i : ℕ} (hNi : N ≤ i) :
    snellEnvelope P 𝓕 X Z N i = Z N := by
  simp only [snellEnvelope, Nat.sub_eq_zero_of_le hNi, min_eq_right hNi, snellEnvelopeAux]

theorem snellEnvelope_succ_of_mem {N i : ℕ} (hi : i < N) (hX : i ∈ X) :
    snellEnvelope P 𝓕 X Z N i =
      fun ω ↦ max (Z i ω) (P[snellEnvelope P 𝓕 X Z N (i + 1) | 𝓕 i] ω) := by
  have hn : N - i = (N - (i + 1)) + 1 := by omega
  rw [snellEnvelope, min_eq_left hi.le, hn, snellEnvelopeAux_succ_of_mem hX]
  simp only [snellEnvelope, min_eq_left (show i + 1 ≤ N by omega)]

theorem snellEnvelope_succ_of_notMem {N i : ℕ} (hi : i < N) (hX : i ∉ X) :
    snellEnvelope P 𝓕 X Z N i = P[snellEnvelope P 𝓕 X Z N (i + 1) | 𝓕 i] := by
  have hn : N - i = (N - (i + 1)) + 1 := by omega
  rw [snellEnvelope, min_eq_left hi.le, hn, snellEnvelopeAux_succ_of_notMem hX]
  simp only [snellEnvelope, min_eq_left (show i + 1 ≤ N by omega)]

theorem snellEnvelope_stronglyAdapted (hZ : Adapted 𝓕 Z) (N : ℕ) :
    StronglyAdapted 𝓕 (snellEnvelope P 𝓕 X Z N) := fun i ↦
  ((snellEnvelopeAux_measurable hZ (N - i) (min i N)).mono (𝓕.mono (min_le_left _ _))
      le_rfl).stronglyMeasurable

theorem snellEnvelope_integrable (hZ : ∀ i, Integrable (Z i) P) (N i : ℕ) :
    Integrable (snellEnvelope P 𝓕 X Z N i) P :=
  snellEnvelopeAux_integrable hZ _ _

/-- The envelope dominates the reward at the exercise times and past the horizon. -/
theorem snellEnvelope_dominates {N i : ℕ} (h : i ∈ X ∨ N ≤ i) (ω : Ω) :
    Z (min i N) ω ≤ snellEnvelope P 𝓕 X Z N i ω := by
  rcases le_or_gt N i with hNi | hiN
  · exact snellEnvelopeAux_dominates (Or.inl (Nat.sub_eq_zero_of_le hNi)) ω
  · exact snellEnvelopeAux_dominates
      (Or.inr (by rw [min_eq_left hiN.le]; exact h.resolve_right hiN.not_ge)) ω

/-- **Minimality**: an integrable supermartingale `U` that dominates the reward almost surely at
the exercise times in `[i, i + n)` and at time `i + n` dominates the envelope with `n` steps
left from `i`. -/
theorem snellEnvelopeAux_le_supermartingale {U : ℕ → Ω → ℝ} (hU : Supermartingale U 𝓕 P)
    (hi : ∀ i, Integrable (Z i) P) (n i : ℕ)
    (hdom : ∀ j, i ≤ j → j ≤ i + n → (j ∈ X ∨ j = i + n) → Z j ≤ᵐ[P] U j) :
    snellEnvelopeAux P 𝓕 X Z n i ≤ᵐ[P] U i := by
  induction n generalizing i with
  | zero => exact hdom i le_rfl le_rfl (Or.inr rfl)
  | succ n ih =>
    have hc := condExp_mono (m := 𝓕 i) (snellEnvelopeAux_integrable hi n (i + 1))
      (hU.integrable (i + 1))
      (ih (i + 1) fun j hj hjn h ↦ hdom j (i.le_succ.trans hj) (by omega)
        (h.imp_right fun h ↦ by omega))
    by_cases hX : i ∈ X
    · rw [snellEnvelopeAux_succ_of_mem hX]
      filter_upwards [hdom i le_rfl (by omega) (Or.inl hX), hc, hU.2.1 i (i + 1) i.le_succ]
        with ω hz hc hu
      exact max_le hz (hc.trans hu)
    · rw [snellEnvelopeAux_succ_of_notMem hX]
      filter_upwards [hc, hU.2.1 i (i + 1) i.le_succ] with ω hc hu
      exact hc.trans hu

/-- **The Snell envelope is the smallest supermartingale** dominating the reward (almost surely)
at the exercise times up to the horizon `N` and at `N`. -/
theorem snellEnvelope_le_supermartingale {N : ℕ} {U : ℕ → Ω → ℝ} (hU : Supermartingale U 𝓕 P)
    (hi : ∀ i, Integrable (Z i) P) (hdom : ∀ j ≤ N, (j ∈ X ∨ j = N) → Z j ≤ᵐ[P] U j)
    {i : ℕ} (hiN : i ≤ N) : snellEnvelope P 𝓕 X Z N i ≤ᵐ[P] U i := by
  simpa only [snellEnvelope, min_eq_left hiN] using
    snellEnvelopeAux_le_supermartingale hU hi (N - i) i fun j hij hj h ↦
      hdom j (by omega) (h.imp_right fun h ↦ by omega)

/-- The envelope is positively homogeneous in the reward. -/
theorem snellEnvelopeAux_const_mul {a : ℝ} (ha : 0 ≤ a) (n i : ℕ) :
    snellEnvelopeAux P 𝓕 X (fun j ω ↦ a * Z j ω) n i =ᵐ[P]
      fun ω ↦ a * snellEnvelopeAux P 𝓕 X Z n i ω := by
  induction n generalizing i with
  | zero => exact Eventually.of_forall fun _ ↦ rfl
  | succ n ih =>
    have hc := condExp_congr_ae (m := 𝓕 i) (ih (i + 1))
    have hm := condExp_smul (μ := P) a (snellEnvelopeAux P 𝓕 X Z n (i + 1)) (𝓕 i)
    by_cases hX : i ∈ X
    · rw [snellEnvelopeAux_succ_of_mem hX, snellEnvelopeAux_succ_of_mem hX]
      filter_upwards [hc, hm] with ω hω hmω
      rw [hω]
      change P[fun ω ↦ a * snellEnvelopeAux P 𝓕 X Z n (i + 1) ω | 𝓕 i] ω = _ at hmω
      rw [hmω]
      exact (mul_max_of_nonneg _ _ ha).symm
    · rw [snellEnvelopeAux_succ_of_notMem hX, snellEnvelopeAux_succ_of_notMem hX]
      filter_upwards [hc, hm] with ω hω hmω
      rw [hω]
      exact hmω

variable [IsProbabilityMeasure P]

/-- **The Snell envelope is a supermartingale.** -/
theorem snellEnvelope_supermartingale (hZ : Adapted 𝓕 Z) (hi : ∀ i, Integrable (Z i) P)
    (N : ℕ) : Supermartingale (snellEnvelope P 𝓕 X Z N) 𝓕 P := by
  refine supermartingale_nat (snellEnvelope_stronglyAdapted hZ N) (snellEnvelope_integrable hi N)
    fun i ↦ ?_
  by_cases hiN : i < N
  · by_cases hX : i ∈ X
    · rw [snellEnvelope_succ_of_mem hiN hX]
      exact Eventually.of_forall fun ω ↦ le_max_right _ _
    · rw [snellEnvelope_succ_of_notMem hiN hX]
  · have hNi : N ≤ i := le_of_not_gt hiN
    rw [snellEnvelope_after_horizon hNi, snellEnvelope_after_horizon (hNi.trans i.le_succ),
      condExp_of_stronglyMeasurable (𝓕.le i)
        (((hZ N).mono (𝓕.mono hNi) le_rfl).stronglyMeasurable) (hi N)]

end MathFin
