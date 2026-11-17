/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Construction
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Dyadic chaining for the Kolmogorov-Chentsov theorem

The deterministic half of the Kolmogorov-Chentsov construction. A function that is
`α`-Hölder on a dense set `D ⊆ ℝ` at scales `≤ δ₀` is uniformly continuous on `D` and so
extends continuously to `ℝ`; the dyadic rationals `{k · 2^(-n) : k ∈ ℤ, n ∈ ℕ}` are such a
dense set, and the level-`n` dyadic truncation `⌊x · 2^n⌋ / 2^n` approximates each real from
below. Chaining these truncations turns a bound `b n` on the consecutive level-`n` dyadic
increments of `f` into `α`-Hölder continuity of `f` on the dyadics of `[0, 1)`
(`dyadic_holder_chaining`), for `b n = C · 2^(-α n)`.

No probability enters here; the random increment bounds are supplied in
`LevyStochCalc.Brownian.ContinuityKolmogorovBounds`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

/-- **Step 2: scale-limited Hölder on a dense set → continuous extension.**

A function `f : ℝ → ℝ` that is α-Hölder on a dense set `D ⊆ ℝ` *at scales
`≤ δ₀`* (i.e. `|f s − f t| ≤ K·|s−t|^α` whenever `s, t ∈ D` and
`|s − t| ≤ δ₀`) is uniformly continuous on `D`, hence extends to a continuous
function
on `ℝ` agreeing with `f` on `D`. The scale restriction suffices because uniform
continuity only constrains small distances; this is exactly what the dyadic
chaining produces (`dyadic_holder_chaining`, scales `≤ 2^{−N}`).

Proof via `Dense.uniformContinuous_extend`. -/
lemma holder_dense_extends_continuous {α K δ₀ : ℝ}
    (hα : 0 < α) (_hK : 0 < K) (hδ₀ : 0 < δ₀)
    (D : Set ℝ) (h_dense : Dense D)
    (f : ℝ → ℝ)
    (h_holder_dyadic : ∀ s ∈ D, ∀ t ∈ D, |s - t| ≤ δ₀ →
      |f s - f t| ≤ K * |s - t| ^ α) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ s ∈ D, g s = f s := by
  -- f restricted to D is uniformly continuous (scale-limited α-Hölder ⇒ UC).
  set fD : D → ℝ := fun x => f x.1 with hfD_def
  have h_uc : UniformContinuous fD := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    -- Choose δ = min δ₀ (ε / (2 * (K + 1)))^(1/α).
    set C : ℝ := 2 * (K + 1) with hC_def
    have hC_pos : 0 < C := by simp [hC_def]; linarith
    refine ⟨min δ₀ ((ε / C) ^ (1/α)), ?_, ?_⟩
    · exact lt_min hδ₀ (Real.rpow_pos_of_pos (div_pos hε hC_pos) _)
    · intro s t h_dist
      have h_dist_pos : 0 ≤ |s.1 - t.1| := abs_nonneg _
      have h_dist_δ₀ : |s.1 - t.1| ≤ δ₀ := by
        rw [show |s.1 - t.1| = dist s.1 t.1 from (Real.dist_eq _ _).symm]
        exact le_of_lt (lt_of_lt_of_le h_dist (min_le_left _ _))
      have h_holder := h_holder_dyadic s.1 s.2 t.1 t.2 h_dist_δ₀
      -- |s.1 - t.1| < δ
      have h_dist_real : |s.1 - t.1| < (ε / C) ^ (1/α) := by
        rw [show |s.1 - t.1| = dist s.1 t.1 from (Real.dist_eq _ _).symm]
        exact lt_of_lt_of_le h_dist (min_le_right _ _)
      -- |s.1 - t.1|^α < ε/C
      have h_pow_lt : |s.1 - t.1| ^ α < ε / C := by
        have h1 : |s.1 - t.1| ^ α < ((ε / C) ^ (1/α)) ^ α :=
          Real.rpow_lt_rpow h_dist_pos h_dist_real hα
        rw [show ((ε / C) ^ (1/α)) ^ α = ε / C from ?_] at h1
        · exact h1
        · rw [← Real.rpow_mul (le_of_lt (div_pos hε hC_pos))]
          rw [one_div, inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]
      -- K · |s.1 - t.1|^α < K · ε / C ≤ ε/2 (when K ≤ K+1, K/(K+1) ≤ 1)
      -- Actually let me just bound by (K+1) · ε/C = ε/2 < ε.
      have hK1_pos : 0 < K + 1 := by linarith
      have h_K_le_K1 : K ≤ K + 1 := by linarith
      have h_holder_K1 : |f s.1 - f t.1| ≤ (K + 1) * |s.1 - t.1| ^ α := by
        refine le_trans h_holder (mul_le_mul_of_nonneg_right h_K_le_K1 ?_)
        exact Real.rpow_nonneg h_dist_pos _
      have h_bd : (K + 1) * |s.1 - t.1| ^ α < (K + 1) * (ε / C) :=
        mul_lt_mul_of_pos_left h_pow_lt hK1_pos
      have h_C_eq : (K + 1) * (ε / C) = ε / 2 := by
        simp only [hC_def]
        have h_K1_ne : (K + 1 : ℝ) ≠ 0 := ne_of_gt hK1_pos
        field_simp
      rw [h_C_eq] at h_bd
      have h_final : |f s.1 - f t.1| < ε / 2 := lt_of_le_of_lt h_holder_K1 h_bd
      have h_dist_eq : dist (fD s) (fD t) = |f s.1 - f t.1| := by
        rw [Real.dist_eq, hfD_def]
      rw [h_dist_eq]
      linarith
  -- Apply Dense.uniformContinuous_extend
  refine ⟨h_dense.extend fD, ?_, ?_⟩
  · -- Continuous (extend fD)
    exact (Dense.uniformContinuous_extend h_dense h_uc).continuous
  · -- ∀ s ∈ D, extend fD s = f s
    intro s hs
    exact Dense.extend_of_ind h_dense h_uc ⟨s, hs⟩

/-- The set of dyadic rationals: `D := {k * 2^{-n} : k ∈ ℤ, n ∈ ℕ}`. Dense in ℝ. -/
def dyadicRationals : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, ∃ n : ℕ, x = (k : ℝ) * (2 : ℝ)^(-n : ℤ)}

/-- `0` is a dyadic rational (`k = 0`, `n = 0`). -/
lemma zero_mem_dyadicRationals : (0 : ℝ) ∈ dyadicRationals := by
  refine ⟨0, 0, ?_⟩
  simp

/-- Every integer is a dyadic rational (`n = 0`). -/
lemma intCast_mem_dyadicRationals (k : ℤ) : (k : ℝ) ∈ dyadicRationals := by
  refine ⟨k, 0, ?_⟩
  simp

/-- **Dyadic rationals are dense in ℝ.** Given any `x : ℝ` and any `r > 0`,
choose `n` with `(1/2)^n < r`, then `k := ⌊x · 2^n⌋`; the dyadic
`k · 2^(-n)` is within `r` of `x`. -/
lemma dense_dyadicRationals : Dense dyadicRationals := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  set k : ℤ := ⌊x * (2 : ℝ)^n⌋ with hk_def
  set y : ℝ := (k : ℝ) * (2 : ℝ)^(-n : ℤ) with hy_def
  refine ⟨y, ?_, ?_⟩
  · rw [Metric.mem_ball]
    have h2n_pos : (0 : ℝ) < (2 : ℝ)^n := by positivity
    have h_pow_neg_eq : ((2 : ℝ) ^ (-n : ℤ)) = ((2 : ℝ)^n)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have h_floor_bound : x * (2 : ℝ)^n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ x * (2 : ℝ)^n :=
      ⟨Int.sub_one_lt_floor _, Int.floor_le _⟩
    have h_diff : y - x = ((k : ℝ) - x * (2 : ℝ)^n) * ((2 : ℝ)^n)⁻¹ := by
      rw [hy_def, h_pow_neg_eq]; field_simp
    rw [Real.dist_eq, h_diff, abs_mul, abs_inv, abs_of_pos h2n_pos]
    have h_bound1 : |((k : ℝ) - x * (2 : ℝ)^n)| ≤ 1 := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [h_floor_bound.1]
      · linarith [h_floor_bound.2]
    have h_step : |((k : ℝ) - x * (2 : ℝ)^n)| * ((2 : ℝ)^n)⁻¹
        ≤ 1 * ((2 : ℝ)^n)⁻¹ := by
      apply mul_le_mul_of_nonneg_right h_bound1
      positivity
    rw [one_mul] at h_step
    refine lt_of_le_of_lt h_step ?_
    have h_inv_eq : ((2 : ℝ)^n)⁻¹ = (1 / 2 : ℝ)^n := by rw [one_div, inv_pow]
    rw [h_inv_eq]
    exact hn
  · exact ⟨k, n, rfl⟩

/-- Dyadic rationals are closed under adding an integer. -/
lemma add_intCast_mem_dyadicRationals {x : ℝ} (hx : x ∈ dyadicRationals) (j : ℤ) :
    x + (j : ℝ) ∈ dyadicRationals := by
  obtain ⟨k, n, rfl⟩ := hx
  refine ⟨k + j * 2 ^ n, n, ?_⟩
  rw [zpow_neg, zpow_natCast]
  push_cast
  field_simp

/-- Dyadic rationals are closed under subtracting an integer. -/
lemma sub_intCast_mem_dyadicRationals {x : ℝ} (hx : x ∈ dyadicRationals) (j : ℤ) :
    x - (j : ℝ) ∈ dyadicRationals := by
  have := add_intCast_mem_dyadicRationals hx (-j)
  simpa [sub_eq_add_neg] using this

/-- For every `t : ℝ`, there is a sequence of dyadic rationals strictly
increasing to `t`. Wrapper around `Dense.exists_seq_strictMono_tendsto` +
`dense_dyadicRationals`. -/
lemma exists_seq_dyadic_tendsto (t : ℝ) :
    ∃ u : ℕ → ℝ, StrictMono u
      ∧ (∀ n, u n ∈ Set.Iio t ∩ dyadicRationals)
      ∧ Filter.Tendsto u Filter.atTop (nhds t) :=
  dense_dyadicRationals.exists_seq_strictMono_tendsto t

/-! ### Deterministic dyadic chaining

A real function whose consecutive level-`n` dyadic increments on `[0,1]` are
bounded by `b n` (with `∑ b n` controlled) is Hölder on the dyadics of `[0,1)`.
This is the path-by-path core of the continuous-modification construction: the
a.s. Borel–Cantelli increment bounds feed `b n = C · 2^(-α n)`. -/

/-- Level-`n` dyadic truncation `⌊x·2ⁿ⌋ / 2ⁿ` — the largest level-`n` dyadic
`≤ x`. -/
noncomputable def dyadicTrunc (n : ℕ) (x : ℝ) : ℝ := (⌊x * 2 ^ n⌋ : ℝ) / 2 ^ n

lemma dyadicTrunc_mem_dyadicRationals (n : ℕ) (x : ℝ) :
    dyadicTrunc n x ∈ dyadicRationals := by
  refine ⟨⌊x * 2 ^ n⌋, n, ?_⟩
  rw [dyadicTrunc, zpow_neg, zpow_natCast, div_eq_mul_inv]

lemma dyadicTrunc_le (n : ℕ) (x : ℝ) : dyadicTrunc n x ≤ x := by
  rw [dyadicTrunc, div_le_iff₀ (by positivity)]
  exact Int.floor_le _

/-- `2⌊y⌋ ≤ ⌊2y⌋ ≤ 2⌊y⌋ + 1`. -/
lemma floor_two_mul_bounds (y : ℝ) :
    2 * ⌊y⌋ ≤ ⌊2 * y⌋ ∧ ⌊2 * y⌋ ≤ 2 * ⌊y⌋ + 1 := by
  refine ⟨?_, ?_⟩
  · apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le y]
  · have h2 : ⌊2 * y⌋ < 2 * ⌊y⌋ + 2 := by
      apply Int.floor_lt.mpr
      push_cast
      linarith [Int.lt_floor_add_one y]
    omega

/-- **Single refinement step.** For `x ∈ [0,1]`, the level-`(n+1)` truncation
differs from the level-`n` truncation by at most one consecutive level-`(n+1)`
dyadic increment, hence `|f(trunc_{n+1} x) − f(trunc_n x)| ≤ b (n+1)`. -/
lemma dyadicTrunc_succ_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {n : ℕ} (hn : N ≤ n + 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |f (dyadicTrunc (n + 1) x) - f (dyadicTrunc n x)| ≤ b (n + 1) := by
  set k : ℤ := ⌊x * 2 ^ n⌋ with hk
  set j : ℤ := ⌊x * 2 ^ (n + 1)⌋ with hj
  have hjk : j = ⌊2 * (x * 2 ^ n)⌋ := by rw [hj]; congr 1; rw [pow_succ]; ring
  obtain ⟨hlo, hhi⟩ := floor_two_mul_bounds (x * 2 ^ n)
  rw [← hjk] at hlo hhi
  have hk0 : 0 ≤ k := by
    rw [hk]; apply Int.floor_nonneg.mpr; positivity
  -- Truncations expressed over the common denominator `2^(n+1)`.
  have hDn : dyadicTrunc n x = ((2 * k : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [dyadicTrunc, ← hk, pow_succ]; push_cast; ring
  have hDn1 : dyadicTrunc (n + 1) x = ((j : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [dyadicTrunc, ← hj]
  rcases (by omega : j = 2 * k ∨ j = 2 * k + 1) with hjeq | hjeq
  · -- No refinement: the two truncations coincide.
    rw [hDn1, hDn, hjeq, sub_self, abs_zero]
    exact hb (n + 1)
  · -- One refinement step `(2k) → (2k+1)` at level `n+1`.
    have hbound : 2 * k + 1 ≤ (2 : ℤ) ^ (n + 1) := by
      have hjle : (j : ℝ) ≤ x * 2 ^ (n + 1) := Int.floor_le _
      have hj_le : (j : ℝ) ≤ (2 : ℝ) ^ (n + 1) :=
        le_trans hjle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (n + 1)])
      have : (j : ℤ) ≤ (2 : ℤ) ^ (n + 1) := by exact_mod_cast hj_le
      omega
    have hap := hf (n + 1) hn (2 * k) (by omega) hbound
    rw [hDn1, hDn, hjeq]
    exact_mod_cast hap

/-- **Telescoping bound across levels.** For `x ∈ [0,1]` and `m ≤ L`, the
truncation increment from level `m` to level `L` is bounded by the sum of the
per-level bounds `b (m+1) + ⋯ + b L`. -/
lemma dyadicTrunc_telescope {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ} (hm : N ≤ m + 1) :
    ∀ L, m ≤ L → |f (dyadicTrunc L x) - f (dyadicTrunc m x)|
      ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    rw [sub_self, abs_zero, Finset.Ico_self, Finset.sum_empty]
  | succ L hmL ih =>
    calc |f (dyadicTrunc (L + 1) x) - f (dyadicTrunc m x)|
        ≤ |f (dyadicTrunc (L + 1) x) - f (dyadicTrunc L x)|
          + |f (dyadicTrunc L x) - f (dyadicTrunc m x)| := abs_sub_le _ _ _
      _ ≤ b (L + 1) + ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
          refine add_le_add ?_ ih
          exact dyadicTrunc_succ_step hb hf (by omega) hx0 hx1
      _ = ∑ n ∈ Finset.Ico (m + 1) (L + 2), b n := by
          rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ L + 1)]
          ring

/-- **Cross-point step at a fixed level.** For `0 ≤ s ≤ t ≤ 1` with
`t − s ≤ 2^{-m}`, the level-`m` truncations of `s` and `t` are equal or adjacent
level-`m` dyadics, so `|f(trunc_m s) − f(trunc_m t)| ≤ b m`. -/
lemma dyadicTrunc_near_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {m : ℕ} (hm : N ≤ m) {s t : ℝ} (hs0 : 0 ≤ s) (ht1 : t ≤ 1) (hst : s ≤ t)
    (hclose : t - s ≤ (1 / 2) ^ m) :
    |f (dyadicTrunc m s) - f (dyadicTrunc m t)| ≤ b m := by
  set ks : ℤ := ⌊s * 2 ^ m⌋ with hks
  set kt : ℤ := ⌊t * 2 ^ m⌋ with hkt
  have hks0 : 0 ≤ ks := by rw [hks]; apply Int.floor_nonneg.mpr; positivity
  have hmono : ks ≤ kt := by
    rw [hks, hkt]; apply Int.floor_le_floor
    exact mul_le_mul_of_nonneg_right hst (by positivity)
  have hclose' : t * 2 ^ m ≤ s * 2 ^ m + 1 := by
    have hmul : (t - s) * 2 ^ m ≤ 1 := by
      calc (t - s) * 2 ^ m ≤ (1 / 2) ^ m * 2 ^ m :=
            mul_le_mul_of_nonneg_right hclose (by positivity)
        _ = 1 := by rw [div_pow, one_pow, div_mul_cancel₀]; positivity
    nlinarith
  have hkt_le : kt ≤ ks + 1 := by
    rw [hkt, hks]
    calc ⌊t * 2 ^ m⌋ ≤ ⌊s * 2 ^ m + 1⌋ := Int.floor_le_floor (by linarith)
      _ = ⌊s * 2 ^ m⌋ + 1 := Int.floor_add_one _
  have hTs : dyadicTrunc m s = ((ks : ℤ) : ℝ) / 2 ^ m := by rw [dyadicTrunc, ← hks]
  have hTt : dyadicTrunc m t = ((kt : ℤ) : ℝ) / 2 ^ m := by rw [dyadicTrunc, ← hkt]
  rcases (by omega : kt = ks ∨ kt = ks + 1) with he | he
  · rw [hTs, hTt, he, sub_self, abs_zero]; exact hb m
  · have hbnd : ks + 1 ≤ (2 : ℤ) ^ m := by
      have hktle : (kt : ℝ) ≤ t * 2 ^ m := Int.floor_le _
      have hkt_le2 : (kt : ℝ) ≤ (2 : ℝ) ^ m :=
        le_trans hktle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m])
      have : (kt : ℤ) ≤ (2 : ℤ) ^ m := by exact_mod_cast hkt_le2
      omega
    have hap := hf m hm ks hks0 hbnd
    rw [hTs, hTt, he, abs_sub_comm]
    exact_mod_cast hap

/-- A dyadic rational coincides with its own level-`L` truncation for all
sufficiently large `L`. -/
lemma dyadicTrunc_eventually_eq {s : ℝ} (hs : s ∈ dyadicRationals) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → dyadicTrunc L s = s := by
  obtain ⟨k, n, hkn⟩ := hs
  refine ⟨n, fun L hL => ?_⟩
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - n) * (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hL]
  have hsL : s * 2 ^ L = ((k * 2 ^ (L - n) : ℤ) : ℝ) := by
    rw [hkn, zpow_neg, zpow_natCast, hpow]
    push_cast
    field_simp
  rw [dyadicTrunc, hsL, Int.floor_intCast, hkn, zpow_neg, zpow_natCast, hpow]
  push_cast
  field_simp

/-- Finite geometric partial sum bounded by the infinite tail
`∑_{a ≤ n < b} rⁿ ≤ rᵃ / (1 − r)` for `0 ≤ r < 1`. -/
lemma sum_Ico_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, r ^ n ≤ r ^ a / (1 - r) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact Summable.sum_le_tsum _ (fun i _ => by positivity)
    (summable_geometric_of_lt_one hr0 hr1)

/-- **Dyadic scale selection.** For `0 < d ≤ 1` there is `m` with
`(1/2)^{m+1} < d ≤ (1/2)^m`. -/
lemma exists_dyadic_scale {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m := by
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < d :=
    exists_pow_lt_of_lt_one hd0 (by norm_num)
  classical
  have hspec : (1 / 2 : ℝ) ^ Nat.find hex < d := Nat.find_spec hex
  have hpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h] at hspec; simp at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel hpos]; exact hspec
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_lt] at hmin
    exact hmin

/-- `((1/2)^α)^m ≤ 2^α · d^α` when `(1/2)^{m+1} < d`. Converts the geometric
level factor `r^m = ((1/2)^α)^m` into a Hölder factor in `d`. -/
lemma rpow_half_pow_le {α : ℝ} (hα : 0 < α) {d : ℝ} (m : ℕ)
    (hd : (1 / 2 : ℝ) ^ (m + 1) < d) :
    ((1 / 2 : ℝ) ^ α) ^ m ≤ (2 : ℝ) ^ α * d ^ α := by
  have hdpos : 0 < d := lt_of_le_of_lt (by positivity) hd
  have hstep : (1 / 2 : ℝ) ^ m < 2 * d := by
    have he : (1 / 2 : ℝ) ^ m = 2 * (1 / 2) ^ (m + 1) := by rw [pow_succ]; ring
    rw [he]; linarith
  have hr_eq : ((1 / 2 : ℝ) ^ α) ^ m = ((1 / 2 : ℝ) ^ m) ^ α := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) m,
        ← Real.rpow_natCast (1 / 2 : ℝ) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2), mul_comm]
  rw [hr_eq]
  calc ((1 / 2 : ℝ) ^ m) ^ α
      ≤ (2 * d) ^ α :=
        Real.rpow_le_rpow (by positivity) (le_of_lt hstep) (le_of_lt hα)
    _ = (2 : ℝ) ^ α * d ^ α := Real.mul_rpow (by norm_num) (le_of_lt hdpos)

/-- **KC exponent identity.** `2ⁿ · ((1/2)ⁿ)^q / ((1/2)^α)ⁿ)^p = ((1/2)^{q−αp−1})ⁿ`.
Collapses the per-level Borel–Cantelli factor (a `2ⁿ` union over level-`n`
dyadics, each a Markov term `(2^{−n})^q / (2^{−αn})^p`) to a single geometric
ratio `(1/2)^{q−αp−1}`, which is `< 1` exactly when `αp < q − 1`. -/
lemma kc_exponent_identity {α p q : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
      = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  have e1 : ((1 / 2 : ℝ) ^ n) ^ q = (1 / 2 : ℝ) ^ ((n : ℝ) * q) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) n, ← Real.rpow_mul (le_of_lt h2)]
  have e2 : (((1 / 2 : ℝ) ^ α) ^ n) ^ p = (1 / 2 : ℝ) ^ (α * (n : ℝ) * p) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) n, ← Real.rpow_mul (le_of_lt h2),
        ← Real.rpow_mul (le_of_lt h2)]
  have e3 : (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt h2), Real.rpow_natCast,
        show (1 / 2 : ℝ) ^ n = (2 ^ n)⁻¹ from by rw [one_div, inv_pow], inv_inv]
  have e4 : ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n
      = (1 / 2 : ℝ) ^ ((q - α * p - 1) * (n : ℝ)) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (q - α * p - 1)) n,
        ← Real.rpow_mul (le_of_lt h2)]
  rw [e1, e2, e3, e4, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt h2),
      ← Real.rpow_add h2, ← Real.rpow_add h2]
  congr 1
  ring

/-- **Deterministic dyadic Hölder chaining.** If the consecutive level-`n`
dyadic increments of `f` on `[0,1]` are bounded by `C · ((1/2)^α)^n` for all
`n ≥ N`, then `f` is α-Hölder on the dyadics of `[0,1]` at scales `≤ 2^{-N}`,
with an explicit constant `K`. This is the path-by-path output of the
Borel–Cantelli increment control. -/
lemma dyadic_holder_chaining {f : ℝ → ℝ} {α C : ℝ} {N : ℕ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ C * ((1 / 2 : ℝ) ^ α) ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
      0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N →
      |f s - f t| ≤ K * |s - t| ^ α := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have h1r : 0 < 1 - r := by linarith
  set b : ℕ → ℝ := fun n => C * r ^ n with hb_def
  have hb : ∀ n, 0 ≤ b n := fun n => by simp only [hb_def]; positivity
  set A : ℝ := C * (1 + 2 * r / (1 - r)) with hA_def
  have hA0 : 0 ≤ A := by
    apply mul_nonneg hC
    have : 0 ≤ 2 * r / (1 - r) := div_nonneg (by positivity) (le_of_lt h1r)
    linarith
  have h2α : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  -- Sum bound: `∑_{Ico (m+1) (L+1)} b ≤ C·r^{m+1}/(1-r)`.
  have hsum : ∀ m L : ℕ, ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n
      ≤ C * r ^ (m + 1) / (1 - r) := by
    intro m L
    simp only [hb_def]
    rw [← Finset.mul_sum]
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hC
    exact sum_Ico_geometric_le (le_of_lt hr0) hr1 (m + 1) (L + 1)
  -- Core bound for an ordered pair `a ≤ c`.
  have core : ∀ a c, a ∈ dyadicRationals → c ∈ dyadicRationals →
      0 ≤ a → c ≤ 1 → a ≤ c → c - a ≤ (1 / 2 : ℝ) ^ N →
      |f a - f c| ≤ (A * 2 ^ α) * (c - a) ^ α := by
    intro a c ha hc ha0 hc1 hac hgap
    rcases eq_or_lt_of_le hac with hac' | hac'
    · subst hac'; simp [Real.zero_rpow hα.ne']
    set d : ℝ := c - a with hd_def
    have hd0 : 0 < d := by simp only [hd_def]; linarith
    have hNle1 : (1 / 2 : ℝ) ^ N ≤ 1 := by
      apply pow_le_one₀ (by norm_num) (by norm_num)
    have hd1 : d ≤ 1 := le_trans hgap hNle1
    obtain ⟨m, hm1, hm2⟩ := exists_dyadic_scale hd0 hd1
    have hmN : N ≤ m := by
      by_contra hlt
      have hNm1 : (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ (m + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [le_trans hgap hNm1, hm1]
    obtain ⟨Ls, hLs⟩ := dyadicTrunc_eventually_eq ha
    obtain ⟨Lt, hLt⟩ := dyadicTrunc_eventually_eq hc
    set L : ℕ := max (max Ls Lt) m with hL_def
    have hsL : dyadicTrunc L a = a :=
      hLs L (le_trans (le_max_left _ _) (le_max_left _ _))
    have htL : dyadicTrunc L c = c :=
      hLt L (le_trans (le_max_right _ _) (le_max_left _ _))
    have hmL : m ≤ L := le_max_right _ _
    have hTa := dyadicTrunc_telescope hb hf ha0 (le_trans hac hc1) (by omega) L hmL
    have hTc := dyadicTrunc_telescope hb hf (le_trans ha0 hac) hc1 (by omega) L hmL
    rw [hsL] at hTa
    rw [htL] at hTc
    have hNear := dyadicTrunc_near_step hb hf hmN ha0 hc1 hac hm2
    -- Triangle: split through the two level-m truncations.
    have htri : |f a - f c|
        ≤ |f a - f (dyadicTrunc m a)|
          + |f (dyadicTrunc m a) - f (dyadicTrunc m c)|
          + |f (dyadicTrunc m c) - f c| := by
      calc |f a - f c|
          ≤ |f a - f (dyadicTrunc m a)| + |f (dyadicTrunc m a) - f c| :=
            abs_sub_le _ _ _
        _ ≤ |f a - f (dyadicTrunc m a)|
            + (|f (dyadicTrunc m a) - f (dyadicTrunc m c)|
              + |f (dyadicTrunc m c) - f c|) := by
            gcongr; exact abs_sub_le _ _ _
        _ = _ := by ring
    have hTc' : |f (dyadicTrunc m c) - f c|
        ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
      rw [abs_sub_comm]; exact hTc
    -- Combine the three pieces.
    have hsumbnd := hsum m L
    have hbm : b m = C * r ^ m := rfl
    have key : |f a - f c| ≤ A * r ^ m := by
      have hchain : |f a - f c|
          ≤ (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) + b m
            + (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) := by
        refine le_trans htri ?_
        gcongr
      refine le_trans hchain ?_
      have hnum : (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) + b m
          + (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n)
          ≤ C * r ^ (m + 1) / (1 - r) + C * r ^ m + C * r ^ (m + 1) / (1 - r) := by
        linarith [hsum m L, hbm]
      refine le_trans hnum (le_of_eq ?_)
      rw [hA_def]
      field_simp
      ring
    refine le_trans key ?_
    rw [show A * 2 ^ α * d ^ α = A * (2 ^ α * d ^ α) from by ring]
    apply mul_le_mul_of_nonneg_left _ hA0
    rw [hr_def]
    exact rpow_half_pow_le hα m hm1
  -- Dispatch by the order of `s, t`.
  refine ⟨A * 2 ^ α, by positivity, ?_⟩
  intro s hs t ht hs0 hs1 ht0 ht1 hclose
  rcases le_total s t with hst | hst
  · have hgap : t - s ≤ (1 / 2 : ℝ) ^ N := by
      rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s), abs_sub_comm]; exact hclose
    have heq : |s - t| = t - s := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [heq]
    exact core s t hs ht hs0 ht1 hst hgap
  · have hgap : s - t ≤ (1 / 2 : ℝ) ^ N := by
      rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]; exact hclose
    have heq : |s - t| = s - t := abs_of_nonneg (by linarith)
    rw [heq, abs_sub_comm]
    exact core t s ht hs ht0 hs1 hst hgap

end LevyStochCalc.Brownian.Continuity
