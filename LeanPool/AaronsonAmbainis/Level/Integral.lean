/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Integration over the level

Real-variable lemmas with no cube in them. The main statement is `level_integration`: an
inequality between a combination of the functions `t ↦ (u - t)⁺ (t - v)⁺` and a combination of
indicators of intervals `[p, q)`, valid at every level `t`, can be integrated over `t`:
`∫ (u - t)⁺ (t - v)⁺ dt = ((u - v)⁺)^3 / 6` and `∫ 1_{[p,q)}(t) dt = (q - p)⁺` (Lemma 7.3 (i)
and (ii) of the paper).
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Level

open Finset

/-- `∫_v^u (u - t)(t - v) dt = (u - v)^3 / 6`. -/
lemma integral_quad (v u : ℝ) : ∫ t in v..u, (u - t) * (t - v) = (u - v) ^ 3 / 6 := by
  have hd : ∀ t ∈ Set.uIcc v u, HasDerivAt
      (fun t : ℝ => -1 / 3 * t ^ 3 + (u + v) / 2 * t ^ 2 - u * v * t) ((u - t) * (t - v)) t := by
    intro t _
    have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
    have h : HasDerivAt (fun t : ℝ => -1 / 3 * t ^ 3 + (u + v) / 2 * t ^ 2 - u * v * t)
        (-1 / 3 * (3 * t ^ 2) + (u + v) / 2 * (2 * t) - u * v * 1) t :=
      ((h3.const_mul (-1 / 3)).add (h2.const_mul ((u + v) / 2))).sub (h1.const_mul (u * v))
    convert h using 1
    ring
  have hc : Continuous fun t : ℝ => (u - t) * (t - v) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  ring

/-- `∫_a^b (u - t)⁺ (t - v)⁺ dt = ((u - v)⁺)^3 / 6` when `a ≤ v` and `u ≤ b`
(Lemma 7.3 (i) of the paper). -/
lemma integral_posParts {a b u v : ℝ} (hub : u ≤ b) (hav : a ≤ v) :
    ∫ t in a..b, max (u - t) 0 * max (t - v) 0 = max (u - v) 0 ^ 3 / 6 := by
  have hc : Continuous fun t : ℝ => max (u - t) 0 * max (t - v) 0 := by fun_prop
  rcases le_or_gt u v with h | h
  · have h0 : ∀ t : ℝ, max (u - t) 0 * max (t - v) 0 = 0 := by
      intro t
      rcases le_or_gt u t with ht | ht
      · rw [max_eq_right (by linarith : u - t ≤ 0), zero_mul]
      · rw [max_eq_right (by linarith : t - v ≤ 0), mul_zero]
    simp only [h0]
    rw [intervalIntegral.integral_zero, max_eq_right (by linarith : u - v ≤ 0)]
    norm_num
  · have e1 : ∫ t in a..v, max (u - t) 0 * max (t - v) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le hav] at ht
      change max (u - t) 0 * max (t - v) 0 = 0
      rw [max_eq_right (by linarith [ht.2] : t - v ≤ 0), mul_zero]
    have e2 : ∫ t in v..u, max (u - t) 0 * max (t - v) 0 = (u - v) ^ 3 / 6 := by
      rw [intervalIntegral.integral_congr (g := fun t => (u - t) * (t - v)), integral_quad]
      intro t ht
      rw [Set.uIcc_of_le h.le] at ht
      change max (u - t) 0 * max (t - v) 0 = (u - t) * (t - v)
      rw [max_eq_left (by linarith [ht.2] : 0 ≤ u - t),
        max_eq_left (by linarith [ht.1] : 0 ≤ t - v)]
    have e3 : ∫ t in u..b, max (u - t) 0 * max (t - v) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le hub] at ht
      change max (u - t) 0 * max (t - v) 0 = 0
      rw [max_eq_right (by linarith [ht.1] : u - t ≤ 0), zero_mul]
    have s1 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable a v) (hc.intervalIntegrable (μ := MeasureTheory.volume) v b)
    have s2 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable v u) (hc.intervalIntegrable (μ := MeasureTheory.volume) u b)
    rw [← s1, ← s2, e1, e2, e3, max_eq_left (by linarith : 0 ≤ u - v)]
    ring

/-- The step function `1_{c ≤ t}`. -/
noncomputable def stp (c t : ℝ) : ℝ := if c ≤ t then 1 else 0

lemma stp_mono (c : ℝ) : Monotone (stp c) := by
  intro s t hst
  unfold stp
  by_cases h : c ≤ s
  · rw [ite_eq_left h, ite_eq_left (h.trans hst)]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

lemma stp_intervalIntegrable (c a b : ℝ) :
    IntervalIntegrable (stp c) MeasureTheory.volume a b :=
  (stp_mono c).intervalIntegrable

/-- `∫_a^b 1_{c ≤ t} dt = b - c` for `c` in `[a, b]` (this gives Lemma 7.3 (ii) of the paper). -/
lemma integral_stp {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) : ∫ t in a..b, stp c t = b - c := by
  have e1 : ∫ t in a..c, stp c t = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hac (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro t ht
    change stp c t = 0
    unfold stp
    rw [ite_eq_right (not_le.mpr ht.2)]
  have e2 : ∫ t in c..b, stp c t = b - c := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)), integral_one]
    intro t ht
    rw [Set.uIcc_of_le hcb] at ht
    change stp c t = 1
    unfold stp
    rw [ite_eq_left ht.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals (stp_intervalIntegrable c a c)
    (stp_intervalIntegrable c c b), e1, e2, zero_add]

/-- The indicator of `[p, q)` as a difference of two step functions. -/
lemma ind_eq_stp (p q t : ℝ) :
    (if p ≤ t ∧ t < q then (1 : ℝ) else 0) = stp p t - stp (max p q) t := by
  unfold stp
  by_cases h1 : p ≤ t
  · by_cases h2 : t < q
    · have h3 : ¬ max p q ≤ t := fun h => absurd ((le_max_right p q).trans h) (not_le.mpr h2)
      rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h1, ite_eq_right h3, sub_zero]
    · rw [ite_eq_right (fun h => h2 h.2), ite_eq_left h1,
        ite_eq_left (max_le h1 (not_lt.mp h2)), sub_self]
  · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1,
      ite_eq_right (fun h => h1 ((le_max_left p q).trans h)), sub_self]

/-- **Integration over the level.** If
`∑_i c_i (u_i - t)⁺ (t - v_i)⁺ ≤ ∑_k d_k 1_{[p_k, q_k)}(t)` for every real `t`, then
`∑_i c_i ((u_i - v_i)⁺)^3 / 6 ≤ ∑_k d_k (q_k - p_k)⁺`. No sign condition on `c`, `d`. -/
theorem level_integration {α β : Type*} (s : Finset α) (r : Finset β)
    (c u v : α → ℝ) (d p q : β → ℝ)
    (h : ∀ t : ℝ, ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0)
        ≤ ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0)) :
    ∑ i ∈ s, c i * (max (u i - v i) 0 ^ 3 / 6) ≤ ∑ k ∈ r, d k * max (q k - p k) 0 := by
  -- a bound `R` for all the levels that occur
  obtain ⟨R, hRs, hRr⟩ : ∃ R : ℝ, (∀ i ∈ s, |u i| ≤ R ∧ |v i| ≤ R) ∧
      (∀ k ∈ r, |p k| ≤ R ∧ |q k| ≤ R) := by
    refine ⟨∑ i ∈ s, (|u i| + |v i|) + ∑ k ∈ r, (|p k| + |q k|), ?_, ?_⟩
    · intro i hi
      have h1 : |u i| + |v i| ≤ ∑ i ∈ s, (|u i| + |v i|) :=
        Finset.single_le_sum (f := fun i => |u i| + |v i|)
          (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hi
      have h2 : 0 ≤ ∑ k ∈ r, (|p k| + |q k|) :=
        Finset.sum_nonneg (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      constructor <;> linarith [abs_nonneg (u i), abs_nonneg (v i)]
    · intro k hk
      have h1 : |p k| + |q k| ≤ ∑ k ∈ r, (|p k| + |q k|) :=
        Finset.single_le_sum (f := fun k => |p k| + |q k|)
          (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hk
      have h2 : 0 ≤ ∑ i ∈ s, (|u i| + |v i|) :=
        Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      constructor <;> linarith [abs_nonneg (p k), abs_nonneg (q k)]
  -- we integrate over `[-R', R']` with `R' = |R|`, so that `-R' ≤ R'` also if `s`, `r` are empty
  have hR0 : -|R| ≤ |R| := by linarith [abs_nonneg R]
  have hRR : R ≤ |R| := le_abs_self R
  -- the left side
  have hLc : ∀ i, Continuous fun t : ℝ => c i * (max (u i - t) 0 * max (t - v i) 0) := by
    intro i
    fun_prop
  have hL : ∫ t in (-|R|)..|R|, ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0)
      = ∑ i ∈ s, c i * (max (u i - v i) 0 ^ 3 / 6) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hLc i).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := abs_le.mp ((hRs i hi).1.trans hRR)
    have hv := abs_le.mp ((hRs i hi).2.trans hRR)
    rw [intervalIntegral.integral_const_mul, integral_posParts hu.2 hv.1]
  have hLi : IntervalIntegrable
      (fun t : ℝ => ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0))
      MeasureTheory.volume (-|R|) |R| := by
    have hcont : Continuous fun t : ℝ => ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0) :=
      continuous_finsetSum s (fun i _ => hLc i)
    exact hcont.intervalIntegrable _ _
  -- the right side
  have hstep : ∀ k, IntervalIntegrable
      (fun t : ℝ => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      MeasureTheory.volume (-|R|) |R| := by
    intro k
    simp only [ind_eq_stp]
    exact ((stp_intervalIntegrable (p k) _ _).sub
      (stp_intervalIntegrable (max (p k) (q k)) _ _)).const_mul (d k)
  have hRint : ∫ t in (-|R|)..|R|, ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0)
      = ∑ k ∈ r, d k * max (q k - p k) 0 := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => hstep k)]
    apply Finset.sum_congr rfl
    intro k hk
    have hp := abs_le.mp ((hRr k hk).1.trans hRR)
    have hq := abs_le.mp ((hRr k hk).2.trans hRR)
    have hm1 : -|R| ≤ max (p k) (q k) := le_trans hp.1 (le_max_left _ _)
    have hm2 : max (p k) (q k) ≤ |R| := max_le hp.2 hq.2
    rw [intervalIntegral.integral_const_mul]
    simp only [ind_eq_stp]
    rw [intervalIntegral.integral_sub (stp_intervalIntegrable _ _ _)
      (stp_intervalIntegrable _ _ _), integral_stp hp.1 hp.2, integral_stp hm1 hm2]
    congr 1
    rcases le_total (p k) (q k) with hpq | hpq
    · rw [max_eq_right hpq, max_eq_left (by linarith : 0 ≤ q k - p k)]
      ring
    · rw [max_eq_left hpq, max_eq_right (by linarith : q k - p k ≤ 0)]
      ring
  have hRi : IntervalIntegrable
      (fun t : ℝ => ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      MeasureTheory.volume (-|R|) |R| := by
    have h1 := IntervalIntegrable.sum r
      (f := fun k (t : ℝ) => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      (μ := MeasureTheory.volume) (a := -|R|) (b := |R|) (fun k _ => hstep k)
    have e : (∑ k ∈ r, fun t : ℝ => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
        = fun t : ℝ => ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0) := by
      funext t
      rw [Finset.sum_apply]
    rw [e] at h1
    exact h1
  have hmono := intervalIntegral.integral_mono_on hR0 hLi hRi (fun t _ => h t)
  rw [hL, hRint] at hmono
  exact hmono

end Level
end AaronsonAmbainis
