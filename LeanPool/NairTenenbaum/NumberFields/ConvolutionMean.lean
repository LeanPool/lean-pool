/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Topology.GDelta.MetrizableSpace

/-! # Transfer of a linear mean through an absolutely convergent convolution

The summatory function of a Dirichlet convolution has the form
`∑ d, g d * A (x / d)`. Absolute convergence of `∑ |g d| / d`
allows its linear mean to be computed by dominated convergence.
-/

@[expose] public section

namespace NairTenenbaum

open Filter Finset Real
open scoped Topology

theorem tendsto_scaled_convolution_mean {A : ℝ → ℝ} {g : ℕ → ℝ} {C L : ℝ}
    (hA0 : A 0 = 0) (hbound : ∀ t : ℝ, 0 ≤ t → |A t| ≤ C * t)
    (hmean : Tendsto (fun t : ℝ => A t / t) atTop (𝓝 L))
    (hsum : Summable (fun d : ℕ => |g d| / d)) :
    Tendsto (fun x : ℝ => (∑' d : ℕ, g d * A (x / d)) / x) atTop
      (𝓝 (L * ∑' d : ℕ, g d / d)) := by
  have hterm (d : ℕ) :
      Tendsto (fun x : ℝ => g d * A (x / d) / x) atTop (𝓝 (L * (g d / d))) := by
    by_cases hd : d = 0
    · subst d
      simp [hA0]
    have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
    have H := (hmean.comp (tendsto_id.atTop_div_const hd0)).const_mul ((g d) / d)
    convert H using 1
    · ext x
      dsimp only [Function.comp_apply, id_eq]
      field_simp
    · congr 1
      ring
  have hdom : ∀ᶠ x : ℝ in atTop, ∀ d : ℕ,
      ‖g d * A (x / d) / x‖ ≤ C * (|g d| / d) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx d
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx]
    apply (div_le_iff₀ hx).mpr
    have H := mul_le_mul_of_nonneg_left
      (hbound (x / d) (div_nonneg hx.le (Nat.cast_nonneg d))) (abs_nonneg (g d))
    convert H using 1
    ring
  have H := tendsto_tsum_of_dominated_convergence (hsum.mul_left C) hterm hdom
  simpa only [tsum_div_const, tsum_mul_left] using H

/-- The real summatory function, including only positive indices. -/
noncomputable def arithmeticSummatory (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n

@[simp] theorem arithmeticSummatory_zero (a : ℕ → ℝ) : arithmeticSummatory a 0 = 0 := by
  simp [arithmeticSummatory]

theorem arithmeticSummatory_limit_of_nat_limit {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, a k) / n) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => arithmeticSummatory a x / x) atTop (𝓝 L) := by
  have H := (h.comp tendsto_nat_floor_atTop).mul
    (tendsto_nat_floor_div_atTop (R := ℝ))
  rw [mul_one] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hf : (⌊x⌋₊ : ℝ) ≠ 0 := by
    have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (zero_le_one.trans hx)).mpr (by simpa using hx)
    exact_mod_cast (show ⌊x⌋₊ ≠ 0 by omega)
  dsimp [arithmeticSummatory]
  field_simp

theorem arithmeticSummatory_linear_bound_of_nat_limit {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, a k) / n) atTop (𝓝 L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → |arithmeticSummatory a x| ≤ C * x := by
  obtain ⟨B, hB⟩ := h.abs.bddAbove_range
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have hn : |(∑ k ∈ Icc 1 ⌊x⌋₊, a k) / (⌊x⌋₊ : ℝ)| ≤ max B 0 :=
    (hB (Set.mem_range_self ⌊x⌋₊)).trans (le_max_left _ _)
  have H : |arithmeticSummatory a x| ≤ max B 0 * (⌊x⌋₊ : ℝ) := by
    by_cases hf : ⌊x⌋₊ = 0
    · simp [arithmeticSummatory, hf]
    have hfpos : (0 : ℝ) < ⌊x⌋₊ := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hf)
    rw [abs_div, abs_of_pos hfpos] at hn
    exact (div_le_iff₀ hfpos).mp hn
  exact H.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) (le_max_right _ _))

theorem tendsto_arithmeticSummatory_convolution_mean {a g : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, a k) / n) atTop (𝓝 L))
    (hg : Summable (fun d : ℕ => |g d| / d)) :
    Tendsto (fun x : ℝ => (∑' d : ℕ, g d * arithmeticSummatory a (x / d)) / x)
      atTop (𝓝 (L * ∑' d : ℕ, g d / d)) := by
  obtain ⟨C, _, hC⟩ := arithmeticSummatory_linear_bound_of_nat_limit h
  exact tendsto_scaled_convolution_mean (arithmeticSummatory_zero a) hC
    (arithmeticSummatory_limit_of_nat_limit h) hg

theorem sum_divisorsAntidiagonal_eq_hyperbola (F : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ de ∈ n.divisorsAntidiagonal, F de.1 de.2) =
      ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), F d e := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun a _ => ⟨a.2.1, a.2.2⟩)
    (fun b _ => ⟨b.1 * b.2, (b.1, b.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d, e⟩ ha
    dsimp only at *
    obtain ⟨hn, hde⟩ := mem_sigma.mp ha
    obtain ⟨heq, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hde
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hd0 : 0 < d := by nlinarith
    have he0 : 0 < e := by nlinarith
    apply mem_sigma.mpr
    dsimp only
    constructor
    · apply mem_Icc.mpr
      constructor
      · omega
      · nlinarith
    · apply mem_Icc.mpr
      exact ⟨he0, (Nat.le_div_iff_mul_le hd0).mpr (by nlinarith)⟩
  · rintro ⟨d, e⟩ hb
    obtain ⟨hd, he⟩ := mem_sigma.mp hb
    obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
    obtain ⟨he1, heN⟩ := mem_Icc.mp he
    have hmul : d * e ≤ N := by
      have := (Nat.le_div_iff_mul_le hd1).mp heN
      simpa [mul_comm] using this
    apply mem_sigma.mpr
    exact ⟨mem_Icc.mpr ⟨Nat.mul_pos hd1 he1, hmul⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hd1 he1).ne'⟩⟩
  · rintro ⟨n, d, e⟩ ha
    have H := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp ha).2).1
    dsimp only at H ⊢
    subst n
    rfl
  · intro b _
    rfl
  · intro a _
    rfl

theorem arithmeticSummatory_mul (a g : ArithmeticFunction ℝ) (x : ℝ) :
    arithmeticSummatory (g * a : ArithmeticFunction ℝ) x = ∑' d : ℕ, g d * arithmeticSummatory a
        (x / d) := by
  classical
  unfold arithmeticSummatory
  simp_rw [ArithmeticFunction.mul_apply, Nat.floor_div_natCast]
  rw [sum_divisorsAntidiagonal_eq_hyperbola (fun d e => g d * a e)]
  simp_rw [← mul_sum]
  symm
  apply tsum_eq_sum
  intro d hd
  by_cases hd0 : d = 0
  · simp [hd0]
  have hlarge : ⌊x⌋₊ < d := by simpa [mem_Icc, Nat.one_le_iff_ne_zero, hd0] using hd
  rw [Nat.div_eq_of_lt hlarge]
  simp

theorem arithmeticFunction_convolution_mean {a g : ArithmeticFunction ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, a k) / n) atTop (𝓝 L))
    (hg : Summable (fun d : ℕ => |g d| / d)) :
    Tendsto (fun x : ℝ => arithmeticSummatory (g * a : ArithmeticFunction ℝ) x / x)
      atTop (𝓝 (L * ∑' d : ℕ, g d / d)) := by
  simpa only [arithmeticSummatory_mul] using tendsto_arithmeticSummatory_convolution_mean h hg

end NairTenenbaum
