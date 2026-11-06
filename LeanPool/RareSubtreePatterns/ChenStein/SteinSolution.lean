/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic


/-!
# The Stein solution for the Poisson law

For a rate `r > 0` and an event `A ⊆ ℕ`, `steinSolution r A` solves the Poisson Stein equation

  `r f(w + 1) - w f(w) = 1_A(w) - Po(r)(A)` for every `w : ℕ`,

and is bounded by one in absolute value. Writing `F = P(Z ≤ w)`, `T = P(Z > w)` and
`p_w = P(Z = w)` for `Z ~ Po(r)`, the explicit numerator is bounded by `F T`, and
`F T ≤ r p_w` follows from the head bound `(r - w) F ≤ r p_w` and the tail bound
`(w + 1 - r) T ≤ r p_w`, both consequences of the recursion `(k + 1) p_{k+1} = r p_k`.

This is the analytic input to the Arratia–Goldstein–Gordon Chen–Stein bound
(Proposition `prop:AGG` of the source); it is the crude Stein factor `‖f‖ ≤ 1` and not the
sharper factors of AGG89.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Nat

namespace PoissonDeclumping.ChenStein

/-- The Poisson recursion `(w + 1) p_{w+1} = r p_w`. -/
lemma succ_mul_poissonMeasure_real_singleton (r : ℝ≥0) (w : ℕ) :
    ((w : ℝ) + 1) * (poissonMeasure r).real {w + 1} = r * (poissonMeasure r).real {w} := by
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton, Nat.factorial_succ]
  push_cast
  have h1 : ((w ! : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma Iic_zero_eq : (Iic 0 : Set ℕ) = {0} := by
  ext k; simp

private lemma Iic_succ_eq (w : ℕ) : Iic (w + 1) = Iic w ∪ {w + 1} := by
  ext k; simp only [mem_Iic, mem_union, mem_singleton_iff]; omega

lemma poissonMeasure_real_inter_Iic_succ (r : ℝ≥0) (A : Set ℕ) (w : ℕ) :
    (poissonMeasure r).real (A ∩ Iic (w + 1)) =
      (poissonMeasure r).real (A ∩ Iic w) + A.indicator 1 (w + 1) *
        (poissonMeasure r).real {w + 1} := by
  rw [Iic_succ_eq, inter_union_distrib_left, measureReal_union _ (MeasurableSet.of_discrete)]
  · congr 1
    by_cases hw : w + 1 ∈ A
    · rw [inter_eq_right.mpr (singleton_subset_iff.mpr hw), indicator_of_mem hw]; simp
    · rw [indicator_of_notMem hw, inter_singleton_eq_empty.mpr hw]; simp
  · refine Disjoint.mono inter_subset_right inter_subset_right ?_
    simp

lemma poissonMeasure_real_Iic_succ (r : ℝ≥0) (w : ℕ) :
    (poissonMeasure r).real (Iic (w + 1)) =
      (poissonMeasure r).real (Iic w) + (poissonMeasure r).real {w + 1} := by
  simpa using poissonMeasure_real_inter_Iic_succ r univ w

/-- Head bound: `(r - w) P(Z ≤ w) ≤ r P(Z = w)` for `Z ~ Po(r)`. -/
lemma sub_mul_poissonMeasure_real_Iic_le (r : ℝ≥0) (w : ℕ) :
    ((r : ℝ) - w) * (poissonMeasure r).real (Iic w) ≤ r * (poissonMeasure r).real {w} := by
  induction w with
  | zero => simp [Iic_zero_eq]
  | succ w ih =>
    rw [poissonMeasure_real_Iic_succ]
    have hF : 0 ≤ (poissonMeasure r).real (Iic w) := measureReal_nonneg
    have hrec := succ_mul_poissonMeasure_real_singleton r w
    push_cast
    linarith

/-- The Poisson weights `exp (-r) r ^ n / n!` as a real function. -/
noncomputable abbrev poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ := Real.exp (-r) * r ^ n / n !

lemma summable_poissonWeight (r : ℝ≥0) : Summable (poissonWeight r) :=
  (hasSum_one_poissonMeasure r).summable

lemma poissonMeasure_real_Iic (r : ℝ≥0) (w : ℕ) :
    (poissonMeasure r).real (Iic w) = ∑ k ∈ Finset.range (w + 1), poissonWeight r k := by
  have : (Iic w : Set ℕ) = ↑(Finset.range (w + 1)) := by
    ext k; simp
  rw [this, ← sum_measureReal_singleton]
  simp [poissonMeasure_real_singleton]

lemma poissonMeasure_real_Ioi (r : ℝ≥0) (w : ℕ) :
    (poissonMeasure r).real (Ioi w) = ∑' n, poissonWeight r (n + (w + 1)) := by
  have h1 := (summable_poissonWeight r).sum_add_tsum_nat_add (w + 1)
  rw [(hasSum_one_poissonMeasure r).tsum_eq] at h1
  have h2 := measureReal_add_measureReal_compl (μ := poissonMeasure r)
    (MeasurableSet.of_discrete (s := Iic w))
  rw [compl_Iic, probReal_univ, poissonMeasure_real_Iic] at h2
  linarith

/-- Tail bound: `(w + 1 - r) P(Z > w) ≤ r P(Z = w)` for `Z ~ Po(r)`. -/
lemma sub_mul_poissonMeasure_real_Ioi_le (r : ℝ≥0) (w : ℕ) :
    ((w : ℝ) + 1 - r) * (poissonMeasure r).real (Ioi w) ≤ r * (poissonMeasure r).real {w} := by
  set p := poissonWeight r with hp
  have hs : Summable (fun n => p (n + w)) :=
    (summable_nat_add_iff w).mpr (summable_poissonWeight r)
  have hs1 : Summable (fun n => p (n + (w + 1))) :=
    (summable_nat_add_iff (w + 1)).mpr (summable_poissonWeight r)
  have hsplit : ∑' n, p (n + w) = p w + ∑' n, p (n + (w + 1)) := by
    rw [hs.tsum_eq_zero_add]
    simp only [zero_add]
    congr 2
    funext n
    ring_nf
  have hterm : ∀ n, ((w : ℝ) + 1) * p (n + (w + 1)) ≤ r * p (n + w) := by
    intro n
    have hrec := succ_mul_poissonMeasure_real_singleton r (n + w)
    simp only [poissonMeasure_real_singleton] at hrec
    have : p (n + (w + 1)) = p (n + w + 1) := by rw [add_assoc]
    rw [this]
    calc ((w : ℝ) + 1) * p (n + w + 1) ≤ (((n + w : ℕ) : ℝ) + 1) * p (n + w + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      _ = r * p (n + w) := hrec
  have hle : ((w : ℝ) + 1) * ∑' n, p (n + (w + 1)) ≤ r * ∑' n, p (n + w) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm (hs1.mul_left _) (hs.mul_left _)
  rw [poissonMeasure_real_Ioi, poissonMeasure_real_singleton]
  rw [hsplit] at hle
  simp only [hp, poissonWeight] at hle ⊢
  nlinarith

/-- `P(Z ≤ w) P(Z > w) ≤ r P(Z = w)` for `Z ~ Po(r)`. -/
lemma poissonMeasure_real_Iic_mul_Ioi_le (r : ℝ≥0) (w : ℕ) :
    (poissonMeasure r).real (Iic w) * (poissonMeasure r).real (Ioi w) ≤
      r * (poissonMeasure r).real {w} := by
  have h1 := sub_mul_poissonMeasure_real_Iic_le r w
  have h2 := sub_mul_poissonMeasure_real_Ioi_le r w
  have hF : 0 ≤ (poissonMeasure r).real (Iic w) := measureReal_nonneg
  have hT : 0 ≤ (poissonMeasure r).real (Ioi w) := measureReal_nonneg
  have hsum : (poissonMeasure r).real (Iic w) + (poissonMeasure r).real (Ioi w) = 1 := by
    have h := measureReal_add_measureReal_compl (μ := poissonMeasure r)
      (MeasurableSet.of_discrete (s := Iic w))
    rwa [compl_Iic, probReal_univ] at h
  have h3 : ((poissonMeasure r).real (Iic w) + (poissonMeasure r).real (Ioi w)) *
      (r * (poissonMeasure r).real {w}) = r * (poissonMeasure r).real {w} := by
    rw [hsum, one_mul]
  linarith [mul_le_mul_of_nonneg_left h1 hT, mul_le_mul_of_nonneg_left h2 hF]

/-- The numerator of the Stein solution is bounded by `P(Z ≤ w) P(Z > w)`. -/
lemma abs_steinNumerator_le (r : ℝ≥0) (A : Set ℕ) (w : ℕ) :
    |(poissonMeasure r).real (A ∩ Iic w) -
        (poissonMeasure r).real A * (poissonMeasure r).real (Iic w)| ≤
      (poissonMeasure r).real (Iic w) * (poissonMeasure r).real (Ioi w) := by
  set μ := poissonMeasure r
  have hsplit : μ.real (A ∩ Iic w) + μ.real (A \ Iic w) = μ.real A :=
    measureReal_inter_add_sdiff (s := A) MeasurableSet.of_discrete
  have ha1 : μ.real (A ∩ Iic w) ≤ μ.real (Iic w) := measureReal_mono inter_subset_right
  have ha2 : μ.real (A \ Iic w) ≤ μ.real (Ioi w) :=
    measureReal_mono (fun k hk => by simpa using hk.2)
  have ha1' : 0 ≤ μ.real (A ∩ Iic w) := measureReal_nonneg
  have ha2' : 0 ≤ μ.real (A \ Iic w) := measureReal_nonneg
  have hsum : μ.real (Iic w) + μ.real (Ioi w) = 1 := by
    have h := measureReal_add_measureReal_compl (μ := μ)
      (MeasurableSet.of_discrete (s := Iic w))
    rwa [compl_Iic, probReal_univ] at h
  rw [← hsplit, abs_le]
  constructor <;> nlinarith

/-- The Stein solution of `r f(w+1) - w f(w) = 1_A(w) - Po(r)(A)`, normalized by `f 0 = 0`. -/
noncomputable def steinSolution (r : ℝ≥0) (A : Set ℕ) : ℕ → ℝ
  | 0 => 0
  | w + 1 => ((poissonMeasure r).real (A ∩ Iic w) -
      (poissonMeasure r).real A * (poissonMeasure r).real (Iic w)) /
      ((r : ℝ) * (poissonMeasure r).real {w})

/-- The Stein solution is bounded by one. -/
theorem abs_steinSolution_le_one (r : ℝ≥0) (A : Set ℕ) (k : ℕ) :
    |steinSolution r A k| ≤ 1 := by
  cases k with
  | zero => simp [steinSolution]
  | succ w =>
    simp only [steinSolution]
    rw [abs_div]
    have hden : 0 ≤ (r : ℝ) * (poissonMeasure r).real {w} := by positivity
    rw [abs_of_nonneg hden]
    exact div_le_one_of_le₀
      ((abs_steinNumerator_le r A w).trans (poissonMeasure_real_Iic_mul_Ioi_le r w)) hden

/-- A function bounded by one changes by at most `2 d` over a step of length `d`. -/
lemma abs_sub_le_two_mul_of_abs_le_one {f : ℕ → ℝ} (hf : ∀ k, |f k| ≤ 1) (a d : ℕ) :
    |f (a + d) - f a| ≤ 2 * d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc |f (a + d) - f a| ≤ |f (a + d)| + |f a| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hf _) (hf _)
      _ ≤ 2 * d := by linarith

/-- The Stein equation: `r f(w+1) - w f(w) = 1_A(w) - Po(r)(A)` for every `w : ℕ`. -/
theorem steinSolution_equation {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) (w : ℕ) :
    (r : ℝ) * steinSolution r A (w + 1) - w * steinSolution r A w =
      A.indicator 1 w - (poissonMeasure r).real A := by
  have hr' : (0 : ℝ) < r := hr
  cases w with
  | zero =>
    have hp := poissonMeasure_real_singleton_pos 0 hr
    simp only [steinSolution, Nat.cast_zero, zero_mul, sub_zero, Iic_zero_eq]
    have : (poissonMeasure r).real (A ∩ {0}) = A.indicator 1 0 * (poissonMeasure r).real {0} := by
      by_cases h0 : (0 : ℕ) ∈ A
      · rw [inter_eq_right.mpr (singleton_subset_iff.mpr h0), indicator_of_mem h0]; simp
      · rw [indicator_of_notMem h0, inter_singleton_eq_empty.mpr h0]; simp
    rw [this]
    field_simp
  | succ w =>
    have hp := poissonMeasure_real_singleton_pos w hr
    have hp1 := poissonMeasure_real_singleton_pos (w + 1) hr
    have hrec := succ_mul_poissonMeasure_real_singleton r w
    simp only [steinSolution]
    rw [poissonMeasure_real_inter_Iic_succ, poissonMeasure_real_Iic_succ]
    push_cast
    field_simp
    linear_combination ((poissonMeasure r).real A * (poissonMeasure r).real (Iic w) -
      (poissonMeasure r).real (A ∩ Iic w)) * hrec

/-- Increments of the Stein solution are bounded by two. -/
theorem abs_steinSolution_succ_sub_le_two (r : ℝ≥0) (A : Set ℕ) (w : ℕ) :
    |steinSolution r A (w + 1) - steinSolution r A w| ≤ 2 := by
  simpa using abs_sub_le_two_mul_of_abs_le_one (abs_steinSolution_le_one r A) w 1

/-- **Stein identity** for the Poisson law: `E[r f(Z+1) - Z f(Z)] = 0` for `Z ~ Po(r)` and any
bounded `f`. (Not needed for the Chen–Stein bound itself, which only uses the Stein equation
pointwise.) -/
theorem integral_steinOperator_poissonMeasure (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) :
    ∫ n, ((r : ℝ) * f (n + 1) - n * f n) ∂(poissonMeasure r) = 0 := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  set p := poissonWeight r with hpdef
  have hp : Summable p := summable_poissonWeight r
  have hp0 : ∀ n, 0 ≤ p n := fun n => by positivity
  have hs1 : Summable (fun n => p n * ((r : ℝ) * f (n + 1))) := by
    refine Summable.of_norm_bounded (hp.mul_right ((r : ℝ) * C)) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 n), abs_mul, abs_of_nonneg r.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf _) r.coe_nonneg) (hp0 n)
  have hrec : ∀ n, p (n + 1) * (((n + 1 : ℕ) : ℝ) * f (n + 1)) =
      p n * ((r : ℝ) * f (n + 1)) := by
    intro n
    have := succ_mul_poissonMeasure_real_singleton r n
    simp only [poissonMeasure_real_singleton] at this
    push_cast
    linear_combination f (n + 1) * this
  have hs2 : Summable (fun n => p n * ((n : ℝ) * f n)) := by
    rw [← summable_nat_add_iff 1]
    simp_rw [hrec]
    exact hs1
  have hsplit : ∑' n, p n * ((r : ℝ) * f (n + 1) - n * f n) =
      ∑' n, p n * ((r : ℝ) * f (n + 1)) - ∑' n, p n * ((n : ℝ) * f n) := by
    rw [← hs1.tsum_sub hs2]
    congr 1
    funext n
    ring
  rw [hsplit, hs2.tsum_eq_zero_add]
  simp_rw [hrec]
  simp

end PoissonDeclumping.ChenStein
