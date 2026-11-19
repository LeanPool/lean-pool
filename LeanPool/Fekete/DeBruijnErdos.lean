/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.Fekete.Window
public import Mathlib.Analysis.PSeries

/-!
# Fekete's lemma with an error term (de Bruijn–Erdős)

If `u (m + n) ≤ u m + u n + f (m + n)` on a window `N ≤ m ≤ n ≤ μ * m` with `μ > 1`, where the
error `f` is monotone and `∑ f n / n ^ 2 < ∞`, then `u n / n` tends to `-∞` or to a
real limit. This is the theorem of de Bruijn and Erdős (for `μ = 2`, `N = 1`), in the generality
of Füredi and Ruzsa. The summability condition is sharp; see
`summable_div_sq_iff_forall_not_tendsto_atTop`.

The bounded-defect case `u (m + n) ≤ u m + u n + C` for all `m, n`, which follows directly from
Fekete's lemma, is `exists_tendsto_div_of_le_add_const`.

## Main statements

* `NearlySubadditive.tendsto_atBot_or_exists_tendsto_of_summable`: the de Bruijn–Erdős dichotomy.
  No sign condition on `f` is needed: the theorem for `f` follows from the one for `max f 0`.
* `NearlySubadditive.exists_tendsto_div_of_summable`,
  `NearlySubadditive.tendsto_div_atBot_of_summable`: the bounded below and unbounded cases.
* `sub_le_sum_Ico_inv_sq`: the telescoping bound `1 / k - 1 / n ≤ ∑_{k ≤ i < n} 1 / i ^ 2`, the
  counterpart of `sum_Ioc_inv_sq_le_sub`.

## Implementation notes

Following de Bruijn and Erdős, we absorb the error into a corrected sequence
`G n = u n + n * T n`, where `T n = ∑' k, f (c * (k + n)) / (k + n) ^ 2` and `c = ⌈1 + μ⌉₊`.
Then `G` is subadditive on the same window and `T n → 0`, so the error-free theorem
`NearlySubadditive.tendsto_atBot_or_exists_tendsto` applies. The rescaling by `c` makes the
correction dominate `f (m + n)` using only the monotonicity of `f`: every argument `c * x` with
`x ≥ m` exceeds `m + n`. (Taking `T n = 3 ∑_{x ≥ n} f x / x ^ 2`, as quoted by Füredi and Ruzsa,
only gives lower bounds in terms of `f x` with `x < m + n`, which is the wrong direction for a
monotone `f`.)

## References

* [N. G. de Bruijn, P. Erdős,
  *Some linear and some quadratic recursion formulas. II*][deBruijnErdos1952]
* [Z. Füredi, I. Z. Ruzsa, *Nearly subadditive sequences*][FurediRuzsa2020]
-/

@[expose] public section

noncomputable section

open Filter Finset
open scoped Topology

/-! ### A telescoping lower bound -/

section Telescoping

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The lower bound matching `sum_Ioc_inv_sq_le_sub`:
`1 / k - 1 / n ≤ ∑_{k ≤ i < n} 1 / i ^ 2`. -/
theorem sub_le_sum_Ico_inv_sq {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (k : α)⁻¹ - (n : α)⁻¹ ≤ ∑ i ∈ Ico k n, ((i : α) ^ 2)⁻¹ := by
  refine Nat.le_induction ?_ ?_ n h
  · simp
  intro n hn IH
  rw [sum_Ico_succ_top hn]
  suffices (n : α)⁻¹ - ((n + 1 : ℕ) : α)⁻¹ ≤ ((n : α) ^ 2)⁻¹ by linarith
  have A : 0 < (n : α) := by simpa using (Nat.pos_of_ne_zero hk).trans_le hn
  push_cast
  field_simp
  linarith

end Telescoping

namespace NearlySubadditive

variable {f u : ℕ → ℝ} {μ : ℝ} {N : ℕ}

/-- The summand of the de Bruijn–Erdős correction, `f (c * x) / x ^ 2`. -/
private def corr (f : ℕ → ℝ) (c x : ℕ) : ℝ := f (c * x) / (x : ℝ) ^ 2

private theorem summable_corr (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) {c : ℕ}
    (hc : 0 < c) : Summable (corr f c) := by
  have h := (hfs.comp_injective (mul_right_injective₀ hc.ne')).mul_left ((c : ℝ) ^ 2)
  refine h.congr fun x ↦ ?_
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [corr]
  have hx' : (x : ℝ) ≠ 0 := by positivity
  have hc' : (c : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, corr, Nat.cast_mul]
  field_simp

/-- A lower bound for a block of the correction: if `p ≤ c * m` then
`f p * (1 / m - 1 / (m + n)) ≤ ∑_{k < n} f (c * (k + m)) / (k + m) ^ 2`. -/
private theorem le_sum_corr (hf0 : 0 ≤ f) (hf : Monotone f) {c m n p : ℕ} (hm : 0 < m)
    (hp : p ≤ c * m) :
    f p * (1 / m - 1 / (m + n : ℕ)) ≤ ∑ k ∈ range n, corr f c (k + m) := by
  have := sub_le_sum_Ico_inv_sq (α := ℝ) hm.ne' (Nat.le_add_right m n)
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at this
  rw [one_div, one_div]
  refine (mul_le_mul_of_nonneg_left this (hf0 p)).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun k _ ↦ ?_
  rw [corr, ← div_eq_mul_inv, add_comm k m]
  exact div_le_div_of_nonneg_right (hf (hp.trans (Nat.mul_le_mul_left c (by omega))))
    (sq_nonneg _)

/-- **De Bruijn–Erdős, Füredi–Ruzsa.** If `u (m + n) ≤ u m + u n + f (m + n)` on the window
`N ≤ m ≤ n ≤ μ * m` with `μ > 1`, where `f` is monotone and `∑ f n / n ^ 2 < ∞`, then
`u n / n` tends either to `-∞` or to a real limit. -/
theorem tendsto_atBot_or_exists_tendsto_of_summable (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) :
    Tendsto (fun n ↦ u n / n) atTop atBot ∨ ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) := by
  -- replacing `f` by `max f 0`, we may assume `f ≥ 0`
  wlog hf0 : 0 ≤ f generalizing f
  · refine this (h.mono (fun n ↦ le_max_left (f n) 0) le_rfl le_rfl)
      (fun a b hab ↦ max_le_max (hf hab) le_rfl)
      (hfs.abs.of_nonneg_of_le (fun n ↦ div_nonneg (le_max_right _ _) (sq_nonneg _)) fun n ↦ ?_)
      fun n ↦ le_max_right _ _
    rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
    exact div_le_div_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (sq_nonneg _)
  set c : ℕ := ⌈1 + μ⌉₊
  have hc : (1 + μ : ℝ) ≤ c := Nat.le_ceil _
  have hc0 : 0 < c := by exact_mod_cast (show (0 : ℝ) < c by linarith)
  have hcs := summable_corr hfs hc0
  set T : ℕ → ℝ := fun n ↦ ∑' k, corr f c (k + n)
  have hT : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add (corr f c)
  -- splitting off a block of the tail
  have hsplit : ∀ m n, T m = ∑ k ∈ range n, corr f c (k + m) + T (m + n) := fun m n ↦ by
    have := ((summable_nat_add_iff m).2 hcs).sum_add_tsum_nat_add n
    simp only [T] at this ⊢
    rw [← this]
    congr 1
    exact tsum_congr fun k ↦ by rw [add_assoc, add_comm n m]
  -- the corrected sequence is subadditive on the window
  set G : ℕ → ℝ := fun n ↦ u n + n * T n
  have hG : NearlySubadditive 0 μ (max N 1) G := by
    intro m n hm hmn hnm
    have hmR : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
    have hnR : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hcm := mul_le_mul_of_nonneg_right hc hmR.le
    have hcn := mul_le_mul_of_nonneg_right hc hnR.le
    have hμn := le_mul_of_one_le_left hnR.le hμ.le
    have hp₁ : m + n ≤ c * m := by
      exact_mod_cast (show ((m + n : ℕ) : ℝ) ≤ c * m by push_cast; linarith)
    have hp₂ : m + n ≤ c * n := by
      exact_mod_cast (show ((m + n : ℕ) : ℝ) ≤ c * n by push_cast; linarith)
    have h1 := mul_le_mul_of_nonneg_left (le_sum_corr (n := n) hf0 hf (by omega) hp₁) hmR.le
    have h2 := mul_le_mul_of_nonneg_left (le_sum_corr (n := m) hf0 hf (by omega) hp₂) hnR.le
    have key : (m : ℝ) * (f (m + n) * (1 / m - 1 / (m + n))) +
        n * (f (m + n) * (1 / n - 1 / (n + m))) = f (m + n) := by
      field_simp; ring
    push_cast at h1 h2
    simp only [G, Pi.zero_apply, add_zero]
    push_cast
    rw [hsplit m n, hsplit n m, add_comm n m]
    linarith [h (le_of_max_le_left hm) hmn hnm]
  -- transfer the conclusion from `G` back to `u`
  have hGu : (fun n ↦ u n / n) =ᶠ[atTop] fun n ↦ G n / n - T n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [G]
    field_simp
    ring
  rcases hG.tendsto_atBot_or_exists_tendsto hμ with hbot | ⟨L, hL⟩
  · refine Or.inl (Tendsto.congr' hGu.symm ?_)
    simpa [sub_eq_add_neg] using hbot.atBot_add hT.neg
  · exact Or.inr ⟨L, Tendsto.congr' hGu.symm (by simpa using hL.sub hT)⟩

/-- **De Bruijn–Erdős**, bounded below case. If `u (m + n) ≤ u m + u n + f (m + n)` on the window
`N ≤ m ≤ n ≤ μ * m` with `μ > 1`, where `f` is monotone and `∑ f n / n ^ 2 < ∞`, and `u n / n` is
bounded below, then `u n / n` converges to a real limit. -/
theorem exists_tendsto_div_of_summable (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    (hbdd : BddBelow (Set.range fun n ↦ u n / n)) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) :=
  (h.tendsto_atBot_or_exists_tendsto_of_summable hμ hf hfs).resolve_left
    fun hbot ↦ not_bddBelow_of_tendsto_atBot hbot hbdd

/-- **De Bruijn–Erdős**, unbounded case. Under the hypotheses of
`NearlySubadditive.exists_tendsto_div_of_summable`, if `u n / n` is not bounded below, then
`u n / n → -∞`. -/
theorem tendsto_div_atBot_of_summable (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    (hbdd : ¬ BddBelow (Set.range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot :=
  (h.tendsto_atBot_or_exists_tendsto_of_summable hμ hf hfs).resolve_right fun ⟨_, hL⟩ ↦
    hbdd hL.bddBelow_range

end NearlySubadditive
