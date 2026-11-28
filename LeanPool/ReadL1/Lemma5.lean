/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma5Window
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Śliwa's Lemma 5

For `e ≠ 0` and `k > 2` there is `m > k` with `|P_{(m-k)aₘ} (Qₘ e)| ≥ aₘ⁻¹` (`ReadL1.lemma5`).

Śliwa (pp. 636–638) argues by contradiction from (1): `|P_{(m-k)aₘ} (Qₘ e)| < aₘ⁻¹` for every
`m > k` (`ReadL1.Hyp1`). In the notation of `ReadL1.Lemma5Coeff`, with `Wₙ = (vₙ₋₂, vₙ₋₁]`:

* (4) `∑_{vₘ₋₁ < i ≤ (m-k)aₘ} |y_{m,i}| < aₘ⁻¹` (`ReadL1.step_four`);
* (5) `∑_{Wₙ} |z_{n,j}| ≤ aₙ⁻¹` (`ReadL1.step_five`), through `y_{m,j} = aₙ eⱼ` on `M_{m,n}`;
* (6), (7) `∑_{Wₙ} |y_{n,j}| < 2aₙ⁻¹`, so `∑_{Wₙ} |eⱼ| < 2aₙ⁻¹ Bₙ₋₁` (`ReadL1.step_window`);
* p. 638: `∑_{j ≤ vₙ₋₁} |z_{n,j}| ≤ aₙ₊₁⁻¹`, `|P_{vₙ₋₁} ∑_{l ≤ vₙ₋₁} eₗ fₗ| < aₙ⁻¹ + aₙ₊₁⁻¹ +
  aₙ₋₁ aₙ⁻¹`, and finally `∑_{j ≤ vₙ₋₁} |eⱼ| < aₙ₋₁⁻¹` (`ReadL1.step_final`) for every `n > k`,
  which forces `e = 0`.

Śliwa's constants are slightly rounded here and there (e.g. `2aₙ⁻¹aₙ₋₁` for
`aₙ⁻¹ + aₙ₊₁⁻¹ + aₙ₋₁aₙ⁻¹`); the growth facts used are `aₘ₊₁ ≥ 2aₘ` and `4aₘ² Bₘ ≤ aₘ₊₁`.
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

/-- Śliwa's assumption (1), to be refuted. -/
def Hyp1 (h : GrowthHyp d) (e : L1) (k : ℕ) : Prop :=
  ∀ m, k < m →
    pnorm (ptrunc ((m - k) * seqA d m) (qPoly h.toPartitionHyp m e)) < (seqA d m : ℝ)⁻¹

section

variable {h : GrowthHyp d} {e : L1} {k : ℕ}

lemma seqA_pos (h : GrowthHyp d) (m : ℕ) : (0 : ℝ) < seqA d m := by
  exact_mod_cast h.one_le_a m

lemma seqV_lt_mul (h : GrowthHyp d) {k n : ℕ} (hkn : k < n) :
    seqV d (n - 1) < (n - k) * seqA d n := by
  have h1 := h.v_lt_a n (n - 1) (by omega)
  have h2 : seqA d n ≤ (n - k) * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- Coefficients of `Qₘ e` below `(m - k)aₘ` sum to less than `aₘ⁻¹`. -/
lemma sum_norm_qCoeff_lt (hk : 2 < k) (H : Hyp1 h e k) {m : ℕ} (hkm : k < m) {s : Finset ℕ}
    (hs : s ⊆ Finset.range ((m - k) * seqA d m + 1)) :
    ∑ j ∈ s, ‖qCoeffCLM h.toPartitionHyp m j e‖ < (seqA d m : ℝ)⁻¹ := by
  refine lt_of_le_of_lt ?_ (H m hkm)
  rw [pnorm_ptrunc_eq_sum]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hs fun _ _ _ ↦ norm_nonneg _).trans_eq ?_
  exact Finset.sum_congr rfl fun j _ ↦ by rw [coeff_qPoly _ (by omega)]

/-- **(4)**: `∑_{vₘ₋₁ < i ≤ (m-k)aₘ} |y_{m,i}| < aₘ⁻¹`. -/
lemma step_four (hk : 2 < k) (H : Hyp1 h e k) {m : ℕ} (hkm : k < m) :
    ∑ i ∈ Finset.Ioc (seqV d (m - 1)) ((m - k) * seqA d m), ‖yCoeff d m i e‖ <
      (seqA d m : ℝ)⁻¹ := by
  have hP := h.toPartitionHyp
  have hyq : ∀ i ∈ Finset.Ioc (seqV d (m - 1)) ((m - k) * seqA d m),
      yCoeff d m i e = qCoeffCLM hP m i e := fun i hi ↦ by
    rw [Finset.mem_Ioc] at hi
    rw [qCoeffCLM_eq_add, zCoeff_eq_zero hP (n := m) (j := i) hi.1 e, add_zero]
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [hyq i hi]]
  exact sum_norm_qCoeff_lt hk H hkm fun i hi ↦ by
    rw [Finset.mem_Ioc] at hi; exact Finset.mem_range.2 (by omega)

/-- Bounding `∑ |z_{n,j}|` through Śliwa's (2), one level `m = n + t + 1` at a time. -/
lemma sum_norm_zCoeff_le (h : GrowthHyp d) {n : ℕ} (hn : 2 ≤ n) (s : Finset ℕ)
    (hs : ∀ j ∈ s, j ≤ seqV d (n - 1)) (e : L1) {g : ℕ → ℝ} (hg : Summable g)
    (hbound : ∀ t, ∑ j ∈ s, (seqA d n : ℝ) * ‖e (zIdx d n j t)‖ ≤ g t) :
    ∑ j ∈ s, ‖zCoeff d n j e‖ ≤ ∑' t, g t := by
  have hP := h.toPartitionHyp
  have hsum : ∀ j ∈ s, Summable fun t ↦ (seqA d n : ℝ) * ‖e (zIdx d n j t)‖ := fun j hj ↦
    ((summable_norm e).comp_injective (zIdx_injective hP (by omega) (hs j hj))).mul_left _
  have hz : ∀ j ∈ s, ‖zCoeff d n j e‖ ≤ ∑' t, (seqA d n : ℝ) * ‖e (zIdx d n j t)‖ := by
    intro j hj
    have hnorm : ∀ t, ‖-(seqA d n : ℂ) * e (zIdx d n j t)‖ =
        (seqA d n : ℝ) * ‖e (zIdx d n j t)‖ := fun t ↦ by
      rw [norm_mul, norm_neg, Complex.norm_natCast]
    rw [← (hasSum_zCoeff h hn (hs j hj) e).tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
    · simpa only [hnorm] using hsum j hj
    · exact tsum_congr hnorm
  calc ∑ j ∈ s, ‖zCoeff d n j e‖ ≤ ∑ j ∈ s, ∑' t, (seqA d n : ℝ) * ‖e (zIdx d n j t)‖ :=
        Finset.sum_le_sum hz
    _ = ∑' t, ∑ j ∈ s, (seqA d n : ℝ) * ‖e (zIdx d n j t)‖ :=
        (Summable.tsum_finsetSum hsum).symm
    _ ≤ ∑' t, g t := Summable.tsum_le_tsum hbound (summable_sum hsum) hg

/-- `aₘ⁻¹ ≤ aₙ⁻¹ / 2 / 2ᵗ` for `m = n + t + 1`. -/
lemma inv_seqA_le_geom (h : GrowthHyp d) {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    (seqA d (n + t + 1) : ℝ)⁻¹ ≤ (seqA d n : ℝ)⁻¹ / 2 / 2 ^ t := by
  have h1 := pow_two_mul_le_seqA h hn (t + 1)
  rw [← add_assoc] at h1
  have h2 : (2 : ℝ) ^ (t + 1) * seqA d n ≤ seqA d (n + t + 1) := by exact_mod_cast h1
  have ha := seqA_pos h n
  calc (seqA d (n + t + 1) : ℝ)⁻¹ ≤ ((2 : ℝ) ^ (t + 1) * seqA d n)⁻¹ :=
        inv_anti₀ (by positivity) h2
    _ = (seqA d n : ℝ)⁻¹ / 2 / 2 ^ t := by rw [pow_succ]; field_simp

/-- **(5)**: `∑_{vₙ₋₂ < j ≤ vₙ₋₁} |z_{n,j}| ≤ aₙ⁻¹`. -/
lemma step_five (hk : 2 < k) (H : Hyp1 h e k) {n : ℕ} (hkn : k < n) :
    ∑ j ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)), ‖zCoeff d n j e‖ ≤ (seqA d n : ℝ)⁻¹ := by
  have hP := h.toPartitionHyp
  rw [← tsum_geometric_two' (seqA d n : ℝ)⁻¹]
  refine sum_norm_zCoeff_le h (by omega) _ (fun j hj ↦ (Finset.mem_Ioc.1 hj).2) e
    (summable_geometric_two' _) fun t ↦ ?_
  have hva := h.v_lt_a (n + t + 1) (n - 1) (by omega)
  have hmul : (t + 1 + 1) * seqA d (n + t + 1) ≤ (n + t + 1 - k) * seqA d (n + t + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hinj : Set.InjOn (fun j ↦ zIdx d n j t)
      (Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)) : Set ℕ) := fun j _ j' _ hjj ↦ by
    simp only [zIdx] at hjj; omega
  have hsub : (Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1))).image (fun j ↦ zIdx d n j t) ⊆
      Finset.Ioc (seqV d (n + t + 1 - 1)) ((n + t + 1 - k) * seqA d (n + t + 1)) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    rw [Finset.mem_Ioc] at hj ⊢
    refine ⟨(zIdx_mem_level hP (by omega) hj.2 t).1, ?_⟩
    simp only [zIdx]
    rw [add_one_mul] at hmul
    omega
  calc ∑ j ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)), (seqA d n : ℝ) * ‖e (zIdx d n j t)‖
      = ∑ j ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)),
          ‖yCoeff d (n + t + 1) (zIdx d n j t) e‖ := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [Finset.mem_Ioc] at hj
        obtain ⟨hw1, hw2⟩ := zIdx_mem_window (d := d) hj.1 hj.2 t
        rw [yCoeff_of_window hP (by omega) (by omega) hw1 hw2, norm_mul, Complex.norm_natCast]
    _ = ∑ i ∈ (Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1))).image (fun j ↦ zIdx d n j t),
          ‖yCoeff d (n + t + 1) i e‖ :=
        (Finset.sum_image (f := fun i ↦ ‖yCoeff d (n + t + 1) i e‖) hinj).symm
    _ ≤ ∑ i ∈ Finset.Ioc (seqV d (n + t + 1 - 1)) ((n + t + 1 - k) * seqA d (n + t + 1)),
          ‖yCoeff d (n + t + 1) i e‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ norm_nonneg _
    _ ≤ (seqA d (n + t + 1) : ℝ)⁻¹ := (step_four hk H (by omega)).le
    _ ≤ (seqA d n : ℝ)⁻¹ / 2 / 2 ^ t := inv_seqA_le_geom h (by omega) t

/-- `‖y‖ ≤ ‖Qₙ e‖ + ‖z‖`, coefficientwise. -/
lemma norm_yCoeff_le (h : GrowthHyp d) (n j : ℕ) (e : L1) :
    ‖yCoeff d n j e‖ ≤ ‖qCoeffCLM h.toPartitionHyp n j e‖ + ‖zCoeff d n j e‖ := by
  rw [show yCoeff d n j e = qCoeffCLM h.toPartitionHyp n j e - zCoeff d n j e by
    rw [qCoeffCLM_eq_add]; ring]
  exact norm_sub_le _ _

/-- **(6), (7)** and Śliwa's estimate for `∑_{Wₙ} |eⱼ|`: below `2aₙ⁻¹ Bₙ₋₁`. -/
lemma step_window (hk : 2 < k) (H : Hyp1 h e k) {n : ℕ} (hkn : k < n) :
    ∑ i ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)), ‖e i‖ <
      2 * (seqA d n : ℝ)⁻¹ * capB d (n - 1) := by
  have hy : ∑ j ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)), ‖yCoeff d n j e‖ <
      2 * (seqA d n : ℝ)⁻¹ := by
    have hq := sum_norm_qCoeff_lt hk H hkn (s := Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)))
      fun j hj ↦ by
        have := seqV_lt_mul h hkn
        rw [Finset.mem_Ioc] at hj; exact Finset.mem_range.2 (by omega)
    have hz := step_five hk H hkn
    calc _ ≤ ∑ j ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)),
          (‖qCoeffCLM h.toPartitionHyp n j e‖ + ‖zCoeff d n j e‖) :=
          Finset.sum_le_sum fun j _ ↦ norm_yCoeff_le h n j e
      _ < 2 * (seqA d n : ℝ)⁻¹ := by rw [Finset.sum_add_distrib]; linarith
  have hB : 0 < capB d (n - 1) := zero_lt_one.trans_le (one_le_capB _)
  exact (sum_norm_window_le h (by omega) e).trans_lt (mul_lt_mul_of_pos_right hy hB)

/-- The window one level up: `∑_{vₘ₋₁ < i ≤ vₘ} |eᵢ| < 2aₘ₊₁⁻¹ Bₘ` for `m ≥ k`. -/
lemma step_level (hk : 2 < k) (H : Hyp1 h e k) {m : ℕ} (hkm : k ≤ m) :
    ∑ i ∈ Finset.Ioc (seqV d (m - 1)) (seqV d m), ‖e i‖ <
      2 * (seqA d (m + 1) : ℝ)⁻¹ * capB d m := by
  have := step_window hk H (n := m + 1) (by omega)
  rwa [show m + 1 - 2 = m - 1 by omega, show m + 1 - 1 = m by omega] at this

/-- `2aₘ₊₁⁻¹ Bₘ ≤ aₘ⁻¹`. -/
lemma two_inv_mul_capB_le (h : GrowthHyp d) {m : ℕ} (hm : 1 ≤ m) :
    2 * (seqA d (m + 1) : ℝ)⁻¹ * capB d m ≤ (seqA d m : ℝ)⁻¹ := by
  have hf := four_sq_mul_capB_le h hm
  have ha := seqA_pos h m
  have ha1 := seqA_pos h (m + 1)
  have ha2 : (1 : ℝ) ≤ seqA d m := by exact_mod_cast h.one_le_a m
  have hB : 0 ≤ capB d m := zero_le_one.trans (one_le_capB m)
  have key : 2 * capB d m * seqA d m ≤ seqA d (m + 1) := by nlinarith
  calc 2 * (seqA d (m + 1) : ℝ)⁻¹ * capB d m
      = (2 * capB d m * seqA d m) * ((seqA d (m + 1) : ℝ)⁻¹ * (seqA d m : ℝ)⁻¹) := by
        field_simp
    _ ≤ seqA d (m + 1) * ((seqA d (m + 1) : ℝ)⁻¹ * (seqA d m : ℝ)⁻¹) := by gcongr
    _ = (seqA d m : ℝ)⁻¹ := by field_simp

/-- Śliwa p. 637 (end): `∑_{vₘ₋₁ < i ≤ cₘ} |eᵢ| < aₘ⁻¹` for `m ≥ k`. -/
lemma step_tail (hk : 2 < k) (H : Hyp1 h e k) {m : ℕ} (hkm : k ≤ m) :
    ∑ i ∈ Finset.Ioc (seqV d (m - 1)) ((m - 1) * seqA d m), ‖e i‖ < (seqA d m : ℝ)⁻¹ := by
  have hvm : (m - 1) * seqA d m ≤ seqV d m := by
    unfold seqV; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  refine lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc_right hvm) fun _ _ _ ↦ norm_nonneg _) ?_
  exact (step_level hk H hkm).trans_le (two_inv_mul_capB_le h (by omega))

/-- `aₙ (2aₘ₊₁⁻¹ Bₘ) ≤ aₙ₊₁⁻¹ / 2 / 2ᵗ` for `m = n + t + 1`. -/
lemma seqA_mul_le_geom (h : GrowthHyp d) {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    (seqA d n : ℝ) * (2 * (seqA d (n + t + 1 + 1) : ℝ)⁻¹ * capB d (n + t + 1)) ≤
      (seqA d (n + 1) : ℝ)⁻¹ / 2 / 2 ^ t := by
  have hf := four_sq_mul_capB_le h (m := n + t + 1) (by omega)
  have hT : (2 : ℝ) ^ t * seqA d (n + 1) ≤ seqA d (n + t + 1) := by
    have := pow_two_mul_le_seqA h (m := n + 1) (by omega) t
    rw [show n + 1 + t = n + t + 1 by omega] at this
    exact_mod_cast this
  have hAm : (seqA d n : ℝ) ≤ seqA d (n + t + 1) := by
    exact_mod_cast seqA_mono h (m' := n + t + 1) hn (by omega)
  set A := (seqA d n : ℝ)
  set Am := (seqA d (n + t + 1) : ℝ)
  set Am1 := (seqA d (n + t + 1 + 1) : ℝ)
  set A1 := (seqA d (n + 1) : ℝ)
  set B := capB d (n + t + 1)
  have hA := seqA_pos h n
  have hA1 := seqA_pos h (n + 1)
  have hAm1 := seqA_pos h (n + t + 1 + 1)
  have hB : 0 ≤ B := zero_le_one.trans (one_le_capB _)
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have hprod : A * (2 ^ t * A1) ≤ Am * Am := mul_le_mul hAm hT (by positivity) (by linarith)
  rw [show A * (2 * Am1⁻¹ * B) = (2 * A * B) / Am1 by field_simp,
    show A1⁻¹ / 2 / 2 ^ t = 1 / (2 * 2 ^ t * A1) by field_simp,
    div_le_div_iff₀ hAm1 (by positivity)]
  calc 2 * A * B * (2 * 2 ^ t * A1) = 4 * B * (A * (2 ^ t * A1)) := by ring
    _ ≤ 4 * B * (Am * Am) := by gcongr
    _ = 4 * Am ^ 2 * B := by ring
    _ ≤ 1 * Am1 := by linarith

/-- Śliwa p. 638 (top): `∑_{j ≤ vₙ₋₁} |z_{n,j}| ≤ aₙ₊₁⁻¹` for `n ≥ k`. -/
lemma step_z_all (hk : 2 < k) (H : Hyp1 h e k) {n : ℕ} (hkn : k ≤ n) :
    ∑ j ∈ Finset.range (seqV d (n - 1) + 1), ‖zCoeff d n j e‖ ≤ (seqA d (n + 1) : ℝ)⁻¹ := by
  have hP := h.toPartitionHyp
  rw [← tsum_geometric_two' (seqA d (n + 1) : ℝ)⁻¹]
  refine sum_norm_zCoeff_le h (by omega) _
    (fun j hj ↦ Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) e (summable_geometric_two' _)
    fun t ↦ ?_
  have hinj : Set.InjOn (fun j ↦ zIdx d n j t)
      (Finset.range (seqV d (n - 1) + 1) : Set ℕ) := fun j _ j' _ hjj ↦ by
    simp only [zIdx] at hjj; omega
  have hsub : (Finset.range (seqV d (n - 1) + 1)).image (fun j ↦ zIdx d n j t) ⊆
      Finset.Ioc (seqV d (n + t + 1 - 1)) (seqV d (n + t + 1)) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact Finset.mem_Ioc.2 (zIdx_mem_level hP (by omega)
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) t)
  calc ∑ j ∈ Finset.range (seqV d (n - 1) + 1), (seqA d n : ℝ) * ‖e (zIdx d n j t)‖
      = (seqA d n : ℝ) * ∑ i ∈ (Finset.range (seqV d (n - 1) + 1)).image
          (fun j ↦ zIdx d n j t), ‖e i‖ := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ (seqA d n : ℝ) * ∑ i ∈ Finset.Ioc (seqV d (n + t + 1 - 1)) (seqV d (n + t + 1)),
          ‖e i‖ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ norm_nonneg _) (seqA_pos h n).le
    _ ≤ (seqA d n : ℝ) * (2 * (seqA d (n + t + 1 + 1) : ℝ)⁻¹ * capB d (n + t + 1)) :=
        mul_le_mul_of_nonneg_left (step_level hk H (by omega)).le (seqA_pos h n).le
    _ ≤ (seqA d (n + 1) : ℝ)⁻¹ / 2 / 2 ^ t := seqA_mul_le_geom h (by omega) t

/-- Śliwa p. 638: `∑_{j ≤ vₙ₋₁} |y_{n,j}| < aₙ⁻¹ + aₙ₊₁⁻¹`. -/
lemma step_y_all (hk : 2 < k) (H : Hyp1 h e k) {n : ℕ} (hkn : k < n) :
    ∑ j ∈ Finset.range (seqV d (n - 1) + 1), ‖yCoeff d n j e‖ <
      (seqA d n : ℝ)⁻¹ + (seqA d (n + 1) : ℝ)⁻¹ := by
  have hq := sum_norm_qCoeff_lt hk H hkn (s := Finset.range (seqV d (n - 1) + 1))
    fun j hj ↦ by
      have := seqV_lt_mul h hkn
      rw [Finset.mem_range] at hj ⊢; omega
  have hz := step_z_all hk H hkn.le
  calc _ ≤ ∑ j ∈ Finset.range (seqV d (n - 1) + 1),
        (‖qCoeffCLM h.toPartitionHyp n j e‖ + ‖zCoeff d n j e‖) :=
        Finset.sum_le_sum fun j _ ↦ norm_yCoeff_le h n j e
    _ < _ := by rw [Finset.sum_add_distrib]; linarith

/-- Śliwa p. 638: `|∑_{l ≤ vₙ₋₁} eₗ fₗ| < aₙ⁻¹ + aₙ₊₁⁻¹ + aₙ₋₁ aₙ⁻¹`. -/
lemma step_S (hk : 2 < k) (H : Hyp1 h e k) {n : ℕ} (hkn : k < n) :
    pnorm (fromCoord d (truncL1 (seqV d (n - 1)) e)) <
      (seqA d n : ℝ)⁻¹ + (seqA d (n + 1) : ℝ)⁻¹ + seqA d (n - 1) * (seqA d n : ℝ)⁻¹ := by
  have hP := h.toPartitionHyp
  set v := seqV d (n - 1) with hv
  set c := (n - 1) * seqA d n with hc
  have hvc : v + 1 ≤ c + 1 := by
    have h1 := hP.v_lt_a n (n - 1) (by omega)
    have h2 : seqA d n ≤ (n - 1) * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
    omega
  set S := fromCoord d (truncL1 v e) with hS
  set R : ℕ →₀ ℂ := ∑ l ∈ Finset.Ico (v + 1) (c + 1), single l (e l) with hR
  have hsplit : truncL1 c e = truncL1 v e + R := by
    rw [truncL1, truncL1, hR, Finset.sum_range_add_sum_Ico _ hvc]
  have hSP : ptrunc v S = S := ptrunc_of_natDegree_le (natDegree_fromCoord_truncL1_le hP v e)
  have hSeq : S = ptrunc v (fromCoord d (truncL1 c e)) - ptrunc v (fromCoord d R) := by
    rw [hsplit, map_add, ptrunc_add, hSP, add_sub_cancel_right]
  have h1 : pnorm (ptrunc v (fromCoord d (truncL1 c e))) <
      (seqA d n : ℝ)⁻¹ + (seqA d (n + 1) : ℝ)⁻¹ := by
    rw [pnorm_ptrunc_eq_sum]
    refine lt_of_eq_of_lt ?_ (step_y_all hk H hkn)
    exact Finset.sum_congr rfl fun j _ ↦ by rw [yCoeff_eq_coeff]
  have hRpoly : fromCoord d R = ∑ l ∈ Finset.Ico (v + 1) (c + 1), e l • fPoly d l := by
    rw [hR, map_sum]; simp only [fromCoord_single]
  have htail : ∑ l ∈ Finset.Ico (v + 1) (c + 1), ‖e l‖ < (seqA d n : ℝ)⁻¹ := by
    rw [Finset.Ico_add_one_add_one_eq_Ioc]; exact step_tail hk H hkn.le
  have h2 : pnorm (ptrunc v (fromCoord d R)) ≤
      seqA d (n - 1) * ∑ l ∈ Finset.Ico (v + 1) (c + 1), ‖e l‖ := by
    rw [hRpoly, ptrunc_sum_smul, Finset.mul_sum]
    refine (pnorm_sum_le _ _).trans (Finset.sum_le_sum fun l hl ↦ ?_)
    rw [Finset.mem_Ico] at hl
    rw [smul_eq_C_mul, pnorm_C_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (pnorm_ptrunc_fPoly_le h (by omega) (by omega) (by omega)) (norm_nonneg _)
  have ha := seqA_pos h (n - 1)
  rw [hSeq]
  refine (pnorm_sub_le _ _).trans_lt ?_
  have h3 : (seqA d (n - 1) : ℝ) * ∑ l ∈ Finset.Ico (v + 1) (c + 1), ‖e l‖ <
      seqA d (n - 1) * (seqA d n : ℝ)⁻¹ := mul_lt_mul_of_pos_left htail ha
  linarith

/-- `Bₙ₋₁ (aₙ⁻¹ + aₙ₊₁⁻¹ + aₙ₋₁ aₙ⁻¹) ≤ aₙ₋₁⁻¹`. -/
lemma capB_mul_le (h : GrowthHyp d) {n : ℕ} (hn : 2 ≤ n) :
    capB d (n - 1) * ((seqA d n : ℝ)⁻¹ + (seqA d (n + 1) : ℝ)⁻¹ +
      seqA d (n - 1) * (seqA d n : ℝ)⁻¹) ≤ (seqA d (n - 1) : ℝ)⁻¹ := by
  have hf := four_sq_mul_capB_le h (m := n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hf
  have ha := seqA_pos h n
  have ha1 := seqA_pos h (n + 1)
  have ha' := seqA_pos h (n - 1)
  have ha'1 : (1 : ℝ) ≤ seqA d (n - 1) := by exact_mod_cast h.one_le_a _
  have hmono : (seqA d n : ℝ) ≤ seqA d (n + 1) := by
    exact_mod_cast seqA_mono h (by omega) (by omega)
  have hB : 0 ≤ capB d (n - 1) := zero_le_one.trans (one_le_capB _)
  have hinv : (seqA d (n + 1) : ℝ)⁻¹ ≤ (seqA d n : ℝ)⁻¹ := inv_anti₀ ha hmono
  set a' := (seqA d (n - 1) : ℝ)
  set A := (seqA d n : ℝ)
  set B := capB d (n - 1)
  calc B * (A⁻¹ + (seqA d (n + 1) : ℝ)⁻¹ + a' * A⁻¹) ≤ B * ((2 + a') * A⁻¹) := by
        gcongr; linarith
    _ = (B * (2 + a') * a') * (A⁻¹ * a'⁻¹) := by field_simp
    _ ≤ A * (A⁻¹ * a'⁻¹) := by
        gcongr
        nlinarith
    _ = a'⁻¹ := by field_simp

/-- **Śliwa p. 638 (end)**: `∑_{j ≤ vₙ₋₁} |eⱼ| < aₙ₋₁⁻¹` for every `n > k`. -/
lemma step_final (hk : 2 < k) (H : Hyp1 h e k) {n : ℕ} (hkn : k < n) :
    ∑ j ∈ Finset.range (seqV d (n - 1) + 1), ‖e j‖ < (seqA d (n - 1) : ℝ)⁻¹ := by
  have hP := h.toPartitionHyp
  have hB : 0 < capB d (n - 1) := zero_lt_one.trans_le (one_le_capB _)
  rw [← nrm_truncL1, ← toCoord_fromCoord hP (truncL1 (seqV d (n - 1)) e)]
  refine (nrm_toCoord_le (natDegree_fromCoord_truncL1_le hP _ e)
    (nrm_xPow_le_cap h (n - 1) (by omega)).2).trans_lt ?_
  exact (mul_lt_mul_of_pos_left (step_S hk H hkn) hB).trans_le (capB_mul_le h (by omega))

end

/-- **Śliwa's Lemma 5.** For `e ≠ 0` and `k > 2` there is `m > k` with
`|P_{(m-k)aₘ} (Qₘ e)| ≥ aₘ⁻¹`. -/
theorem lemma5 (h : GrowthHyp d) {e : L1} (he : e ≠ 0) {k : ℕ} (hk : 2 < k) :
    ∃ m, k < m ∧
      (seqA d m : ℝ)⁻¹ ≤ pnorm (ptrunc ((m - k) * seqA d m) (qPoly h.toPartitionHyp m e)) := by
  by_contra hcon
  push Not at hcon
  have H : Hyp1 h e k := hcon
  apply he
  refine lp.ext (funext fun i ↦ ?_)
  rw [lp.coeFn_zero, Pi.zero_apply]
  by_contra hi
  have hpos : 0 < ‖e i‖ := norm_pos_iff.2 hi
  obtain ⟨N, hN⟩ := exists_nat_gt (‖e i‖)⁻¹
  set n := k + i + N + 2 with hn
  have hfin := step_final hk H (n := n) (by omega)
  have hiv : i ≤ seqV d (n - 1) :=
    (le_seqV_succ h.toPartitionHyp i).trans (seqV_mono h.toPartitionHyp (by omega))
  have hle : ‖e i‖ ≤ ∑ j ∈ Finset.range (seqV d (n - 1) + 1), ‖e j‖ :=
    Finset.single_le_sum (fun j _ ↦ norm_nonneg (e j)) (Finset.mem_range.2 (by omega))
  have hNa : (N : ℝ) ≤ seqA d (n - 1) := by
    exact_mod_cast (show N ≤ n - 1 by omega).trans (le_seqA h (by omega))
  have ha := seqA_pos h (n - 1)
  have h1 : 1 < ‖e i‖ * N := by
    rw [inv_lt_iff_one_lt_mul₀ hpos] at hN; linarith
  have h2 : ‖e i‖ * seqA d (n - 1) < 1 := by
    have := mul_lt_mul_of_pos_right (hle.trans_lt hfin) ha
    rwa [inv_mul_cancel₀ ha.ne'] at this
  nlinarith [mul_le_mul_of_nonneg_left hNa hpos.le]

end ReadL1
