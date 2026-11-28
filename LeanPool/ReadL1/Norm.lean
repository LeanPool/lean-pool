/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Basis
public import LeanPool.ReadL1.Growth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

/-!
# The norm, and Śliwa's Lemma 1 (b)

Śliwa puts `‖∑ cᵢ fᵢ‖ = ∑ |cᵢ|`, so in coordinates in the basis `(fᵢ)` the norm is
`‖g‖ = ∑ⱼ |gⱼ|` (`ReadL1.nrm`).

This file proves the facts about `xⁱ` that the boundedness proof (Lemma 2) uses:

* the recursion defining `xⁱ`, one block kind at a time (`ReadL1.xPow_of_J` and friends);
* on a `J` or `L` block, `xⁱ` is a multiple of one basis vector, so its norm is the inverse
  weight (`ReadL1.nrm_xPow_of_J`, `ReadL1.nrm_xPow_of_L`);
* **Lemma 1 (b)** (Śliwa p. 630): `‖xⁱ - x^{i - r aₙ}‖ ≤ 2 / aₙ₋ᵣ` on `Iₙ,ᵣ`, and
  `‖xⁱ - bₙʳ x^{i - r bₙ}‖ ≤ 2 bₙ^{r - 1}` on `Kₙ,ᵣ`. Both differences telescope: stepping down
  by `aₙ` (or `bₙ`) moves `i` to the block `Iₙ,ᵣ₋₁` (or `Kₙ,ᵣ₋₁`), and each step contributes
  one basis vector.
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-! ### The coordinate norm -/

/-- Śliwa's norm in coordinates: `‖g‖ = ∑ⱼ |gⱼ|`. -/
noncomputable def nrm (g : ℕ →₀ ℂ) : ℝ := ∑ j ∈ g.support, ‖g j‖

lemma nrm_eq_sum_of_subset (g : ℕ →₀ ℂ) {s : Finset ℕ} (hs : g.support ⊆ s) :
    nrm g = ∑ j ∈ s, ‖g j‖ :=
  Finset.sum_subset hs fun j _ hj ↦ by simp [Finsupp.notMem_support_iff.1 hj]

lemma nrm_nonneg (g : ℕ →₀ ℂ) : 0 ≤ nrm g := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

@[simp] lemma nrm_zero : nrm 0 = 0 := by simp [nrm]

lemma nrm_single (i : ℕ) (c : ℂ) : nrm (single i c) = ‖c‖ := by
  rw [nrm_eq_sum_of_subset _ (support_single_subset)]
  simp

lemma nrm_add_le (g h : ℕ →₀ ℂ) : nrm (g + h) ≤ nrm g + nrm h := by
  classical
  have hs : (g + h).support ⊆ g.support ∪ h.support := support_add
  rw [nrm_eq_sum_of_subset _ hs, nrm_eq_sum_of_subset g Finset.subset_union_left,
    nrm_eq_sum_of_subset h Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ ↦ by simpa using norm_add_le (g j) (h j)

lemma nrm_smul (c : ℂ) (g : ℕ →₀ ℂ) : nrm (c • g) = ‖c‖ * nrm g := by
  rw [nrm_eq_sum_of_subset _ (support_smul), nrm, Finset.mul_sum]
  simp

lemma nrm_neg (g : ℕ →₀ ℂ) : nrm (-g) = nrm g := by
  simpa using nrm_smul (-1) g

lemma nrm_sub_le (g h : ℕ →₀ ℂ) : nrm (g - h) ≤ nrm g + nrm h := by
  simpa [sub_eq_add_neg, nrm_neg] using nrm_add_le g (-h)

lemma nrm_sum_le {ι : Type*} (s : Finset ι) (g : ι → ℕ →₀ ℂ) :
    nrm (∑ k ∈ s, g k) ≤ ∑ k ∈ s, nrm (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact (nrm_add_le _ _).trans (by linarith)

/-! ### The recursion for `xⁱ`, block by block -/

private lemma xPow_unfold (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) :
    ∃ i', i = i' + 1 ∧ block d (i' + 1) = B := by
  obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le (Block.one_le_of_mem h hB)
  exact ⟨i', by ring, by rw [show 1 + i' = i' + 1 by ring] at hB; exact block_eq h hB⟩

lemma xPow_of_J (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .J) :
    xPow d i = (weight (seqA d B.n) B.r i : ℂ)⁻¹ • single i 1 := by
  obtain ⟨i', rfl, hb⟩ := xPow_unfold h hB
  rw [xPow, hb]; simp [hk]

lemma xPow_of_L (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .L) :
    xPow d i = (weight (seqB d B.n) B.r i : ℂ)⁻¹ • single i 1 := by
  obtain ⟨i', rfl, hb⟩ := xPow_unfold h hB
  rw [xPow, hb]; simp [hk]

lemma xPow_of_I (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .I) :
    xPow d i = (seqA d (B.n - B.r) : ℂ)⁻¹ • single i 1 + xPow d (i - seqA d B.n) := by
  obtain ⟨i', rfl, hb⟩ := xPow_unfold h hB
  rw [xPow, hb]
  simp only [hk]
  rw [dite_eq_left (Nat.one_le_iff_ne_zero.1 (h.one_le_a _))]

lemma xPow_of_K (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i) (hk : B.kind = .K) :
    xPow d i = single i 1 + (seqB d B.n : ℂ) • xPow d (i - seqB d B.n) := by
  obtain ⟨i', rfl, hb⟩ := xPow_unfold h hB
  rw [xPow, hb]
  simp only [hk]
  rw [dite_eq_left (lt_of_le_of_lt (Nat.zero_le _) (h.a_lt_b _)).ne']

/-! ### Exact norms on `J` and `L` blocks -/

lemma nrm_xPow_of_J (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .J) : nrm (xPow d i) = (weight (seqA d B.n) B.r i)⁻¹ := by
  rw [xPow_of_J h hB hk, nrm_smul, nrm_single, norm_one, mul_one, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (weight_pos _ _ _).le]

lemma nrm_xPow_of_L (h : PartitionHyp d) {i : ℕ} {B : Block} (hB : B.Mem d i)
    (hk : B.kind = .L) : nrm (xPow d i) = (weight (seqB d B.n) B.r i)⁻¹ := by
  rw [xPow_of_L h hB hk, nrm_smul, nrm_single, norm_one, mul_one, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (weight_pos _ _ _).le]

/-! ### Lemma 1 (b): telescoping on `I` and `K` blocks -/

/-- `v` is monotone. -/
lemma seqV_mono (h : PartitionHyp d) : Monotone (seqV d) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [seqV_zero]
  · exact (seqV_lt_succ h hn).le

/-- Stepping down by `j aₙ` from `Iₙ,ᵣ` lands in `Iₙ,ᵣ₋ⱼ`. -/
lemma mem_I_sub (h : PartitionHyp d) {n r i j : ℕ} (hB : (⟨n, r, .I⟩ : Block).Mem d i)
    (hj : j < r) : (⟨n, r - j, .I⟩ : Block).Mem d (i - j * seqA d n) := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := hB
  dsimp only at hr1 hrn hlo hhi
  have hmul : (r - j) * seqA d n + j * seqA d n = r * seqA d n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hj.le]
  have hv : seqV d (n - r - 1) ≤ seqV d (n - (r - j) - 1) := seqV_mono h (by omega)
  refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only <;> omega

/-- **Lemma 1 (b), `I` blocks, as an identity:** on `Iₙ,ᵣ`,
`xⁱ - x^{i - r aₙ} = ∑_{j < r} a_{n-r+j}⁻¹ δ_{i - j aₙ}`. -/
lemma xPow_sub_of_I (h : PartitionHyp d) {n r i : ℕ} (hB : (⟨n, r, .I⟩ : Block).Mem d i) :
    ∀ k ≤ r, xPow d i - xPow d (i - k * seqA d n) =
      ∑ j ∈ Finset.range k, (seqA d (n - (r - j)) : ℂ)⁻¹ • single (i - j * seqA d n) 1 := by
  intro k
  induction k with
  | zero => intro; simp
  | succ k ih =>
    intro hk
    have hmem := mem_I_sub h hB (j := k) (by omega)
    have hstep := xPow_of_I h hmem rfl
    dsimp only at hstep
    rw [Finset.sum_range_succ, ← ih (by omega), hstep,
      show i - k * seqA d n - seqA d n = i - (k + 1) * seqA d n by rw [Nat.sub_sub]; ring_nf]
    abel

/-- **Lemma 1 (b), `I` blocks:** `‖xⁱ - x^{i - r aₙ}‖ ≤ 2 / aₙ₋ᵣ` on `Iₙ,ᵣ`. The `j`-th term of the
telescoped sum has size `1 / aₙ₋ᵣ₊ⱼ ≤ 1 / (2ʲ aₙ₋ᵣ)`. -/
lemma nrm_xPow_sub_of_I (h : GrowthHyp d) {n r i : ℕ} (hB : (⟨n, r, .I⟩ : Block).Mem d i) :
    nrm (xPow d i - xPow d (i - r * seqA d n)) ≤ 2 / seqA d (n - r) := by
  have hrn : r < n := hB.2.1
  have ha : (0 : ℝ) < seqA d (n - r) := by exact_mod_cast h.one_le_a _
  rw [xPow_sub_of_I h.toPartitionHyp hB r le_rfl]
  refine (nrm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range r, nrm ((seqA d (n - (r - j)) : ℂ)⁻¹ • single (i - j * seqA d n) 1)
      ≤ ∑ j ∈ Finset.range r, (1 / 2 : ℝ) ^ j / seqA d (n - r) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        have hjr : j < r := Finset.mem_range.1 hj
        rw [nrm_smul, nrm_single, norm_one, mul_one, norm_inv, Complex.norm_natCast]
        -- `aₙ₋ᵣ₊ⱼ ≥ 2ʲ aₙ₋ᵣ`.
        have hle := pow_two_mul_le_seqA h (m := n - r) (by omega) j
        rw [show n - r + j = n - (r - j) by omega] at hle
        have hle' : (2 : ℝ) ^ j * seqA d (n - r) ≤ seqA d (n - (r - j)) := by exact_mod_cast hle
        rw [div_eq_mul_inv, one_div_pow, one_div, ← mul_inv]
        exact inv_anti₀ (by positivity) hle'
    _ = (∑ j ∈ Finset.range r, (1 / 2 : ℝ) ^ j) / seqA d (n - r) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ 2 / seqA d (n - r) := div_le_div_of_nonneg_right (sum_geometric_two_le r) ha.le

/-- Stepping down by `j bₙ` from `Kₙ,ᵣ` lands in `Kₙ,ᵣ₋ⱼ`. -/
lemma mem_K_sub {n r i j : ℕ} (hB : (⟨n, r, .K⟩ : Block).Mem d i) (hj : j < r) :
    (⟨n, r - j, .K⟩ : Block).Mem d (i - j * seqB d n) := by
  obtain ⟨hr1, hrn, hlo, hhi⟩ := hB
  dsimp only at hr1 hrn hlo hhi
  have hmul : (r - j) * seqB d n + j * seqB d n = r * seqB d n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hj.le]
  have hmulA : (r - j) * seqA d n ≤ r * seqA d n := Nat.mul_le_mul_right _ (by omega)
  have hexp : (r - j) * (seqA d n + seqB d n) = (r - j) * seqA d n + (r - j) * seqB d n := by
    ring
  have hexp' : r * (seqA d n + seqB d n) = r * seqA d n + r * seqB d n := by ring
  refine ⟨by dsimp; omega, by dsimp; omega, ?_, ?_⟩ <;> dsimp only <;> omega

/-- **Lemma 1 (b), `K` blocks, as an identity:** on `Kₙ,ᵣ`,
`xⁱ - bₙᵏ x^{i - k bₙ} = ∑_{j < k} bₙʲ δ_{i - j bₙ}` for `k ≤ r`. -/
lemma xPow_sub_of_K (h : PartitionHyp d) {n r i : ℕ} (hB : (⟨n, r, .K⟩ : Block).Mem d i) :
    ∀ k ≤ r, xPow d i - (seqB d n : ℂ) ^ k • xPow d (i - k * seqB d n) =
      ∑ j ∈ Finset.range k, (seqB d n : ℂ) ^ j • single (i - j * seqB d n) 1 := by
  intro k
  induction k with
  | zero => intro; simp
  | succ k ih =>
    intro hk
    have hstep := xPow_of_K h (mem_K_sub hB (j := k) (by omega)) rfl
    dsimp only at hstep
    rw [Finset.sum_range_succ, ← ih (by omega), hstep,
      show i - k * seqB d n - seqB d n = i - (k + 1) * seqB d n by rw [Nat.sub_sub]; ring_nf,
      smul_add, smul_smul, ← pow_succ]
    abel

/-- `∑_{j < r} bʲ ≤ 2 b^{r - 1}` for `b ≥ 2` and `r ≥ 1`. -/
lemma sum_pow_le_two_mul_pow {b : ℝ} (hb : 2 ≤ b) {r : ℕ} (hr : 1 ≤ r) :
    ∑ j ∈ Finset.range r, b ^ j ≤ 2 * b ^ (r - 1) := by
  induction r with
  | zero => omega
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp
    · rw [Finset.sum_range_succ]
      have := ih hr0
      have hpow : b ^ r = b * b ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hr0]
      have hb0 : 0 ≤ b ^ (r - 1) := pow_nonneg (by linarith) _
      rw [show r + 1 - 1 = r by omega, hpow] at *
      nlinarith

/-- **Lemma 1 (b), `K` blocks:** `‖xⁱ - bₙʳ x^{i - r bₙ}‖ ≤ 2 bₙ^{r - 1}` on `Kₙ,ᵣ`. -/
lemma nrm_xPow_sub_of_K (h : GrowthHyp d) {n r i : ℕ} (hB : (⟨n, r, .K⟩ : Block).Mem d i) :
    nrm (xPow d i - (seqB d n : ℂ) ^ r • xPow d (i - r * seqB d n)) ≤
      2 * (seqB d n : ℝ) ^ (r - 1) := by
  have hr1 : 1 ≤ r := hB.1
  rw [xPow_sub_of_K h.toPartitionHyp hB r le_rfl]
  refine (nrm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range r, nrm ((seqB d n : ℂ) ^ j • single (i - j * seqB d n) 1)
      = ∑ j ∈ Finset.range r, (seqB d n : ℝ) ^ j := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [nrm_smul, nrm_single, norm_one, mul_one, norm_pow, Complex.norm_natCast]
    _ ≤ 2 * (seqB d n : ℝ) ^ (r - 1) :=
        sum_pow_le_two_mul_pow (by exact_mod_cast h.two_le_b n) hr1

end ReadL1
