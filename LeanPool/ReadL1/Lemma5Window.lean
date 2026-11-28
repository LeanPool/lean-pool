/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma5Coeff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.SplitIfs

/-!
# Tools for Lemma 5: growth facts, truncations, and the coordinate window

* `ReadL1.four_sq_mul_capB_le`: `4aₘ² Bₘ ≤ aₘ₊₁`, the one growth fact Lemma 5 needs beyond
  `aₘ₊₁ ≥ 2aₘ`;
* `ReadL1.truncL1`: the finite sequence `∑_{l ≤ N} eₗ δₗ`, whose polynomial has coefficients
  `y_{n,j}` when `N = (n - 1)aₙ`;
* `ReadL1.sum_norm_window_le`: Śliwa's estimate (p. 637) `∑_{vₙ₋₂ < i ≤ vₙ₋₁} |eᵢ| ≤
  (∑_{vₙ₋₂ < j ≤ vₙ₋₁} |y_{n,j}|) Bₙ₋₁`, from the support facts of `ReadL1.Coord`;
* `ReadL1.pnorm_ptrunc_fPoly_le`: `|P_{vₙ₋₁} fₗ| ≤ aₙ₋₁` for `vₙ₋₁ < l ≤ (n - 1)aₙ` (p. 638).
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

/- ### Growth facts -/

/-- **`4aₘ² Bₘ ≤ aₘ₊₁`**: from `aₘ₊₁ ≥ α^{2bₘ}`, `α bₘ² < α^{√bₘ/4}` and `aₘ < bₘ`. -/
lemma four_sq_mul_capB_le (h : GrowthHyp d) {m : ℕ} (hm : 1 ≤ m) :
    4 * (seqA d m : ℝ) ^ 2 * capB d m ≤ seqA d (m + 1) := by
  have hb := h.rpow_b m hm
  have hab : (seqA d m : ℝ) < seqB d m := by
    have h1 := h.a_small m hm
    have h2 : seqA d m ≤ 8 * m * seqA d m := Nat.le_mul_of_pos_left _ (by omega)
    exact_mod_cast (by omega : seqA d m < seqB d m)
  have hb1 : (1 : ℝ) ≤ seqB d m := by exact_mod_cast (h.two_le_b m).trans' (by norm_num)
  have hsq : Real.sqrt (seqB d m) ≤ seqB d m :=
    calc Real.sqrt (seqB d m) ≤ Real.sqrt ((seqB d m : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = seqB d m := Real.sqrt_sq (by positivity)
  have hαpos : ∀ x : ℝ, 0 < alpha ^ x := fun x ↦ Real.rpow_pos_of_pos alpha_pos x
  have h1 : alpha ^ (Real.sqrt (seqB d m) / 4) ≤ alpha ^ (seqB d m : ℝ) :=
    alpha_rpow_le (by linarith [Real.sqrt_nonneg (seqB d m : ℝ)])
  have h2 : capB d m ≤ alpha ^ (seqB d m : ℝ) := alpha_rpow_le hsq
  have h3 : alpha ^ (2 * seqB d m) = alpha ^ (seqB d m : ℝ) * alpha ^ (seqB d m : ℝ) := by
    rw [Real.rpow_natCast, ← pow_add, two_mul]
  have h4 := h.alpha_pow_two_b_le m hm
  have hcap : 0 ≤ capB d m := zero_le_one.trans (one_le_capB m)
  have ha0 : (0 : ℝ) ≤ seqA d m := Nat.cast_nonneg _
  have h5 : 4 * (seqA d m : ℝ) ^ 2 ≤ alpha * (seqB d m : ℝ) ^ 2 := by
    rw [alpha]; nlinarith
  calc 4 * (seqA d m : ℝ) ^ 2 * capB d m ≤ (alpha * (seqB d m : ℝ) ^ 2) * capB d m := by gcongr
    _ ≤ alpha ^ (seqB d m : ℝ) * alpha ^ (seqB d m : ℝ) :=
        mul_le_mul (by linarith) h2 hcap (hαpos _).le
    _ = alpha ^ (2 * seqB d m) := h3.symm
    _ ≤ seqA d (m + 1) := h4

/-- `aₘ ≥ m`. -/
lemma le_seqA (h : GrowthHyp d) {m : ℕ} (hm : 1 ≤ m) : m ≤ seqA d m := by
  have h1 := pow_two_mul_le_seqA h (le_refl 1) (m - 1)
  rw [show 1 + (m - 1) = m by omega] at h1
  have h2 : m - 1 < 2 ^ (m - 1) := Nat.lt_two_pow_self
  have h3 : 2 ^ (m - 1) ≤ 2 ^ (m - 1) * seqA d 1 := Nat.le_mul_of_pos_right _ (h.one_le_a 1)
  omega

/- ### Truncations -/

/-- The finite sequence `∑_{l ≤ N} eₗ δₗ`. -/
noncomputable def truncL1 (N : ℕ) (e : L1) : ℕ →₀ ℂ :=
  ∑ l ∈ Finset.range (N + 1), single l (e l)

lemma truncL1_apply (N : ℕ) (e : L1) (i : ℕ) : truncL1 N e i = if i ≤ N then e i else 0 := by
  simp [truncL1, Finsupp.finsetSum_apply, Finsupp.single_apply]

lemma mem_support_truncL1 {N : ℕ} {e : L1} {j : ℕ} (hj : j ∈ (truncL1 N e).support) : j ≤ N := by
  rw [Finsupp.mem_support_iff, truncL1_apply] at hj
  by_contra hjN
  exact hj (ite_eq_right hjN)

lemma nrm_truncL1 (N : ℕ) (e : L1) : nrm (truncL1 N e) = ∑ l ∈ Finset.range (N + 1), ‖e l‖ := by
  rw [nrm_eq_sum_of_subset _ (s := Finset.range (N + 1))
    (fun j hj ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (mem_support_truncL1 hj)))]
  exact Finset.sum_congr rfl fun l hl ↦ by
    rw [truncL1_apply, ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))]

lemma coeff_fromCoord_truncL1 (N : ℕ) (e : L1) (j : ℕ) :
    (fromCoord d (truncL1 N e)).coeff j =
      ∑ l ∈ Finset.range (N + 1), e l * (fPoly d l).coeff j := by
  simp [truncL1, map_sum, fromCoord_single]

lemma yCoeff_eq_coeff (n j : ℕ) (e : L1) :
    yCoeff d n j e = (fromCoord d (truncL1 ((n - 1) * seqA d n) e)).coeff j :=
  (coeff_fromCoord_truncL1 _ e j).symm

lemma natDegree_fromCoord_truncL1_le (h : PartitionHyp d) (N : ℕ) (e : L1) :
    (fromCoord d (truncL1 N e)).natDegree ≤ N :=
  natDegree_fromCoord_le h fun _ hj ↦ mem_support_truncL1 hj

/- ### Norms through coordinates -/

lemma sum_norm_le_nrm (g : ℕ →₀ ℂ) (s : Finset ℕ) : ∑ i ∈ s, ‖g i‖ ≤ nrm g := by
  classical
  rw [nrm_eq_sum_of_subset g (Finset.subset_union_right (s₁ := s))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ ↦ norm_nonneg _

lemma toCoord_apply_eq_sum {p : ℂ[X]} {N : ℕ} (hp : p.natDegree ≤ N) (i : ℕ) :
    toCoord d p i = ∑ j ∈ Finset.range (N + 1), p.coeff j * xPow d j i := by
  rw [toCoord_apply, Polynomial.sum_over_range' p (f := fun i c ↦ c • xPow d i)
    (fun n ↦ zero_smul ℂ _) (N + 1) (by omega), Finsupp.finsetSum_apply]
  simp [Finsupp.smul_apply]

lemma support_subset_range {p : ℂ[X]} {N : ℕ} (hp : p.natDegree ≤ N) :
    p.support ⊆ Finset.range (N + 1) := fun k hk ↦
  Finset.mem_range.2 (Nat.lt_succ_of_le ((le_natDegree_of_mem_supp k hk).trans hp))

/-- `‖y‖ ≤ B |y|` when every `‖xʲ‖` involved is at most `B`. -/
lemma nrm_toCoord_le {p : ℂ[X]} {N : ℕ} {B : ℝ} (hp : p.natDegree ≤ N)
    (hB : ∀ j ≤ N, nrm (xPow d j) ≤ B) : nrm (toCoord d p) ≤ B * pnorm p := by
  rw [toCoord_apply, Polynomial.sum_over_range' p (f := fun i c ↦ c • xPow d i)
    (fun n ↦ zero_smul ℂ _) (N + 1) (by omega)]
  refine (nrm_sum_le _ _).trans ?_
  rw [pnorm_eq_sum_of_subset p (support_subset_range hp), Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  rw [nrm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
    (norm_nonneg _)

lemma pnorm_ptrunc_eq_sum (N : ℕ) (p : ℂ[X]) :
    pnorm (ptrunc N p) = ∑ i ∈ Finset.range (N + 1), ‖p.coeff i‖ := by
  rw [pnorm_eq_sum_of_subset _ (support_subset_range (natDegree_ptrunc_le N p))]
  exact Finset.sum_congr rfl fun i hi ↦ by
    rw [coeff_ptrunc, ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]

/- ### The window `(vₙ₋₂, vₙ₋₁]` -/

/-- **Śliwa p. 637**: `∑_{vₙ₋₂ < i ≤ vₙ₋₁} |eᵢ| ≤ (∑_{vₙ₋₂ < j ≤ vₙ₋₁} |y_{n,j}|) Bₙ₋₁`. On the
window, `eᵢ` is the `i`-th coordinate of `∑_{j ≤ cₙ} y_{n,j} xʲ`, and only `j` in the window
contribute: lower `j` by triangularity, higher `j` by the gap. -/
theorem sum_norm_window_le (h : GrowthHyp d) {n : ℕ} (hn : 2 < n) (e : L1) :
    ∑ i ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)), ‖e i‖ ≤
      (∑ j ∈ Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)), ‖yCoeff d n j e‖) * capB d (n - 1) := by
  have hP := h.toPartitionHyp
  set W := Finset.Ioc (seqV d (n - 2)) (seqV d (n - 1)) with hW
  set c := (n - 1) * seqA d n with hc
  set Y := fromCoord d (truncL1 c e) with hYdef
  have hY : toCoord d Y = truncL1 c e := toCoord_fromCoord hP _
  have hYdeg : Y.natDegree ≤ c := natDegree_fromCoord_truncL1_le hP c e
  have hvc : seqV d (n - 1) ≤ c := by
    have h1 := hP.v_lt_a n (n - 1) (by omega)
    have h2 : seqA d n ≤ (n - 1) * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hWc : W ⊆ Finset.range (c + 1) := fun j hj ↦ by
    rw [hW, Finset.mem_Ioc] at hj; exact Finset.mem_range.2 (by omega)
  have hei : ∀ i ∈ W, e i = ∑ j ∈ W, yCoeff d n j e * xPow d j i := by
    intro i hi
    rw [hW, Finset.mem_Ioc] at hi
    calc e i = truncL1 c e i := by rw [truncL1_apply, ite_eq_left (by omega)]
      _ = toCoord d Y i := by rw [hY]
      _ = ∑ j ∈ Finset.range (c + 1), Y.coeff j * xPow d j i := toCoord_apply_eq_sum hYdeg i
      _ = ∑ j ∈ W, yCoeff d n j e * xPow d j i := by
          rw [← Finset.sum_subset hWc fun j hj hjW ↦ ?_]
          · exact Finset.sum_congr rfl fun j _ ↦ by rw [yCoeff_eq_coeff]
          · rw [hW, Finset.mem_Ioc] at hjW
            rw [Finset.mem_range] at hj
            by_cases hjlo : j ≤ seqV d (n - 2)
            · rw [xPow_apply_eq_zero hP (by omega), mul_zero]
            · rw [xPow_apply_gap hP (by omega) hi.1 hi.2 j (by omega) (by omega), mul_zero]
  calc ∑ i ∈ W, ‖e i‖ = ∑ i ∈ W, ‖∑ j ∈ W, yCoeff d n j e * xPow d j i‖ :=
        Finset.sum_congr rfl fun i hi ↦ by rw [hei i hi]
    _ ≤ ∑ i ∈ W, ∑ j ∈ W, ‖yCoeff d n j e‖ * ‖xPow d j i‖ :=
        Finset.sum_le_sum fun i _ ↦ (norm_sum_le _ _).trans_eq (by simp)
    _ = ∑ j ∈ W, ‖yCoeff d n j e‖ * ∑ i ∈ W, ‖xPow d j i‖ := by
        rw [Finset.sum_comm]; simp [Finset.mul_sum]
    _ ≤ ∑ j ∈ W, ‖yCoeff d n j e‖ * capB d (n - 1) := by
        refine Finset.sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [hW, Finset.mem_Ioc] at hj
        exact (sum_norm_le_nrm _ W).trans ((nrm_xPow_le_cap h (n - 1) (by omega)).2 j hj.2)
    _ = (∑ j ∈ W, ‖yCoeff d n j e‖) * capB d (n - 1) := Finset.sum_mul _ _ _ |>.symm

/- ### `|P_{vₙ₋₁} fₗ| ≤ aₙ₋₁` above `vₙ₋₁` -/

lemma ptrunc_X_pow_eq_zero {N l : ℕ} (hl : N < l) : ptrunc N (X ^ l : ℂ[X]) = 0 := by
  ext k
  rw [coeff_ptrunc, coeff_X_pow, coeff_zero]
  split_ifs <;> first | rfl | omega

lemma ptrunc_sum_smul (N : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (p : ℕ → ℂ[X]) :
    ptrunc N (∑ l ∈ s, c l • p l) = ∑ l ∈ s, c l • ptrunc N (p l) := by
  ext k
  simp only [coeff_ptrunc, finsetSum_coeff, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **`|P_{vₙ₋₁} fₗ| ≤ aₙ₋₁`** for `vₙ₋₁ < l ≤ (n - 1)aₙ` (Śliwa p. 638): such `l` lie in `J` or
`I` blocks of level `n`; `P_{vₙ₋₁}` kills `xˡ` and leaves at most `aₙ₋ᵣ x^{l - aₙ}`. -/
lemma pnorm_ptrunc_fPoly_le (h : GrowthHyp d) {n l : ℕ} (hn : 2 ≤ n) (hl1 : seqV d (n - 1) < l)
    (hl2 : l ≤ (n - 1) * seqA d n) :
    pnorm (ptrunc (seqV d (n - 1)) (fPoly d l)) ≤ seqA d (n - 1) := by
  have hP := h.toPartitionHyp
  have hvn : (n - 1) * seqA d n ≤ seqV d n := by
    unfold seqV; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hlev := block_level hP (m := n - 1) (i := l) (by omega) hl1
    (by rw [show n - 1 + 1 = n by omega]; omega)
  have hB := block_mem hP (i := l) (by omega)
  rcases hbl : block d l with ⟨n', r, k⟩
  rw [hbl] at hB hlev
  dsimp only at hlev
  rw [show n' = n by omega] at hB
  have ha0 : (0 : ℝ) ≤ seqA d (n - 1) := Nat.cast_nonneg _
  cases k with
  | J =>
    rw [fPoly_of_J hP hB rfl, ptrunc_C_mul, ptrunc_X_pow_eq_zero hl1, mul_zero, pnorm_zero]
    exact ha0
  | I =>
    rw [fPoly_of_I hP hB rfl, ptrunc_C_mul, ptrunc_sub, ptrunc_X_pow_eq_zero hl1, zero_sub,
      pnorm_C_mul, Complex.norm_natCast]
    dsimp only
    have hr := hB.1
    have hrn := hB.2.1
    dsimp only at hr hrn
    have hneg : pnorm (-ptrunc (seqV d (n - 1)) (X ^ (l - seqA d n)) : ℂ[X]) ≤ 1 := by
      rw [← zero_sub]
      refine (pnorm_sub_le _ _).trans ?_
      rw [pnorm_zero, zero_add]
      exact (pnorm_ptrunc_le _ _).trans (pnorm_X_pow _).le
    have hmono : (seqA d (n - r) : ℝ) ≤ seqA d (n - 1) := by
      exact_mod_cast seqA_mono h (by omega) (by omega)
    calc (seqA d (n - r) : ℝ) * pnorm (-ptrunc (seqV d (n - 1)) (X ^ (l - seqA d n)))
        ≤ seqA d (n - r) * 1 := by gcongr
      _ ≤ seqA d (n - 1) := by rw [mul_one]; exact hmono
  | L =>
    obtain ⟨-, -, hlo, -⟩ := hB
    dsimp only at hlo
    omega
  | K =>
    obtain ⟨hr1, -, hlo, -⟩ := hB
    dsimp only at hr1 hlo
    have hab := hP.a_lt_b n
    have : seqA d n + seqB d n ≤ r * (seqA d n + seqB d n) := Nat.le_mul_of_pos_left _ hr1
    have hn1 : (n - 1) * seqA d n = (n - 2) * seqA d n + seqA d n := by
      rw [show n - 1 = n - 2 + 1 by omega, add_one_mul]
    omega

end ReadL1
