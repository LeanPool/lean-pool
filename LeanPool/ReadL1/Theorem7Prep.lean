/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Cyclic
public import LeanPool.ReadL1.Lemma5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# Preparations for Theorem 7

* Polynomials in the operator: `f(T) e` lies in the orbit span of `e`
  (`ReadL1.aeval_mem_orbitSpan`), and on finite sequences `f(T)` multiplies by `f`
  (`ReadL1.aeval_readOp_toL1`).
* (S1) through Lemma 4: `‖f(T) e - f(T) Qₘ e‖ ≤ α |f| ‖e‖` when the powers of `f` lie in `Kₘ,₁`
  (`ReadL1.norm_aeval_sub_le`).
* `|Qₘ e| ≤ Aₘ ‖e‖` (`ReadL1.pnorm_qPoly_le_capA`), from `|fₗ| ≤ Aₘ` for `l ≤ (m - 1)aₘ`
  (`ReadL1.pnorm_fPoly_le`). Śliwa (p. 640) gets `√Aₘ · √Aₘ` through `‖Qₘ‖ ≤ √Aₘ` and
  `|y| ≤ √Aₘ ‖y‖`; the bound here is the same, reached through the basis directly.
* The norm estimates in (S2), (S3) and (S5).
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

/- ### Polynomials in the operator -/

lemma aeval_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] E)
    (f : ℂ[X]) (x : E) : aeval T f x = ∑ s ∈ f.support, f.coeff s • (T ^ s) x := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, _root_.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, _root_.smul_apply]

lemma aeval_end_apply_eq_sum (T : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ)) (f : ℂ[X]) (x : ℕ →₀ ℂ) :
    aeval T f x = ∑ s ∈ f.support, f.coeff s • (T ^ s) x := by
  rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply]

/-- `f(T) x` lies in the span of the orbit of `x`. -/
lemma aeval_mem_orbitSpan {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E →L[ℂ] E)
    (f : ℂ[X]) (x : E) : aeval T f x ∈ orbitSpan T x := by
  rw [aeval_apply_eq_sum]
  exact Submodule.sum_mem _ fun s _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

/-- On finite sequences, `f(T)` is `f(T₀)`. -/
lemma aeval_readOp_toL1 (h : GrowthHyp d) (f : ℂ[X]) (g : ℕ →₀ ℂ) :
    aeval (readOp h) f (toL1 g) = toL1 (aeval (T₀ d) f g) := by
  rw [aeval_apply_eq_sum, aeval_end_apply_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [readOp_pow_toL1, map_smul]

/-- `f(T)` applied to the coordinates of `y` gives the coordinates of `f y`. -/
lemma aeval_readOp_toL1_toCoord (h : GrowthHyp d) (f y : ℂ[X]) :
    aeval (readOp h) f (toL1 (toCoord d y)) = toL1 (toCoord d (f * y)) := by
  rw [aeval_readOp_toL1, aeval_T₀_toCoord h.toPartitionHyp]

/-- **(S1)**: `‖f(T) e - f(T) Qₘ e‖ ≤ α |f| ‖e‖` when every power of `f` lies in `Kₘ,₁`. -/
lemma norm_aeval_sub_le (h : GrowthHyp d) {m : ℕ} (hm : 2 < m) (f : ℂ[X])
    (hf : ∀ s ∈ f.support, InK1 d m s) (e : L1) :
    ‖aeval (readOp h) f e - aeval (readOp h) f (readQ h hm.le e)‖ ≤ alpha * pnorm f * ‖e‖ := by
  rw [aeval_apply_eq_sum, aeval_apply_eq_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [pnorm_eq_sum_of_subset f le_rfl, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  rw [← smul_sub, norm_smul]
  have hs' : ‖(readOp h ^ s) e - (readOp h ^ s) (readQ h hm.le e)‖ ≤ alpha * ‖e‖ := by
    have heq : (readOp h ^ s) e - (readOp h ^ s) (readQ h hm.le e) =
        (readOp h ^ s - readOp h ^ s * readQ h hm.le) e := rfl
    rw [heq]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (lemma4 h hm (hf s hs)) (norm_nonneg _))
  calc ‖f.coeff s‖ * ‖(readOp h ^ s) e - (readOp h ^ s) (readQ h hm.le e)‖
      ≤ ‖f.coeff s‖ * (alpha * ‖e‖) := mul_le_mul_of_nonneg_left hs' (norm_nonneg _)
    _ = alpha * ‖f.coeff s‖ * ‖e‖ := by ring

lemma pnorm_X_pow_mul (k : ℕ) (p : ℂ[X]) : pnorm (X ^ k * p) = pnorm p := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, pnorm_X_mul, ih]

/-- `xᵃ (Pₙ v) = Pₙ₊ₐ (xᵃ v)`. -/
lemma X_pow_mul_ptrunc (a n : ℕ) (v : ℂ[X]) : X ^ a * ptrunc n v = ptrunc (n + a) (X ^ a * v) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', mul_assoc, ih, X_mul_ptrunc, ← mul_assoc, ← pow_succ', add_assoc]

/- ### `|Qₘ e| ≤ Aₘ ‖e‖` -/

/-- `|Qₘ e| ≤ C ‖e‖` when every `|Qₘ fₗ| ≤ C`. -/
lemma pnorm_qPoly_le (h : PartitionHyp d) {m : ℕ} (hm : 2 ≤ m) {C : ℝ}
    (hC : ∀ l, pnorm (qPolyBasis d m l) ≤ C) (e : L1) : pnorm (qPoly h m e) ≤ C * ‖e‖ := by
  set N := (m - 1) * seqA d m
  have hsum : ∀ j, Summable fun l ↦ ‖e l‖ * ‖(qPolyBasis d m l).coeff j‖ := fun j ↦ by
    simpa only [norm_mul] using summable_norm_qTerm h m j e
  rw [pnorm_eq_sum_of_subset _ (support_subset_range (natDegree_qPoly_le h m e))]
  calc ∑ j ∈ Finset.range (N + 1), ‖(qPoly h m e).coeff j‖
      ≤ ∑ j ∈ Finset.range (N + 1), ∑' l, ‖e l‖ * ‖(qPolyBasis d m l).coeff j‖ := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [coeff_qPoly h hm, qCoeffCLM_apply]
        refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
        · simpa only [norm_mul] using hsum j
        · simp only [norm_mul]
    _ = ∑' l, ∑ j ∈ Finset.range (N + 1), ‖e l‖ * ‖(qPolyBasis d m l).coeff j‖ :=
        (Summable.tsum_finsetSum fun j _ ↦ hsum j).symm
    _ ≤ ∑' l, ‖e l‖ * C := by
        refine Summable.tsum_le_tsum (fun l ↦ ?_) (summable_sum fun j _ ↦ hsum j)
          ((summable_norm e).mul_right C)
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← pnorm_eq_sum_of_subset _ (support_subset_range (natDegree_qPolyBasis_le h hm l))]
        exact hC l
    _ = C * ‖e‖ := by rw [tsum_mul_right, norm_eq_tsum, mul_comm]

lemma capA_mono (h : GrowthHyp d) {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : capA d n ≤ capA d m :=
  alpha_rpow_le (Real.sqrt_le_sqrt (by exact_mod_cast seqA_mono h hn hnm))

lemma capB_le_capA_succ (h : GrowthHyp d) {m : ℕ} (hm : 1 ≤ m) : capB d m ≤ capA d (m + 1) := by
  have := h.rpow_b_add_two_le m hm; unfold capB capA; linarith

/-- `α x² ≤ α^{√x}` from `α x² < α^{√x/4}`. -/
lemma rpow_quarter_le (x : ℝ) : alpha ^ (Real.sqrt x / 4) ≤ alpha ^ Real.sqrt x :=
  alpha_rpow_le (by linarith [Real.sqrt_nonneg x])

lemma two_mul_le_capA (h : GrowthHyp d) {n : ℕ} (hn : 1 ≤ n) : 2 * (seqA d n : ℝ) ≤ capA d n := by
  have h1 := h.rpow_a n hn
  have ha : (1 : ℝ) ≤ seqA d n := by exact_mod_cast h.one_le_a n
  have h2 := rpow_quarter_le (seqA d n : ℝ)
  have h3 : 2 * (seqA d n : ℝ) ≤ alpha * (seqA d n : ℝ) ^ 2 := by rw [alpha]; nlinarith
  unfold capA
  linarith

lemma one_add_le_capA_succ (h : GrowthHyp d) {n : ℕ} (hn : 1 ≤ n) :
    1 + (seqB d n : ℝ) ≤ capA d (n + 1) := by
  have h1 := h.rpow_b n hn
  have hb : (1 : ℝ) ≤ seqB d n := by exact_mod_cast (h.two_le_b n).trans' (by norm_num)
  have h2 := rpow_quarter_le (seqB d n : ℝ)
  have h3 := capB_le_capA_succ h hn
  have h4 : 1 + (seqB d n : ℝ) ≤ alpha * (seqB d n : ℝ) ^ 2 := by rw [alpha]; nlinarith
  unfold capB at h3
  linarith

/-- The exponent numerator `(2r - 1)c - 2i` is at most `c` once `i ≥ (r - 1)c`. -/
lemma weight_numer_le {c r i : ℕ} (hr : 1 ≤ r) (hi : (r - 1) * c ≤ i) :
    (2 * (r : ℝ) - 1) * c - 2 * i ≤ c := by
  have hi' : ((r - 1 : ℕ) : ℝ) * c ≤ i := by exact_mod_cast hi
  rw [Nat.cast_sub hr, Nat.cast_one] at hi'
  linarith

lemma pnorm_C_mul_X_pow (c : ℂ) (i : ℕ) : pnorm (C c * X ^ i) = ‖c‖ := by
  rw [pnorm_C_mul, pnorm_X_pow, mul_one]

lemma pnorm_one : pnorm (1 : ℂ[X]) = 1 := by rw [← C_1, pnorm_C, norm_one]

/-- **`|fₗ| ≤ Aₘ`** for `l ≤ (m - 1)aₘ`. -/
lemma pnorm_fPoly_le (h : GrowthHyp d) {m l : ℕ} (hm : 2 ≤ m) (hl : l ≤ (m - 1) * seqA d m) :
    pnorm (fPoly d l) ≤ capA d m := by
  have hP := h.toPartitionHyp
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · rw [fPoly_zero, pnorm_one]; exact one_le_capA m
  have hB := block_mem hP hl0
  rcases hbl : block d l with ⟨n, r, k⟩
  rw [hbl] at hB
  obtain ⟨hlo, hhi, hX⟩ := Block.mem_level hP hB
  have hr1 := hB.1
  have hrn := hB.2.1
  dsimp only at hlo hhi hX hr1 hrn
  have hvm : (m - 1) * seqA d m ≤ seqV d m := by
    unfold seqV; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hnm : n ≤ m := by
    by_contra hmn
    have := seqV_mono hP (show m ≤ n - 1 by omega)
    omega
  -- At level `m` itself only `J` and `I` blocks reach below `(m - 1)aₘ`.
  have hLK : k = .L ∨ k = .K → n < m := fun hk ↦ by
    by_contra hnm'
    obtain rfl : n = m := by omega
    rcases hX.1 hl with h' | h' <;> rcases hk with hk | hk <;> rw [hk] at h' <;> simp at h'
  have ha : 0 < seqA d n := hP.one_le_a n
  cases k with
  | J =>
    rw [fPoly_of_J hP hB rfl, pnorm_C_mul_X_pow, Complex.norm_real,
      Real.norm_of_nonneg (weight_pos _ _ _).le]
    have hJ := hB.2.2.1
    dsimp only at hJ
    calc weight (seqA d n) r l ≤ alpha ^ (Real.sqrt (seqA d n) / 2) :=
          weight_le_half ha (weight_numer_le hr1 (by omega))
      _ ≤ capA d n := alpha_rpow_le (by linarith [Real.sqrt_nonneg (seqA d n : ℝ)])
      _ ≤ capA d m := capA_mono h (by omega) hnm
  | L =>
    have hnm' := hLK (Or.inl rfl)
    rw [fPoly_of_L hP hB rfl, pnorm_C_mul_X_pow, Complex.norm_real,
      Real.norm_of_nonneg (weight_pos _ _ _).le]
    have hL := hB.2.2.1
    dsimp only at hL
    have hb : 0 < seqB d n := lt_of_le_of_lt (Nat.zero_le _) (hP.a_lt_b n)
    have hle : (r - 1) * seqB d n ≤ l := by omega
    calc weight (seqB d n) r l ≤ alpha ^ (Real.sqrt (seqB d n) / 2) :=
          weight_le_half hb (weight_numer_le hr1 hle)
      _ ≤ capB d n := alpha_rpow_le (by linarith [Real.sqrt_nonneg (seqB d n : ℝ)])
      _ ≤ capA d (n + 1) := capB_le_capA_succ h (by omega)
      _ ≤ capA d m := capA_mono h (by omega) (by omega)
  | I =>
    rw [fPoly_of_I hP hB rfl, pnorm_C_mul, Complex.norm_natCast]
    have hX2 : pnorm (X ^ l - X ^ (l - seqA d n) : ℂ[X]) ≤ 2 := by
      refine (pnorm_sub_le _ _).trans ?_
      rw [pnorm_X_pow, pnorm_X_pow]; norm_num
    have hmono : (seqA d (n - r) : ℝ) ≤ seqA d n := by
      exact_mod_cast seqA_mono h (by omega) (by omega)
    have ha0 : (0 : ℝ) ≤ seqA d (n - r) := Nat.cast_nonneg _
    calc (seqA d (n - r) : ℝ) * pnorm (X ^ l - X ^ (l - seqA d n) : ℂ[X])
        ≤ seqA d n * 2 := mul_le_mul hmono hX2 (pnorm_nonneg _) (Nat.cast_nonneg _)
      _ ≤ capA d n := by linarith [two_mul_le_capA h (n := n) (by omega)]
      _ ≤ capA d m := capA_mono h (by omega) hnm
  | K =>
    have hnm' := hLK (Or.inr rfl)
    rw [fPoly_of_K hP hB rfl]
    calc pnorm (X ^ l - C (seqB d n : ℂ) * X ^ (l - seqB d n))
        ≤ 1 + seqB d n := by
          refine (pnorm_sub_le _ _).trans ?_
          rw [pnorm_X_pow, pnorm_C_mul_X_pow, Complex.norm_natCast]
      _ ≤ capA d (n + 1) := one_add_le_capA_succ h (by omega)
      _ ≤ capA d m := capA_mono h (by omega) (by omega)

lemma pnorm_qPolyBasis_le_capA (h : GrowthHyp d) {m : ℕ} (hm : 2 ≤ m) (l : ℕ) :
    pnorm (qPolyBasis d m l) ≤ capA d m := by
  have hA := two_mul_le_capA h (n := m) (by omega)
  have ha : (0 : ℝ) ≤ seqA d m := Nat.cast_nonneg _
  rcases le_or_gt l ((m - 1) * seqA d m) with hl | hl
  · rw [qPolyBasis_of_le hl]; exact pnorm_fPoly_le h hm hl
  · rw [qPolyBasis_of_gt h.toPartitionHyp hl]
    split_ifs
    · rw [smul_eq_C_mul, pnorm_C_mul_X_pow, norm_neg, Complex.norm_natCast]; linarith
    · rw [pnorm_zero]; linarith

/-- **`|Qₘ e| ≤ Aₘ`** for `‖e‖ ≤ 1`. -/
lemma pnorm_qPoly_le_capA (h : GrowthHyp d) {m : ℕ} (hm : 2 ≤ m) {e : L1} (he : ‖e‖ ≤ 1) :
    pnorm (qPoly h.toPartitionHyp m e) ≤ capA d m := by
  refine (pnorm_qPoly_le h.toPartitionHyp hm (pnorm_qPolyBasis_le_capA h hm) e).trans ?_
  have := one_le_capA (d := d) m
  nlinarith [norm_nonneg e]

/- ### The norm estimates of (S2), (S3), (S5) -/

/-- (S2): `‖xʲ‖ ≤ 1` on `((m - 1)aₘ + bₘ, 2(m - 1)aₘ + bₘ] ⊂ Lₘ,₂`. -/
lemma nrm_xPow_le_one_of_L2 (h : GrowthHyp d) {m j : ℕ} (hm : 3 ≤ m)
    (hj1 : (m - 1) * seqA d m + seqB d m < j) (hj2 : j ≤ 2 * ((m - 1) * seqA d m) + seqB d m) :
    nrm (xPow d j) ≤ 1 := by
  have hP := h.toPartitionHyp
  have hab := h.a_small m (by omega)
  have h8 : 8 * m * seqA d m = 8 * (m * seqA d m) := by ring
  have hm1 : m * seqA d m = (m - 1) * seqA d m + seqA d m := by
    rw [show m = m - 1 + 1 by omega, add_one_mul, Nat.add_sub_cancel]
  have hB : (⟨m, 2, .L⟩ : Block).Mem d j := by
    refine ⟨by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; omega
  rw [nrm_xPow_of_L hP hB rfl]
  dsimp only
  refine inv_le_one_of_one_le₀ (one_le_alpha_rpow ?_)
  have hb : (0 : ℝ) < seqB d m := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hab
  refine div_nonneg ?_ (Real.sqrt_nonneg _)
  have : (2 * j : ℝ) ≤ 3 * seqB d m := by exact_mod_cast (by omega : 2 * j ≤ 3 * seqB d m)
  push_cast
  linarith

/-- (S2): `‖F - Pₐ F‖ ≤ |F|` when every `‖xʲ‖ ≤ 1` for `a < j ≤ deg F`. -/
lemma nrm_toCoord_sub_ptrunc_le {F : ℂ[X]} {a N : ℕ} (hF : F.natDegree ≤ N)
    (hx : ∀ j, a < j → j ≤ N → nrm (xPow d j) ≤ 1) :
    nrm (toCoord d (F - ptrunc a F)) ≤ pnorm F := by
  have hdeg : (F - ptrunc a F).natDegree ≤ N := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    have hj' : N < j := by exact_mod_cast hj
    rw [coeff_sub, coeff_ptrunc, coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  rw [toCoord_apply, Polynomial.sum_over_range' _ (f := fun i c ↦ c • xPow d i)
    (fun n ↦ zero_smul ℂ _) (N + 1) (by omega)]
  refine (nrm_sum_le _ _).trans ?_
  rw [pnorm_eq_sum_of_subset F (support_subset_range hF)]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  rw [nrm_smul, coeff_sub, coeff_ptrunc]
  split_ifs with hja
  · simp
  · rw [sub_zero]
    exact (mul_le_mul_of_nonneg_left (hx j (by omega)
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (norm_nonneg _)).trans_eq (mul_one _)

/-- (S3): for `aₘ ≤ j ≤ (m - 1)aₘ`, `j + bₘ ∈ Kₘ,₁`, so `bₘ⁻¹ x^{j+bₘ} - xʲ = bₘ⁻¹ f_{j+bₘ}`. -/
lemma toCoord_K_diff (h : PartitionHyp d) {m j : ℕ} (hm : 2 ≤ m) (hj1 : seqA d m ≤ j)
    (hj2 : j ≤ (m - 1) * seqA d m) :
    toCoord d (C (seqB d m : ℂ)⁻¹ * X ^ (j + seqB d m) - X ^ j) =
      (seqB d m : ℂ)⁻¹ • single (j + seqB d m) 1 := by
  have hB : (⟨m, 1, .K⟩ : Block).Mem d (j + seqB d m) := by
    refine ⟨by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩
    · dsimp only; omega
    · dsimp only; omega
  have hb : (seqB d m : ℂ) ≠ 0 := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) (h.a_lt_b m)).ne'
  rw [single_eq_of_K h hB rfl]
  dsimp only
  rw [Nat.add_sub_cancel, map_sub, toCoord_C_mul, toCoord_X_pow, toCoord_X_pow, smul_sub,
    smul_smul, inv_mul_cancel₀ hb, one_smul]

/-- (S3): `‖(bₘ⁻¹ x^{bₘ} - 1) w‖ ≤ bₘ⁻¹ |w|` for `w` with powers in `[aₘ, (m - 1)aₘ]`. -/
lemma nrm_toCoord_K_mul_le (h : PartitionHyp d) {m : ℕ} (hm : 2 ≤ m) {w : ℂ[X]}
    (hw0 : ∀ j < seqA d m, w.coeff j = 0) (hwdeg : w.natDegree ≤ (m - 1) * seqA d m) :
    nrm (toCoord d ((C (seqB d m : ℂ)⁻¹ * X ^ seqB d m - 1) * w)) ≤
      (seqB d m : ℝ)⁻¹ * pnorm w := by
  set c := (m - 1) * seqA d m
  have hterm : ∀ j ∈ Finset.range (c + 1),
      nrm (toCoord d ((C (seqB d m : ℂ)⁻¹ * X ^ seqB d m - 1) * monomial j (w.coeff j))) ≤
        (seqB d m : ℝ)⁻¹ * ‖w.coeff j‖ := fun j hj ↦ by
    rw [Finset.mem_range] at hj
    by_cases hja : j < seqA d m
    · rw [hw0 j hja, monomial_zero_right, mul_zero, map_zero, nrm_zero, norm_zero, mul_zero]
    · rw [show (C (seqB d m : ℂ)⁻¹ * X ^ seqB d m - 1) * monomial j (w.coeff j) =
          C (w.coeff j) * (C (seqB d m : ℂ)⁻¹ * X ^ (j + seqB d m) - X ^ j) by
        rw [← C_mul_X_pow_eq_monomial, pow_add]; ring,
        toCoord_C_mul, toCoord_K_diff h hm (by omega) (by omega), nrm_smul, nrm_smul,
        nrm_single, norm_one, mul_one, norm_inv, Complex.norm_natCast, mul_comm]
  rw [as_sum_range' w (c + 1) (by omega), Finset.mul_sum, map_sum]
  refine (nrm_sum_le _ _).trans ?_
  rw [← as_sum_range' w (c + 1) (by omega), pnorm_eq_sum_of_subset w (support_subset_range hwdeg),
    Finset.mul_sum]
  exact Finset.sum_le_sum hterm

/-- (S5) by Lemma 1 (b): `‖x^{(m-k+1)aₘ} - x⁰‖ ≤ 2 / aₖ₋₁`. -/
lemma nrm_xPow_sub_zero_le (h : GrowthHyp d) {m k : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) :
    nrm (xPow d ((m - k + 1) * seqA d m) - xPow d 0) ≤ 2 / seqA d (k - 1) := by
  have hB : (⟨m, m - k + 1, .I⟩ : Block).Mem d ((m - k + 1) * seqA d m) := by
    refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_⟩
    dsimp only; omega
  have := nrm_xPow_sub_of_I h hB
  rwa [Nat.sub_self, show m - (m - k + 1) = k - 1 by omega] at this

end ReadL1
