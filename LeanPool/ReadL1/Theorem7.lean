/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Theorem7Prep
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Abel

/-!
# Śliwa's Theorem 7: no nontrivial closed invariant subspace

Under the growth facts (`ReadL1.Theorem7Hyp`: those of `ReadL1.GrowthHyp` and Śliwa's
`α aₘ Aₘ Rₘ < bₘ`, p. 640), Read's operator on ℓ¹ has no nontrivial closed invariant subspace
(`ReadL1.theorem7`).

The heart is `ReadL1.exists_aeval_near_delta`: for `0 < ‖e‖ ≤ 1` and `δ > 0` some polynomial
`f` has `‖f(T) e - x⁰‖ < δ`. Śliwa's proof: take `k > 2` with `6aₖ₋₁⁻¹ < δ`, `m` from Lemma 5,
`y = Qₘ e`, `q` from Lemma 6 (with `ε = (aₘAₘ)⁻¹`, `M = Aₘ`) and `f = bₘ⁻¹ x^{aₘ+bₘ} q`; then

```
f(T)e - x⁰ = (f(T)e - z) + (z - P_a z) + (P_a z - P_c t)
    + (P_c t - x^{(m-k+1)aₘ}) + (x^{(m-k+1)aₘ} - x⁰)
```

with `z = f y`, `t = x^{aₘ} q y`, `a = (m - 1)aₘ + bₘ`, `c = (m - 1)aₘ`, and the five terms are
below `aₘ⁻¹`, `aₘ⁻¹`, `aₘ⁻¹`, `aₘ⁻¹`, `2aₖ₋₁⁻¹` ((S1)–(S5)).

The vector `x⁰ = δ₀` has dense orbit span (its orbit is `x⁰, x¹, x², …`, spanning the finite
sequences), so `ReadL1.isEmpty_closedInvariantSubspace_of_cyclic` finishes.
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

/-- The growth facts for Theorem 7: those of `GrowthHyp`, and `α aₘ Aₘ Rₘ < bₘ` with
`Rₘ = (aₘAₘ)^{(2(m-2)aₘ)!}` (Śliwa p. 640). -/
structure Theorem7Hyp (d : ℕ → ℕ) : Prop extends GrowthHyp d where
  r_bound : ∀ m, 3 ≤ m →
    alpha * seqA d m * capA d m * (seqA d m * capA d m) ^ (2 * ((m - 2) * seqA d m)).factorial <
      seqB d m

lemma toL1_toCoord_one : toL1 (toCoord d (1 : ℂ[X])) = δ 0 := by
  rw [← pow_zero X, toCoord_X_pow]
  simp [xPow, toL1_single]

/-- The coordinates of a polynomial `p` are `p(T) x⁰`. -/
lemma toL1_toCoord_eq_aeval (h : GrowthHyp d) (p : ℂ[X]) :
    toL1 (toCoord d p) = aeval (readOp h) p (δ 0) := by
  rw [← toL1_toCoord_one, aeval_readOp_toL1_toCoord, mul_one]

/-- **The vector `x⁰` has dense orbit span.** -/
lemma dense_orbitSpan_delta (h : GrowthHyp d) :
    (orbitSpan (readOp h) (δ 0)).topologicalClosure = ⊤ := by
  have hP := h.toPartitionHyp
  -- Every finite sequence is in the orbit span.
  have hfin : ∀ g : ℕ →₀ ℂ, toL1 g ∈ orbitSpan (readOp h) (δ 0) := fun g ↦ by
    rw [← toCoord_fromCoord hP g, toL1_toCoord_eq_aeval h]
    exact aeval_mem_orbitSpan _ _ _
  refine eq_top_iff.2 fun x _ ↦ ?_
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.one_ne_top x).tendsto_sum_nat
    (Filter.Eventually.of_forall fun N ↦ ?_)
  have hsingle : ∀ i, lp.single 1 i (x i) = toL1 (single i (x i)) := fun i ↦ by
    refine lp.ext (funext fun k ↦ ?_)
    rw [toL1_apply, lp.single_apply, Pi.single_apply, Finsupp.single_apply]
    by_cases hik : k = i
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  simp only [hsingle, ← map_sum]
  exact hfin _

section

variable (h : Theorem7Hyp d)
include h

lemma two_lt_capA {m : ℕ} (hm : 1 ≤ m) : 2 < capA d m := by
  have h1 := two_mul_le_capA h.toGrowthHyp hm
  have h2 : (4096 : ℝ) ≤ seqA d m := by exact_mod_cast h.a_big m hm
  linarith

lemma one_lt_seqA {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ) < seqA d m := by
  have h2 : (4096 : ℝ) ≤ seqA d m := by exact_mod_cast h.a_big m hm
  linarith

/-- **The approximation**: for `0 < ‖e‖ ≤ 1` and `δ > 0`, some `f(T) e` is within `δ` of `x⁰`. -/
theorem exists_aeval_near_delta {e : L1} (he0 : e ≠ 0) (he1 : ‖e‖ ≤ 1) {δ' : ℝ} (hδ : 0 < δ') :
    ∃ f : ℂ[X], ‖aeval (readOp h.toGrowthHyp) f e - δ 0‖ < δ' := by
  have hG := h.toGrowthHyp
  have hP := hG.toPartitionHyp
  -- Choose `k > 2` with `6 / aₖ₋₁ < δ`.
  obtain ⟨N, hN⟩ := exists_nat_gt (6 / δ')
  set k := N + 3 with hk
  have hk2 : 2 < k := by omega
  have hak : 6 / (seqA d (k - 1) : ℝ) < δ' := by
    have h1 : (N : ℝ) + 2 ≤ seqA d (k - 1) := by
      exact_mod_cast (show N + 2 ≤ k - 1 by omega).trans (le_seqA hG (by omega))
    have h2 : 0 < (seqA d (k - 1) : ℝ) := seqA_pos hG _
    rw [div_lt_iff₀ h2]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  -- Lemma 5 gives `m`.
  obtain ⟨m, hkm, h5⟩ := lemma5 hG he0 hk2
  have hm3 : 3 ≤ m := by omega
  set a := seqA d m with ha_def
  set b := seqB d m with hb_def
  set A := capA d m with hA_def
  set n := (m - 2) * a with hn_def
  set m' := (m - k) * a with hm'_def
  have ha1 : (1 : ℝ) < a := one_lt_seqA h (by omega)
  have ha0 : (0 : ℝ) < a := by linarith
  have hA2 : 2 < A := two_lt_capA h (by omega)
  have hA0 : (0 : ℝ) < A := by linarith
  have hb0 : (0 : ℝ) < b := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) (hP.a_lt_b m)
  have haN : 1 ≤ a := hP.one_le_a m
  -- `y = Qₘ e`, `|y| ≤ Aₘ`.
  set y := qPoly hP m e with hy_def
  have hy : pnorm y ≤ A := pnorm_qPoly_le_capA hG (by omega) he1
  -- Lemma 6 with `ε = (aₘAₘ)⁻¹`, `M = Aₘ`.
  have hn1 : 1 ≤ n := by
    rw [hn_def]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hm'n : m' ≤ n := Nat.mul_le_mul_right _ (by omega)
  have haA : 2 < a * A := by nlinarith
  obtain ⟨q, hqd, hqn, hqe⟩ := lemma6 hn1 hm'n (ε := (a * A)⁻¹) (M := A) (by positivity)
    (by rw [inv_lt_comm₀ (by positivity) (by norm_num)]; norm_num; linarith)
    hA2 (by rw [inv_inv]; nlinarith) hy
    (by rw [show A * ((a : ℝ) * A)⁻¹ = (a : ℝ)⁻¹ by field_simp]; exact h5)
  rw [inv_inv] at hqn
  set R := (a * A) ^ (2 * n).factorial with hR_def
  have hR0 : 0 ≤ R := by positivity
  -- The growth fact `α aₘ Aₘ Rₘ < bₘ` and its two uses.
  have hr := h.r_bound m hm3
  rw [← ha_def, ← hA_def, ← hb_def, ← hn_def] at hr
  have hα : (1 : ℝ) ≤ alpha := one_le_alpha
  have hN1 : alpha * (b : ℝ)⁻¹ * R < (a : ℝ)⁻¹ := by
    rw [show alpha * (b : ℝ)⁻¹ * R = alpha * R / b by ring, div_lt_iff₀ hb0, inv_mul_eq_div,
      lt_div_iff₀ ha0]
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ A by linarith)
      (by positivity : (0 : ℝ) ≤ alpha * a * R)]
  have hN2 : (b : ℝ)⁻¹ * R * A < (a : ℝ)⁻¹ := by
    rw [show (b : ℝ)⁻¹ * R * A = R * A / b by ring, div_lt_iff₀ hb0, inv_mul_eq_div,
      lt_div_iff₀ ha0]
    nlinarith [mul_le_mul_of_nonneg_right hα (by positivity : (0 : ℝ) ≤ a * A * R)]
  -- `f = bₘ⁻¹ x^{aₘ+bₘ} q`.
  set f := C (b : ℂ)⁻¹ * (X ^ (a + b) * q) with hf_def
  have hfn : pnorm f = (b : ℝ)⁻¹ * pnorm q := by
    rw [hf_def, pnorm_C_mul, pnorm_X_pow_mul, norm_inv, Complex.norm_natCast]
  have hfK : ∀ s ∈ f.support, InK1 d m s := fun s hs ↦ by
    rw [Polynomial.mem_support_iff, hf_def, coeff_C_mul, coeff_X_pow_mul'] at hs
    split_ifs at hs with hle
    · have hq0 : q.coeff (s - (a + b)) ≠ 0 := right_ne_zero_of_mul hs
      have := le_natDegree_of_ne_zero hq0
      change a + b ≤ s ∧ s ≤ (m - 1) * a + b
      refine ⟨hle, ?_⟩
      have hna : n + a = (m - 1) * a := by
        rw [hn_def, ← add_one_mul, show m - 2 + 1 = m - 1 by omega]
      omega
    · simp at hs
  have hfdeg : f.natDegree ≤ a + b + n :=
    (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans
      (add_le_add (natDegree_X_pow_le _) hqd))
  have hydeg : y.natDegree ≤ (m - 1) * a := natDegree_qPoly_le hP m e
  -- The pieces, as vectors of ℓ¹.
  set c := (m - 1) * a with hc_def
  set F := f * y with hF_def
  set t := X ^ a * (q * y) with ht_def
  have hFt : F = C (b : ℂ)⁻¹ * (X ^ b * t) := by rw [hF_def, hf_def, ht_def, pow_add]; ring
  have hz : aeval (readOp hG) f (readQ hG (by omega : 2 ≤ m) e) = toL1 (toCoord d F) := by
    rw [← toL1_toCoord_qPoly hG (by omega : 2 ≤ m), aeval_readOp_toL1_toCoord]
  -- (S1)
  have hS1 : ‖aeval (readOp hG) f e - toL1 (toCoord d F)‖ < (a : ℝ)⁻¹ := by
    rw [← hz]
    refine (norm_aeval_sub_le hG (by omega) f hfK e).trans_lt ?_
    calc alpha * pnorm f * ‖e‖ ≤ alpha * ((b : ℝ)⁻¹ * R) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (by rw [hfn]; exact mul_le_mul_of_nonneg_left hqn (by positivity)) alpha_pos.le)
            he1 (norm_nonneg _) (by have := alpha_pos; positivity)
      _ = alpha * (b : ℝ)⁻¹ * R := by ring
      _ < (a : ℝ)⁻¹ := hN1
  -- (S2)
  have hFdeg : F.natDegree ≤ 2 * c + b := by
    rw [hF_def]
    have := (natDegree_mul_le (p := f) (q := y)).trans (add_le_add hfdeg hydeg)
    have hna : n + a = c := by rw [hn_def, hc_def, ← add_one_mul, show m - 2 + 1 = m - 1 by omega]
    omega
  have hF : pnorm F ≤ (b : ℝ)⁻¹ * R * A := by
    refine (pnorm_mul_le f y).trans ?_
    rw [hfn]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hqn (by positivity)) hy (pnorm_nonneg _)
      (by positivity)
  have hS2 : ‖toL1 (toCoord d F) - toL1 (toCoord d (ptrunc (c + b) F))‖ < (a : ℝ)⁻¹ := by
    rw [← map_sub, ← map_sub, norm_toL1]
    refine (nrm_toCoord_sub_ptrunc_le hFdeg fun j hj1 hj2 ↦ ?_).trans_lt (hF.trans_lt hN2)
    exact nrm_xPow_le_one_of_L2 hG hm3 hj1 hj2
  -- (S3)
  have hqy : pnorm (q * y) ≤ R * A :=
    (pnorm_mul_le q y).trans (mul_le_mul hqn hy (pnorm_nonneg _) hR0)
  have hS3 : ‖toL1 (toCoord d (ptrunc (c + b) F)) - toL1 (toCoord d (ptrunc c t))‖ <
      (a : ℝ)⁻¹ := by
    rw [← map_sub, ← map_sub, norm_toL1]
    have hPF : ptrunc (c + b) F - ptrunc c t = (C (b : ℂ)⁻¹ * X ^ b - 1) * ptrunc c t := by
      rw [hFt, ptrunc_C_mul, ← X_pow_mul_ptrunc]; ring
    rw [hPF]
    refine (nrm_toCoord_K_mul_le hP (by omega) (fun j hj ↦ ?_) (natDegree_ptrunc_le c t)).trans_lt
      ?_
    · rw [coeff_ptrunc, ht_def, coeff_X_pow_mul', ite_eq_right (show ¬ a ≤ j by omega)]
      simp
    · calc (b : ℝ)⁻¹ * pnorm (ptrunc c t) ≤ (b : ℝ)⁻¹ * (R * A) := by
            refine mul_le_mul_of_nonneg_left ((pnorm_ptrunc_le c t).trans ?_) (by positivity)
            rw [ht_def, pnorm_X_pow_mul]; exact hqy
        _ = (b : ℝ)⁻¹ * R * A := by ring
        _ < (a : ℝ)⁻¹ := hN2
  -- (S4)
  have hS4 : ‖toL1 (toCoord d (ptrunc c t)) - toL1 (toCoord d (X ^ ((m - k + 1) * a)))‖ <
      (a : ℝ)⁻¹ := by
    rw [← map_sub, ← map_sub, norm_toL1]
    have hcn : c = n + a := by
      rw [hn_def, hc_def, ← add_one_mul, show m - 2 + 1 = m - 1 by omega]
    have heq : ptrunc c t - X ^ ((m - k + 1) * a) = X ^ a * (ptrunc n (q * y) - X ^ m') := by
      rw [ht_def, hcn, ← X_pow_mul_ptrunc, hm'_def, mul_sub, ← pow_add,
        show a + (m - k) * a = (m - k + 1) * a by ring]
    have hdeg : (ptrunc c t - X ^ ((m - k + 1) * a)).natDegree ≤ c :=
      (natDegree_sub_le _ _).trans (max_le (natDegree_ptrunc_le c t)
        ((natDegree_X_pow_le _).trans (Nat.mul_le_mul_right _ (by omega))))
    refine (nrm_toCoord_le hdeg (nrm_xPow_le_cap hG m (by omega)).1).trans_lt ?_
    rw [heq, pnorm_X_pow_mul]
    calc A * pnorm (ptrunc n (q * y) - X ^ m') < A * (a * A)⁻¹ := mul_lt_mul_of_pos_left hqe hA0
      _ = (a : ℝ)⁻¹ := by field_simp
  -- (S5)
  have hS5 : ‖toL1 (toCoord d (X ^ ((m - k + 1) * a))) - δ 0‖ ≤ 2 / seqA d (k - 1) := by
    rw [← toL1_toCoord_one, ← map_sub, norm_toL1, toCoord_X_pow, ← pow_zero X, toCoord_X_pow]
    exact nrm_xPow_sub_zero_le hG (by omega) (by omega)
  -- Assemble.
  have hak1 : (seqA d (k - 1) : ℝ) ≤ a := by exact_mod_cast seqA_mono hG (by omega) (by omega)
  have hinv : (a : ℝ)⁻¹ ≤ (seqA d (k - 1) : ℝ)⁻¹ := inv_anti₀ (seqA_pos hG _) hak1
  refine ⟨f, ?_⟩
  have hsplit : aeval (readOp hG) f e - δ 0 =
      (aeval (readOp hG) f e - toL1 (toCoord d F)) +
      (toL1 (toCoord d F) - toL1 (toCoord d (ptrunc (c + b) F))) +
      (toL1 (toCoord d (ptrunc (c + b) F)) - toL1 (toCoord d (ptrunc c t))) +
      (toL1 (toCoord d (ptrunc c t)) - toL1 (toCoord d (X ^ ((m - k + 1) * a)))) +
      (toL1 (toCoord d (X ^ ((m - k + 1) * a))) - δ 0) := by abel
  rw [hsplit]
  set u1 := aeval (readOp hG) f e - toL1 (toCoord d F)
  set u2 := toL1 (toCoord d F) - toL1 (toCoord d (ptrunc (c + b) F))
  set u3 := toL1 (toCoord d (ptrunc (c + b) F)) - toL1 (toCoord d (ptrunc c t))
  set u4 := toL1 (toCoord d (ptrunc c t)) - toL1 (toCoord d (X ^ ((m - k + 1) * a)))
  set u5 := toL1 (toCoord d (X ^ ((m - k + 1) * a))) - δ 0
  have t1 := norm_add_le (u1 + u2 + u3 + u4) u5
  have t2 := norm_add_le (u1 + u2 + u3) u4
  have t3 := norm_add_le (u1 + u2) u3
  have t4 := norm_add_le u1 u2
  have h6 : 6 / (seqA d (k - 1) : ℝ) = 4 * (seqA d (k - 1) : ℝ)⁻¹ + 2 / seqA d (k - 1) := by ring
  linarith

end

/-- **Śliwa's Theorem 7.** Read's operator has no nontrivial closed invariant subspace. -/
theorem theorem7 (h : Theorem7Hyp d) :
    IsEmpty (InvariantSubspaceProblem.ClosedInvariantSubspace (readOp h.toGrowthHyp)) := by
  refine isEmpty_closedInvariantSubspace_of_cyclic (readOp h.toGrowthHyp) (δ 0)
    (dense_orbitSpan_delta h.toGrowthHyp) fun x hx ↦ ?_
  -- Scale `x` to norm one; its orbit span does not change.
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set e := ((‖x‖⁻¹ : ℝ) : ℂ) • x with he
  have he1 : ‖e‖ = 1 := by
    rw [he, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ hxn.ne']
  have he0 : e ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at he1; exact zero_ne_one he1
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨f, hf⟩ := exists_aeval_near_delta h he0 he1.le hε
  refine ⟨aeval (readOp h.toGrowthHyp) f e, ?_, ?_⟩
  · rw [he, map_smul]
    exact Submodule.smul_mem _ _ (aeval_mem_orbitSpan _ f x)
  · rwa [dist_eq_norm, norm_sub_rev]

end ReadL1
