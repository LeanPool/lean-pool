/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Algorithms.Gd
public import LeanPool.LongTails.Proofs.Execution
public import LeanPool.LongTails.Setups.SmoothAndConvex
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.OracleTemplate.Gradient

open LongTails.Setups.SmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma execute_gd (oracle : E → E) (L : ℝ) (x0 : E) (K : ℕ) :
    execute { answer := fun _ query _ => oracle query.2 } (gd (L, x0)) (fun _ => K) =
      (fun x => x - (1 / L) • oracle x)^[K] x0 := by
  exact execute_iterate oracle (gd (L, x0)) K ()

lemma smooth_upper_bound {f : E → ℝ} {oracle : E → E} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (oracle x) x)
    (hlip : ∀ x y, ‖oracle x - oracle y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪oracle x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d)
  let F' := fun t : ℝ => ⟪oracle (x + t • d), d⟫
  have hF : ∀ t, HasDerivAt F (F' t) t := by
    intro t
    have h := (hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add x)
    simp only [id_eq, one_smul, toDual_apply_apply] at h
    exact h
  let B := fun t : ℝ => f x + t * ⟪oracle x, d⟫ + t ^ 2 * (L / 2 * ‖d‖ ^ 2)
  have hB : ∀ t, HasDerivAt B (⟪oracle x, d⟫ + L * ‖d‖ ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).mul_const ⟪oracle x, d⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * ‖d‖ ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1, F' t ≤ ⟪oracle x, d⟫ + L * ‖d‖ ^ 2 * t := by
    intro t ht
    have h := (real_inner_le_norm (oracle (x + t • d) - oracle x) d).trans
      (mul_le_mul_of_nonneg_right (hlip (x + t • d) x) (norm_nonneg d))
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, inner_sub_left] at h
    dsimp [F']
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hderiv
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, d] using h

lemma convex_support {f : E → ℝ} {oracle : E → E}
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (oracle x) x)
    (x y : E) : ⟪oracle x, y - x⟫ ≤ f y - f x := by
  have hconv := hc.comp_affineMap (AffineMap.lineMap x y)
  have hd : HasFDerivAt f ((toDual ℝ E) (oracle x))
      ((AffineMap.lineMap x y) (0 : ℝ)) := by
    simpa using (hg x).hasFDerivAt
  have hline : HasDerivAt (f ∘ AffineMap.lineMap x y) ⟪oracle x, y - x⟫ (0 : ℝ) := by
    simpa using hd.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
  have h := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simp) (by simp) (by norm_num) hline
  simpa [slope_def_field] using h

lemma descent {f : E → ℝ} {oracle : E → E} {L : ℝ}
    (hL : 0 < L) (hg : ∀ x, HasGradientAt f (oracle x) x)
    (hlip : ∀ x y, ‖oracle x - oracle y‖ ≤ L * ‖x - y‖) (x : E) :
    f (x - (1 / L) • oracle x) ≤ f x - ‖oracle x‖ ^ 2 / (2 * L) := by
  have h := smooth_upper_bound hg hlip x (x - (1 / L) • oracle x)
  have he : x - (1 / L) • oracle x - x = -(1 / L) • oracle x := by module
  rw [he] at h
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.mpr hL)] at h
  convert h using 1
  field_simp
  ring

private lemma convex_step {f : E → ℝ} {oracle : E → E} {L : ℝ}
    (hL : 0 < L) (hc : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (oracle x) x)
    (hlip : ∀ x y, ‖oracle x - oracle y‖ ≤ L * ‖x - y‖) (x u : E) :
    f (x - (1 / L) • oracle x) - f u ≤
      L / 2 * (‖x - u‖ ^ 2 - ‖x - (1 / L) • oracle x - u‖ ^ 2) := by
  have hd := descent hL hg hlip x
  have hs := convex_support hc hg x u
  have he : x - (1 / L) • oracle x - u = (x - u) - (1 / L) • oracle x := by module
  rw [he, norm_sub_sq_real (x - u) ((1 / L) • oracle x)]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
  have hi : ⟪x - u, oracle x⟫ = -⟪oracle x, u - x⟫ := by
    rw [real_inner_comm, ← inner_neg_right]
    congr 1
    module
  rw [hi]
  have hne : L ≠ 0 := ne_of_gt hL
  have heq : L / 2 *
      (‖x - u‖ ^ 2 - (‖x - u‖ ^ 2 - 2 * ((1 / L) * -⟪oracle x, u - x⟫) +
        (1 / L) ^ 2 * ‖oracle x‖ ^ 2)) =
      -⟪oracle x, u - x⟫ - ‖oracle x‖ ^ 2 / (2 * L) := by field_simp; ring
  rw [heq]
  linarith

lemma gd_accuracy (f : E → ℝ) (oracle : E → E)
    (L R ε : ℝ) (x0 xstar : E)
    (hL : 0 < L) (hR : 0 ≤ R) (hε : 0 < ε)
    (hc : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (oracle x) x)
    (hlip : ∀ x y, ‖oracle x - oracle y‖ ≤ L * ‖x - y‖)
    (hdist : ‖x0 - xstar‖ ≤ R)
    (K : ℕ)
    (hbudget : max 1 ⌈L * R ^ 2 / (2 * ε)⌉₊ ≤ K) :
    f (execute { answer := fun _ query _ => oracle query.2 } (gd (L, x0)) (fun _ => K)) -
        f xstar ≤ ε := by
  let T := fun x => x - (1 / L) • oracle x
  let x := fun k => T^[k] x0
  have hx : ∀ k, x (k + 1) = x k - (1 / L) • oracle (x k) := by
    intro k
    exact Function.iterate_succ_apply' T k x0
  have hsum : ∀ n, (∑ k ∈ Finset.range n, (f (x (k + 1)) - f xstar)) ≤
      L / 2 * (‖x0 - xstar‖ ^ 2 - ‖x n - xstar‖ ^ 2) := by
    intro n
    induction n with
    | zero => simp [x]
    | succ n ih =>
      have hs := convex_step hL hc hg hlip (x n) xstar
      rw [← hx n] at hs
      rw [Finset.sum_range_succ]
      linarith
  have hmono : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    have hd := descent hL hg hlip (x k)
    rw [← hx k] at hd
    have hn : 0 ≤ ‖oracle (x k)‖ ^ 2 / (2 * L) := by positivity
    linarith
  rw [execute_gd]
  change f (x K) - f xstar ≤ ε
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hbudget)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hle := Finset.sum_le_sum (s := Finset.range K)
    (fun k hk => sub_le_sub_right
      (hmono (by have := Finset.mem_range.mp hk; omega : k + 1 ≤ K)) (f xstar))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  have hrate : f (x K) - f xstar ≤ L * ‖x0 - xstar‖ ^ 2 / (2 * (K : ℝ)) := by
    apply (le_div_iff₀ (show 0 < 2 * (K : ℝ) by positivity)).mpr
    have hs := hsum K
    nlinarith [sq_nonneg ‖x K - xstar‖]
  have hceil : L * R ^ 2 / (2 * ε) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right 1 _).trans hbudget))
  have hR2 : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := by
    nlinarith [norm_nonneg (x0 - xstar)]
  have hbound : L * ‖x0 - xstar‖ ^ 2 / (2 * (K : ℝ)) ≤ ε := by
    apply (div_le_iff₀ (show 0 < 2 * (K : ℝ) by positivity)).mpr
    have hh := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hceil
    have hnum := mul_le_mul_of_nonneg_left hR2 hL.le
    nlinarith
  exact hrate.trans hbound

end LongTails.OracleTemplate.Gradient
