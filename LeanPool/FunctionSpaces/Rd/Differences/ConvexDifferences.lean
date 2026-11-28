/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Differences.DomainModuli
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Differences and derivatives within convex sets

On a convex set `Ω` with nonempty interior, the differences of a function that is smooth *within*
`Ω` are controlled by its derivatives within `Ω`, at the points whose steps stay in `Ω`: if
`x, x + h, …, x + r h ∈ Ω` and `‖D^i a‖ ≤ C` on `Ω` for `i ≤ r`, then

`|Δ_h^r a(x)| ≤ 2^r r^(r+1) C ‖h‖^r`   (`Rd.norm_higherDiff_le_of_iteratedFDerivWithin`).

The model is the closed half-space, where the derivatives of functions on the boundary are
one-sided; on `Ω = V` the bound is `Rd.norm_higherDiff_le_of_iteratedFDeriv` of
`FunctionSpaces.Rd.Differences.PointwiseMultipliers` up to the constant.

The proof restricts `a` to the segment, `g(t) = a(x + t h)` on `[0, r]`, which lies in `Ω` by
convexity. Taylor's theorem on the interval (Mathlib's `taylor_mean_remainder_bound`) writes
`g = T + R` with a polynomial `T` of degree `< r` and `|R(t)| ≤ ‖g^(r)‖_∞ t^r / (r-1)!`; the
differences of order `r` of `T` vanish (`Rd.fwdDiff_iter_taylorWithinEval_eq_zero`, from Mathlib's
`fwdDiff_iter_sum_mul_pow_eq_zero`), so `|Δ_1^r g(0)| ≤ 2^r r^r ‖g^(r)‖_∞ / (r-1)!`
(`Rd.norm_fwdDiff_iter_le_of_iteratedDerivWithin`). The chain rule (Mathlib's
`norm_iteratedFDerivWithin_comp_le`) bounds `‖g^(r)‖_∞ ≤ r! C ‖h‖^r`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Nat

namespace Rd

/-! ### One variable -/

/-- Forward differences commute with the inclusion `ℝ → ℂ`:
`Δ_1^m (F ∘ ofReal) = (Δ_1^m F) ∘ ofReal`. -/
theorem fwdDiff_iter_comp_ofReal (F : ℂ → ℂ) (m : ℕ) :
    (fwdDiff (1 : ℝ))^[m] (fun t : ℝ => F t) = fun t : ℝ => (fwdDiff (1 : ℂ))^[m] F t := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext t
    simp only [fwdDiff]
    push_cast
    rfl

/-- **The differences of order `n + 1` of a Taylor polynomial of degree `n` vanish**. -/
theorem fwdDiff_iter_taylorWithinEval_eq_zero (g : ℝ → ℂ) (n : ℕ) (s : Set ℝ) :
    (fwdDiff (1 : ℝ))^[n + 1] (taylorWithinEval g n s 0) = 0 := by
  set F : ℂ → ℂ := fun z => ∑ k ∈ Finset.range (n + 1),
    ((k ! : ℂ)⁻¹ * iteratedDerivWithin k g s 0) * z ^ k
  have hT : taylorWithinEval g n s 0 = fun t : ℝ => F t := by
    funext t
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.real_smul]
    push_cast
    ring
  rw [hT, fwdDiff_iter_comp_ofReal, fwdDiff_iter_sum_mul_pow_eq_zero]
  rfl

/-- **Differences of order `r` and the `r`-th derivative on an interval**: if `g` is of class
`C^r` on `[0, r]`, `r = n + 1`, and `‖g^(r)‖ ≤ C` there, then
`|Δ_1^r g(0)| ≤ 2^r r^r C / (r-1)!`. -/
theorem norm_fwdDiff_iter_le_of_iteratedDerivWithin {g : ℝ → ℂ} {n : ℕ}
    (hg : ContDiffOn ℝ (n + 1) g (Icc 0 (n + 1))) {C : ℝ}
    (hC : ∀ y ∈ Icc (0 : ℝ) (n + 1), ‖iteratedDerivWithin (n + 1) g (Icc 0 (n + 1)) y‖ ≤ C) :
    ‖(fwdDiff (1 : ℝ))^[n + 1] g 0‖ ≤ 2 ^ (n + 1) * ((n : ℝ) + 1) ^ (n + 1) / n ! * C := by
  have hn : (0 : ℝ) ≤ n + 1 := by positivity
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, hn⟩)
  set T := taylorWithinEval g n (Icc 0 ((n : ℝ) + 1)) 0
  have hT := congrFun (fwdDiff_iter_taylorWithinEval_eq_zero g n (Icc 0 ((n : ℝ) + 1))) 0
  have hrem : ∀ l ∈ Finset.range (n + 2), ‖g l - T l‖ ≤ C * ((n : ℝ) + 1) ^ (n + 1) / n ! :=
    fun l hl => by
      have hl' : (l : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      refine (taylor_mean_remainder_bound (by exact_mod_cast hg) ⟨Nat.cast_nonneg l, hl'⟩
        hC).trans ?_
      rw [sub_zero]
      gcongr
  have hsplit : (fwdDiff (1 : ℝ))^[n + 1] g 0 = ∑ l ∈ Finset.range (n + 2),
      ((-1 : ℂ) ^ (n + 1 - l) * ((n + 1).choose l : ℂ)) * (g l - T l) := by
    have h1 := higherDiff_apply (n + 1) (1 : ℝ) g 0
    have h2 := higherDiff_apply (n + 1) (1 : ℝ) T 0
    rw [hT, Pi.zero_apply] at h2
    simp only [smul_eq_mul, mul_one, zero_add] at h1 h2
    rw [h1, ← sub_zero (∑ l ∈ _, _), h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hsplit]
  calc ‖∑ l ∈ Finset.range (n + 2), ((-1 : ℂ) ^ (n + 1 - l) * ((n + 1).choose l : ℂ)) *
        (g l - T l)‖
      ≤ ∑ l ∈ Finset.range (n + 2), ((n + 1).choose l : ℝ) *
          (C * ((n : ℝ) + 1) ^ (n + 1) / n !) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
          Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (hrem l hl) (Nat.cast_nonneg _)
    _ = 2 ^ (n + 1) * ((n : ℝ) + 1) ^ (n + 1) / n ! * C := by
        rw [← Finset.sum_mul]
        have hsum : ∑ l ∈ Finset.range (n + 2), ((n + 1).choose l : ℝ) = 2 ^ (n + 1) := by
          exact_mod_cast Nat.sum_range_choose (n + 1)
        rw [hsum]
        ring

/-! ### Lines in a convex set -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The line `t ↦ x + t h`**: its derivatives of order `i ≥ 1` have norm at most `‖h‖^i`
(the first derivative is `h`, the higher ones vanish). -/
theorem norm_iteratedFDeriv_line_le (x h : E) {i : ℕ} (hi : 1 ≤ i) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun t : ℝ => x + t • h) t‖ ≤ ‖h‖ ^ i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rw [← norm_iteratedFDeriv_fderiv]
  have hd : fderiv ℝ (fun t : ℝ => x + t • h) = fun _ => (ContinuousLinearMap.id ℝ ℝ).smulRight h :=
    funext fun t => (((hasFDerivAt_id t).smul_const h).const_add x).fderiv
  rw [hd]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero, ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id, one_mul, pow_one]
  · rw [iteratedFDeriv_const_of_ne hk.ne', Pi.zero_apply, norm_zero]
    positivity

/-- **Steps in a convex set**: if `x` and `x + r h` lie in the convex set `Ω`, so does `x + t h`
for `0 ≤ t ≤ r`. -/
theorem add_smul_mem_of_mem_stepSet {Ω : Set E} (hΩ : Convex ℝ Ω) {r : ℕ} {h x : E}
    (hx : x ∈ stepSet Ω r h) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) r) : x + t • h ∈ Ω := by
  have hx0 : x ∈ Ω := by simpa using hx 0 (Nat.zero_le r)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : t = 0 := le_antisymm (by simpa using ht.2) ht.1
    simpa [this] using hx0
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hxr : x + (r : ℝ) • h ∈ Ω := hx r le_rfl
  have h1 := hΩ.add_smul_mem hx0 (y := (r : ℝ) • h) (by simpa using hxr)
    (t := t / r) ⟨div_nonneg ht.1 hr'.le, (div_le_one hr').2 ht.2⟩
  rwa [smul_smul, div_mul_cancel₀ t hr'.ne'] at h1

/-- **Differences of order `r ≥ 1` within a convex set**: if `a` is of class `C^r` within the
convex set `Ω` with nonempty interior and `‖D^i a‖ ≤ C` on `Ω` for `i ≤ r`, then
`|Δ_h^r a(x)| ≤ 2^r r^(r+1) C ‖h‖^r` whenever `x, x + h, …, x + r h ∈ Ω`. -/
theorem norm_higherDiff_le_of_iteratedFDerivWithin {Ω : Set E} (hΩ : Convex ℝ Ω)
    (hint : (interior Ω).Nonempty) {a : E → ℂ} {r : ℕ} (hr : 1 ≤ r)
    (ha : ContDiffOn ℝ r a Ω) {C : ℝ}
    (hC : ∀ i ≤ r, ∀ y ∈ Ω, ‖iteratedFDerivWithin ℝ i a Ω y‖ ≤ C) {h x : E}
    (hx : x ∈ stepSet Ω r h) :
    ‖(fwdDiff h)^[r] a x‖ ≤ 2 ^ r * (r : ℝ) ^ (r + 1) * C * ‖h‖ ^ r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hr
  set γ : ℝ → E := fun t => x + t • h
  set I : Set ℝ := Icc 0 ((n : ℝ) + 1)
  have hΩu : UniqueDiffOn ℝ Ω := uniqueDiffOn_convex hΩ hint
  have hIu : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by positivity)
  have hγ' : ContDiff ℝ ⊤ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγ : ContDiff ℝ (n + 1) γ := hγ'.of_le le_top
  have hmaps : MapsTo γ I Ω := fun t ht =>
    add_smul_mem_of_mem_stepSet hΩ hx ⟨ht.1, by push_cast; exact ht.2⟩
  have ha' : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) a Ω := by exact_mod_cast ha
  have hg : ContDiffOn ℝ (n + 1) (a ∘ γ) I := ha'.comp hγ.contDiffOn hmaps
  -- the differences of `a` along `h` are those of `a ∘ γ` along `1`
  have hdiff : (fwdDiff h)^[n + 1] a x = (fwdDiff (1 : ℝ))^[n + 1] (a ∘ γ) 0 := by
    rw [higherDiff_apply, higherDiff_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [γ]
  -- the derivative of order `n + 1` of `a ∘ γ`
  have hder : ∀ t ∈ I, ‖iteratedDerivWithin (n + 1) (a ∘ γ) I t‖ ≤
      (n + 1) ! * C * ‖h‖ ^ (n + 1) := fun t ht => by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    simp only [norm_one, Finset.prod_const_one, mul_one]
    refine norm_iteratedFDerivWithin_comp_le (N := (n + 1 : ℕ)) (by exact_mod_cast ha)
      (by exact_mod_cast hγ.contDiffOn) le_rfl hΩu hIu hmaps ht
      (fun i hi => hC i hi _ (hmaps ht)) fun i hi1 _ => ?_
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hIu
      (hγ'.contDiffAt.of_le (by exact_mod_cast le_top)) ht]
    exact norm_iteratedFDeriv_line_le x h hi1 t
  rw [hdiff]
  refine (norm_fwdDiff_iter_le_of_iteratedDerivWithin hg hder).trans_eq ?_
  push_cast
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end Rd
