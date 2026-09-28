/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import LeanPool.MovingSofa.LeanCert.Core.DerivativeIntervals
/-!
# Generic Taylor Series Abstractions

This file provides generic Taylor series machinery for verified numerics.
We wrap Mathlib's Taylor expansion theorems in forms convenient for our
interval arithmetic framework.

## Phase Status

**This module is now Phase 3 complete.** The main Taylor remainder bound theorem
`taylor_remainder_bound` is fully proved with no `sorry` markers.

The theorem provides rigorous bounds on Taylor polynomial approximation errors
using Lagrange's form of the remainder.

## Main definitions

* `TaylorApprox` - A Taylor approximation with explicit remainder bounds
* Generic theorems for composing Taylor approximations

## Design notes

This file provides the abstract theory. Specific Taylor expansions for
`exp`, `sin`, `cos`, etc. are built using this machinery in conjunction
with Mathlib's calculus lemmas.
-/

/-! ### Taylor approximation structure -/

@[expose] public section

namespace LeanCert.Core

/-- A Taylor approximation of a function on an interval.

Given a function `f`, center `c`, and radius `r`, this represents:
- A polynomial approximation `poly` of degree `n`
- A remainder bound `R` such that for all `x` with `|x - c| ≤ r`:
  `|f(x) - poly(x - c)| ≤ R`
-/
structure TaylorApprox where
  /-- Degree of the polynomial -/
  degree : ℕ
  /-- Polynomial coefficients (Taylor coefficients at center) -/
  coeffs : Fin (degree + 1) → ℚ
  /-- Remainder bound -/
  remainder : ℚ
  /-- The remainder is non-negative -/
  remainder_nonneg : 0 ≤ remainder

namespace TaylorApprox

/-- Evaluate the polynomial part at a point -/
noncomputable def evalPoly (ta : TaylorApprox) (x : ℝ) : ℝ :=
  ∑ i : Fin (ta.degree + 1), (ta.coeffs i : ℝ) * x ^ (i : ℕ)

end TaylorApprox

/-! ### Derivative bounds -/

/-- A bound on the n-th derivative of a function on an interval -/
structure DerivBound where
  /-- The derivative order -/
  order : ℕ
  /-- Upper bound on |f^(n)(x)| for x in the interval -/
  bound : ℚ
  /-- The bound is non-negative -/
  bound_nonneg : 0 ≤ bound

/-! ### Taylor remainder bounds -/

/-! ### Helper lemmas for iteratedDerivWithin conversion -/

/-- Unique differentiability at the left endpoint of a closed interval. -/
lemma uniqueDiffWithinAt_Icc_left {c x : ℝ} (hcx : c < x) :
    UniqueDiffWithinAt ℝ (Set.Icc c x) c := by
  apply uniqueDiffWithinAt_convex (convex_Icc c x)
  · rw [interior_Icc]; exact Set.nonempty_Ioo.mpr hcx
  · rw [closure_Icc]; exact Set.left_mem_Icc.mpr (le_of_lt hcx)

/-- Unique differentiability at the right endpoint of a closed interval. -/
lemma uniqueDiffWithinAt_Icc_right {c x : ℝ} (hcx : c < x) :
    UniqueDiffWithinAt ℝ (Set.Icc c x) x := by
  apply uniqueDiffWithinAt_convex (convex_Icc c x)
  · rw [interior_Icc]; exact Set.nonempty_Ioo.mpr hcx
  · rw [closure_Icc]; exact Set.right_mem_Icc.mpr (le_of_lt hcx)

/-- At the left endpoint of [c, x], derivWithin equals deriv for differentiable functions. -/
lemma derivWithin_Icc_left_eq_deriv {f : ℝ → ℝ} {c x : ℝ}
    (hcx : c < x) (hf : DifferentiableAt ℝ f c) :
    derivWithin f (Set.Icc c x) c = deriv f c := by
  have hderiv := hf.hasDerivAt
  have hderiv_within : HasDerivWithinAt f (deriv f c) (Set.Icc c x) c := hderiv.hasDerivWithinAt
  exact hderiv_within.derivWithin (uniqueDiffWithinAt_Icc_left hcx)

/-- At the right endpoint of [c, x], derivWithin equals deriv for differentiable functions. -/
lemma derivWithin_Icc_right_eq_deriv {f : ℝ → ℝ} {c x : ℝ}
    (hcx : c < x) (hf : DifferentiableAt ℝ f x) :
    derivWithin f (Set.Icc c x) x = deriv f x := by
  have hderiv := hf.hasDerivAt
  have hderiv_within : HasDerivWithinAt f (deriv f x) (Set.Icc c x) x := hderiv.hasDerivWithinAt
  exact hderiv_within.derivWithin (uniqueDiffWithinAt_Icc_right hcx)

/-- Helper lemma: `iteratedDerivWithin` on `Icc a b` equals `iteratedDeriv` at interior points.

This bridges Mathlib's `iteratedDerivWithin`-based Taylor theorems with global `iteratedDeriv`. -/
lemma iteratedDerivWithin_Icc_interior_eq {f : ℝ → ℝ} {a b : ℝ} {x : ℝ} {n : ℕ}
    (_hab : a < b) (hx : x ∈ Set.Ioo a b) :
    iteratedDerivWithin n f (Set.Icc a b) x = iteratedDeriv n f x := by
  open Set Filter Topology in
  have h_nhds : Icc a b ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv]
  congr 1
  have heq : (Set.Icc a b : Set ℝ) =ᶠ[𝓝 x] (Set.univ : Set ℝ) := by
    filter_upwards [h_nhds] with y hy
    exact propext ⟨fun _ => trivial, fun _ => hy⟩
  rw [iteratedFDerivWithin_congr_set heq n, iteratedFDerivWithin_univ]

/-- At the left endpoint of [c, x], iteratedDerivWithin equals iteratedDeriv for ContDiff functions.
-/
lemma iteratedDerivWithin_Icc_left_eq_iteratedDeriv {f : ℝ → ℝ} {c x : ℝ} {n : ℕ}
    (hcx : c < x) (hf : ContDiff ℝ n f) :
    iteratedDerivWithin n f (Set.Icc c x) c = iteratedDeriv n f c := by
  open Set in
  induction n generalizing f with
  | zero => simp only [iteratedDerivWithin_zero, iteratedDeriv_zero]
  | succ n ih =>
    have hf_n : ContDiff ℝ n f := hf.of_le (by simp : (n : WithTop ℕ∞) ≤ (n + 1 : ℕ))
    rw [iteratedDerivWithin_succ', iteratedDeriv_succ']
    have h_ne_zero : ((n : ℕ) + 1 : WithTop ℕ∞) ≠ 0 := by simp
    have h_eq_derivWithin : EqOn (derivWithin f (Icc c x)) (deriv f) (Icc c x) := by
      intro y hy
      rcases eq_or_ne y c with rfl | hne_c
      · exact derivWithin_Icc_left_eq_deriv hcx
            ((hf.differentiable h_ne_zero).differentiableAt)
      · rcases eq_or_ne y x with rfl | hne_x
        · exact derivWithin_Icc_right_eq_deriv hcx
              ((hf.differentiable h_ne_zero).differentiableAt)
        · apply derivWithin_of_mem_nhds
          apply Icc_mem_nhds
          · exact lt_of_le_of_ne hy.1 (Ne.symm hne_c)
          · exact lt_of_le_of_ne hy.2 hne_x
    have h_congr : EqOn (iteratedDerivWithin n (derivWithin f (Icc c x)) (Icc c x))
                        (iteratedDerivWithin n (deriv f) (Icc c x)) (Icc c x) :=
      iteratedDerivWithin_congr (n := n) h_eq_derivWithin
    have hc_mem : c ∈ Icc c x := left_mem_Icc.mpr (le_of_lt hcx)
    rw [h_congr hc_mem]
    have hdf : ContDiff ℝ n (deriv f) := by
      have h := hf.iterate_deriv' n 1
      simp only [Function.iterate_one] at h
      exact h
    exact ih hdf

/-- At the left endpoint of [c, x], iteratedDerivWithin equals iteratedDeriv for functions
    that are ContDiffOn on an open set containing c.

    This is useful for functions like log that are only smooth on (0, ∞). -/
lemma iteratedDerivWithin_Icc_left_eq_iteratedDeriv_of_isOpen {f : ℝ → ℝ} {c x : ℝ} {n : ℕ} {U :
  Set ℝ}
    (hU_open : IsOpen U) (hcU : c ∈ U) (hcx : c < x) (hI_sub : Set.Icc c x ⊆ U)
    (hf : ContDiffOn ℝ n f U) :
    iteratedDerivWithin n f (Set.Icc c x) c = iteratedDeriv n f c := by
  open Set in
  induction n generalizing f with
  | zero => simp only [iteratedDerivWithin_zero, iteratedDeriv_zero]
  | succ n ih =>
    have hf_n : ContDiffOn ℝ n f U := hf.of_le (by simp : (n : WithTop ℕ∞) ≤ (n + 1 : ℕ))
    rw [iteratedDerivWithin_succ', iteratedDeriv_succ']
    have h_ne_zero : ((n : ℕ) + 1 : WithTop ℕ∞) ≠ 0 := by simp
    -- For each y in Icc c x, derivWithin f = deriv f
    have h_eq_derivWithin : EqOn (derivWithin f (Icc c x)) (deriv f) (Icc c x) := by
      intro y hy
      rcases eq_or_ne y c with rfl | hne_c
      · -- At c: use that f is differentiable at c (from ContDiffOn on open U)
        exact derivWithin_Icc_left_eq_deriv hcx
            ((hf.differentiableOn h_ne_zero).differentiableAt (hU_open.mem_nhds hcU))
      · rcases eq_or_ne y x with rfl | hne_x
        · -- At x: use right endpoint lemma
          exact derivWithin_Icc_right_eq_deriv hcx
              ((hf.differentiableOn h_ne_zero).differentiableAt (hU_open.mem_nhds (hI_sub hy)))
        · -- Interior: Icc is a neighborhood
          apply derivWithin_of_mem_nhds
          apply Icc_mem_nhds
          · exact lt_of_le_of_ne hy.1 (Ne.symm hne_c)
          · exact lt_of_le_of_ne hy.2 hne_x
    have h_congr : EqOn (iteratedDerivWithin n (derivWithin f (Icc c x)) (Icc c x))
                        (iteratedDerivWithin n (deriv f) (Icc c x)) (Icc c x) :=
      iteratedDerivWithin_congr (n := n) h_eq_derivWithin
    have hc_mem : c ∈ Icc c x := left_mem_Icc.mpr (le_of_lt hcx)
    rw [h_congr hc_mem]
    have hdf : ContDiffOn ℝ n (deriv f) U := hf.deriv_of_isOpen hU_open le_rfl
    exact ih hdf
/-- Taylor remainder bound for c < x case with ContDiffOn hypothesis.

    For functions that are ContDiffOn on an open set containing [a, b], this provides
    the same Lagrange remainder bound as the global ContDiff version. -/
theorem taylor_remainder_bound_on_c_lt_x {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hI_sub : Set.Icc a b ⊆ U)
    (hca : a ≤ c)
    (hf : ContDiffOn ℝ (m + 1) f U)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hcx : c < x) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  have hcx_le : c ≤ x := le_of_lt hcx
  have hcI : c ∈ Icc a b := ⟨hca, le_trans hcx_le hx.2⟩
  have hI_sub' : Icc c x ⊆ Icc a b := Icc_subset_Icc hca hx.2
  have hI_sub_U : Icc c x ⊆ U := fun y hy => hI_sub (hI_sub' hy)
  have hcU : c ∈ U := hI_sub hcI
  have hf_on : ContDiffOn ℝ (m + 1) f (Icc c x) := hf.mono hI_sub_U
  have hf_on_m : ContDiffOn ℝ m f (Icc c x) := by
    have hm_le : (m : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by simp
    exact hf_on.of_le hm_le
  have hf_diff : DifferentiableOn ℝ (iteratedDerivWithin m f (Icc c x)) (Ioo c x) := by
    have huniq := uniqueDiffOn_Icc hcx
    have hm_lt : (m : WithTop ℕ∞) < (m + 1 : ℕ) := by
      have : (m : ℕ) < m + 1 := Nat.lt_succ_self m
      exact_mod_cast this
    have hdiff := hf_on.differentiableOn_iteratedDerivWithin hm_lt huniq
    exact hdiff.mono Ioo_subset_Icc_self
  have hf_on_m' : ContDiffOn ℝ m f (uIcc c x) := by rwa [uIcc_of_le hcx_le]
  have hf_diff' : DifferentiableOn ℝ (iteratedDerivWithin m f (uIcc c x)) (uIoo c x) := by
    rwa [uIcc_of_le hcx_le, uIoo_of_lt hcx]
  obtain ⟨ξ, hξ_mem, hLagrange⟩ :=
    taylor_mean_remainder_lagrange (x₀ := c) (x := x) hcx.ne hf_on_m' hf_diff'
  have hξ_mem_Ioo : ξ ∈ Ioo c x := by rwa [uIoo_of_lt hcx] at hξ_mem
  rw [uIcc_of_le hcx_le] at hLagrange
  have hξ_ab : ξ ∈ Icc a b := hI_sub' (Ioo_subset_Icc_self hξ_mem_Ioo)
  have hderiv_ξ : iteratedDerivWithin (m + 1) f (Icc c x) ξ = iteratedDeriv (m + 1) f ξ :=
    iteratedDerivWithin_Icc_interior_eq hcx hξ_mem_Ioo
  have hsum_eq : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i =
                 taylorWithinEval f m (Icc c x) c x := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro i hi
    have hderiv_c : iteratedDerivWithin i f (Icc c x) c = iteratedDeriv i f c := by
      have hi_lt : i < m + 1 := mem_range.mp hi
      have hi_le : (i : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
        have : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp hi_lt
        exact le_of_lt (by exact_mod_cast Nat.lt_add_one_of_le this)
      exact iteratedDerivWithin_Icc_left_eq_iteratedDeriv_of_isOpen hU_open hcU hcx hI_sub_U
        (hf.of_le hi_le)
    rw [hderiv_c]
    simp only [smul_eq_mul]
    ring
  rw [hsum_eq, hLagrange, hderiv_ξ]
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hfact_pos : (0 : ℝ) < ((m + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [abs_of_pos hfact_pos]
  have hxc_pos : 0 < x - c := sub_pos.mpr hcx
  rw [abs_pow, abs_of_pos hxc_pos]
  have hbound := hM ξ hξ_ab
  have h_pow_fact_pos : 0 < (x - c) ^ (m + 1) / (m + 1).factorial := by
    apply div_pos
    · exact pow_pos hxc_pos _
    · exact hfact_pos
  calc |iteratedDeriv (m + 1) f ξ| * (x - c) ^ (m + 1) / ↑(m + 1).factorial
      = |iteratedDeriv (m + 1) f ξ| * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by ring
    _ ≤ M * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by
        apply mul_le_mul_of_nonneg_right hbound (le_of_lt h_pow_fact_pos)
    _ = M * (x - c) ^ (m + 1) / ↑(m + 1).factorial := by ring

/-- Helper: translation invariance of iteratedDeriv for ContDiffOn on open sets. -/
private lemma iteratedDeriv_translate_of_contDiffOn {f : ℝ → ℝ} {k : ℝ} {n : ℕ} {U : Set ℝ}
    (hU_open : IsOpen U) (t : ℝ) (ht : t + k ∈ U)
    (hf : ContDiffOn ℝ n f U) :
    iteratedDeriv n (fun y => f (y + k)) t = iteratedDeriv n f (t + k) := by
  induction n generalizing f with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    -- Since t + k ∈ U and U is open, there's a neighborhood of t where y + k ∈ U for all y
    have h_nhds_mem : ∀ᶠ y in nhds t, y + k ∈ U := by
      have hcont : Continuous (fun y => y + k) := continuous_id.add continuous_const
      have hU_nhds : U ∈ nhds (t + k) := hU_open.mem_nhds ht
      exact hcont.continuousAt.preimage_mem_nhds hU_nhds
    -- Derivative equality in a neighborhood of t
    have h_deriv_eq_near : ∀ᶠ y in nhds t, deriv (fun z => f (z + k)) y = deriv f (y + k) := by
      filter_upwards [h_nhds_mem] with y hy_mem
      have hf' : ContDiffOn ℝ 1 f U := hf.of_le (by norm_cast; omega)
      have hdiff : DifferentiableAt ℝ f (y + k) :=
        (hf'.differentiableOn one_ne_zero).differentiableAt (hU_open.mem_nhds hy_mem)
      have hlin : DifferentiableAt ℝ (fun z => z + k) y :=
        differentiableAt_id.add (differentiableAt_const _)
      have h := deriv_comp y hdiff hlin
      simp only [deriv_add_const, deriv_id'', mul_one] at h
      exact h
    have h_iter_eq : iteratedDeriv n (deriv fun z => f (z + k)) t =
                     iteratedDeriv n (fun y => deriv f (y + k)) t :=
      Filter.EventuallyEq.iteratedDeriv_eq n h_deriv_eq_near
    rw [h_iter_eq]
    have hdf : ContDiffOn ℝ n (deriv f) U := hf.deriv_of_isOpen hU_open le_rfl
    exact ih hdf

/-- Key lemma for reflection: derivatives of g(t) = f(2c - t) when f is smooth on an open set.

This is a local version of `iteratedDeriv_reflect` that works with ContDiffOn on an open set
rather than global ContDiff. -/
lemma iteratedDeriv_reflect_of_contDiffOn {f : ℝ → ℝ} {c : ℝ} {n : ℕ} {U : Set ℝ}
    (hU_open : IsOpen U) (hf : ContDiffOn ℝ n f U) (t : ℝ) (ht : 2 * c - t ∈ U) :
    iteratedDeriv n (fun s => f (2 * c - s)) t = (-1 : ℝ) ^ n * iteratedDeriv n f (2 * c - t) := by
  -- Rewrite as f ∘ (· + 2c) ∘ (- ·)
  have heq : (fun s => f (2 * c - s)) = (fun s => (fun y => f (y + 2 * c)) (-s)) := by
    ext s; ring_nf
  rw [heq]
  rw [iteratedDeriv_comp_neg n (fun y => f (y + 2 * c)) t]
  simp only [smul_eq_mul]
  congr 1
  -- Use the translation helper
  have hmt : -t + 2 * c = 2 * c - t := by ring
  rw [← hmt] at ht
  convert iteratedDeriv_translate_of_contDiffOn hU_open (-t) ht hf using 1
  rw [hmt]
/-- Taylor remainder bound for x < c case with ContDiffOn hypothesis.

    For functions that are ContDiffOn on an open set containing [a, b], this provides
    the same Lagrange remainder bound as the global ContDiff version.

    The proof uses reflection: define g(t) = f(2c - t), apply Lagrange to g on [c, 2c-x],
    then convert back. -/
theorem taylor_remainder_bound_on_x_lt_c {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hI_sub : Set.Icc a b ⊆ U)
    (hcb : c ≤ b)
    (hf : ContDiffOn ℝ (m + 1) f U)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hxc : x < c) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  -- Define reflected function g(t) = f(2c - t)
  set g : ℝ → ℝ := fun t => f (2 * c - t) with hg_def
  -- Define V = preimage of U under reflection (the reflected open set)
  set V : Set ℝ := (fun t => 2 * c - t) ⁻¹' U with hV_def
  -- V is open (preimage of open set under continuous function)
  have hV_open : IsOpen V := by
    apply IsOpen.preimage _ hU_open
    exact continuous_const.sub continuous_id
  -- g is ContDiffOn V
  have hg_ContDiffOn : ContDiffOn ℝ (m + 1) g V := by
    have hlin : ContDiff ℝ ⊤ (fun t => 2 * c - t) := contDiff_const.sub contDiff_id
    -- g = f ∘ (2c - ·) and (2c - ·) maps V into U
    have hmaps : Set.MapsTo (fun t => 2 * c - t) V U := fun t ht => ht
    have hlin_on : ContDiffOn ℝ (m + 1) (fun t => 2 * c - t) V :=
      (hlin.contDiffOn.mono (Set.subset_univ _)).of_le le_top
    exact ContDiffOn.comp hf hlin_on hmaps
  -- The interval [c, 2c-x]
  have h_interval_lt : c < 2 * c - x := by linarith
  -- [c, 2c-x] maps under t ↦ 2c-t to [x, c] ⊆ [a,b] ⊆ U
  -- So [c, 2c-x] ⊆ V
  have hJ_sub_V : Icc c (2 * c - x) ⊆ V := by
    intro t ht
    -- 2c - t ∈ [x, c] ⊆ [a,b] ⊆ U
    have ht_lower : x ≤ 2 * c - t := by linarith [ht.2]
    have ht_upper : 2 * c - t ≤ c := by linarith [ht.1]
    have h2ct_in_ab : 2 * c - t ∈ Icc a b := by
      refine mem_Icc.mpr ⟨?_, ?_⟩
      · exact le_trans hx.1 ht_lower
      · exact le_trans ht_upper hcb
    exact hI_sub h2ct_in_ab
  -- c ∈ V since c maps to c ∈ [a,b] ⊆ U
  have hcV : c ∈ V := by
    have hc_ab : c ∈ Icc a b := ⟨le_trans hx.1 (le_of_lt hxc), hcb⟩
    -- Need to show c ∈ V, i.e., (fun t => 2 * c - t) c ∈ U, i.e., 2c - c = c ∈ U
    change c ∈ V
    simp only [hV_def, Set.mem_preimage]
    have h2cc : 2 * c - c = c := by ring
    rw [h2cc]
    exact hI_sub hc_ab
  -- Helper: map [c, 2c-x] to [a,b]
  have h_map_to_ab : ∀ t ∈ Icc c (2 * c - x), 2 * c - t ∈ Icc a b := by
    intro t ht
    have ht_lower : x ≤ 2 * c - t := by linarith [ht.2]
    have ht_upper : 2 * c - t ≤ c := by linarith [ht.1]
    exact ⟨le_trans hx.1 ht_lower, le_trans ht_upper hcb⟩
  -- Derivative bound for g using reflection formula
  have hg_deriv_bound : ∀ y ∈ Icc c (2 * c - x), ‖iteratedDeriv (m + 1) g y‖ ≤ M := by
    intro y hy
    have h2cy_ab : 2 * c - y ∈ Icc a b := h_map_to_ab y hy
    have h2cy_U : 2 * c - y ∈ U := hI_sub h2cy_ab
    -- Use the reflection formula
    have hg_deriv : iteratedDeriv (m + 1) g y = (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f (2 *
      c - y) :=
      iteratedDeriv_reflect_of_contDiffOn hU_open hf y h2cy_U
    rw [hg_deriv, norm_mul, Real.norm_eq_abs]
    have h_neg_one : |(-1 : ℝ) ^ (m + 1)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [h_neg_one, one_mul]
    exact hM (2 * c - y) h2cy_ab
  -- Now apply taylor_remainder_bound_on_c_lt_x to g
  have hcV' : a ≤ c := le_trans hx.1 (le_of_lt hxc)
  -- g is ContDiffOn V and Icc c (2c-x) ⊆ V
  have h_taylor_g := taylor_remainder_bound_on_c_lt_x hV_open hJ_sub_V (le_refl c)
      hg_ContDiffOn hg_deriv_bound (2 * c - x) ⟨le_of_lt h_interval_lt, le_refl _⟩ h_interval_lt
  -- g(2c-x) = f(x)
  have hg_at_2cmx : g (2 * c - x) = f x := by simp only [hg_def, sub_sub_cancel]
  -- g^(i)(c) = (-1)^i * f^(i)(c)
  have hg_deriv_c : ∀ i ≤ m + 1, iteratedDeriv i g c = (-1 : ℝ) ^ i * iteratedDeriv i f c := by
    intro i hi
    have hcU : c ∈ U := hI_sub ⟨le_trans hx.1 (le_of_lt hxc), hcb⟩
    have h2cc : 2 * c - c = c := by ring
    rw [← h2cc] at hcU
    have hfi : ContDiffOn ℝ i f U := hf.of_le (by exact_mod_cast hi)
    have hrefl := iteratedDeriv_reflect_of_contDiffOn hU_open hfi c hcU
    simp only [h2cc] at hrefl
    exact hrefl
  -- Now convert the Taylor sum
  -- ∑ (iteratedDeriv i g c / i!) * ((2c-x) - c)^i = ∑ (iteratedDeriv i f c / i!) * (x - c)^i
  have hsum_eq : ∑ i ∈ range (m + 1), (iteratedDeriv i g c / i.factorial) * ((2 * c - x) - c) ^ i =
                 ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i := by
    apply sum_congr rfl
    intro i hi
    have hi_le : i ≤ m + 1 := le_of_lt (mem_range.mp hi)
    rw [hg_deriv_c i hi_le]
    have h_diff : (2 * c - x) - c = c - x := by ring
    rw [h_diff]
    have h_pow : (c - x : ℝ) ^ i = (-1 : ℝ) ^ i * (x - c) ^ i := by
      have : c - x = -(x - c) := by ring
      rw [this, neg_eq_neg_one_mul, mul_pow]
    rw [h_pow]
    -- Simplify: (-1)^i * f^(i)(c) / i! * ((-1)^i * (x-c)^i)
    have h_neg_sq : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := by rw [← pow_add]; norm_num
    -- Goal: (-1)^i * iteratedDeriv i f c / i! * ((-1)^i * (x-c)^i) = iteratedDeriv i f c / i! *
    -- (x-c)^i
    calc (-1 : ℝ) ^ i * iteratedDeriv i f c / ↑i.factorial * ((-1) ^ i * (x - c) ^ i)
        = ((-1 : ℝ) ^ i * (-1) ^ i) * (iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i) := by ring
      _ = 1 * (iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i) := by rw [h_neg_sq]
      _ = iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i := by ring
  -- Use h_taylor_g with the conversions
  rw [hg_at_2cmx, hsum_eq] at h_taylor_g
  -- The RHS: M * |(2c-x) - c|^(m+1) / (m+1)! = M * |x - c|^(m+1) / (m+1)!
  have h_abs_eq : |(2 * c - x) - c| = |x - c| := by
    have h : (2 * c - x) - c = c - x := by ring
    rw [h, abs_sub_comm]
  rw [h_abs_eq] at h_taylor_g
  exact h_taylor_g
/-- Combined Taylor remainder bound with ContDiffOn hypothesis.

    For functions that are ContDiffOn on an open set containing [a, b], this provides
    the Lagrange remainder bound for any x ∈ [a, b] and center c ∈ [a, b]. -/
theorem taylor_remainder_bound_on {f : ℝ → ℝ} {a b c : ℝ} {n : ℕ} {M : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hI_sub : Set.Icc a b ⊆ U)
    (hca : a ≤ c) (hcb : c ≤ b)
    (hf : ContDiffOn ℝ n f U)
    (hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n f x‖ ≤ M)
    (_hMnonneg : 0 ≤ M) :
    ∀ x ∈ Set.Icc a b,
      ‖f x - ∑ i ∈ Finset.range n, (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ n / n.factorial := by
  open Set Finset in
  intro x hx
  cases n with
  | zero =>
    simp only [range_zero, sum_empty, sub_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_zero, mul_one]
    have h : f = iteratedDeriv 0 f := iteratedDeriv_zero.symm
    rw [h]
    exact hM x hx
  | succ m =>
    by_cases hxc : x = c
    · -- Case x = c: both sides are 0
      have hrhs : M * |x - c| ^ (m + 1) / ↑(m + 1).factorial = 0 := by
        rw [hxc, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_div]
      rw [hrhs]
      have hsum : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i = f c := by
        rw [hxc]
        simp only [sub_self]
        rw [sum_eq_single 0]
        · simp [iteratedDeriv_zero]
        · intro i _ hi
          have hpos : 0 < i := Nat.pos_of_ne_zero hi
          have : (0 : ℝ) ^ i = 0 := zero_pow hpos.ne'
          simp [this]
        · simp
      rw [hsum, hxc, sub_self, norm_zero]
    · rcases lt_or_gt_of_ne hxc with hxc_lt | hcx_lt
      · exact taylor_remainder_bound_on_x_lt_c hU_open hI_sub hcb hf hM x hx hxc_lt
      · exact taylor_remainder_bound_on_c_lt_x hU_open hI_sub hca hf hM x hx hcx_lt

/-- Key lemma: derivatives of reflected function g(t) = f(2c - t).

For the `x < c` case, we use reflection: define g(t) = f(2c - t), apply Lagrange
to g on [c, 2c-x], then convert back. This lemma shows how g's derivatives
relate to f's derivatives. -/
lemma iteratedDeriv_reflect {f : ℝ → ℝ} {c : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) (t : ℝ) :
    iteratedDeriv n (fun s => f (2 * c - s)) t = (-1 : ℝ) ^ n * iteratedDeriv n f (2 * c - t) := by
  have heq : (fun s => f (2 * c - s)) = (fun s => (fun x => f (x + 2 * c)) (-s)) := by
    ext s; ring_nf
  rw [heq]
  rw [iteratedDeriv_comp_neg n (fun x => f (x + 2 * c)) t]
  simp only [smul_eq_mul]
  congr 1
  clear heq
  induction n generalizing f with
  | zero => simp only [iteratedDeriv_zero]; ring_nf
  | succ n ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hf' : ContDiff ℝ (n + 1) f := hf
    have hderiv_eq : deriv (fun x => f (x + 2 * c)) = fun x => deriv f (x + 2 * c) := by
      ext x
      have hdiff : DifferentiableAt ℝ f (x + 2 * c) :=
        (hf'.differentiable (by simp : ((n : ℕ) + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      have hlin : DifferentiableAt ℝ (fun y => y + 2 * c) x :=
        differentiableAt_id.add (differentiableAt_const _)
      have h1 := deriv_comp x hdiff hlin
      simp only [deriv_add_const, deriv_id'', mul_one] at h1
      exact h1
    rw [hderiv_eq]
    have hdf : ContDiff ℝ n (deriv f) := by
      have h := hf'.iterate_deriv' n 1
      simp only [Function.iterate_one] at h
      exact h
    exact ih hdf

/-- Auxiliary lemma: (-1)^n * (-1)^n = 1 for any natural n. -/
lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add]
  norm_num
/-- Taylor remainder bound for c < x case (Lagrange form).

For `c < x`, we apply `taylor_mean_remainder_lagrange` on `[c, x]` and convert
`iteratedDerivWithin` to `iteratedDeriv` using the helper lemmas above. -/
theorem taylor_remainder_bound_c_lt_x {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ}
    (hca : a ≤ c)
    (hf : ContDiff ℝ (m + 1) f)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hcx : c < x) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  have hcx_le : c ≤ x := le_of_lt hcx
  have hI_sub : Icc c x ⊆ Icc a b := Icc_subset_Icc hca hx.2
  have hf_on : ContDiffOn ℝ (m + 1) f (Icc c x) := hf.contDiffOn.mono hI_sub
  have hf_on_m : ContDiffOn ℝ m f (Icc c x) := by
    have hm_le : (m : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by simp
    exact hf_on.of_le hm_le
  have hf_diff : DifferentiableOn ℝ (iteratedDerivWithin m f (Icc c x)) (Ioo c x) := by
    have huniq := uniqueDiffOn_Icc hcx
    have hm_lt : (m : WithTop ℕ∞) < (m + 1 : ℕ) := by
      have : (m : ℕ) < m + 1 := Nat.lt_succ_self m
      exact_mod_cast this
    have hdiff := hf_on.differentiableOn_iteratedDerivWithin hm_lt huniq
    exact hdiff.mono Ioo_subset_Icc_self
  have hf_on_m' : ContDiffOn ℝ m f (uIcc c x) := by rwa [uIcc_of_le hcx_le]
  have hf_diff' : DifferentiableOn ℝ (iteratedDerivWithin m f (uIcc c x)) (uIoo c x) := by
    rwa [uIcc_of_le hcx_le, uIoo_of_lt hcx]
  obtain ⟨ξ, hξ_mem, hLagrange⟩ :=
    taylor_mean_remainder_lagrange (x₀ := c) (x := x) hcx.ne hf_on_m' hf_diff'
  have hξ_mem_Ioo : ξ ∈ Ioo c x := by rwa [uIoo_of_lt hcx] at hξ_mem
  rw [uIcc_of_le hcx_le] at hLagrange
  have hξ_ab : ξ ∈ Icc a b := hI_sub (Ioo_subset_Icc_self hξ_mem_Ioo)
  have hderiv_ξ : iteratedDerivWithin (m + 1) f (Icc c x) ξ = iteratedDeriv (m + 1) f ξ :=
    iteratedDerivWithin_Icc_interior_eq hcx hξ_mem_Ioo
  have hsum_eq : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i =
                 taylorWithinEval f m (Icc c x) c x := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro i hi
    have hderiv_c : iteratedDerivWithin i f (Icc c x) c = iteratedDeriv i f c := by
      have hi_lt : i < m + 1 := mem_range.mp hi
      have hi_le : (i : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
        have : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp hi_lt
        exact le_of_lt (by exact_mod_cast Nat.lt_add_one_of_le this)
      exact iteratedDerivWithin_Icc_left_eq_iteratedDeriv hcx (hf.of_le hi_le)
    rw [hderiv_c]
    simp only [smul_eq_mul]
    ring
  rw [hsum_eq, hLagrange, hderiv_ξ]
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hfact_pos : (0 : ℝ) < ((m + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [abs_of_pos hfact_pos]
  have hxc_pos : 0 < x - c := sub_pos.mpr hcx
  rw [abs_pow, abs_of_pos hxc_pos]
  have hbound := hM ξ hξ_ab
  have h_pow_fact_pos : 0 < (x - c) ^ (m + 1) / (m + 1).factorial := by
    apply div_pos
    · exact pow_pos hxc_pos _
    · exact hfact_pos
  calc |iteratedDeriv (m + 1) f ξ| * (x - c) ^ (m + 1) / ↑(m + 1).factorial
      = |iteratedDeriv (m + 1) f ξ| * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by ring
    _ ≤ M * ((x - c) ^ (m + 1) / ↑(m + 1).factorial) := by
        apply mul_le_mul_of_nonneg_right hbound (le_of_lt h_pow_fact_pos)
    _ = M * (x - c) ^ (m + 1) / ↑(m + 1).factorial := by ring
/-- Taylor remainder bound for x < c case (Lagrange form via reflection).

For `x < c`, we define g(t) = f(2c - t), apply `taylor_mean_remainder_lagrange` on `[c, 2c-x]`,
then use `iteratedDeriv_reflect` to convert back to f's derivatives. The key insight is that
g's Taylor expansion at c, evaluated at 2c-x, equals f's Taylor expansion at c, evaluated at x,
because the (-1)^i factors from the derivatives cancel with the (-1)^i factors from the powers. -/
theorem taylor_remainder_bound_x_lt_c {f : ℝ → ℝ} {a b c : ℝ} {m : ℕ} {M : ℝ}
    (hcb : c ≤ b)
    (hf : ContDiff ℝ (m + 1) f)
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDeriv (m + 1) f y‖ ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) (hxc : x < c) :
    ‖f x - ∑ i ∈ Finset.range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ (m + 1) / (m + 1).factorial := by
  open Set Finset in
  -- Define reflected function g(t) = f(2c - t)
  set g : ℝ → ℝ := fun t => f (2 * c - t) with hg_def
  -- g is smooth
  have hg_smooth : ContDiff ℝ (m + 1) g := by
    have hlin : ContDiff ℝ ⊤ (fun t => 2 * c - t) := contDiff_const.sub contDiff_id
    exact hf.comp (hlin.of_le le_top)
  -- The interval [c, 2c - x]
  have h_interval_lt : c < 2 * c - x := by linarith
  -- Apply taylor_mean_remainder_lagrange to g on [c, 2c - x]
  have hg_on : ContDiffOn ℝ (m + 1) g (Icc c (2 * c - x)) := hg_smooth.contDiffOn
  have h_interval_le : c ≤ 2 * c - x := le_of_lt h_interval_lt
  have hg_on_m : ContDiffOn ℝ m g (Icc c (2 * c - x)) := by
    have hm_le : (m : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by norm_cast; omega
    exact hg_on.of_le hm_le
  have hg_diff : DifferentiableOn ℝ (iteratedDerivWithin m g (Icc c (2 * c - x))) (Ioo c (2 * c -
    x)) := by
    have huniq := uniqueDiffOn_Icc h_interval_lt
    have hm_lt : (m : WithTop ℕ∞) < (m + 1 : ℕ) := by
      have : (m : ℕ) < m + 1 := Nat.lt_succ_self m
      exact_mod_cast this
    have hdiff := hg_on.differentiableOn_iteratedDerivWithin hm_lt huniq
    exact hdiff.mono Ioo_subset_Icc_self
  have hg_on_m' : ContDiffOn ℝ m g (uIcc c (2 * c - x)) := by rwa [uIcc_of_le h_interval_le]
  have hg_diff' : DifferentiableOn ℝ (iteratedDerivWithin m g (uIcc c (2 * c - x))) (uIoo c (2 * c
    - x)) := by
    rwa [uIcc_of_le h_interval_le, uIoo_of_lt h_interval_lt]
  obtain ⟨ξ', hξ'_mem, hLagrange⟩ :=
    taylor_mean_remainder_lagrange (x₀ := c) (x := 2 * c - x)
      h_interval_lt.ne hg_on_m' hg_diff'
  have hξ'_mem_Ioo : ξ' ∈ Ioo c (2 * c - x) := by
    rwa [uIoo_of_lt h_interval_lt] at hξ'_mem
  rw [uIcc_of_le h_interval_le] at hLagrange
  -- ξ = 2c - ξ' ∈ (x, c)
  set ξ := 2 * c - ξ' with hξ_def
  have hξ'_lt_2cmx : ξ' < 2 * c - x := hξ'_mem_Ioo.2
  have hξ'_gt_c : c < ξ' := hξ'_mem_Ioo.1
  have hξ_gt_x : x < ξ := by simp only [hξ_def]; linarith
  have hξ_lt_c : ξ < c := by simp only [hξ_def]; linarith
  have hξ_ab : ξ ∈ Icc a b :=
    ⟨le_trans hx.1 (le_of_lt hξ_gt_x), le_trans (le_of_lt hξ_lt_c) hcb⟩
  have hg_at_2cmx : g (2 * c - x) = f x := by simp only [hg_def, sub_sub_cancel]
  -- g^{(k)}(c) = (-1)^k * f^{(k)}(c)
  have hg_deriv : ∀ k ≤ m + 1, iteratedDeriv k g c = (-1 : ℝ) ^ k * iteratedDeriv k f c := by
    intro k hk
    have hg_eq : g = fun s => f (2 * c - s) := hg_def
    rw [hg_eq]
    rw [iteratedDeriv_reflect (hf.of_le (by exact_mod_cast hk)) c]
    congr 1
    ring_nf
  -- Key: taylorWithinEval g m (Icc c (2c-x)) c (2c-x) = ∑ ... of f's Taylor coeffs
  have hTaylor_g_to_f : taylorWithinEval g m (Icc c (2 * c - x)) c (2 * c - x) =
                        ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i := by
    rw [taylor_within_apply]
    apply sum_congr rfl
    intro i hi
    have hi_lt : i < m + 1 := mem_range.mp hi
    have hi_le : i ≤ m + 1 := le_of_lt hi_lt
    have hi_le' : (i : WithTop ℕ∞) ≤ (m + 1 : ℕ) := by
      have : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp hi_lt
      exact le_of_lt (by exact_mod_cast Nat.lt_add_one_of_le this)
    have hderiv_c : iteratedDerivWithin i g (Icc c (2 * c - x)) c = iteratedDeriv i g c :=
      iteratedDerivWithin_Icc_left_eq_iteratedDeriv h_interval_lt (hg_smooth.of_le hi_le')
    rw [hderiv_c, hg_deriv i hi_le]
    simp only [smul_eq_mul]
    have h_diff : (2 * c - x) - c = c - x := by ring
    rw [h_diff]
    have h_pow : (c - x : ℝ) ^ i = (-1 : ℝ) ^ i * (x - c) ^ i := by
      have : c - x = -(x - c) := by ring
      rw [this, neg_eq_neg_one_mul, mul_pow]
    rw [h_pow]
    have h_neg_sq : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := neg_one_pow_mul_self i
    have hgoal : (↑i.factorial : ℝ)⁻¹ * ((-1 : ℝ) ^ i * (x - c) ^ i) * ((-1 : ℝ) ^ i *
      iteratedDeriv i f c)
               = iteratedDeriv i f c / ↑i.factorial * (x - c) ^ i := by
      have h1 : (↑i.factorial : ℝ)⁻¹ * ((-1 : ℝ) ^ i * (x - c) ^ i) * ((-1 : ℝ) ^ i *
        iteratedDeriv i f c)
              = ((-1 : ℝ) ^ i * (-1 : ℝ) ^ i) * ((↑i.factorial : ℝ)⁻¹ * (x - c) ^ i *
                iteratedDeriv i f c) := by ring
      rw [h1, h_neg_sq, one_mul]
      field_simp
    exact hgoal
  -- Now use Lagrange formula
  rw [hg_at_2cmx] at hLagrange
  rw [← hTaylor_g_to_f, hLagrange]
  have h_pow_rhs : ((2 * c - x) - c : ℝ) ^ (m + 1) = (c - x) ^ (m + 1) := by ring
  have hderiv_ξ' : iteratedDerivWithin (m + 1) g (Icc c (2 * c - x)) ξ' = iteratedDeriv (m + 1) g
    ξ' :=
    iteratedDerivWithin_Icc_interior_eq h_interval_lt hξ'_mem_Ioo
  -- iteratedDeriv (m+1) g ξ' = (-1)^(m+1) * iteratedDeriv (m+1) f ξ
  have hg_deriv_ξ' : iteratedDeriv (m + 1) g ξ' = (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f ξ
    := by
    have hg_eq : g = fun s => f (2 * c - s) := hg_def
    have h := @iteratedDeriv_reflect f c (m + 1) hf ξ'
    simp only [hg_eq, hξ_def, h]
  rw [hderiv_ξ', hg_deriv_ξ', h_pow_rhs]
  have h_pow_eq : (c - x : ℝ) ^ (m + 1) = (-1 : ℝ) ^ (m + 1) * (x - c) ^ (m + 1) := by
    have : c - x = -(x - c) := by ring
    rw [this, neg_eq_neg_one_mul, mul_pow]
  rw [h_pow_eq]
  -- Simplify
  have h_simplify : (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f ξ * ((-1 : ℝ) ^ (m + 1) * (x - c)
    ^ (m + 1)) / ↑(m + 1).factorial =
                   iteratedDeriv (m + 1) f ξ * (x - c) ^ (m + 1) / ↑(m + 1).factorial := by
    have h_neg_sq := neg_one_pow_mul_self (m + 1)
    have h1 : (-1 : ℝ) ^ (m + 1) * iteratedDeriv (m + 1) f ξ * ((-1 : ℝ) ^ (m + 1) * (x - c) ^ (m
      + 1)) / ↑(m + 1).factorial =
              ((-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (m + 1)) * (iteratedDeriv (m + 1) f ξ * (x - c) ^
                (m + 1)) / ↑(m + 1).factorial := by ring
    rw [h1, h_neg_sq, one_mul]
  rw [h_simplify]
  -- Bound the norm
  rw [norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hfact_pos : (0 : ℝ) < ((m + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [abs_of_pos hfact_pos]
  rw [abs_pow]
  have hbound := hM ξ hξ_ab
  have hxc_ne : x - c ≠ 0 := by linarith
  have h_pow_fact_pos : 0 < |x - c| ^ (m + 1) / (m + 1).factorial := by
    apply div_pos
    · apply pow_pos; exact abs_pos.mpr hxc_ne
    · exact hfact_pos
  calc |iteratedDeriv (m + 1) f ξ| * |x - c| ^ (m + 1) / ↑(m + 1).factorial
      = |iteratedDeriv (m + 1) f ξ| * (|x - c| ^ (m + 1) / ↑(m + 1).factorial) := by ring
    _ ≤ M * (|x - c| ^ (m + 1) / ↑(m + 1).factorial) := by
        apply mul_le_mul_of_nonneg_right hbound (le_of_lt h_pow_fact_pos)
    _ = M * |x - c| ^ (m + 1) / ↑(m + 1).factorial := by ring
/-- Lagrange form remainder bound for Taylor approximation.

If `|f^(n)(x)| ≤ M` for all x in [a, b], and `c ∈ [a, b]`, then the Taylor polynomial
of degree `n-1` (sum over range n) satisfies: for any `x ∈ [a, b]`:
  `|f(x) - T_{n-1}(x; c)| ≤ M * |x - c|^n / n!`

Note: The sum `∑ i ∈ Finset.range n` gives terms 0..n-1 (degree n-1 polynomial).
The remainder involves the n-th derivative, matching our bound on `iteratedDeriv n f`.

All cases are fully proved:
- **Case n = 0**: Direct bound. ✓
- **Case n > 0, x = c**: Trivial (both sides zero). ✓
- **Case n > 0, c < x**: Via `taylor_remainder_bound_c_lt_x`. ✓
- **Case n > 0, x < c**: Via `taylor_remainder_bound_x_lt_c` (reflection). ✓
-/
theorem taylor_remainder_bound {f : ℝ → ℝ} {a b c : ℝ} {n : ℕ} {M : ℝ}
    (_hab : a ≤ b) (hca : a ≤ c) (hcb : c ≤ b)
    (hf : ContDiff ℝ n f)
    (hM : ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n f x‖ ≤ M)
    (_hMnonneg : 0 ≤ M) :
    ∀ x ∈ Set.Icc a b,
      ‖f x - ∑ i ∈ Finset.range n, (iteratedDeriv i f c / i.factorial) * (x - c) ^ i‖
        ≤ M * |x - c| ^ n / n.factorial := by
  open Set Finset in
  intro x hx
  cases n with
  | zero =>
    -- Case n = 0: sum is empty, need ‖f x‖ ≤ M
    simp only [range_zero, sum_empty, sub_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_zero, mul_one]
    have h : f = iteratedDeriv 0 f := iteratedDeriv_zero.symm
    rw [h]
    exact hM x hx
  | succ m =>
    by_cases hxc : x = c
    · -- Case x = c: both sides are 0
      have hrhs : M * |x - c| ^ (m + 1) / ↑(m + 1).factorial = 0 := by
        rw [hxc, sub_self, abs_zero, zero_pow (Nat.succ_ne_zero m), mul_zero, zero_div]
      rw [hrhs]
      have hsum : ∑ i ∈ range (m + 1), (iteratedDeriv i f c / i.factorial) * (x - c) ^ i = f c := by
        rw [hxc]
        simp only [sub_self]
        rw [sum_eq_single 0]
        · simp [iteratedDeriv_zero]
        · intro i _ hi
          have hpos : 0 < i := Nat.pos_of_ne_zero hi
          have : (0 : ℝ) ^ i = 0 := zero_pow hpos.ne'
          simp [this]
        · simp
      rw [hsum, hxc, sub_self, norm_zero]
    · -- Case x ≠ c
      rcases lt_or_gt_of_ne hxc with hxc_lt | hcx_lt
      · -- Case x < c: use reflection approach
        exact taylor_remainder_bound_x_lt_c hcb hf hM x hx hxc_lt
      · -- Case c < x: fully proved
        exact taylor_remainder_bound_c_lt_x hca hf hM x hx hcx_lt

/-! ### Common Taylor expansions -/

/-- Taylor coefficients for exp at 0: 1/n! -/
def expTaylorCoeff (n : ℕ) : ℚ := 1 / n.factorial

/-- Taylor coefficients for sin at 0 -/
def sinTaylorCoeff (n : ℕ) : ℚ :=
  if n % 2 = 0 then 0
  else if (n / 2) % 2 = 0 then 1 / n.factorial
  else -1 / n.factorial

/-- Taylor coefficients for cos at 0 -/
def cosTaylorCoeff (n : ℕ) : ℚ :=
  if n % 2 = 1 then 0
  else if (n / 2) % 2 = 0 then 1 / n.factorial
  else -1 / n.factorial

/-! ### Derivative bounds for common functions -/

/-- All derivatives of exp are bounded by exp on any bounded interval -/
theorem exp_deriv_bound {a b : ℝ} (_hab : a ≤ b) (n : ℕ) :
    ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n Real.exp x‖ ≤ Real.exp b := by
  intro x hx
  rw [iteratedDeriv_eq_iterate]
  rw [Real.iter_deriv_exp]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  exact Real.exp_le_exp.mpr hx.2

/-- All derivatives of sin and cos are bounded by 1.
    The derivatives cycle: sin → cos → -sin → -cos → sin → ... -/
theorem sin_cos_deriv_bound (n : ℕ) :
    ∀ x : ℝ, ‖iteratedDeriv n Real.sin x‖ ≤ 1 ∧ ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
  intro x
  -- Prove by induction that both bounds hold together
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact ⟨Real.abs_sin_le_one x, Real.abs_cos_le_one x⟩
  | succ n ih =>
    constructor
    · -- sin case: d/dx sin = cos
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.sin = Real.cos := Real.deriv_sin
      rw [hderiv]
      exact ih.2
    · -- cos case: d/dx cos = -sin
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.cos = fun y => -Real.sin y := Real.deriv_cos'
      rw [hderiv]
      rw [iteratedDeriv_fun_neg n Real.sin x, norm_neg]
      exact ih.1

/-- cosh x ≤ exp |x| for all x -/
theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have habs_neg : -x ≤ |x| := neg_le_abs x
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr habs_neg
  linarith

/-- |sinh x| ≤ cosh x for all x -/
theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hcosh_sq : Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1 := Real.cosh_sq x
  have hsinh_sq_le : Real.sinh x ^ 2 ≤ Real.cosh x ^ 2 := by linarith [sq_nonneg (Real.cosh x)]
  rw [abs_le]
  constructor
  · -- -cosh x ≤ sinh x
    have h : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    nlinarith [sq_nonneg (Real.cosh x + Real.sinh x), sq_nonneg (Real.cosh x - Real.sinh x)]
  · -- sinh x ≤ cosh x
    have h : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
    nlinarith [sq_nonneg (Real.cosh x + Real.sinh x), sq_nonneg (Real.cosh x - Real.sinh x)]

/-- All derivatives of sinh and cosh are bounded by exp(max(|a|, |b|)) on [a, b].
    The derivatives cycle: sinh → cosh → sinh → cosh → ... -/
theorem sinh_cosh_deriv_bound {a b : ℝ} (_hab : a ≤ b) (n : ℕ) :
    ∀ x ∈ Set.Icc a b, ‖iteratedDeriv n Real.sinh x‖ ≤ Real.exp (max (|a|) (|b|)) ∧
                       ‖iteratedDeriv n Real.cosh x‖ ≤ Real.exp (max (|a|) (|b|)) := by
  intro x hx
  set M := Real.exp (max (|a|) (|b|)) with hM_def
  have habs_x_le : |x| ≤ max (|a|) (|b|) := by
    rw [abs_le]
    constructor
    · calc -max (|a|) (|b|) ≤ -|a| := neg_le_neg (le_max_left _ _)
        _ ≤ a := neg_abs_le a
        _ ≤ x := hx.1
    · calc x ≤ b := hx.2
        _ ≤ |b| := le_abs_self b
        _ ≤ max (|a|) (|b|) := le_max_right _ _
  have hcosh_bound : Real.cosh x ≤ M := by
    calc Real.cosh x ≤ Real.exp |x| := cosh_le_exp_abs x
      _ ≤ Real.exp (max (|a|) (|b|)) := Real.exp_le_exp.mpr habs_x_le
  have hsinh_bound : |Real.sinh x| ≤ M := by
    calc |Real.sinh x| ≤ Real.cosh x := abs_sinh_le_cosh x
      _ ≤ M := hcosh_bound
  -- Prove by induction that both bounds hold
  induction n with
  | zero =>
    simp only [iteratedDeriv_zero, Real.norm_eq_abs]
    exact ⟨hsinh_bound, by rw [abs_of_pos (Real.cosh_pos x)]; exact hcosh_bound⟩
  | succ n ih =>
    constructor
    · -- sinh case: d/dx sinh = cosh
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.sinh = Real.cosh := by
        funext x
        exact LeanCert.Core.DerivativeIntervals.sinh_deriv_eq x
      rw [hderiv]
      exact ih.2
    · -- cosh case: d/dx cosh = sinh
      rw [iteratedDeriv_succ']
      have hderiv : deriv Real.cosh = Real.sinh := Real.deriv_cosh
      rw [hderiv]
      exact ih.1

/- The n-th iterated derivative of log at x > 0 is (-1)^(n-1) * (n-1)! * x^(-n) for n ≥ 1. -/
theorem iteratedDeriv_log {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n Real.log x = (-1)^(n-1) * (n-1).factorial * x^(-(n : ℤ)) := by
    match n with
    | 1 =>
      -- n = 1: iteratedDeriv 1 log x = deriv log x = 1/x = x^(-1)
      simp only [iteratedDeriv_one, Real.deriv_log', tsub_self, pow_zero, Nat.factorial_zero,
        Nat.cast_one, mul_one, Int.reduceNeg, zpow_neg, zpow_one, one_mul]
    | n + 2 =>
      -- n + 2: use induction
      -- iteratedDeriv (n+2) log = deriv (iteratedDeriv (n+1) log)
      rw [iteratedDeriv_succ]
      -- By IH: iteratedDeriv (n+1) log y = (-1)^n * n! * y^(-(n+1)) for y > 0
      have h_eq : ∀ y : ℝ, 0 < y → iteratedDeriv (n + 1) Real.log y =
          (-1 : ℝ)^n * n.factorial * y^(-(n + 1 : ℤ)) := fun y hy => iteratedDeriv_log
            n.succ_ne_zero hy
      have h_deriv_eq : deriv (iteratedDeriv (n + 1) Real.log) x =
          deriv (fun y => (-1 : ℝ)^n * n.factorial * y^(-(n + 1 : ℤ))) x := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [eventually_gt_nhds hx] with y hy
        exact h_eq y hy
      rw [h_deriv_eq]
      have hdiff : DifferentiableAt ℝ (fun y => y ^ (-(n + 1 : ℤ))) x := by
        apply DifferentiableAt.zpow differentiableAt_id
        left; exact hx.ne'
      rw [deriv_const_mul _ hdiff, deriv_zpow (-(n + 1 : ℤ)) x]
      simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
        Int.cast_natCast, Nat.add_one_sub_one, Nat.cast_add, Nat.cast_ofNat]
      rw [pow_succ (-1 : ℝ) n, Nat.factorial_succ]
      push_cast
      calc
        (-1) ^ n * n.factorial * ((-1 + -(n : ℤ)) * x ^ (-1 + -(n : ℤ) - 1))
        _ = (-1) ^ n * n.factorial * ((-1 + -(n : ℤ)) * x ^ (-2 + -(n : ℤ))) := by congr 3; grind
        _ = (-1) ^ n * -1 * ((↑n + 1) * n.factorial) * x ^ (-2 + -(n : ℤ)) := by simp; ring

end LeanCert.Core
