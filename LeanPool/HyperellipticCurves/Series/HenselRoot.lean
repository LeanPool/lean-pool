/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Series.PSeries
public import Mathlib.RingTheory.Henselian

import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Identities

/-!
# Hensel roots in a complete local ring

A complete local ring `O` (adically complete at its maximal ideal) is Henselian
(`ChabautyColeman.instHenselianLocalRing`), so `Mathlib`'s `HenselianLocalRing.is_henselian`
lifts simple approximate roots of *monic* polynomials. We add the missing **uniqueness**
(`ChabautyColeman.hensel_unique`) and a **non-monic (smooth)** existence result
(`ChabautyColeman.exists_smooth_root`, by Newton iteration): for any `g` with `g(a₀) ∈ 𝔪` and
`g'(a₀)` a unit there is a root `x ≡ a₀`. Together these give the Weierstrass-disk root
`ChabautyColeman.exists_weierstrass_root`: for `y ∈ 𝔪`, a unique `x ≡ ω` with `f(x) = y²`, when
`f(ω) = 0` and `f'(ω)` is a unit — the implicit-function step of the disk charts.

## Main statements

* `ChabautyColeman.hensel_unique`: uniqueness of a simple root modulo `𝔪`.
* `ChabautyColeman.exists_smooth_root`: existence of a root of a non-monic `g` with `g'(a₀)` a
  unit — the smooth Hensel lemma (needed for the infinity chart's non-monic equation).
* `ChabautyColeman.exists_weierstrass_root`: existence of the Weierstrass-disk root of `f = y²`.
* `ChabautyColeman.exists_lift_curve_point`: a point of the residue curve with nonzero
  `y`-coordinate lifts to a point over `O`.
* `ChabautyColeman.exists_sq_eq_of_sub_one_mem`: an element congruent to `1` modulo `𝔪` is a
  square.

Blueprint node: `thm:hensel` (series/implicit-function form for `lem:disk-param`).
-/

@[expose] public section

open IsLocalRing Polynomial

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

variable [IsLocalRing O]

/-- **Hensel uniqueness**: if `x` and `x'` are congruent modulo `𝔪`, `f'(x')` is a unit, and
`f(x) = f(x')`, then `x = x'`. In particular a simple root modulo `𝔪` is unique. -/
theorem hensel_unique {f : O[X]} {x x' : O} (hxx : x - x' ∈ maximalIdeal O)
    (hu : IsUnit (f.derivative.eval x')) (heq : f.eval x = f.eval x') : x = x' := by
  set q := ((taylor x' f).divX).eval (x - x') with hqdef
  have key : f.eval x - f.eval x' = q * (x - x') := by
    have h3 := congrArg (Polynomial.eval (x - x')) (Polynomial.divX_mul_X_add (taylor x' f))
    simp only [eval_add, eval_mul, eval_X, eval_C] at h3
    rw [taylor_coeff_zero, taylor_eval, show (x - x') + x' = x by ring, ← hqdef] at h3
    rw [← h3]; ring
  have hmem : q - f.derivative.eval x' ∈ maximalIdeal O := by
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub (x - x') 0 ((taylor x' f).divX)
    rw [sub_zero, ← hqdef, ← coeff_zero_eq_eval_zero, coeff_divX, taylor_coeff_one] at hc
    rw [hc]; exact Ideal.mul_mem_right c _ hxx
  have hqu : IsUnit q :=
    notMem_maximalIdeal.mp fun hqmem ↦
      (notMem_maximalIdeal.mpr hu) (by simpa using sub_mem hqmem hmem)
  exact sub_eq_zero.mp ((IsUnit.mul_right_eq_zero hqu).mp (by rw [← key, heq, sub_self]))

/-- **Fixed-slope Newton contraction step.** If `g(b) ∈ 𝔪 ^ k` with `k ≥ 1` and the slope
approximation satisfies `1 - c · g'(b) ∈ 𝔪`, then the Newton update `b - c · g(b)` improves the
approximation to `g(b - c · g(b)) ∈ 𝔪 ^ (k+1)`: the quadratic Taylor remainder lands in
`𝔪 ^ (2k) ⊆ 𝔪 ^ (k+1)` and the linear part factors as `g(b) · (1 - c · g'(b))`. -/
theorem eval_newton_step_mem {g : O[X]} {b c : O} {k : ℕ} (hk : 1 ≤ k)
    (hb : g.eval b ∈ maximalIdeal O ^ k)
    (hslope : 1 - c * g.derivative.eval b ∈ maximalIdeal O) :
    g.eval (b - c * g.eval b) ∈ maximalIdeal O ^ (k + 1) := by
  set δ := -(c * g.eval b) with hδ
  have hδmem : δ ∈ maximalIdeal O ^ k := neg_mem (Ideal.mul_mem_left _ _ hb)
  obtain ⟨r, hr⟩ := g.binomExpansion b δ
  rw [show b - c * g.eval b = b + δ by rw [hδ]; ring, hr,
    show g.eval b + g.derivative.eval b * δ = g.eval b * (1 - c * g.derivative.eval b) from
      by rw [hδ]; ring]
  have hlin : g.eval b * (1 - c * g.derivative.eval b) ∈ maximalIdeal O ^ (k + 1) := by
    rw [pow_succ]; exact Ideal.mul_mem_mul hb hslope
  have h2k : δ ^ 2 ∈ maximalIdeal O ^ (2 * k) := by
    rw [sq, two_mul, pow_add]; exact Ideal.mul_mem_mul hδmem hδmem
  exact add_mem hlin (Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by lia) h2k))

section smooth

variable [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O]

/-- **Univariate smooth Hensel** (non-monic): if `g(a₀) ∈ 𝔪` and `g'(a₀)` is a unit, then `g`
has a root congruent to `a₀` modulo `𝔪`. Proved by Newton iteration with fixed slope; the
increments lie in increasing powers of `𝔪` and converge by completeness. (Uniqueness is
`hensel_unique`.) -/
theorem exists_smooth_root {g : O[X]} {a₀ : O} (h0 : g.eval a₀ ∈ maximalIdeal O)
    (hu : IsUnit (g.derivative.eval a₀)) :
    ∃ x, g.eval x = 0 ∧ x - a₀ ∈ maximalIdeal O := by
  set c := Ring.inverse (g.derivative.eval a₀)
  have hcu : c * g.derivative.eval a₀ = 1 := Ring.inverse_mul_cancel _ hu
  set b : ℕ → O := fun n ↦ Nat.rec a₀ (fun _ bn ↦ bn - c * g.eval bn) n
  have hbs : ∀ n, b (n + 1) = b n - c * g.eval (b n) := fun _ ↦ rfl
  have hb0 : b 0 = a₀ := rfl
  have hstep k (hk : g.eval (b k) ∈ maximalIdeal O ^ (k + 1)) :
      b (k + 1) - b k ∈ maximalIdeal O ^ (k + 1) := by
    rw [hbs, show b k - c * g.eval (b k) - b k = -(c * g.eval (b k)) by ring]
    exact neg_mem (Ideal.mul_mem_left _ _ hk)
  have hinv : ∀ n, g.eval (b n) ∈ maximalIdeal O ^ (n + 1) ∧ b n - a₀ ∈ maximalIdeal O := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hb0, zero_add, pow_one]; exact h0
      · rw [hb0, sub_self]; exact (maximalIdeal O).zero_mem
    | succ n ih =>
      obtain ⟨hgn, hbn⟩ := ih
      have hbn1 : b (n + 1) - a₀ ∈ maximalIdeal O :=
        (show b (n + 1) - a₀ = (b (n + 1) - b n) + (b n - a₀) by ring) ▸
          add_mem (Ideal.pow_le_self (Nat.succ_ne_zero n) (hstep n hgn)) hbn
      refine ⟨?_, hbn1⟩
      have hderiv : g.derivative.eval (b n) - g.derivative.eval a₀ ∈ maximalIdeal O := by
        obtain ⟨q, hq⟩ := sub_dvd_eval_sub (b n) a₀ g.derivative
        rw [hq]; exact Ideal.mul_mem_right q _ hbn
      have hm1 : 1 - c * g.derivative.eval (b n) ∈ maximalIdeal O := by
        have he : 1 - c * g.derivative.eval (b n)
            = c * (g.derivative.eval a₀ - g.derivative.eval (b n)) := by linear_combination -hcu
        rw [he]
        exact Ideal.mul_mem_left _ _ (by rw [← neg_sub]; exact neg_mem hderiv)
      rw [hbs]
      exact eval_newton_step_mem (by lia) hgn hm1
  have hincr k : b (k + 1) - b k ∈ maximalIdeal O ^ (k + 1) := hstep k (hinv k).1
  obtain ⟨z, hz0, hzn⟩ :=
    PSeries.exists_limit_of_sub_mem_pow (fun n (_ : Unit) ↦ b n) (fun k _ ↦ hincr k)
  refine ⟨z (), PSeries.eq_zero_of_forall_mem_pow _ fun n ↦ ?_, hz0 ()⟩
  have hgz : g.eval (z ()) - g.eval (b n) ∈ maximalIdeal O ^ n := by
    obtain ⟨q, hq⟩ := sub_dvd_eval_sub (z ()) (b n) g
    rw [hq]; exact Ideal.mul_mem_right q _ (hzn n ())
  rw [show g.eval (z ()) = (g.eval (z ()) - g.eval (b n)) + g.eval (b n) by ring]
  exact add_mem hgz (Ideal.pow_le_pow_right (by lia) (hinv n).1)

/-- **Lifting a non-Weierstrass point from the residue field**: a point of the reduced curve
with invertible `y`-coordinate is the reduction of a point of the curve over `O`. -/
theorem exists_lift_curve_point {f : O[X]} (h2 : IsUnit (2 : O)) {x' y' : ResidueField O}
    (hy : y' ^ 2 = (f.map (residue O)).eval x') (hy0 : y' ≠ 0) :
    ∃ x y : O, y ^ 2 = f.eval x ∧ residue O x = x' ∧ residue O y = y' := by
  obtain ⟨x, rfl⟩ := residue_surjective x'
  obtain ⟨y₀, rfl⟩ := residue_surjective y'
  have hy0' : IsUnit y₀ := (residue_ne_zero_iff_isUnit _).mp hy0
  obtain ⟨y, hroot, hcong⟩ := exists_smooth_root (g := X ^ 2 - C (f.eval x)) (a₀ := y₀)
    ((residue_eq_zero_iff _).mp (by
      simp only [eval_sub, eval_pow, eval_X, eval_C, map_sub, map_pow, sub_eq_zero]
      exact hy.trans (eval_map_apply _ _)))
    (by
      simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
        eval_X, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      exact h2.mul hy0')
  refine ⟨x, y, by simpa [sub_eq_zero] using hroot, rfl, ?_⟩
  exact residue_eq_of_sub_mem hcong

end smooth

variable [IsAdicComplete (maximalIdeal O) O]

/-- A complete local ring is Henselian. -/
instance instHenselianLocalRing : HenselianLocalRing O where
  is_henselian f hf a₀ h₁ h₂ :=
    (inferInstance : HenselianRing O (maximalIdeal O)).is_henselian f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk _))

/-- The Weierstrass-disk root: for `y ∈ 𝔪`, a root `x ≡ ω` of `f(X) = y²`, existing since
`f(ω) = 0` (so `f(ω) - y² ∈ 𝔪`) and `f'(ω)` is a unit. Uniqueness is `hensel_unique`. -/
theorem exists_weierstrass_root {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) {y : O} (hy : y ∈ maximalIdeal O) :
    ∃ x, f.eval x = y ^ 2 ∧ x - ω ∈ maximalIdeal O := by
  have hmon : (f - C (y ^ 2)).Monic := hf.sub_of_left <|
    degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hdeg)
  obtain ⟨x, hx1, hx2⟩ := HenselianLocalRing.is_henselian (f - C (y ^ 2)) hmon ω
    (by rw [eval_sub, eval_C, hω, zero_sub]
        exact neg_mem (Ideal.pow_mem_of_mem _ hy 2 (by norm_num)))
    (by rwa [derivative_sub, derivative_C, sub_zero])
  rw [IsRoot, eval_sub, eval_C, sub_eq_zero] at hx1
  exact ⟨x, hx1, hx2⟩

/-- **Square roots in a complete local ring**: an element congruent to `1` modulo the maximal
ideal is a square, in residue characteristic `≠ 2`. Hensel's lemma for `X ^ 2 - c` at the
approximate root `1`. -/
theorem exists_sq_eq_of_sub_one_mem (h2 : IsUnit (2 : O)) {c : O}
    (hc : c - 1 ∈ maximalIdeal O) :
    ∃ d : O, d ^ 2 = c ∧ d - 1 ∈ maximalIdeal O := by
  obtain ⟨d, hd1, hd2⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C c)
    (monic_X_pow_sub_C c two_ne_zero) 1 (by simpa using neg_mem hc)
    (by
      simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
        eval_pow, eval_X, one_pow, mul_one, Nat.cast_ofNat]
      exact h2)
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hd1
  exact ⟨d, hd1, hd2⟩

end ChabautyColeman

end
