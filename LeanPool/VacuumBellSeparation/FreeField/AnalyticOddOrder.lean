/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The odd-order obstruction in the source injectivity argument

An analytic square cannot equal a coefficient with an odd-order zero times
another nonzero analytic square. The massive one-variable polynomial has a
simple zero at `i M`, so entire `F,G` satisfying the manuscript's squared
Fourier relation must vanish. This is the scalar analytic step.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace VacuumBellSeparation

/-- The parity obstruction for analytic functions, where the order is defined. -/
theorem analytic_square_odd_order_locally_zero {f g q : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hq : AnalyticAt ℂ q z)
    (horder : analyticOrderAt q z = (2 * n + 1 : ℕ))
    (hrel : (f ^ 2) =ᶠ[𝓝 z] q * (g ^ 2)) :
    (∀ᶠ w in 𝓝 z, f w = 0) ∧ (∀ᶠ w in 𝓝 z, g w = 0) := by
  have hord := analyticOrderAt_congr hrel
  rw [analyticOrderAt_pow hf, analyticOrderAt_mul hq (hg.pow 2),
    analyticOrderAt_pow hg, horder] at hord
  have hgTop : analyticOrderAt g z = ⊤ := by
    by_contra hgTop
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hgTop
    have hfTop : analyticOrderAt f z ≠ ⊤ := by
      intro h
      simp only [h, nsmul_eq_mul, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, ENat.mul_top, Nat.cast_add, Nat.cast_mul, Nat.cast_one, ← hb] at hord
      exact ENat.top_ne_natCast (2 * n + 1 + 2 * b) (by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hord)
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfTop
    rw [← ha, ← hb] at hord
    simp only [nsmul_eq_mul] at hord
    have hnat : 2 * a = (2 * n + 1) + 2 * b := by exact_mod_cast hord
    omega
  have hgloc := analyticOrderAt_eq_top.mp hgTop
  refine ⟨?_, hgloc⟩
  filter_upwards [hrel, hgloc] with w hw hgw
  have hw' : f w ^ 2 = 0 := by simpa [hgw] using hw
  exact eq_zero_of_pow_eq_zero hw'

/-- On the complex plane, local zero germs extend to global zero functions. -/
theorem entire_square_odd_order_zero {f g q : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hq : AnalyticAt ℂ q z) (horder : analyticOrderAt q z = (2 * n + 1 : ℕ))
    (hrel : (f ^ 2) =ᶠ[𝓝 z] q * (g ^ 2)) : f = 0 ∧ g = 0 := by
  obtain ⟨hf0, hg0⟩ := analytic_square_odd_order_locally_zero
    (hf z (mem_univ z)) (hg z (mem_univ z)) hq horder hrel
  exact ⟨hf.eq_of_eventuallyEq analyticOnNhd_const hf0,
    hg.eq_of_eventuallyEq analyticOnNhd_const hg0⟩

/-- The massive polynomial has the simple nonreal branch zero used in Section 2.2. -/
theorem massive_polynomial_analyticOrder {M : ℝ} (hM : 0 < M) :
    analyticOrderAt (fun z : ℂ => -(z ^ 2 + (M : ℂ) ^ 2)) (Complex.I * (M : ℂ)) = 1 := by
  have ha : AnalyticAt ℂ (fun z : ℂ => -(z ^ 2 + (M : ℂ) ^ 2))
      (Complex.I * (M : ℂ)) := by fun_prop
  apply ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · rw [mul_pow, Complex.I_sq]
    ring
  · have hd : HasDerivAt (fun z : ℂ => -(z ^ 2 + (M : ℂ) ^ 2))
        (-(2 * (Complex.I * (M : ℂ)))) (Complex.I * (M : ℂ)) := by
      convert! (((hasDerivAt_id' (x := Complex.I * (M : ℂ))).pow 2).add_const
        ((M : ℂ) ^ 2)).neg using 1; simp
    rw [hd.deriv]
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num)
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hM.ne')))

/-- Entire functions satisfying the squared massive Fourier relation vanish identically. -/
theorem entire_massive_square_zero {M : ℝ} (hM : 0 < M) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hrel : ∀ z : ℂ, f z ^ 2 = -(z ^ 2 + (M : ℂ) ^ 2) * g z ^ 2) :
    f = 0 ∧ g = 0 := by
  apply entire_square_odd_order_zero (n := 0)
    (q := fun z : ℂ => -(z ^ 2 + (M : ℂ) ^ 2))
    (z := Complex.I * (M : ℂ)) hf hg (by fun_prop)
    (by simpa using massive_polynomial_analyticOrder hM)
  exact Filter.Eventually.of_forall hrel

/-- Equality on the real axis determines an entire function, by a punctured sequence tending to
zero. -/
theorem entire_eq_of_real_eq {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hreal : ∀ x : ℝ, f (x : ℂ) = g (x : ℂ)) : f = g := by
  have ht0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero]
      using (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht0, Filter.Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity
  apply hf.eq_of_frequently_eq hg
  exact ht.frequently (Filter.Eventually.frequently
    (Filter.Eventually.of_forall fun n => hreal (1 / ((n : ℝ) + 1))))

/-- The scalar step of the manuscript's complex source-injectivity argument, starting on real
momenta. -/
theorem entire_massive_square_zero_of_real {M : ℝ} (hM : 0 < M) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hreal : ∀ x : ℝ, f (x : ℂ) ^ 2 =
      -((x : ℂ) ^ 2 + (M : ℂ) ^ 2) * g (x : ℂ) ^ 2) : f = 0 ∧ g = 0 := by
  have hq : AnalyticOnNhd ℂ (fun z : ℂ => -(z ^ 2 + (M : ℂ) ^ 2)) univ := by
    intro z _
    fun_prop
  have heq := entire_eq_of_real_eq (hf.pow 2) (hq.mul (hg.pow 2)) hreal
  exact entire_massive_square_zero hM hf hg (fun z => congrFun heq z)

end VacuumBellSeparation
