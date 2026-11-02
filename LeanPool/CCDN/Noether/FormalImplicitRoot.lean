/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.Basic
import LeanPool.CCDN.ForMathlib.Polynomial
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal

/-! A simple root over the constant field lifts to a formal power
series root. Newton iteration and coefficient stabilization prove existence. -/

@[expose] public section
namespace CCDN
noncomputable section

private def formalNewtonSequence {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b u : K) : ℕ → PowerSeries K
  | 0 => PowerSeries.C b
  | n + 1 => formalNewtonSequence f b u n - PowerSeries.C u * f.eval (formalNewtonSequence f b u n)

private lemma formalNewton_step {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b u : K)
    (hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1)
    (g : PowerSeries K) (hg : PowerSeries.constantCoeff g = b)
    {k : ℕ} (hk : 1 ≤ k) (hfg : PowerSeries.X ^ k ∣ f.eval g) :
    PowerSeries.X ^ (k + 1) ∣ f.eval (g - PowerSeries.C u * f.eval g) := by
  let g' := g - PowerSeries.C u * f.eval g
  have hXf : (PowerSeries.X : PowerSeries K) ∣ f.eval g := by
    simpa only [pow_one] using (pow_dvd_pow PowerSeries.X hk).trans hfg
  have hXdiff : (PowerSeries.X : PowerSeries K) ∣ g' - g := by
    have hh := dvd_mul_of_dvd_right hXf (PowerSeries.C u)
    convert dvd_neg.mpr hh using 1
    dsimp [g']
    ring
  obtain ⟨q, he, hq⟩ := Polynomial.exists_divided_difference f g' g
  have hqder : (PowerSeries.X : PowerSeries K) ∣ q - f.derivative.eval g := hXdiff.trans hq
  have hbase : (PowerSeries.X : PowerSeries K) ∣ 1 - PowerSeries.C u * f.derivative.eval g := by
    apply PowerSeries.X_dvd_iff.mpr
    simp only [map_sub, map_one, map_mul, PowerSeries.constantCoeff_C,
      ← Polynomial.eval_map_apply, hg, hu, sub_self]
  have hbracket : (PowerSeries.X : PowerSeries K) ∣ 1 - PowerSeries.C u * q := by
    have hh := dvd_mul_of_dvd_left hqder (PowerSeries.C u)
    convert dvd_sub hbase hh using 1
    ring
  have heq : f.eval g' = f.eval g * (1 - PowerSeries.C u * q) := by
    dsimp only [g'] at he
    linear_combination he
  rw [heq, pow_succ]
  exact mul_dvd_mul hfg hbracket

private lemma formalNewton_precision {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b u : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1) (n : ℕ) :
    PowerSeries.constantCoeff (formalNewtonSequence f b u n) = b ∧
      PowerSeries.X ^ (n + 1) ∣ f.eval (formalNewtonSequence f b u n) := by
  induction n with
  | zero =>
      refine ⟨by simp [formalNewtonSequence], ?_⟩
      rw [show (0 : ℕ) + 1 = 1 by omega, pow_one]
      apply PowerSeries.X_dvd_iff.mpr
      simp only [formalNewtonSequence, ← Polynomial.eval_map_apply, PowerSeries.constantCoeff_C,
        hroot]
  | succ n ih =>
      refine ⟨?_, formalNewton_step f b u hu _ ih.1 (by omega) ih.2⟩
      simp only [formalNewtonSequence, map_sub, map_mul, PowerSeries.constantCoeff_C,
        ← Polynomial.eval_map_apply, ih.1, hroot, mul_zero, sub_zero]

private lemma formalNewton_stabilizes {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b u : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1)
    {n m : ℕ} (hnm : n ≤ m) :
    PowerSeries.X ^ (n + 1) ∣ formalNewtonSequence f b u m - formalNewtonSequence f b u n := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
      have hprec := (formalNewton_precision f b u hroot hu m).2
      have hd := (pow_dvd_pow (PowerSeries.X : PowerSeries K) (Nat.add_le_add_right hnm 1)).trans
        hprec
      have hh := dvd_mul_of_dvd_right hd (PowerSeries.C u)
      convert dvd_sub ih hh using 1
      simp only [formalNewtonSequence]
      ring

/-- Every simple root of the constant polynomial lifts to a formal root. -/
theorem exists_formal_simple_root {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b : K)
    (hroot : (f.map PowerSeries.constantCoeff).eval b = 0)
    (hder : (f.derivative.map PowerSeries.constantCoeff).eval b ≠ 0) :
    ∃ g : PowerSeries K, PowerSeries.constantCoeff g = b ∧ f.eval g = 0 := by
  let u := ((f.derivative.map PowerSeries.constantCoeff).eval b)⁻¹
  have hu : u * (f.derivative.map PowerSeries.constantCoeff).eval b = 1 := inv_mul_cancel₀ hder
  let g := PowerSeries.mk (fun n => PowerSeries.coeff n (formalNewtonSequence f b u n))
  have happrox (n : ℕ) : PowerSeries.X ^ (n + 1) ∣ g - formalNewtonSequence f b u n := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro j hj
    have hh := formalNewton_stabilizes f b u hroot hu (show j ≤ n by omega)
    have hc := PowerSeries.X_pow_dvd_iff.mp hh j (by omega)
    simp only [map_sub] at hc ⊢
    dsimp only [g]
    rw [PowerSeries.coeff_mk]
    exact sub_eq_zero.mpr (sub_eq_zero.mp hc).symm
  refine ⟨g, ?_, ?_⟩
  · have hh := happrox 0
    simp only [zero_add, pow_one] at hh
    have hc := PowerSeries.X_dvd_iff.mp hh
    simpa only [map_sub, formalNewtonSequence, PowerSeries.constantCoeff_C, sub_eq_zero] using hc
  · apply PowerSeries.ext
    intro n
    have hdiff := (happrox n).trans (Polynomial.sub_dvd_eval_sub g (formalNewtonSequence f b u n) f)
    have hprec := (formalNewton_precision f b u hroot hu n).2
    have hh : PowerSeries.X ^ (n + 1) ∣ f.eval g := by
      convert dvd_add hdiff hprec using 1
      ring
    have hc := PowerSeries.X_pow_dvd_iff.mp hh n (by omega)
    simpa only [map_zero] using hc

/-- The simple formal branch is unique among roots with the chosen constant. -/
theorem formal_simple_root_unique {K : Type*} [Field K]
    (f : Polynomial (PowerSeries K)) (b : K)
    (hder : (f.derivative.map PowerSeries.constantCoeff).eval b ≠ 0)
    {g h : PowerSeries K} (hg : PowerSeries.constantCoeff g = b)
    (hh : PowerSeries.constantCoeff h = b) (hfg : f.eval g = 0) (hfh : f.eval h = 0) : g = h := by
  obtain ⟨q, he, hq⟩ := Polynomial.exists_divided_difference f g h
  have hX : (PowerSeries.X : PowerSeries K) ∣ g - h := PowerSeries.X_dvd_iff.mpr (by simp [hg, hh])
  have hc := PowerSeries.X_dvd_iff.mp (hX.trans hq)
  simp only [map_sub, ← Polynomial.eval_map_apply, hh, sub_eq_zero] at hc
  have hq0 : q ≠ 0 := by
    intro hz
    apply hder
    simpa only [hz, map_zero] using hc.symm
  rw [hfg, hfh, sub_self] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hq0)

end
end CCDN
