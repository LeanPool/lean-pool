/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Semilocal rings have stable range one

In a commutative ring with finitely many maximal ideals, if `a` and `b` are coprime then
`a + t * b` is a unit for some `t`. The element `t` is chosen by the Chinese remainder theorem,
maximal ideal by maximal ideal.

## Main statements

* `IsCoprime.exists_isUnit_add_mul`: a semilocal ring has stable range one.
-/

public section

variable {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]

/-- A semilocal ring has stable range one: if `a` and `b` are coprime, then `a + t * b` is a
unit for some `t`. This is due to Bass, see [Bass, *K-theory and stable algebra*][bass1964]. -/
theorem IsCoprime.exists_isUnit_add_mul {a b : R} (h : IsCoprime a b) :
    ∃ t : R, IsUnit (a + t * b) := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum R ↦ m.asIdeal) :=
    fun m n hmn ↦ Ideal.isCoprime_of_isMaximal fun e ↦ hmn (MaximalSpectrum.ext e)
  -- modulo `m`, take `t = 0` if `b ∈ m`, and `t = b⁻¹ (1 - a)` otherwise
  let x : MaximalSpectrum R → R := fun m ↦
    if hb : b ∈ m.asIdeal then 0 else (m.isMaximal.exists_inv hb).choose * (1 - a)
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hcop x
  refine ⟨t, by_contra fun hu ↦ ?_⟩
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  have htm := ht ⟨m, hm⟩
  obtain ⟨u, v, huv⟩ := h
  refine hm.ne_top <| (Ideal.eq_top_iff_one _).2 ?_
  by_cases hb : b ∈ m
  · simp only [x, hb, ↓reduceDIte, sub_zero] at htm
    have ha : a ∈ m := by simpa using m.sub_mem hmem (m.mul_mem_left t hb)
    rw [← huv]
    exact m.add_mem (m.mul_mem_left _ ha) (m.mul_mem_left _ hb)
  · obtain ⟨k, hk, hy⟩ := (hm.exists_inv hb).choose_spec
    simp only [x, hb, ↓reduceDIte] at htm
    have e : (1 : R) = (a + t * b) - (t - (hm.exists_inv hb).choose * (1 - a)) * b +
        (1 - a) * k := by
      linear_combination (-(1 - a)) * hy
    rw [e]
    exact m.add_mem (m.sub_mem hmem (m.mul_mem_right _ htm)) (m.mul_mem_left _ hk)
