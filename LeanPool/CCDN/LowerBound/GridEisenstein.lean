/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp

/-! Explicit absolutely irreducible equations through a Cartesian grid.
The construction uses Eisenstein at the inner coordinate zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- A monic bivariate polynomial reducing to a pure power at the inner
coordinate zero is irreducible if its constant coefficient has a simple zero. -/
private theorem irreducible_of_bivariate_eisenstein {K : Type*} [Field K]
    (f : K[X][X]) (hm : f.Monic) (hd : 0 < f.natDegree)
    (hred : f.map (evalRingHom 0) = X ^ f.natDegree)
    (hsimple : (f.coeff 0).coeff 1 ≠ 0) : Irreducible f := by
  let P : Ideal K[X] := Ideal.span {X}
  have hp : P.IsPrime := Ideal.isPrime_span_singleton_of_prime prime_X
  apply Polynomial.IsEisensteinAt.irreducible (𝓟 := P) _ hp hm.isPrimitive hd
  refine ⟨hm.leadingCoeff_notMem hp.ne_top, ?_, ?_⟩
  · intro i hi
    apply Ideal.mem_span_singleton.mpr
    apply X_dvd_iff.mpr
    have he := congrArg (fun q : K[X] => q.coeff i) hred
    simpa [coeff_map, coeff_X_pow, ne_of_lt hi, ← coeff_zero_eq_eval_zero] using he
  · intro h
    change f.coeff 0 ∈ (Ideal.span ({X} : Set K[X])) ^ 2 at h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    exact hsimple ((X_pow_dvd_iff.mp h) 1 (by decide))

/-- The inner correction has prescribed degree and makes the first coefficient
of the constant outer coefficient nonzero. -/
def gridEisensteinCorrection {K : Type*} [Field K] (V : K[X]) (k : ℕ) : K[X] :=
  V * (X ^ k + C (V.coeff 1 / V.coeff 0 + 1) * X)

/-- The outer variable is the first coordinate, the inner variable the second.
At roots of V in both coordinates all three summands vanish. -/
def gridEisensteinPolynomial {K : Type*} [Field K] (V : K[X]) (k : ℕ) : K[X][X] :=
  V.map C + C (V * C (V.coeff 0)⁻¹) * (X ^ V.natDegree - V.map C) +
    C (gridEisensteinCorrection V k)

/-- The `i`-th coefficient of `gridEisensteinPolynomial V k` in the outer variable, written out from
its three summands. -/
lemma gridEisensteinPolynomial_coeff {K : Type*} [Field K]
    (V : K[X]) (k i : ℕ) :
    (gridEisensteinPolynomial V k).coeff i =
      C (V.coeff i) + V * C (V.coeff 0)⁻¹ *
        ((X ^ V.natDegree : K[X][X]).coeff i - C (V.coeff i)) +
      if i = 0 then gridEisensteinCorrection V k else 0 := by
  simp only [gridEisensteinPolynomial, coeff_add, coeff_map, coeff_C_mul, coeff_sub, coeff_C]

private lemma gridEisensteinPolynomial_natDegree_le {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) : (gridEisensteinPolynomial V k).natDegree ≤ V.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [gridEisensteinPolynomial_coeff]
  rw [ite_eq_right (by omega : i ≠ 0)]
  simp [coeff_eq_zero_of_natDegree_lt hi, coeff_X_pow, ne_of_gt hi]

private lemma gridEisensteinPolynomial_topCoeff {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree) :
    (gridEisensteinPolynomial V k).coeff V.natDegree = 1 := by
  rw [gridEisensteinPolynomial_coeff, hm.coeff_natDegree]
  simp [ne_of_gt hd]

private lemma gridEisensteinPolynomial_monic {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree) :
    (gridEisensteinPolynomial V k).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one V.natDegree
    (gridEisensteinPolynomial_natDegree_le V k)
    (gridEisensteinPolynomial_topCoeff V k hm hd)

private lemma gridEisensteinPolynomial_natDegree {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree) :
    (gridEisensteinPolynomial V k).natDegree = V.natDegree := by
  apply le_antisymm (gridEisensteinPolynomial_natDegree_le V k)
  apply le_natDegree_of_ne_zero
  rw [gridEisensteinPolynomial_topCoeff V k hm hd]
  exact one_ne_zero

private lemma gridEisensteinPolynomial_reduction {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (h0 : V.coeff 0 ≠ 0) (hk : 0 < k) :
    (gridEisensteinPolynomial V k).map (evalRingHom 0) = X ^ V.natDegree := by
  have he : (evalRingHom (0 : K)).comp C = RingHom.id K := by ext a; simp
  simp only [gridEisensteinPolynomial, gridEisensteinCorrection, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, map_map, he, map_id]
  simp [← coeff_zero_eq_eval_zero, h0, ne_of_gt hk]

private lemma gridEisensteinPolynomial_simple {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (h0 : V.coeff 0 ≠ 0)
    (hd : 0 < V.natDegree) (hk : 2 ≤ k) :
    ((gridEisensteinPolynomial V k).coeff 0).coeff 1 = V.coeff 0 := by
  have hc : (gridEisensteinPolynomial V k).coeff 0 =
      C (V.coeff 0) - V + gridEisensteinCorrection V k := by
    rw [gridEisensteinPolynomial_coeff]
    simp only [coeff_X_pow, ne_of_lt hd, ite_false, zero_sub, ite_true]
    rw [mul_neg, mul_assoc, ← C_mul, inv_mul_cancel₀ h0, C_1, mul_one]
    rfl
  rw [hc]
  simp only [gridEisensteinCorrection, mul_add, coeff_add, coeff_sub, coeff_C,
    one_ne_zero, ite_false, zero_sub]
  rw [coeff_mul_X_pow', ite_eq_right (by omega : ¬ k ≤ 1)]
  rw [← mul_assoc, coeff_mul_X, coeff_mul_C]
  field_simp
  ring

/-- Absolute irreducibility of the explicit construction, over every field. -/
theorem gridEisensteinPolynomial_irreducible {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (hm : V.Monic) (hd : 0 < V.natDegree)
    (h0 : V.coeff 0 ≠ 0) (hk : 2 ≤ k) :
    Irreducible (gridEisensteinPolynomial V k) := by
  apply irreducible_of_bivariate_eisenstein _ (gridEisensteinPolynomial_monic V k hm hd)
  · rwa [gridEisensteinPolynomial_natDegree V k hm hd]
  · rw [gridEisensteinPolynomial_natDegree V k hm hd]
    exact gridEisensteinPolynomial_reduction V k h0 (by omega)
  · rw [gridEisensteinPolynomial_simple V k h0 hd hk]
    exact h0

/-- `gridEisensteinPolynomial V k` vanishes at every point `(x, y)` whose coordinates are both roots
of `V`. -/
lemma gridEisensteinPolynomial_eval_zero {K : Type*} [Field K]
    (V : K[X]) (k : ℕ) (x y : K) (hx : V.eval x = 0) (hy : V.eval y = 0) :
    ((gridEisensteinPolynomial V k).map (evalRingHom y)).eval x = 0 := by
  have he : (evalRingHom y).comp C = RingHom.id K := by ext a; simp
  simp [gridEisensteinPolynomial, gridEisensteinCorrection, map_map, he, hx, hy]

end
end CCDN
