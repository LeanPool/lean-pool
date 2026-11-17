/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The resultant against a product of linear factors, over any commutative ring

Mathlib proves `Res(P, Q) = ∏ Q(αᵢ)` over a domain for a split polynomial `P`
(`Polynomial.resultant_eq_prod_eval`); for `P = ∏ᵢ (X − αᵢ)` it follows from multiplicativity
(`Polynomial.resultant_prod_left`) with no hypothesis on the ring.

## Main statements

* `Polynomial.resultant_prod_X_sub_C_left`, `Polynomial.resultant_prod_X_sub_C_left'`:
  `Res(∏ᵢ (X − αᵢ), Q) = ∏ᵢ Q(αᵢ)`, with a formal degree `n ≥ deg Q` or the default one.
* `Polynomial.prod_add_add_eq_resultant`: the composed sum
  `∏ᵢⱼ (t + aᵢ + bⱼ) = Res_z(∏ᵢ (z + aᵢ), ∏ⱼ (t − z + bⱼ))`.
* `Polynomial.prod_X_add_add_eq_resultant`: the same over the polynomial ring in `t`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] {ι κ : Type*}

/-- **Resultant against a product of linear factors**, over any commutative ring: for
`P = ∏ᵢ (X − αᵢ)` and a polynomial `Q` read with formal degree `n ≥ deg Q`,
`Res(P, Q) = ∏ᵢ Q(αᵢ)`. -/
theorem resultant_prod_X_sub_C_left (s : Finset ι) (α : ι → R) (Q : R[X]) (n : ℕ)
    (hn : Q.natDegree ≤ n) :
    (∏ i ∈ s, (X - C (α i))).resultant Q (∏ i ∈ s, (X - C (α i))).natDegree n =
      ∏ i ∈ s, Q.eval (α i) := by
  nontriviality R
  rw [resultant_prod_left _ _ _ _ (by simp) hn]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hn]

/-- The same, with the formal degrees left at their defaults. -/
theorem resultant_prod_X_sub_C_left' (s : Finset ι) (α : ι → R) (Q : R[X]) :
    (∏ i ∈ s, (X - C (α i))).resultant Q = ∏ i ∈ s, Q.eval (α i) :=
  resultant_prod_X_sub_C_left s α Q _ le_rfl

/-- **Composed sum as a resultant**: for `t` and families `aᵢ`, `bⱼ` of a commutative ring,
`∏ᵢⱼ (t + aᵢ + bⱼ) = Res_z(∏ᵢ (z + aᵢ), ∏ⱼ (t − z + bⱼ))`. -/
theorem prod_add_add_eq_resultant (s : Finset ι) (t' : Finset κ) (a : ι → R) (b : κ → R)
    (t : R) :
    ∏ i ∈ s, ∏ j ∈ t', (t + a i + b j) =
      (∏ i ∈ s, (X + C (a i))).resultant (∏ j ∈ t', (C t - X + C (b j))) := by
  have hP : ∏ i ∈ s, (X + C (a i)) = ∏ i ∈ s, (X - C (-a i)) := by
    simp [sub_eq_add_neg]
  rw [hP, resultant_prod_X_sub_C_left']
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [eval_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [eval_add, eval_sub, eval_C, eval_X]
  ring

/-- **Composed sum over the polynomial ring in `t`**: in `R[t]`, with `t = X`,
`∏ᵢⱼ (t + aᵢ + bⱼ) = Res_z(∏ᵢ (z + aᵢ), ∏ⱼ (t − z + bⱼ))`, the resultant being taken in
`R[t][z]`. -/
theorem prod_X_add_add_eq_resultant (s : Finset ι) (t' : Finset κ) (a : ι → R) (b : κ → R) :
    ∏ i ∈ s, ∏ j ∈ t', (X + C (a i) + C (b j) : R[X]) =
      (∏ i ∈ s, (X + C (C (a i)) : R[X][X])).resultant
        (∏ j ∈ t', (C X - X + C (C (b j)))) :=
  prod_add_add_eq_resultant s t' (fun i ↦ C (a i)) (fun j ↦ C (b j)) X

end Polynomial
