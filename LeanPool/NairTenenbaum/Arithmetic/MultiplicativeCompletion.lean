/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # Multiplicative completion and Dirichlet inverses

Values on prime powers determine a multiplicative arithmetic function. Applying
this construction to a Dirichlet inverse proves that inversion preserves
multiplicativity, without a recurrence over coprime pairs.
-/

@[expose] public section

namespace NairTenenbaum

open Finset ArithmeticFunction

variable {R : Type*} [CommRing R]

/-- The multiplicative arithmetic function determined by the specified prime-power values. -/
noncomputable def multiplicativeCompletion (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun p k => f (p ^ k)), by simp⟩

theorem multiplicativeCompletion_isMultiplicative (f : ArithmeticFunction R) :
    (multiplicativeCompletion f).IsMultiplicative := by
  apply IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [multiplicativeCompletion]
  · intro m n hm hn hcop
    simp only [multiplicativeCompletion, coe_mk, hm, hn, mul_ne_zero hm hn, ↓reduceIte]
    rw [Nat.factorization_mul_of_coprime hcop]
    exact Finsupp.prod_add_index_of_disjoint hcop.disjoint_primeFactors _

theorem multiplicativeCompletion_prime_pow (f : ArithmeticFunction R) (hf : f 1 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    multiplicativeCompletion f (p ^ k) = f (p ^ k) := by
  simp only [multiplicativeCompletion, coe_mk, pow_ne_zero _ hp.ne_zero, ↓reduceIte,
    hp.factorization_pow]
  apply Finsupp.prod_single_index
  simpa using hf

theorem convolution_prime_pow_congr {f g g' : ArithmeticFunction R} {p k : ℕ}
    (hp : p.Prime) (hg : ∀ j ≤ k, g (p ^ j) = g' (p ^ j)) :
    (f * g) (p ^ k) = (f * g') (p ^ k) := by
  simp only [mul_apply]
  apply sum_congr rfl
  intro de hde
  have H := (Nat.mem_divisorsAntidiagonal.mp hde).1
  have hd : de.2 ∣ p ^ k := H ▸ dvd_mul_left de.2 de.1
  obtain ⟨j, hj, heq⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [heq, hg j hj]

theorem isMultiplicative_of_mul_eq_one {f g : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hfg : f * g = 1) : g.IsMultiplicative := by
  have hg1 : g 1 = 1 := by
    have H := congrArg (fun a : ArithmeticFunction R => a 1) hfg
    simpa only [mul_apply_one, hf.1, one_mul, one_one] using H
  have H : f * multiplicativeCompletion g = 1 := by
    apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
      (hf.mul (multiplicativeCompletion_isMultiplicative g)) _ isMultiplicative_one).mpr
    intro p k hp
    rw [convolution_prime_pow_congr hp (fun j _ => multiplicativeCompletion_prime_pow g hg1 hp j),
        hfg]
  have heq : multiplicativeCompletion g = g := by
    calc
      multiplicativeCompletion g = (g * f) * multiplicativeCompletion g := by
        rw [mul_comm g f, hfg, one_mul]
      _ = g * (f * multiplicativeCompletion g) := mul_assoc _ _ _
      _ = g := by rw [H, mul_one]
  exact heq ▸ multiplicativeCompletion_isMultiplicative g

theorem dirichletInverse_isMultiplicative {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hu : Invertible (f 1)) :
    (dirichletInverse f hu).IsMultiplicative :=
  isMultiplicative_of_mul_eq_one hf (self_mul_dirichletInverse f hu)

end NairTenenbaum
