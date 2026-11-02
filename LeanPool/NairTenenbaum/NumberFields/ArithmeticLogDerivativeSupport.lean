/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.NumberFields.ArithmeticLogDerivative
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! # Prime-power support of a multiplicative logarithmic derivative

The first-order logarithmic weighting is encoded in the square-zero extension
of the real numbers. Multiplicativity there gives the coprime splitting identity.
-/

@[expose] public section

namespace NairTenenbaum

open Finset ArithmeticFunction

/-- The first-order arithmetic jet whose tangent component carries the logarithmic weight. -/
noncomputable def arithmeticLogJet (f : ArithmeticFunction ℝ) :
    ArithmeticFunction (TrivSqZeroExt ℝ ℝ) :=
  ⟨fun n => (f n, f n * Real.log n), by simp; rfl⟩

/-- The constant first-order jet of an arithmetic function. -/
noncomputable def arithmeticConstantJet (f : ArithmeticFunction ℝ) :
    ArithmeticFunction (TrivSqZeroExt ℝ ℝ) :=
  ⟨fun n => (f n, 0), by simp; rfl⟩

@[simp] theorem arithmeticLogJet_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticLogJet f n = ((f n, f n * Real.log n) : TrivSqZeroExt ℝ ℝ) := rfl

@[simp] theorem arithmeticConstantJet_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticConstantJet f n = ((f n, 0) : TrivSqZeroExt ℝ ℝ) := rfl

theorem arithmeticLogJet_isMultiplicative {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) :
    (arithmeticLogJet f).IsMultiplicative := by
  apply IsMultiplicative.iff_ne_zero.mpr
  constructor
  · apply TrivSqZeroExt.ext <;> simp [arithmeticLogJet_apply, hf.1]
  · intro m n hm hn hcop
    apply TrivSqZeroExt.ext
    · change f (m * n) = f m * f n
      exact hf.2 hcop
    · change f (m * n) * Real.log ((m * n : ℕ) : ℝ) =
        f m * (f n * Real.log (n : ℝ)) + (f m * Real.log (m : ℝ)) * f n
      rw [hf.2 hcop, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn)]
      ring

theorem arithmeticConstantJet_isMultiplicative {f : ArithmeticFunction ℝ} (hf :
    f.IsMultiplicative) :
    (arithmeticConstantJet f).IsMultiplicative := by
  constructor
  · apply TrivSqZeroExt.ext <;> simp [arithmeticConstantJet_apply, hf.1]
  · intro m n hcop
    apply TrivSqZeroExt.ext
    · change f (m * n) = f m * f n
      exact hf.2 hcop
    · change (0 : ℝ) = f m * 0 + 0 * f n
      ring

theorem arithmeticLogJet_mul_fst (f g : ArithmeticFunction ℝ) (n : ℕ) :
    ((arithmeticLogJet f * arithmeticConstantJet g) n).fst = (f * g) n := by
  simp only [mul_apply, TrivSqZeroExt.fst_sum]
  apply sum_congr rfl
  intro de _
  rfl

theorem arithmeticLogJet_mul_snd (f g : ArithmeticFunction ℝ) (n : ℕ) :
    ((arithmeticLogJet f * arithmeticConstantJet g) n).snd = arithmeticLogDerivative f g n := by
  simp only [arithmeticLogDerivative, mul_apply, TrivSqZeroExt.snd_sum]
  apply sum_congr rfl
  intro de _
  change f de.1 * 0 + (f de.1 * Real.log (de.1 : ℝ)) * g de.2 =
    (f de.1 * Real.log (de.1 : ℝ)) * g de.2
  ring

theorem arithmeticLogDerivative_coprime {f g : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) {m n : ℕ} (hcop : m.Coprime n) :
    arithmeticLogDerivative f g (m * n) =
      (f * g) m * arithmeticLogDerivative f g n + arithmeticLogDerivative f g m * (f * g) n := by
  have H := (arithmeticLogJet_isMultiplicative hf).mul (arithmeticConstantJet_isMultiplicative hg)
  have HE := congrArg TrivSqZeroExt.snd (H.2 hcop)
  simpa only [TrivSqZeroExt.snd_mul, arithmeticLogJet_mul_snd, arithmeticLogJet_mul_fst,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] using HE

theorem arithmeticLogDerivative_eq_zero_of_not_primePower {f g : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) (hfg : f * g = 1)
    {n : ℕ} (hn : ¬ IsPrimePow n) : arithmeticLogDerivative f g n = 0 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk => exact (hn (hp.prime.isPrimePow.pow hk.ne')).elim
  | zero => exact ArithmeticFunction.map_zero
  | one => simp [arithmeticLogDerivative]
  | coprime a b ha hb hab _ _ =>
    rw [arithmeticLogDerivative_coprime hf hg hab, hfg,
      one_apply_ne ha.ne', one_apply_ne hb.ne', zero_mul, mul_zero, add_zero]

end NairTenenbaum
