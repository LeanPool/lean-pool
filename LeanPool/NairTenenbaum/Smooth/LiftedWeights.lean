/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.AppendArithmetic
public import LeanPool.NairTenenbaum.Smooth.RootSmoothTail

/-! # Encoding arbitrary scalar weights in doubled exponent substitutions

An additional coordinate for each factor carries the lifted scalar weight.
The weighted mass is squared, so dividing the smooth-tail parameter by two
preserves both the decay exponent and the cutoff in Lemma 2.
-/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

/-- Append a diagonal block containing the column sums of the original matrix. -/
def liftedExponents {k r : ℕ} (γ : Fin k → Fin r → ℕ) : Fin (k + r) → Fin r → ℕ :=
  Fin.append γ (fun i j => if i = j then totalExponent γ i else 0)

@[simp] theorem totalExponent_lifted {k r : ℕ} (γ : Fin k → Fin r → ℕ) (i : Fin r) :
    totalExponent (liftedExponents γ) i = 2 * totalExponent γ i := by
  simp [totalExponent, liftedExponents, Fin.sum_univ_add, two_mul]

@[simp] theorem weightedMass_lifted {k r : ℕ} (γ : Fin k → Fin r → ℕ) (n : Tuple r) :
    weightedMass (liftedExponents γ) n = weightedMass γ n ^ 2 := by
  simp only [weightedMass, totalExponent_lifted, mul_comm 2, pow_mul, Finset.prod_pow]

theorem liftedExponents_pos {k r : ℕ} {γ : Fin k → Fin r → ℕ}
    (hγ : ∀ i, 0 < totalExponent γ i) : ∀ i, 0 < totalExponent (liftedExponents γ) i := by
  intro i
  simpa using Nat.mul_pos (by decide : 0 < 2) (hγ i)

/-- The scalar factors are evaluated on prime-factor roots of the new coordinates. -/
noncomputable def liftedArithmeticMap {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (F : ArithmeticMap k) (θ : Fin r → ℕ → ℝ) :
    ArithmeticMap (k + r) :=
  appendArithmeticMap F (productArithmeticMap (fun i n =>
    θ i (positiveFloorRoot ⟨totalExponent γ i, hγ i⟩ (n 0))))

theorem admissible_liftedArithmeticMap {k r : ℕ} {A B T ε : ℝ}
    {F : ArithmeticMap k} {θ : Fin r → ℕ → ℝ}
    (hF : Admissible A B ε F) (hθ : ∀ i, Admissible A T ε (fun n : Tuple 1 => θ i (n 0)))
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (γ : Fin k → Fin r → ℕ) (hγ : ∀ i, 0 < totalExponent γ i) :
    Admissible A (B * T ^ r) ε (liftedArithmeticMap γ hγ F θ) :=
  admissible_appendArithmeticMap hF
    (admissible_productArithmeticMap (fun i => admissible_floorRoot (hθ i) hA hT hε
      ⟨totalExponent γ i, hγ i⟩)) (zero_le_one.trans hA) hB (pow_nonneg hT _)

@[simp] theorem pullback_lifted {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (F : ArithmeticMap k) (θ : Fin r → ℕ → ℝ)
    (n : Tuple r) :
    pullback (liftedExponents γ) (liftedArithmeticMap γ hγ F θ) n =
      pullback γ F n * ∏ i, θ i (n i) := by
  have hr (i : Fin r) : positiveFloorRoot ⟨totalExponent γ i, hγ i⟩
      (n i ^ totalExponent γ i) = n i := positiveFloorRoot_pow _ _
  simp only [pullback, liftedArithmeticMap, appendArithmeticMap, substitute, liftedExponents,
    Fin.append_left, productArithmeticMap, Fin.append_right, pow_ite, pow_zero, prod_ite_eq,
    mem_univ, ↓reduceIte, hr, mul_eq_mul_right_iff]
  exact Or.inl rfl

theorem rootTupleWeight_lifted {k r : ℕ} (γ : Fin k → Fin r → ℕ)
    (hγ : ∀ i, 0 < totalExponent γ i) (F : ArithmeticMap k) (θ : Fin r → ℕ → ℝ)
    (n : Tuple r) :
    rootTupleWeight (liftedExponents γ) (liftedArithmeticMap γ hγ F θ) (fun _ => X) n =
      pullback γ F n * ∏ i, θ i (n i) / (n i : ℝ) := by
  simp only [rootTupleWeight, pullback_lifted, rootCount_X, Nat.cast_one]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  simp only [mul_one_div]

end NairTenenbaum
