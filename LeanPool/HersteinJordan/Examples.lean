/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module

/-
Adapted from https://github.com/stalex444/herstein-jordan-homomorphisms at
34dffa8aace3a1b565b11cbb561db3a58fa203da. The original MIT notice follows.

MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
public import LeanPool.HersteinJordan.Basic

/-!
# Herstein's theorem: primeness of matrix rings and the three examples

* `matrix_prime`: a matrix ring over a prime ring (with identity) is prime, in the same
  `∀`-form used by the theorem.
* `mul_or_antimul_onto_matrix`: the theorem with a matrix ring as target (a corollary; not one of
  the compared statements).
* Three examples. In each, one hypothesis of `HersteinJordan.mul_or_antimul_of_prime` is dropped,
  the others hold, and the map is neither multiplicative nor anti-multiplicative:
  * `blockTranspose`, `a ↦ diag(a, aᵀ)` from `2 × 2` to `4 × 4` integer matrices: not onto;
  * `sndTranspose`, `(a, b) ↦ (a, bᵀ)` on pairs of `2 × 2` integer matrices: target not prime;
  * `sumMod2`, `(x, y) ↦ x + y` from `𝔽₂ × 𝔽₂` to `𝔽₂`: target has 2-torsion.
-/

@[expose] public section

namespace HersteinJordan

open Matrix

/-- A matrix ring over a prime ring is prime. -/
theorem matrix_prime {m : Type*} [Fintype m] {T : Type*} [Ring T]
    (hT : ∀ a b : T, (∀ x, a * x * b = 0) → a = 0 ∨ b = 0) :
    ∀ A B : Matrix m m T, (∀ X, A * X * B = 0) → A = 0 ∨ B = 0 := by
  classical
  intro A B h
  by_cases hA : A = 0
  · exact Or.inl hA
  · right
    obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hA (Matrix.ext hc)
    ext k l
    refine (hT (A i j) (B k l) fun x => ?_).resolve_left hij
    have e : (A * single j k x * B) i l = A i j * x * B k l := by
      rw [Matrix.mul_apply, Finset.sum_eq_single k]
      · rw [mul_single_apply_same]
      · intro q _ hq
        rw [mul_single_apply_of_ne (hbj := hq), zero_mul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [← e, h]
    rfl

/-- The integers are prime in the `∀`-form. -/
theorem int_prime : ∀ a b : ℤ, (∀ x, a * x * b = 0) → a = 0 ∨ b = 0 := by
  intro a b h
  have := h 1
  rw [mul_one] at this
  exact mul_eq_zero.mp this

/-- Integer matrices have no 2-torsion. -/
theorem int_matrix_no_two_torsion {m n : Type*} (x : Matrix m n ℤ) (h : x + x = 0) : x = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.zero_apply] at this ⊢
  omega

/-- **Corollary (not compared).** A Jordan homomorphism onto a matrix ring over a prime ring
without 2-torsion is multiplicative or anti-multiplicative. -/
theorem mul_or_antimul_onto_matrix {R : Type*} [NonUnitalRing R]
    {m : Type*} [Fintype m] {T : Type*} [Ring T]
    (φ : R →+ Matrix m m T)
    (hJ : ∀ a b, φ (a * b + b * a) = φ a * φ b + φ b * φ a)
    (hsurj : Function.Surjective φ)
    (hT : ∀ a b : T, (∀ x, a * x * b = 0) → a = 0 ∨ b = 0)
    (h2 : ∀ x : T, x + x = 0 → x = 0) :
    (∀ a b, φ (a * b) = φ a * φ b) ∨ (∀ a b, φ (a * b) = φ b * φ a) := by
  refine mul_or_antimul_of_prime φ hJ hsurj (matrix_prime hT) fun x hx => ?_
  ext i j
  exact h2 _ (by simpa using congrFun (congrFun hx i) j)

/-! ### Example 1: surjectivity cannot be dropped -/

/-- `a ↦ diag(a, aᵀ)`. -/
def blockTranspose : Matrix (Fin 2) (Fin 2) ℤ →+ Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ where
  toFun a := fromBlocks a 0 0 aᵀ
  map_zero' := by simp
  map_add' a b := by simp [fromBlocks_add]

theorem blockTranspose_jordan (a b : Matrix (Fin 2) (Fin 2) ℤ) :
    blockTranspose (a * b + b * a) =
      blockTranspose a * blockTranspose b + blockTranspose b * blockTranspose a := by
  simp [blockTranspose, fromBlocks_multiply, fromBlocks_add, transpose_mul, add_comm]

theorem blockTranspose_not_mul :
    ¬ ∀ a b, blockTranspose (a * b) = blockTranspose a * blockTranspose b := by
  intro h
  have := congrFun (congrFun (h !![0, 1; 0, 0] !![0, 0; 1, 0]) (Sum.inr 0)) (Sum.inr 0)
  simp [blockTranspose, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem blockTranspose_not_antimul :
    ¬ ∀ a b, blockTranspose (a * b) = blockTranspose b * blockTranspose a := by
  intro h
  have := congrFun (congrFun (h !![0, 1; 0, 0] !![0, 0; 1, 0]) (Sum.inl 0)) (Sum.inl 0)
  simp [blockTranspose, Matrix.mul_apply, Fin.sum_univ_two] at this

/-! ### Example 2: primeness cannot be dropped -/

/-- `(a, b) ↦ (a, bᵀ)`. -/
def sndTranspose : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ →+
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ where
  toFun p := (p.1, p.2ᵀ)
  map_zero' := by simp
  map_add' p q := by simp

theorem sndTranspose_jordan (p q : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ) :
    sndTranspose (p * q + q * p) =
      sndTranspose p * sndTranspose q + sndTranspose q * sndTranspose p := by
  ext1
  · simp [sndTranspose]
  · simp [sndTranspose, transpose_mul, add_comm]

theorem sndTranspose_surjective : Function.Surjective sndTranspose := by
  intro p
  exact ⟨(p.1, p.2ᵀ), by simp [sndTranspose]⟩

theorem sndTranspose_not_mul :
    ¬ ∀ p q, sndTranspose (p * q) = sndTranspose p * sndTranspose q := by
  intro h
  have := congrFun (congrFun (congrArg Prod.snd
    (h (0, !![0, 1; 0, 0]) (0, !![0, 0; 1, 0]))) 0) 0
  simp [sndTranspose, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem sndTranspose_not_antimul :
    ¬ ∀ p q, sndTranspose (p * q) = sndTranspose q * sndTranspose p := by
  intro h
  have := congrFun (congrFun (congrArg Prod.fst
    (h (!![0, 1; 0, 0], 0) (!![0, 0; 1, 0], 0))) 0) 0
  simp [sndTranspose] at this

/-! ### Example 3: the hypothesis on 2 cannot be dropped -/

/-- `(x, y) ↦ x + y` on `𝔽₂ × 𝔽₂`. -/
def sumMod2 : ZMod 2 × ZMod 2 →+ ZMod 2 :=
  AddMonoidHom.fst (ZMod 2) (ZMod 2) + AddMonoidHom.snd (ZMod 2) (ZMod 2)

theorem sumMod2_jordan (a b : ZMod 2 × ZMod 2) :
    sumMod2 (a * b + b * a) = sumMod2 a * sumMod2 b + sumMod2 b * sumMod2 a := by
  revert a b; decide

theorem sumMod2_surjective : Function.Surjective sumMod2 := by
  decide

theorem zmod2_prime : ∀ x y : ZMod 2, (∀ z, x * z * y = 0) → x = 0 ∨ y = 0 := by
  decide

theorem sumMod2_not_mul : ¬ ∀ a b, sumMod2 (a * b) = sumMod2 a * sumMod2 b := by
  decide

theorem sumMod2_not_antimul : ¬ ∀ a b, sumMod2 (a * b) = sumMod2 b * sumMod2 a := by
  decide

end HersteinJordan
