/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Degeneration.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Polynomial.Interpolation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PolynomialOverhead
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Characters decrease under polynomial degeneration

Finite interpolation expresses a polynomial's leading coefficient as a sum
of evaluations.  Applying it after tensor powering gives only a linear
overhead, which disappears in the exponential growth rate.  No continuity
assumption on the character is used.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

variable (χ : Character K)
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Scalar multiplication is a restriction, including when the scalar is zero. -/
theorem value_scale_le (c : K) (T : Tensor K X Y Z) :
    χ.value (fun x y z => c * T x y z) ≤ χ.value T := by
  classical
  have heq : Tensor.restrict
      (fun x' x => if x = x' then c else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T =
      fun x y z => c * T x y z := by
    funext x y z
    simp [Tensor.restrict, ite_mul, mul_ite]
  simpa only [heq] using χ.monotone T
    (fun x' x => if x = x' then c else 0)
    (fun y' y => if y = y' then 1 else 0)
    (fun z' z => if z = z' then 1 else 0)

/-- Nonzero scalar multiplication preserves a character. -/
theorem value_scale (c : K) (hc : c ≠ 0) (T : Tensor K X Y Z) :
    χ.value (fun x y z => c * T x y z) = χ.value T := by
  apply le_antisymm (χ.value_scale_le c T)
  have h := χ.value_scale_le c⁻¹ (fun x y z => c * T x y z)
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h

/-- Adding tensors is a restriction of their independent direct sum. -/
theorem value_sum_le {ι : Type} [Fintype ι] (T : ι → Tensor K X Y Z) :
    χ.value (fun x y z => ∑ i, T i x y z) ≤ ∑ i, χ.value (T i) := by
  classical
  have heq : Tensor.restrict
      (fun x (p : ι × X) => if p.2 = x then 1 else 0)
      (fun y (p : ι × Y) => if p.2 = y then 1 else 0)
      (fun z (p : ι × Z) => if p.2 = z then 1 else 0)
      (Tensor.directSum T) = fun x y z => ∑ i, T i x y z := by
    funext x y z
    simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
      ite_mul, mul_ite, ite_and]
  rw [← χ.map_directSum T, ← heq]
  exact χ.monotone (Tensor.directSum T) _ _ _

/-- Exact interpolation bounds any polynomial coefficient by the sum of the
character values of finitely many evaluation tensors. -/
theorem value_coefficient_le [IsAlgClosed K] (P : Tensor (Polynomial K) X Y Z) (d D : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D) :
    χ.value (fun x y z => (P x y z).coeff d) ≤
      ∑ i : Fin (D + 1), χ.value (fun x y z => (P x y z).eval (interpolationNode K D i)) := by
  classical
  let w : Fin (D + 1) → K := fun i =>
    (Lagrange.basis Finset.univ (interpolationNode K D) i).coeff d
  have heq : (fun x y z => (P x y z).coeff d) =
      fun x y z => ∑ i : Fin (D + 1), w i * (P x y z).eval (interpolationNode K D i) := by
    funext x y z
    have hlt : (P x y z).degree < Fintype.card (Fin (D + 1)) := by
      simp only [Fintype.card_fin]
      exact lt_of_le_of_lt (hdegree x y z)
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self D))
    simpa only [w, mul_comm] using Tensor.coeff_eq_sum_eval
      (interpolationNode K D) (interpolationNode_injective D) (P x y z) d hlt
  rw [heq]
  apply (χ.value_sum_le _).trans
  exact Finset.sum_le_sum fun i _ => χ.value_scale_le (w i) _

/-- A uniform bound on nonzero evaluations bounds the leading tensor.  The
proof uses tensor powers and removes their linear interpolation overhead. -/
theorem value_le_of_polynomialApproximation [IsAlgClosed K]
    {U : Tensor K X Y Z} {r d D : ℕ}
    (A : Tensor.PolynomialApproximation U r d D) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ t : K, t ≠ 0 →
      χ.value (fun x y z => (A.polynomial x y z).eval t) ≤ b) :
    χ.value U ≤ b := by
  apply le_of_pow_le_linear_mul_pow (K := (D : ℝ)) hb
  intro n
  have hcoefficient := χ.value_coefficient_le (A.power n).polynomial
    (d * n) (D * n) (A.power n).degree_bound
  have hleading : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power U n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [hleading, χ.value_power] at hcoefficient
  apply hcoefficient.trans
  calc
    (∑ i : Fin (D * n + 1), χ.value
        (fun x y z => ((A.power n).polynomial x y z).eval
          (interpolationNode K (D * n) i))) ≤
        ∑ _i : Fin (D * n + 1), b ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have heval : (fun x y z => ((A.power n).polynomial x y z).eval
          (interpolationNode K (D * n) i)) =
          Tensor.power (fun x y z => (A.polynomial x y z).eval
            (interpolationNode K (D * n) i)) n := by
        funext x y z
        simp only [Tensor.PolynomialApproximation.power, Tensor.power,
          Polynomial.eval_prod]
      rw [heval, χ.value_power]
      exact pow_le_pow_left₀ (χ.nonneg _)
        (hbound _ (interpolationNode_ne_zero _ _)) n
    _ = ((n : ℝ) * (D : ℝ) + 1) * b ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring

omit [Fintype Z] in
omit [Fintype X] [Fintype Y] in
private theorem exists_rankAtMost (T : Tensor K X Y Z) [Finite X] [Finite Y] :
    ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let : Fintype Y := Fintype.ofFinite Y
  let a : X × Y → X → K := fun p x => if p.1 = x then 1 else 0
  let b : X × Y → Y → K := fun p y => if p.2 = y then 1 else 0
  let c : X × Y → Z → K := fun p z => T p.1 p.2 z
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [Tensor.rankOne, a, b, c, Fintype.sum_prod_type, ite_mul, mul_ite]
  exact ⟨Fintype.card (X × Y), heq ▸ Tensor.rankAtMost_sum_rankOne a b c⟩

/-- The character axioms imply monotonicity under polynomial degeneration.
Continuity of the character is neither assumed nor used. -/
theorem value_polynomialRestrictionDegeneration_le [IsAlgClosed K]
    {X' Y' Z' : Type} [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor K X Y Z} {U : Tensor K X' Y' Z'} {k Lx Ly Lz : ℕ}
    (L : Tensor.PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    χ.value U ≤ χ.value T := by
  obtain ⟨r, hr⟩ := exists_rankAtMost T
  apply χ.value_le_of_polynomialApproximation
    (restrictionDegeneration_approximation L hr) (χ.nonneg T)
  intro t ht
  have heval : (fun x y z =>
      ((restrictionDegeneration_approximation L hr).polynomial x y z).eval t) =
      Tensor.restrict (fun x' x => (L.leftMap x' x).eval t)
        (fun y' y => (L.middleMap y' y).eval t)
        (fun z' z => (L.rightMap z' z).eval t) T := by
    funext x y z
    exact restrictionDegeneration_eval L t x y z
  rw [heval]
  exact χ.monotone T _ _ _

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
