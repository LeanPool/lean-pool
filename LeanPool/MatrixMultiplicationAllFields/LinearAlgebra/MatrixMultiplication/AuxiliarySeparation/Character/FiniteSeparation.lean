/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/FiniteSeparation.lean`,
by Jeroen Zuiddam, 2026: Proposition 3.1 with the period `separationPeriod K M ∈ {3M-2, 3M-1}`,
which is nonzero in `K` and at most `5M`, and a primitive root of unity from `IsAlgClosed`
(upstream: `L = 5M` in ℂ); `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it; `haveI` -> `have`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Degeneration
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The character bound from finite separation

The explicit Fourier and square-weight construction gives a polynomial tensor
whose nonzero evaluations restrict from `L ≤ 5M` complete source copies, where
the period `L ∈ {3M - 2, 3M - 1}` is chosen nonzero in the field.
Character monotonicity follows by interpolation and tensor powering; it does
not require continuity of the character.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
theorem polynomial_rank_bound
    (P : Tensor (Polynomial K) X Y Z) :
    Tensor.RankAtMost P (Fintype.card (X × Y)) := by
  classical
  let a : X × Y → X → Polynomial K := fun i x => if i.1 = x then 1 else 0
  let b : X × Y → Y → Polynomial K := fun i y => if i.2 = y then 1 else 0
  let c : X × Y → Z → Polynomial K := fun i z => P i.1 i.2 z
  have heq : P = fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
    funext x y z
    simp [Tensor.rankOne, a, b, c, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- The explicit separation polynomial, viewed as a polynomial approximation
to its constant tensor. Its rank bound is supplied by a coordinate expansion. -/
def separationPolynomialApproximation {L : ℕ} {ζ : K} (hM : 0 < M)
    (hL : (L : K) ≠ 0) (hLM : 3 * M < L + 3) (hζ : IsPrimitiveRoot ζ L)
    (B : Fin M → Tensor K X Y Z) :
    Tensor.PolynomialApproximation (separationTarget B)
      (Fintype.card ((X × Fin M) × ((Fin M × Y) × Fin M))) 0 ((M - 1) ^ 2) where
  polynomial := separationPolynomial L ζ B
  rank_bound := polynomial_rank_bound _
  vanishes := by
    intro _ _ _ k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact congrFun (congrFun (congrFun (separationPolynomial_coeff_zero hM hL hLM hζ B) x) y) z
  degree_bound := separationPolynomial_degree hM hL hLM hζ B

open Classical in
/-- A period for the finite Fourier filter that is nonzero in `K`: one of the
two consecutive integers `3M - 2`, `3M - 1`.  (The paper uses `5M`, which is
zero in characteristic `5`.) -/
def separationPeriod (K : Type) [Field K] (M : ℕ) : ℕ :=
  if ((3 * M - 2 : ℕ) : K) = 0 then 3 * M - 1 else 3 * M - 2

theorem separationPeriod_ne_zero (hM : 0 < M) :
    ((separationPeriod K M : ℕ) : K) ≠ 0 := by
  unfold separationPeriod
  split_ifs with h
  · intro h'
    have h1 : ((3 * M - 1 : ℕ) : K) = ((3 * M - 2 : ℕ) : K) + 1 := by
      rw [← Nat.cast_succ]
      congr 1
      omega
    rw [h1, h, zero_add] at h'
    exact one_ne_zero h'
  · exact h

theorem separationPeriod_lt (hM : 0 < M) : 3 * M < separationPeriod K M + 3 := by
  unfold separationPeriod
  split_ifs <;> omega

theorem separationPeriod_le (hM : 0 < M) : separationPeriod K M ≤ 5 * M := by
  unfold separationPeriod
  split_ifs <;> omega

/-- An algebraically closed field contains a primitive root of unity of every
order that is nonzero in it. -/
theorem exists_isPrimitiveRoot_of_ne_zero [IsAlgClosed K] {L : ℕ} (hL : (L : K) ≠ 0) :
    ∃ ζ : K, IsPrimitiveRoot ζ L := by
  have : NeZero (L : K) := ⟨hL⟩
  have hLpos : 0 < L := Nat.pos_of_ne_zero (by rintro rfl; simp at hL)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic L K)
    (Polynomial.degree_cyclotomic_pos L K hLpos).ne'
  exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).mp hz⟩

namespace Character

variable (χ : Character K)

/-- The separated constant tensor costs at most the character of `L` source
copies, for the period `L = separationPeriod K M ≤ 5M`.  This uses the explicit
polynomial, not topological continuity. -/
theorem value_separationTarget_le [IsAlgClosed K] (hM : 0 < M) (B : Fin M → Tensor K X Y Z) :
    χ.value (separationTarget B) ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  classical
  set L := separationPeriod K M with hLdef
  have hL : (L : K) ≠ 0 := separationPeriod_ne_zero hM
  have hLM : 3 * M < L + 3 := separationPeriod_lt hM
  have hL5 : L ≤ 5 * M := separationPeriod_le hM
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne_zero hL
  have hbound : χ.value (separationTarget B) ≤
      χ.value (Tensor.directSum (fun _ : Fin L => sharedFirstTensor B)) := by
    apply χ.value_le_of_polynomialApproximation
      (separationPolynomialApproximation hM hL hLM hζ B) (χ.nonneg _)
    intro t ht
    change χ.value (fun x y z => (separationPolynomial L ζ B x y z).eval t) ≤ _
    rw [separationPolynomial_eval hM hL hLM hζ B t ht]
    exact χ.monotone _ _ _ _
  rw [χ.value_copies] at hbound
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_right _ (χ.nonneg _)
  exact_mod_cast hL5

/-- Character accounting for the genuine direct sum in the separated tensor. -/
theorem value_separationTarget (hM : 0 < M) (B : Fin M → Tensor K X Y Z) :
    χ.value (separationTarget B) =
      (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX := by
  classical
  rw [separationTarget_eq_directSum, χ.value_reindex, χ.map_directSum]
  simp only [χ.map_product, χ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul]

/-- Exact finite character separation: the common first coordinate can be
separated at a cost of `5M` (in fact `L ≤ 5M`), retaining an
`M`-dimensional first-leg dot factor. -/
theorem finiteSeparation_bound [IsAlgClosed K] (hM : 0 < M) (B : Fin M → Tensor K X Y Z) :
    (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  rw [← χ.value_separationTarget hM B]
  exact χ.value_separationTarget_le hM B

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
