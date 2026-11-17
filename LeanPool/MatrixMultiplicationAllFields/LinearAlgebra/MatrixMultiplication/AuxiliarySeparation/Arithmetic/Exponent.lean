/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Arithmetic/Exponent.lean`, by
Jeroen Zuiddam, 2026: rewritten: the passage from exact-rank bounds to arithmetic cost now works
over an arbitrary field, through the library's field-generic block recursion
(`omega_le_of_arbitrarily_close_rankBounds`, `omega_le_exactRankExponent`); no declaration here
needs `K` algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Rectangular.ASI
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# From exact tensor rank to arithmetic complexity

This file supplies the arithmetic conversion in Section 6.2, over an arbitrary
field `F`.  It uses the division-free straight-line programs of
`MatrixMultiplication.Arithmetic`: loading inputs and constants is free, and each
scalar addition, subtraction, or multiplication costs one.  Correctness means
matrix multiplication on every pair of inputs.

The block recursion is the field-generic one of
`Arithmetic.rectangularAdmissibleExponent_of_rankAtMost` (with aspect `k = 1`).
The substantive tensor estimates are separate: any family of exact
decompositions of `⟨n,n,n⟩` over `F` with ranks `≤ n^(τ+δ)` for every `δ > 0`
gives `omega F ≤ τ`.  In particular `omega K ≤ exactRankExponent K`.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

section Bridge

variable {F : Type*} [Field F]

/-- A finite exact decomposition over `F` gives an arithmetic bound over `F` by
block substitution, including all the scalar operations in the linear
combinations, followed by padding to arbitrary positive sizes. -/
theorem admissibleExponent_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matMul F n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    MatrixMultiplication.Arithmetic.AdmissibleExponent F τ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsq : (n : ℝ) ^ (2 : ℕ) ≤ (n : ℝ) ^ τ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by exact_mod_cast hτ)
  apply (MatrixMultiplication.Arithmetic.admissibleExponent_iff_rectangular_one F τ).mpr
  exact MatrixMultiplication.Arithmetic.rectangularAdmissibleExponent_of_rankAtMost
    (a := n) (b := n) hn zero_le_one (by simp) hRank (by linarith) hR
    (by simpa [pow_two] using hsq) hsq

theorem omega_le_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matMul F n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    MatrixMultiplication.Arithmetic.omega F ≤ τ :=
  MatrixMultiplication.Arithmetic.omega_le_of_admissibleExponent
    (admissibleExponent_of_rankAtMost hn hRank hτ hR)

/-- Near-optimal finite blocks suffice: no finite decomposition is required
to attain the limiting exponent. -/
theorem omega_le_of_arbitrarily_close_rankBounds {τ : ℝ} (hτ : 2 ≤ τ)
    (hRank : ∀ δ : ℝ, 0 < δ → ∃ n R : ℕ, 2 ≤ n ∧
      Tensor.RankAtMost (Tensor.matMul F n n n) R ∧
        (R : ℝ) ≤ (n : ℝ) ^ (τ + δ)) :
    MatrixMultiplication.Arithmetic.omega F ≤ τ := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨n, R, hn, hRank, hR⟩ := hRank δ hδ
  exact omega_le_of_rankAtMost hn hRank (by linarith) hR

end Bridge

section AlgClosed

variable {K : Type} [Field K]

/-- General exact-rank-to-arithmetic bridge.  The proof uses a lower bound for
every finite-block exponent, so it does not require attainment of the infimum. -/
theorem omega_le_exactRankExponent :
    MatrixMultiplication.Arithmetic.omega K ≤ exactRankExponent K := by
  apply omega_le_of_arbitrarily_close_rankBounds (exactRankExponent_lower (K := K))
  intro δ hδ
  exact exists_rankAtMost_of_exponent_slack hδ

/-- Explicit epsilon-complexity conclusion from an exact-rank exponent bound. -/
theorem arithmeticComplexity_of_exactRankExponent_le {τ : ℝ}
    (hτ : exactRankExponent K ≤ τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : MatrixMultiplication.Arithmetic.MatrixAlgorithm K n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε) :=
  (MatrixMultiplication.Arithmetic.admissibleExponent_iff_omega_le.mpr
    (omega_le_exactRankExponent.trans hτ)) ε hε

end AlgClosed

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
