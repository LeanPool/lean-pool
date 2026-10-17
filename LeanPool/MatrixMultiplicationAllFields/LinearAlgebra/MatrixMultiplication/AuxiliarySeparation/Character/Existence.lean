/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Existence.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed; docstrings updated from ℂ to `K`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.StateObstruction
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.MultiplicativeStates
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Obstruction
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Characters
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Detecting characters for matrix multiplication over `K`

This proves Lemma 3.1, including Appendix A. Finite inconsistency would
produce a positive scalar-gain catalyst, ruled out by the exact-rank exponent.
A compact normalized state space then yields a multiplicative state, which
transfers to the concrete coefficient-level character interface.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Lemma 3.1: normalized, additive, multiplicative, restriction-monotone
characters detect every integer strictly below the exact-rank growth value. -/
theorem exists_detecting_character {d k : ℕ} (hd : 2 ≤ d)
    (hk : (k : ℝ) < (d : ℝ) ^ exactRankExponent K) :
    ∃ χ : Character K, (k : ℝ) ≤ χ.value (Tensor.matMul K d d d) := by
  have hnonempty := normalizedStates_nonempty_of_no_catalyst
    TensorSemiring.rank (TensorSemiring.matrixClass K d) k
    TensorSemiring.zero_le TensorSemiring.le_rank
    (fun _ _ _ _ h₁ h₂ => TensorSemiring.add_mono h₁ h₂)
    (fun D s m hm hcat => no_tensor_catalytic_gain (by omega) hk ⟨D, s, m, hm, hcat⟩)
  have hdom (z x : (TensorSemiring.TensorClass K)) :
      z * x ≤ (TensorSemiring.rank x : (TensorSemiring.TensorClass K)) * z := by
    calc
      z * x ≤ z * (TensorSemiring.rank x : (TensorSemiring.TensorClass K)) :=
        TensorSemiring.mul_mono le_rfl (TensorSemiring.le_rank x)
      _ = (TensorSemiring.rank x : (TensorSemiring.TensorClass K)) * z := mul_comm _ _
  obtain ⟨φ, hφ, _, hdetect⟩ := exists_monotone_semiringHom_of_normalizedStates
    TensorSemiring.rank (TensorSemiring.matrixClass K d) (k : ℝ)
    (fun z hz => TensorSemiring.one_le_of_ne_zero hz)
    (fun _ _ _ h => TensorSemiring.mul_mono le_rfl h) hdom hnonempty
  exact ⟨Character.ofTensorClassHom φ hφ, hdetect⟩

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
