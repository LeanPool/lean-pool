/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Convolution/RankLowerBound.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Rank
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Exact rank of polynomial convolution

Each output coefficient of polynomial multiplication occurs in some product
of two input monomials. Choosing one such pair for each output gives an
identity minor in the output flattening. Together with evaluation and
interpolation, this proves the exact rank of `C(a,b)` for positive dimensions.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Choosing one product for every output monomial gives an identity minor
of the output flattening. -/
theorem convolution_identity_minor {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (x : Fin (a + b - 1) → Fin a) (y : Fin (a + b - 1) → Fin b),
      ∀ k l, convolution K a b (x k) (y k) l = if k = l then 1 else 0 := by
  choose x y hxy using fun k : Fin (a + b - 1) => convolution_output_supported (K := K) ha hb k
  have hsum (k : Fin (a + b - 1)) : (x k).val + (y k).val = k.val :=
    (convolution_eq_one_iff _ _ _).mp (hxy k)
  refine ⟨x, y, ?_⟩
  intro k l
  simp only [convolution_apply, hsum, Fin.val_inj]

/-- Every rank decomposition of convolution has at least one term per output
coefficient. -/
theorem convolution_rank_lower {a b r : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hRank : Tensor.RankAtMost (convolution K a b) r) : a + b - 1 ≤ r := by
  obtain ⟨x, y, hxy⟩ := convolution_identity_minor (K := K) ha hb
  simpa using hRank.card_le_of_identity x y id hxy

/-- Polynomial multiplication has exact rank `a+b-1` when both inputs have
positive dimension. -/
theorem exactRank_convolution [IsAlgClosed K] {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    exactRank (convolution K a b) = a + b - 1 := by
  apply le_antisymm (exactRank_le (convolution_rankAtMost a b))
  exact convolution_rank_lower ha hb (exactRank_spec _)

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
