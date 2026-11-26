/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.SpectralBooks.ExactExponent

/-!
# Exact square, dual and rectangular matrix multiplication exponents

Source: url:https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean
Authors: OpenAI
Status: verified
Main declarations: `MatrixMultiplicationAllFields.SpectralBooks.square_exponent`,
  `MatrixMultiplicationAllFields.SpectralBooks.dual_exponent`,
  `MatrixMultiplicationAllFields.SpectralBooks.rectangular_exponent`
Tags: matrix-multiplication, arithmetic-complexity, tensor-rank, rectangular-exponents
MSC: 68Q17, 15A69, 68Q25
-/

/-!
## Arithmetic model and sources

The pinned Lean file states all three exact results for division-free programs.
The November 24, 2026 preprint states the square equality for formal circuits
allowing division, bounds the dual exponent, and gives rectangular rank lower bounds.
-/
