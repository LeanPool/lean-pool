/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.SignFormula

/-! # Signatures by sign queries

Part of the SVI polynomial-sign certificate (#174).

Sign programs computing the sign variations of a parameter polynomial whose specialisation has
degree exactly `n` (`variationProgram_eval`), the characteristic sign-variation difference
`signatureTest` of each of the four specialised universal matrices (`signatureProgram_eval`), and
their combination, which on the degree branch `n = (polynomial p).derivative.natDegree` evaluates
to `matrixCountFour (polynomial p)` (`countProgram_eval`).

## Main definitions

* `symbolicCoeffList`: the coefficients of a parameter-ring polynomial from degree `n` down to `0`.
* `variationProgram`: the sign program computing the sign variations of `Q` read at degree `n`.
* `signatureProgram`: the sign program computing the signature test of the `i`-th universal
  matrix at size `n`.
* `countProgram`: the sign program combining the four signature tests as `a + b - c - d`.

## Main results

* `variationProgram_eval`: if the specialisation of `Q` at `p` has degree exactly `n`, the program
  evaluates to its number of sign variations.
* `signatureProgram_eval`: `signatureProgram n i` evaluates at `p` to `signatureTest` of the
  specialised universal matrix.
* `countProgram_eval`: at `n = (polynomial p).derivative.natDegree`, `countProgram n` evaluates at
  `p` to `matrixCountFour (polynomial p)`.

## Tags

sign program, matrix signature, characteristic polynomial, Hermite matrices, SVI, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

/-- The coefficients of `Q` from degree `n` down to `0`. -/
noncomputable def symbolicCoeffList (n : ℕ) (Q : Polynomial ParameterRing) : List ParameterRing :=
  (List.range (n+1)).reverse.map Q.coeff

/-- The program computing the sign variations of `Q` read at degree `n` (`variationProgram_eval`).
-/
noncomputable def variationProgram (n : ℕ) (Q : Polynomial ParameterRing) : SignProgram ℕ :=
  (signListProgram (symbolicCoeffList n Q)).bind fun ss ↦ .pure ss.signVariations

theorem variationProgram_eval (p : Params) (n : ℕ) (Q : Polynomial ParameterRing)
    (hd : (Q.map (parameterEval p)).degree = n) :
    (variationProgram n Q).eval p = (Q.map (parameterEval p)).signVariations := by
  have hc : (Q.map (parameterEval p)).coeff = fun r ↦ parameterEval p (Q.coeff r) := by
    funext r
    exact coeff_map _ _
  have hne : Q.map (parameterEval p) ≠ 0 := fun h0 ↦ by simp [h0] at hd
  simp only [variationProgram, SignProgram.eval_bind, SignProgram.eval, symbolicCoeffList,
    Polynomial.signVariations, coeffList_of_ne_zero hne, natDegree_eq_of_degree_eq_some hd,
hc]
  refine Eq.trans ?_ (List.signVariations_map_sign _)
  simp [List.map_reverse, List.map_map, Function.comp_def]

/-- The program computing the signature test of the `i`-th universal matrix at size `n`
(`signatureProgram_eval`). -/
noncomputable def signatureProgram (n : ℕ) (i : Fin 4) : SignProgram ℤ :=
  let Q := (universalMatrices n i).charpoly
  (variationProgram n Q).bind fun v ↦
    (variationProgram n (Q.comp (-X))).bind fun w ↦ .pure ((v : ℤ) - (w : ℤ))

theorem signatureProgram_eval (p : Params) (n : ℕ) (i : Fin 4) :
    (signatureProgram n i).eval p =
      signatureTest ((universalMatrices n i).map (parameterEval p)) := by
  have hd : ((universalMatrices n i).charpoly.map (parameterEval p)).degree = n := by
    rw [← Matrix.charpoly_map, Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
  have hd' : (((universalMatrices n i).charpoly.comp (-X)).map (parameterEval p)).degree = n := by
    simpa only [map_comp, Polynomial.map_neg, map_X, degree_comp_neg_X] using hd
  simp only [signatureProgram, SignProgram.eval_bind, variationProgram_eval p n _ hd,
    variationProgram_eval p n _ hd', SignProgram.eval, signatureTest,
    Matrix.charpoly_map, map_comp, Polynomial.map_neg, map_X]

/-- The program combining the four signature tests as `a + b − c − d` (`countProgram_eval`). -/
noncomputable def countProgram (n : ℕ) : SignProgram ℤ :=
  (signatureProgram n 0).bind fun a ↦
    (signatureProgram n 1).bind fun b ↦
      (signatureProgram n 2).bind fun c ↦
        (signatureProgram n 3).bind fun d ↦ .pure (a+b-c-d)

theorem countProgram_eval (p : Params) :
    (countProgram (polynomial p).derivative.natDegree).eval p = matrixCountFour (polynomial p) := by
  simp only [countProgram, SignProgram.eval_bind, signatureProgram_eval, universalMatrices_eval,
    SignProgram.eval, matrixCountFour]

end SVI
end MathFin
