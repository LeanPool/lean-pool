/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Definitions
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCube
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Coarse-graining support: Support.Deterministic.MultiscaleQuantities

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

open scoped BigOperators
open scoped MatrixOrder

namespace HCPolySupport

/-- A multiscale aggregation exponent, either a real value or infinity. -/
inductive MultiscaleExponent where
  | finite (value : ℝ)
  | infinity

/-- The sum of squared coordinates of a full block vector. -/
@[expose]
def fullBlockVecNormSq {d : ℕ} (x : FullBlockVec d) : ℝ :=
  ∑ i, x i ^ 2

/-- The sum of squared entries of a matrix. -/
@[expose]
def matNormSq {d : ℕ} (A : Mat d) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

/-- The Frobenius norm of a real matrix. -/
@[expose]
noncomputable def matNorm {d : ℕ} (A : Mat d) : ℝ :=
  Real.sqrt (matNormSq A)

/-- The sum of values on a finite set divided by its cardinality, yielding zero for the empty
set. -/
@[expose]
noncomputable def finsetAverage {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  ((s.card : ℝ)⁻¹) * s.sum f

/-- The real supremum of the values attained on a finite set. -/
@[expose]
noncomputable def finsetSsup {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  sSup (f '' (↑s : Set α))

/-- The Frobenius norm of the upper-left coarse block matrix on a cube. -/
@[expose]
noncomputable def coarseBBlockNorm {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) : ℝ :=
  matNorm (coarseBlockMatrix (cubeSet Q) a).upperLeft

/-- The Frobenius norm of the lower-right coarse block matrix on a cube. -/
@[expose]
noncomputable def coarseSigmaStarInvBlockNorm {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) : ℝ :=
  matNorm (coarseBlockMatrix (cubeSet Q) a).lowerRight

/-- The real supremum of upper-left coarse block norms over descendants at scale `k`. -/
@[expose]
noncomputable def maxDescendantBBlockNormAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : CoeffField d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => coarseBBlockNorm R a)

/-- The real supremum of lower-right coarse block norms over descendants at scale `k`. -/
@[expose]
noncomputable def maxDescendantSigmaStarInvNormAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : CoeffField d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => coarseSigmaStarInvBlockNorm R a)

/-- The geometric normalization factor `1 - 3 ^ (-s * q)`. -/
@[expose]
noncomputable def geometricDiscount (s q : ℝ) : ℝ :=
  1 - Real.rpow (3 : ℝ) (-s * q)

/-- The depth-`n` geometric weight `(1 - 3 ^ (-s * q)) * 3 ^ (-s * q * n)`. -/
@[expose]
noncomputable def geometricWeight (s q : ℝ) (n : ℕ) : ℝ :=
  geometricDiscount s q * Real.rpow (3 : ℝ) (-s * q * (n : ℝ))

/-- The weighted sum of descendant upper-left block maxima to power `q/2`, raised to `2/q`. -/
@[expose]
noncomputable def LambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : CoeffField d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
    (2 / q)

/-- The weighted sum of descendant lower-right block maxima to power `q/2`, raised to `-2/q`. -/
@[expose]
noncomputable def lambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : CoeffField d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
    (-2 / q)

/-- The real supremum over depths of upper-left block maxima weighted by `3 ^ (-2 * s * n)`. -/
@[expose]
noncomputable def LambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : CoeffField d) : ℝ :=
  sSup
    { m | ∃ n : ℕ,
        m =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a }

/-- The inverse real supremum of lower-right block maxima weighted by `3 ^ (-2 * s * n)`. -/
@[expose]
noncomputable def lambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : CoeffField d) : ℝ :=
  (sSup
    { m | ∃ n : ℕ,
        m =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a })⁻¹

/-- The upper multiscale quantity, using the power-sum or supremum formula according to the
exponent. -/
@[expose]
noncomputable def LambdaSq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) (a : CoeffField d) : ℝ :=
  match q with
  | .finite q => LambdaSqFinite Q s q a
  | .infinity => LambdaSqInfinity Q s a

/-- The lower multiscale quantity, using the inverse power-sum or inverse supremum formula. -/
@[expose]
noncomputable def lambdaSq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) (a : CoeffField d) : ℝ :=
  match q with
  | .finite q => lambdaSqFinite Q s q a
  | .infinity => lambdaSqInfinity Q s a

/--
Deterministic cube-level contrast ratio `Λ_{s,1}(Q) / λ_{t,1}(Q)`.
This is not the annealed Chapter-5 sequence `Θ_n`.
-/
@[expose]
noncomputable def ThetaRatio {d : ℕ} (Q : TriadicCube d) (s t : ℝ)
    (a : CoeffField d) : ℝ :=
  LambdaSq Q s (.finite 1) a / lambdaSq Q t (.finite 1) a

/-- The full block-coordinate matrix associated with the constant coefficient matrix `a0`. -/
@[expose]
noncomputable def constantFullBlockMatrix {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  toFullBlockMat (blockMatrixOfCoeff a0)

/-- The continuous-functional-calculus square root of the constant full block matrix. -/
@[expose]
noncomputable def constantFullBlockMatrixSqrt {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  CFC.sqrt (constantFullBlockMatrix a0)

/-- The matrix inverse of the square root of the constant full block matrix. -/
@[expose]
noncomputable def constantFullBlockMatrixInvSqrt {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  (constantFullBlockMatrixSqrt a0)⁻¹

/-- Block responses on unit block vectors, with inputs transformed by the inverse square root
and square root of the constant block matrix. -/
@[expose]
noncomputable def normalizedBlockResponseValueSet {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) : Set ℝ :=
  { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
      m =
        BlockJ (cubeSet Q)
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
          a }

/-- The real supremum of block responses normalized by the constant block matrix. -/
@[expose]
noncomputable def normalizedBlockResponseMax {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) : ℝ :=
  sSup (normalizedBlockResponseValueSet Q a a0)

/-- The real supremum of normalized block responses over descendants at scale `k`. -/
@[expose]
noncomputable def maxDescendantNormalizedBlockResponseAtScale {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => normalizedBlockResponseMax R a a0)

/-- The descendant mean of normalized responses to power `p/2`, raised to `1/p`; at infinity,
the square root of their real supremum. -/
@[expose]
noncomputable def scaleResponseAtScale {d : ℕ} (Q : TriadicCube d) (k : ℤ)
    (p : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  match p with
  | .finite p =>
      Real.rpow
        (finsetAverage (descendantsAtScale Q k)
          (fun R => Real.rpow (normalizedBlockResponseMax R a a0) (p / 2)))
        (1 / p)
  | .infinity =>
      Real.rpow (maxDescendantNormalizedBlockResponseAtScale Q k a a0) (1 / 2)

/-- The geometrically weighted `q`-power sum of scale responses below scale `n`, raised to
`1/q`. -/
@[expose]
noncomputable def HomogenizationErrorFinite {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p : MultiscaleExponent) (q : ℝ) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  Real.rpow
    (∑' l : ℕ,
      geometricWeight s q l *
        Real.rpow (scaleResponseAtScale Q (n - (l : ℤ)) p a a0) q)
    (1 / q)

/-- The real supremum of scale responses below `n`, weighted by `3 ^ (-s * l)`. -/
@[expose]
noncomputable def HomogenizationErrorInfinity {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  sSup
    { m | ∃ l : ℕ,
        m =
          Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            scaleResponseAtScale Q (n - (l : ℤ)) p a a0 }

/-- The multiscale response error, using power-sum or supremum aggregation over scales. -/
@[expose]
noncomputable def HomogenizationError {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p q : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  match q with
  | .finite q => HomogenizationErrorFinite Q n s p q a a0
  | .infinity => HomogenizationErrorInfinity Q n s p a a0

/-- The multiscale response error starting at the parent cube's own scale. -/
@[expose]
noncomputable def HomogenizationErrorOnCube {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  HomogenizationError Q Q.scale s p q a a0

end HCPolySupport
