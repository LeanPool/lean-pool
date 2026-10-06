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

inductive MultiscaleExponent where
  | finite (value : ℝ)
  | infinity

@[expose]
def fullBlockVecNormSq {d : ℕ} (x : FullBlockVec d) : ℝ :=
  ∑ i, x i ^ 2

@[expose]
def matNormSq {d : ℕ} (A : Mat d) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

@[expose]
noncomputable def matNorm {d : ℕ} (A : Mat d) : ℝ :=
  Real.sqrt (matNormSq A)

@[expose]
noncomputable def finsetAverage {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  ((s.card : ℝ)⁻¹) * s.sum f

@[expose]
noncomputable def finsetSsup {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  sSup (f '' (↑s : Set α))

@[expose]
noncomputable def coarseBBlockNorm {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) : ℝ :=
  matNorm (coarseBlockMatrix (cubeSet Q) a).upperLeft

@[expose]
noncomputable def coarseSigmaStarInvBlockNorm {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) : ℝ :=
  matNorm (coarseBlockMatrix (cubeSet Q) a).lowerRight

@[expose]
noncomputable def maxDescendantBBlockNormAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : CoeffField d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => coarseBBlockNorm R a)

@[expose]
noncomputable def maxDescendantSigmaStarInvNormAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : CoeffField d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => coarseSigmaStarInvBlockNorm R a)

@[expose]
noncomputable def geometricDiscount (s q : ℝ) : ℝ :=
  1 - Real.rpow (3 : ℝ) (-s * q)

@[expose]
noncomputable def geometricWeight (s q : ℝ) (n : ℕ) : ℝ :=
  geometricDiscount s q * Real.rpow (3 : ℝ) (-s * q * (n : ℝ))

@[expose]
noncomputable def LambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : CoeffField d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
    (2 / q)

@[expose]
noncomputable def lambdaSqFinite {d : ℕ} (Q : TriadicCube d) (s q : ℝ)
    (a : CoeffField d) : ℝ :=
  Real.rpow
    (∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2))
    (-2 / q)

@[expose]
noncomputable def LambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : CoeffField d) : ℝ :=
  sSup
    { m | ∃ n : ℕ,
        m =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a }

@[expose]
noncomputable def lambdaSqInfinity {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : CoeffField d) : ℝ :=
  (sSup
    { m | ∃ n : ℕ,
        m =
          Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) *
            maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a })⁻¹

@[expose]
noncomputable def LambdaSq {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : MultiscaleExponent) (a : CoeffField d) : ℝ :=
  match q with
  | .finite q => LambdaSqFinite Q s q a
  | .infinity => LambdaSqInfinity Q s a

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

@[expose]
noncomputable def constantFullBlockMatrix {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  toFullBlockMat (blockMatrixOfCoeff a0)

@[expose]
noncomputable def constantFullBlockMatrixSqrt {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  CFC.sqrt (constantFullBlockMatrix a0)

@[expose]
noncomputable def constantFullBlockMatrixInvSqrt {d : ℕ} (a0 : Mat d) : FullBlockMat d :=
  (constantFullBlockMatrixSqrt a0)⁻¹

@[expose]
noncomputable def normalizedBlockResponseValueSet {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) : Set ℝ :=
  { m | ∃ e : FullBlockVec d, fullBlockVecNormSq e = 1 ∧
      m =
        BlockJ (cubeSet Q)
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixInvSqrt a0) e))
          (ofFullBlockVec (Matrix.mulVec (constantFullBlockMatrixSqrt a0) e))
          a }

@[expose]
noncomputable def normalizedBlockResponseMax {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) : ℝ :=
  sSup (normalizedBlockResponseValueSet Q a a0)

@[expose]
noncomputable def maxDescendantNormalizedBlockResponseAtScale {d : ℕ}
    (Q : TriadicCube d) (k : ℤ) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  finsetSsup (descendantsAtScale Q k) (fun R => normalizedBlockResponseMax R a a0)

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

@[expose]
noncomputable def HomogenizationErrorFinite {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p : MultiscaleExponent) (q : ℝ) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  Real.rpow
    (∑' l : ℕ,
      geometricWeight s q l *
        Real.rpow (scaleResponseAtScale Q (n - (l : ℤ)) p a a0) q)
    (1 / q)

@[expose]
noncomputable def HomogenizationErrorInfinity {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  sSup
    { m | ∃ l : ℕ,
        m =
          Real.rpow (3 : ℝ) (-s * (l : ℝ)) *
            scaleResponseAtScale Q (n - (l : ℤ)) p a a0 }

@[expose]
noncomputable def HomogenizationError {d : ℕ} (Q : TriadicCube d) (n : ℤ)
    (s : ℝ) (p q : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  match q with
  | .finite q => HomogenizationErrorFinite Q n s p q a a0
  | .infinity => HomogenizationErrorInfinity Q n s p a a0

@[expose]
noncomputable def HomogenizationErrorOnCube {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (p q : MultiscaleExponent) (a : CoeffField d) (a0 : Mat d) : ℝ :=
  HomogenizationError Q Q.scale s p q a a0

end HCPolySupport
