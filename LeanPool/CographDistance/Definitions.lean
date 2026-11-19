/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic

/-!
# Distance eigenvalues of connected cographs below `-2`

Statement file for Open Problem "Distance eigenvalues of cographs below -2 and sharpness", part (i),
of Manna, Mandal and Tura, *The Spectral Theory of Cographs: A Survey, Organized by Graph Matrix*,
arXiv:2611.06981v1 (4 November 2026):

> Is there `ε > 0` such that `(-2-ε, -2)` contains no distance eigenvalue of any connected cograph?

`OpenProblemI_negative` says that the answer is no.

Definitions follow the survey: a cograph is a finite simple graph with no induced path on four
vertices; the distance matrix of a connected graph is `D(G) = (d(u,v))_{u,v}`.
-/

@[expose] public section

namespace CographDist

/-- The distance matrix `D(G) = (d(u,v))_{u,v}` over `ℝ`, with Mathlib's graph distance.
(Mathlib's `dist` is `0` for unreachable pairs; this file uses it only for connected graphs.) -/
noncomputable def distMatrix {V : Type*} (G : SimpleGraph V) : Matrix V V ℝ :=
  fun u v => (G.dist u v : ℝ)

/-- `μ` is a (real) distance eigenvalue of `G`: `D(G) x = μ x` for some nonzero real vector `x`. -/
def IsDistEigenvalue {V : Type*} [Fintype V] (G : SimpleGraph V) (μ : ℝ) : Prop :=
  ∃ x : V → ℝ, x ≠ 0 ∧ (distMatrix G).mulVec x = μ • x

end CographDist
