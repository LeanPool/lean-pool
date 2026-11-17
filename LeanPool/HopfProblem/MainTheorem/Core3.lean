/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module
public import LeanPool.HopfProblem.MainTheorem.Core2
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Geometry.Manifold.IsManifold.Basic

public import LeanPool.HopfProblem.InternalPrelude
public import LeanPool.HopfProblem.Threefold.SixSphereComplexAtlas

/-!
# Hopf problem: main theorem · core 3

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators ComplexConjugate ContDiff ContinuousMap ENNReal EuclideanSpace Fin.NatCast
  InnerProductSpace Interval Matrix NNReal Pointwise RealInnerProductSpace

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

public
theorem mathoverflow_1973 :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  exact SixSphereComplexAtlas.exists_complex_atlas

end Mathoverflow1973

end
