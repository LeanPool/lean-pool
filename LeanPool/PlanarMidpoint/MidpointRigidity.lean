/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.DifferentialRigidity
public import LeanPool.PlanarMidpoint.CanonicalMidpoints
public import LeanPool.PlanarMidpoint.AnalyticObstruction
public import Mathlib.Tactic.NormNum

/-!
# Planar Euclidean midpoint rigidity

This proves the dimension-two case of Nielsen–Okamura Conjecture 9.1
(arXiv:2609.07551v2, Section 9). The midpoint hypothesis uses actual canonical
short geodesics of the two Euclidean dual connections. The proof includes
the construction of those local germs and their fourth-order obstruction.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace PlanarMidpoint

/-- Twice continuously differentiable coefficients already suffice for planar
dual-geodesic midpoint rigidity. -/
theorem planar_midpoint_rigidity_C2 (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (smoothC : ContDiffOn ℝ 2 C Ω)
    (complementary : LocalMidpointInvariance Ω C) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c := by
  apply planar_obstruction_rigidity Ω C openΩ connectedΩ
    (smoothC.differentiableOn (by norm_num))
  intro p hp h
  exact obstruction_of_short_complementary_pairs openΩ hp smoothC
    (localMidpointInvariance_arbitrarilyShort openΩ hp smoothC complementary) h

/-- Nielsen–Okamura Conjecture 9.1 in dimension two, with its full geometric
midpoint hypothesis and no assumed fourth-order condition. -/
theorem planar_dual_midpoint_rigidity (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (smoothC : ContDiffOn ℝ ∞ C Ω)
    (complementary : LocalMidpointInvariance Ω C) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c :=
  planar_midpoint_rigidity_C2 Ω C openΩ connectedΩ (smoothC.of_le (by simp)) complementary

end PlanarMidpoint
