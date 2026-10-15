/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic


/-!
# Local affine-parameter geodesic midpoints

The definition uses actual position and velocity curves satisfying the
geodesic equation. Uniqueness is only asserted on the parameter interval
and among short curves in the specified neighborhood. There is no
regularity assumption on the dependence of the curves on their endpoints.
-/

@[expose] public section

open Set Metric

namespace PlanarMidpoint

/-- Position and velocity curves satisfying the affine geodesic ODE on `[0, 1]`. -/
def IsGeodesicSegment (C : E → Coeff) (σ : ℝ) (γ v : ℝ → E) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (v t) t) ∧
  (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (-σ • K (C (γ t)) (v t) (v t)) t)

/-- A geodesic with prescribed endpoints and small position and velocity. -/
def IsShortGeodesic (C : E → Coeff) (σ : ℝ) (p : E) (r : ℝ)
    (P Q : E) (γ v : ℝ → E) : Prop :=
  IsGeodesicSegment C σ γ v ∧ γ 0 = P ∧ γ 1 = Q ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - p‖ < r ∧ ‖v t‖ < r

/-- A midpoint map supplied by the unique short geodesic near a diagonal point. -/
def IsCanonicalLocalMidpoint (Ω : Set E) (C : E → Coeff) (σ : ℝ)
    (p : E) (r : ℝ) (W : Set (E × E)) (A : E → E → E) : Prop :=
  0 < r ∧ ball p r ⊆ Ω ∧ IsOpen W ∧ (p, p) ∈ W ∧
  ∀ P Q, (P, Q) ∈ W → ∃ γ v,
    IsShortGeodesic C σ p r P Q γ v ∧ A P Q = γ midpointTime ∧
    ∀ γ' v', IsShortGeodesic C σ p r P Q γ' v' →
      ∀ t ∈ Icc (0 : ℝ) 1, γ' t = γ t ∧ v' t = v t

/-- Complementarity of the canonical local midpoint maps of `D+K` and `D-K`
near every diagonal point. The definition exposes the actual geodesic ODE. -/
def LocalMidpointInvariance (Ω : Set E) (C : E → Coeff) : Prop :=
  ∀ p ∈ Ω, ∃ rPlus rMinus W APlus AMinus,
    IsCanonicalLocalMidpoint Ω C 1 p rPlus W APlus ∧
    IsCanonicalLocalMidpoint Ω C (-1) p rMinus W AMinus ∧
    ∀ P Q, (P, Q) ∈ W → APlus P Q + AMinus P Q = P + Q

/-- A formulation with arbitrarily small short curves, used only as an
intermediate consequence of canonical midpoint invariance. -/
def ArbitrarilyShortComplementaryPairs (C : E → Coeff) (p : E) : Prop :=
  ∀ r > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ P Q,
    P ∈ ball p δ → Q ∈ ball p δ → ∃ γPlus vPlus γMinus vMinus,
      IsShortGeodesic C 1 p r P Q γPlus vPlus ∧
      IsShortGeodesic C (-1) p r P Q γMinus vMinus ∧
      γPlus (1 / 2) + γMinus (1 / 2) = P + Q

end PlanarMidpoint
