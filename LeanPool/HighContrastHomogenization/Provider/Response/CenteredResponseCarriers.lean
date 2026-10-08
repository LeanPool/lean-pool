/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjoint
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockPositivity
public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationLoads

/-!
# High-contrast homogenization: Provider.Response.CenteredResponseCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Centered primal and adjoint response carriers

For a coefficient law and one bounded convex domain, the centered response is
the annealed response energy minus one half of the product of the two separately
annealed optimizer averages.  The adjoint response is evaluated at the
transpose of the same coefficient sample; no pushforward of the law is used.

The remaining carriers are the skew and symmetric parts of the Schur coordinate
of the annealed block, the corrected response block, its geometric-mean metric,
and the two metric-adapted loads.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The canonical response optimizer `v_{p,q}` on an arbitrary Chapter 2
domain. -/
@[expose]
def centeredResponseOptimizer (U : Domain d) (a : CoeffSpace d)
    (p q : Vec d) : Solution U (a.coeffOn U) :=
  (canonicalMaximizer (responseExistenceTheory U (a.coeffOn U)) p q).toSolution

/-- The chosen primal optimizer realizes the response supremum. -/
theorem centeredResponseOptimizer_isMaximizer (U : Domain d) (a : CoeffSpace d)
    (p q : Vec d) :
    Book.Ch02.IsResponseMaximizer U (a.coeffOn U) p q
      (centeredResponseOptimizer U a p q) :=
  (canonicalMaximizer (responseExistenceTheory U (a.coeffOn U)) p q).isMaximizer

/-- The canonical adjoint optimizer `v*_{p,q}` at the same sample. -/
@[expose]
def centeredAdjointOptimizer (U : Domain d) (a : CoeffSpace d)
    (p q : Vec d) : Solution U (a.transpose.coeffOn U) :=
  centeredResponseOptimizer U a.transpose p q

/-- The chosen adjoint optimizer realizes the adjoint response supremum. -/
theorem centeredAdjointOptimizer_isMaximizer (U : Domain d) (a : CoeffSpace d)
    (p q : Vec d) :
    Book.Ch02.IsResponseMaximizer U (a.transpose.coeffOn U) p q
      (centeredAdjointOptimizer U a p q) :=
  centeredResponseOptimizer_isMaximizer U a.transpose p q

/-- The annealed spatial average of the primal optimizer gradient.  As for the
annealed block, the finite-dimensional expectation is defined entrywise. -/
@[expose]
def annealedOptimizerGradient (P : Measure (CoeffSpace d)) (U : Domain d)
    (p q : Vec d) : Vec d :=
  fun i => ∫ a, averageGradient U (a.coeffOn U)
    (centeredResponseOptimizer U a p q) i ∂P

/-- The annealed spatial average of the primal optimizer flux. -/
@[expose]
def annealedOptimizerFlux (P : Measure (CoeffSpace d)) (U : Domain d)
    (p q : Vec d) : Vec d :=
  fun i => ∫ a, averageFlux U (a.coeffOn U)
    (centeredResponseOptimizer U a p q) i ∂P

/-- The annealed spatial average of the adjoint optimizer gradient. -/
@[expose]
def annealedAdjointOptimizerGradient (P : Measure (CoeffSpace d))
    (U : Domain d) (p q : Vec d) : Vec d :=
  fun i => ∫ a, averageGradient U (a.transpose.coeffOn U)
    (centeredAdjointOptimizer U a p q) i ∂P

/-- The annealed spatial average of the adjoint optimizer flux. -/
@[expose]
def annealedAdjointOptimizerFlux (P : Measure (CoeffSpace d))
    (U : Domain d) (p q : Vec d) : Vec d :=
  fun i => ∫ a, averageFlux U (a.transpose.coeffOn U)
    (centeredAdjointOptimizer U a p q) i ∂P

/-- The deterministic centered primal response
`J_tilde_a(U;p,q)`. -/
@[expose]
def centeredResponse (P : Measure (CoeffSpace d)) (U : Domain d)
    (p q : Vec d) : ℝ :=
  (∫ a, responseJ U (a.coeffOn U) p q ∂P) -
    (1 / 2 : ℝ) * vecDot (annealedOptimizerGradient P U p q)
      (annealedOptimizerFlux P U p q)

/-- The deterministic centered adjoint response
`J_tilde_{aᵗ}(U;p,q)`. -/
@[expose]
def centeredAdjointResponse (P : Measure (CoeffSpace d)) (U : Domain d)
    (p q : Vec d) : ℝ :=
  (∫ a, responseJ U (a.transpose.coeffOn U) p q ∂P) -
    (1 / 2 : ℝ) * vecDot (annealedAdjointOptimizerGradient P U p q)
      (annealedAdjointOptimizerFlux P U p q)

/-- The skew part `h_rsp = 1/2 (K-Kᵗ)` of the annealed Schur coordinate. -/
@[expose]
def responseSkew (K : Mat d) : Mat d :=
  (2 : ℝ)⁻¹ • (K - Kᴴ)

/-- The symmetric part `k_rsp = 1/2 (K+Kᵗ)` of the annealed Schur coordinate. -/
@[expose]
def responseSymmetric (K : Mat d) : Mat d :=
  (2 : ℝ)⁻¹ • (K + Kᴴ)

/-- The corrected response block
`b_rsp = S + k_rspᵗ S_*⁻¹ k_rsp`. -/
@[expose]
def centeredResponseBlock (S SStar K : Mat d) : Mat d :=
  S + (responseSymmetric K)ᴴ * SStar⁻¹ * responseSymmetric K

/-- The response metric `m_rsp = b_rsp # S_*`. -/
@[expose]
def centeredResponseMetric (S SStar K : Mat d) : Mat d :=
  matGeomMean (centeredResponseBlock S SStar K) SStar

/-- The response-coordinate load `p_e = m_rsp^{-1/2} e`. -/
@[expose]
def centeredResponseLoadP (S SStar K : Mat d) (e : Vec d) : Vec d :=
  matSqrt (centeredResponseMetric S SStar K)⁻¹ *ᵥ e

/-- The response-coordinate load `q_e = m_rsp^{1/2} e`. -/
@[expose]
def centeredResponseLoadQ (S SStar K : Mat d) (e : Vec d) : Vec d :=
  matSqrt (centeredResponseMetric S SStar K) *ᵥ e

end

end HCPolySupport.HighContrast.Response
