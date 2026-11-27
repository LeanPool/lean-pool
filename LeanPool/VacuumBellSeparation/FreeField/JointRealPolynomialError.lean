/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointRealCoordinates
public import LeanPool.VacuumBellSeparation.FreeField.JointPhysicalPolynomialError
public import LeanPool.VacuumBellSeparation.Polynomial.ComplexDerivativeRestriction
public import LeanPool.VacuumBellSeparation.FreeField.JointSmoothKernelLocalBound

/-!
# Actual real Euclidean derivatives of the physical polynomial error

Complex derivative estimates are transferred by the original real-linear
coordinate inclusion. Smoothness holds on an open radius-three box around
each actual component, so the local cutoff construction applies directly.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open Gaussian MvPolynomial Metric Set

/-- Joint real polynomial error defined as `jointPhysicalPolynomialError F s n a b ∘
jointComplexCoordinates`. -/
def jointRealPolynomialError (F : (Fin 6 → ℂ) → ℂ) (s : ℝ) (n : ℕ)
    (a b : Bool) : JointKernelSpace → ℂ :=
  jointPhysicalPolynomialError F s n a b ∘ jointComplexCoordinates

/-- Set of points satisfying the joint open component box condition. -/
def jointOpenComponentBox (s : ℝ) (a b : Bool) : Set JointKernelSpace :=
  {x | x.fst ∈ ball (jointSpatialCenter s a) 3 ∧ x.snd ∈ ball (jointSpatialCenter s b) 3}

theorem isOpen_jointOpenComponentBox (s : ℝ) (a b : Bool) :
    IsOpen (jointOpenComponentBox s a b) :=
  (isOpen_ball.preimage
    (WithLp.fstL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))).continuous).inter
      (isOpen_ball.preimage
        (WithLp.sndL 2 ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))).continuous)

theorem jointKernelBox_subset_openComponent (s : ℝ) (a b : Bool) :
    jointKernelBox (jointSpatialCenter s a) (jointSpatialCenter s b) 2 ⊆
      jointOpenComponentBox s a b := by
  intro x hx
  exact ⟨lt_of_le_of_lt hx.1 (by norm_num : (2 : ℝ) < 3),
    lt_of_le_of_lt hx.2 (by norm_num : (2 : ℝ) < 3)⟩

theorem jointRealPolynomialError_contDiffOn {s : ℝ} (hs : 600 ≤ s)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (n : ℕ) (a b : Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (jointRealPolynomialError F s n a b) (jointOpenComponentBox s a b) := by
  intro x hx
  have hs₀ : 0 < s := by linarith
  have hsmall : 3 / s ≤ 1 / 100 := (div_le_iff₀ hs₀).mpr (by linarith)
  have hw := (jointComplexCoordinates_in_component s 3 a b x
    (ball_subset_closedBall hx.1) (ball_subset_closedBall hx.2)).normalize hs₀
  have ha : AnalyticAt ℂ (jointPhysicalPolynomialError F s n a b) (jointComplexCoordinates x) :=
    ((jointComponentKernel_analyticAt hsmall F hF a b _ hw).sub
      (jointMidpointPolynomial_analyticAt F n _)).comp (jointPhysicalMidpoint_analyticAt s _)
  have hc : ContDiffAt ℂ (⊤ : ℕ∞) (jointPhysicalPolynomialError F s n a b)
      (jointComplexCoordinates x) := ha.contDiffAt
  exact ((hc.restrict_scalars ℝ).comp x
    jointComplexCoordinates.contDiff.contDiffAt).contDiffWithinAt

theorem jointRealPolynomialError_derivative {s M : ℝ} (hs : 600 ≤ s) (hM : 0 ≤ M)
    (F : (Fin 6 → ℂ) → ℂ)
    (hF : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), AnalyticAt ℂ F z)
    (hbound : ∀ z ∈ coordinateClosedPolydisc 6 (1 / 100), ‖F z‖ ≤ M)
    (n : ℕ) (a b : Bool) (x : JointKernelSpace)
    (hx : x ∈ jointKernelBox (jointSpatialCenter s a) (jointSpatialCenter s b) 2)
    {k : ℕ} (hk : k ≤ 4) :
    ‖iteratedFDeriv ℝ k (jointRealPolynomialError F s n a b) x‖ ≤
      11680000 * M * (78643200 / s) ^ n := by
  have hw := jointComplexCoordinates_in_component s 2 a b x hx.1 hx.2
  have h := jointPhysicalPolynomialError_ball hs hM F hF hbound n a b _ hw
  have hs₀ : 0 < s := by linarith
  exact (norm_iteratedFDeriv_real_comp_le jointComplexCoordinates norm_jointComplexCoordinates_le
    x (by positivity) h.1 h.2 hk).trans_eq (by ring)

end VacuumBellSeparation
