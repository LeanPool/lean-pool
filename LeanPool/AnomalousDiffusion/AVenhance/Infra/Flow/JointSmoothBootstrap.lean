/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointC3All

/-! An all-orders joint-flow bootstrap from regularity of the spatial jet. -/

@[expose] public section

open Homogenization
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Observation-time velocity in the arbitrary-order joint smoothness bootstrap. -/
def JointSmoothBootstrap.flowTimeVelocityN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  JointC1.flowTimeVelocity b X p

/-- Spatial Jacobian in the arbitrary-order joint smoothness bootstrap. -/
def JointSmoothBootstrap.flowSpatialJacobianN
    (X : ℝ → Vec 2 → ℝ → Vec 2) (p : ℝ × Vec 2 × ℝ) :
    Vec 2 →L[ℝ] Vec 2 :=
  JointC1.flowSpatialDerivativeAt X p

/-- Starting-time velocity in the arbitrary-order joint smoothness bootstrap. -/
def JointSmoothBootstrap.flowStartVelocityN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : Vec 2 :=
  JointC1.flowStartVelocity b X p

/-- Starting-time differential in the arbitrary-order joint smoothness bootstrap. -/
def JointSmoothBootstrap.flowStartCLMN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : ℝ →L[ℝ] Vec 2 :=
  JointC1.flowStartDerivativeCLM b X p

/-- Position and starting-time differential in the arbitrary-order joint smoothness bootstrap. -/
def JointSmoothBootstrap.flowParameterDerivativeN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  JointC1.flowPairDerivativeAt b X p

/-- Full joint differential in the arbitrary-order joint smoothness bootstrap. -/
def JointSmoothBootstrap.flowJointDerivativeN
    (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (p : ℝ × Vec 2 × ℝ) : (ℝ × Vec 2 × ℝ) →L[ℝ] Vec 2 :=
  JointC1.flowJointDerivativeAt b X p

end

end AVenhance.Infra.Flow
