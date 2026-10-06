/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselMildContinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap

/-!
# Complete Sobolev tensor paths on a closed time interval

Clamping a Sobolev velocity path to its lifespan gives a continuous
quadratic tensor path with a uniform bound and a local Lipschitz estimate.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete H²ᵏ tensor path, extended to real time by clamping. -/
@[expose]
def regularisedBesselClampedTensorPath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2 :=
  fun s => regularisedBesselTensorQuadratic ρ ε hε k
    (u (regularizedMildTimeClamp T hT s))

/-- The clamped complete tensor path is continuous. -/
theorem regularisedBesselClampedTensorPath_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    Continuous (regularisedBesselClampedTensorPath ρ ε hε k T hT u) := by
  exact (regularisedBesselTensorQuadratic_continuous ρ ε hε k).comp
    (u.continuous.comp (regularizedMildTimeClamp_continuous T hT))

/-- A uniform velocity bound gives a quadratic bound for the
clamped complete tensor path. -/
theorem regularisedBesselClampedTensorPath_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (u : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (R : ℝ) (hR : 0 ≤ R) (hu : ∀ t, ‖u t‖ ≤ R) (s : ℝ) :
    ‖regularisedBesselClampedTensorPath ρ ε hε k T hT u s‖ ≤
      regularisedBesselTensorConstant ρ ε hε k * R ^ 2 := by
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hsq : ‖u (regularizedMildTimeClamp T hT s)‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).2
      (hu (regularizedMildTimeClamp T hT s))
  exact (regularisedBesselTensorQuadratic_norm_le ρ ε hε k
    (u (regularizedMildTimeClamp T hT s))).trans
      (mul_le_mul_of_nonneg_left hsq hC)

/-- On a common bounded ball, the clamped complete tensor path is
Lipschitz in the trajectory supremum norm. -/
theorem regularisedBesselClampedTensorPath_difference_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (u v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (R : ℝ)
    (hu : ∀ t, ‖u t‖ ≤ R) (hv : ∀ t, ‖v t‖ ≤ R) (s : ℝ) :
    ‖regularisedBesselClampedTensorPath ρ ε hε k T hT u s -
      regularisedBesselClampedTensorPath ρ ε hε k T hT v s‖ ≤
      regularisedBesselTensorConstant ρ ε hε k * (2 * R) * ‖u - v‖ := by
  let q := regularizedMildTimeClamp T hT s
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hdiff : ‖u q - v q‖ ≤ ‖u - v‖ := by
    simpa using (u - v).norm_coe_le_norm q
  have hsum : ‖u q‖ + ‖v q‖ ≤ 2 * R := by
    have h1 := hu q
    have h2 := hv q
    linarith only [h1, h2]
  calc
    ‖regularisedBesselClampedTensorPath ρ ε hε k T hT u s -
        regularisedBesselClampedTensorPath ρ ε hε k T hT v s‖ ≤
      regularisedBesselTensorConstant ρ ε hε k *
        ‖u q - v q‖ * (‖u q‖ + ‖v q‖) := by
          exact regularisedBesselTensorQuadratic_difference_norm_le
            ρ ε hε k (u q) (v q)
    _ ≤ regularisedBesselTensorConstant ρ ε hε k *
          ‖u - v‖ * (2 * R) := by gcongr
    _ = regularisedBesselTensorConstant ρ ε hε k * (2 * R) * ‖u - v‖ := by ring

end CKN.Leray

end
