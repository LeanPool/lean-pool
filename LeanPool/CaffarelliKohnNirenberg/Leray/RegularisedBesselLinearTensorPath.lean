/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLocalMap

/-!
# Linearized complete Sobolev tensor path

Fixing the physical L² velocity in the first factor of the regularized
tensor leaves a bounded linear map in its complete Sobolev second factor.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The clamped complete tensor path with a prescribed physical L²
first factor and an unknown complete Sobolev second factor. -/
@[expose]
def regularisedBesselLinearTensorPath
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2 :=
  fun s => regularisedBesselTensorMap ρ ε hε k
    (g (regularizedMildTimeClamp T hT s))
    (v (regularizedMildTimeClamp T hT s))

/-- The prescribed L² path and complete Sobolev path produce a
continuous complete tensor path. -/
theorem regularisedBesselLinearTensorPath_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)) :
    Continuous (regularisedBesselLinearTensorPath ρ ε hε k T hT g v) := by
  unfold regularisedBesselLinearTensorPath
  exact (regularisedBesselTensorMap ρ ε hε k).continuous₂.comp₂
    (g.continuous.comp (regularizedMildTimeClamp_continuous T hT))
    (v.continuous.comp (regularizedMildTimeClamp_continuous T hT))

/-- A uniform physical L² bound makes the linearized tensor path
bounded linearly in the complete Sobolev trajectory norm. -/
theorem regularisedBesselLinearTensorPath_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ q, ‖g q‖ ≤ B)
    (s : ℝ) :
    ‖regularisedBesselLinearTensorPath ρ ε hε k T hT g v s‖ ≤
      regularisedBesselTensorConstant ρ ε hε k * B * ‖v‖ := by
  let F := regularisedBesselTensorMap ρ ε hε k
  let q := regularizedMildTimeClamp T hT s
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  change ‖F (g q) (v q)‖ ≤
    regularisedBesselTensorConstant ρ ε hε k * B * ‖v‖
  calc
    ‖F (g q) (v q)‖ ≤ ‖F‖ * ‖g q‖ * ‖v q‖ := F.le_opNorm₂ _ _
    _ ≤ regularisedBesselTensorConstant ρ ε hε k * B * ‖v q‖ := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (regularisedBesselTensorMap_norm_le ρ ε hε k).2
          (norm_nonneg (g q))) (norm_nonneg (v q))
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg q) hC) (norm_nonneg (v q))
      exact h1.trans h2
    _ ≤ regularisedBesselTensorConstant ρ ε hε k * B * ‖v‖ :=
      mul_le_mul_of_nonneg_left (v.norm_coe_le_norm q)
        (mul_nonneg hC hB)

/-- With the physical coefficient fixed, the complete tensor path is
globally Lipschitz in the Sobolev trajectory norm. -/
theorem regularisedBesselLinearTensorPath_difference_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (g : C(RegularizedMildTimeInterval T, ComplexVectorL2))
    (v w : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (B : ℝ) (hB : 0 ≤ B) (hg : ∀ q, ‖g q‖ ≤ B)
    (s : ℝ) :
    ‖regularisedBesselLinearTensorPath ρ ε hε k T hT g v s -
      regularisedBesselLinearTensorPath ρ ε hε k T hT g w s‖ ≤
      regularisedBesselTensorConstant ρ ε hε k * B * ‖v - w‖ := by
  let F := regularisedBesselTensorMap ρ ε hε k
  let q := regularizedMildTimeClamp T hT s
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  change ‖F (g q) (v q) - F (g q) (w q)‖ ≤ _
  rw [← map_sub]
  calc
    ‖F (g q) (v q - w q)‖ ≤ ‖F‖ * ‖g q‖ * ‖v q - w q‖ :=
      F.le_opNorm₂ _ _
    _ ≤ regularisedBesselTensorConstant ρ ε hε k * B * ‖v - w‖ := by
      have h1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (regularisedBesselTensorMap_norm_le ρ ε hε k).2
          (norm_nonneg (g q))) (norm_nonneg (v q - w q))
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg q) hC)
        (norm_nonneg (v q - w q))
      have h3 : ‖v q - w q‖ ≤ ‖v - w‖ := by
        simpa using (v - w).norm_coe_le_norm q
      exact (h1.trans h2).trans
        (mul_le_mul_of_nonneg_left h3 (mul_nonneg hC hB))

end CKN.Leray

end
