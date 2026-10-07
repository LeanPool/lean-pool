/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorMap
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselEmbedding
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselSchwartzPhysical

/-!
# The quadratic regularized tensor on complete Sobolev data

The bounded bilinear map and the continuous physical L² realization
give a locally Lipschitz quadratic nonlinearity in H²ᵏ.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The complete Sobolev tensor formed from one Sobolev velocity and
its underlying spatial L² field. -/
@[expose]
def regularisedBesselTensorQuadratic
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (u : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2 :=
  regularisedBesselTensorMap ρ ε hε k
    (regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity) u) u

/-- The quadratic tensor grows at most quadratically in the complete
H²ᵏ norm. -/
theorem regularisedBesselTensorQuadratic_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (u : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    ‖regularisedBesselTensorQuadratic ρ ε hε k u‖ ≤
      regularisedBesselTensorConstant ρ ε hε k * ‖u‖ ^ 2 := by
  let F := regularisedBesselTensorMap ρ ε hε k
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hF := (regularisedBesselTensorMap_norm_le ρ ε hε k).2
  have hE : ‖E u‖ ≤ ‖u‖ :=
    regularisedBesselSobolevToL2_norm_le ((2 * k : ℕ) : ℝ)
      (by positivity) u
  change ‖F (E u) u‖ ≤
    regularisedBesselTensorConstant ρ ε hε k * ‖u‖ ^ 2
  calc
    ‖F (E u) u‖ ≤ ‖F‖ * ‖E u‖ * ‖u‖ := F.le_opNorm₂ _ _
    _ ≤ regularisedBesselTensorConstant ρ ε hε k * ‖u‖ * ‖u‖ := by
      gcongr
    _ = regularisedBesselTensorConstant ρ ε hε k * ‖u‖ ^ 2 := by ring

/-- The quadratic tensor is locally Lipschitz in the complete H²ᵏ
norm, with the two factors displayed separately. -/
theorem regularisedBesselTensorQuadratic_difference_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (u v : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    ‖regularisedBesselTensorQuadratic ρ ε hε k u -
      regularisedBesselTensorQuadratic ρ ε hε k v‖ ≤
      regularisedBesselTensorConstant ρ ε hε k *
        ‖u - v‖ * (‖u‖ + ‖v‖) := by
  let F := regularisedBesselTensorMap ρ ε hε k
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  have hF := (regularisedBesselTensorMap_norm_le ρ ε hε k).2
  have hE : ‖E (u - v)‖ ≤ ‖u - v‖ :=
    regularisedBesselSobolevToL2_norm_le ((2 * k : ℕ) : ℝ)
      (by positivity) (u - v)
  have hEv : ‖E v‖ ≤ ‖v‖ :=
    regularisedBesselSobolevToL2_norm_le ((2 * k : ℕ) : ℝ)
      (by positivity) v
  have hId : F (E u) u - F (E v) v =
      F (E (u - v)) u + F (E v) (u - v) := by
    rw [map_sub E, map_sub F, sub_apply, map_sub]
    abel
  change ‖F (E u) u - F (E v) v‖ ≤
    regularisedBesselTensorConstant ρ ε hε k *
      ‖u - v‖ * (‖u‖ + ‖v‖)
  rw [hId]
  calc
    ‖F (E (u - v)) u + F (E v) (u - v)‖ ≤
        ‖F (E (u - v)) u‖ + ‖F (E v) (u - v)‖ := norm_add_le _ _
    _ ≤ ‖F‖ * ‖E (u - v)‖ * ‖u‖ +
        ‖F‖ * ‖E v‖ * ‖u - v‖ := by
      exact add_le_add (F.le_opNorm₂ _ _) (F.le_opNorm₂ _ _)
    _ ≤ regularisedBesselTensorConstant ρ ε hε k *
          ‖u - v‖ * (‖u‖ + ‖v‖) := by
      have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
      calc
        ‖F‖ * ‖E (u - v)‖ * ‖u‖ + ‖F‖ * ‖E v‖ * ‖u - v‖ ≤
            regularisedBesselTensorConstant ρ ε hε k * ‖E (u - v)‖ * ‖u‖ +
              regularisedBesselTensorConstant ρ ε hε k * ‖E v‖ * ‖u - v‖ := by
          gcongr
        _ ≤ regularisedBesselTensorConstant ρ ε hε k * ‖u - v‖ * ‖u‖ +
              regularisedBesselTensorConstant ρ ε hε k * ‖v‖ * ‖u - v‖ := by
          gcongr
        _ = regularisedBesselTensorConstant ρ ε hε k * ‖u - v‖ *
              (‖u‖ + ‖v‖) := by ring

end CKN.Leray

end
