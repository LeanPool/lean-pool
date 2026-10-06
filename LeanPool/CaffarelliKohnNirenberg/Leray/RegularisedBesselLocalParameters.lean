/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselClampedTensorPath

/-!
# Local lifespan for the complete Sobolev mild equation

The lifespan is chosen from a positive bound for the tensor map and
the initial complete Sobolev norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A positive coefficient larger than the complete tensor operator norm. -/
@[expose]
def regularisedBesselLocalCoefficient
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ) : ℝ :=
  1 + regularisedBesselTensorConstant ρ ε hε k

/-- The closed ball radius used for the complete Sobolev contraction. -/
@[expose]
def regularisedBesselLocalRadius
    (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) : ℝ :=
  2 * (1 + ‖b‖)

/-- A strictly positive local lifespan for complete H²ᵏ data. -/
@[expose]
def regularisedBesselLocalLifespan
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) : ℝ :=
  (16 * regularisedBesselLocalCoefficient ρ ε hε k * (1 + ‖b‖))⁻¹ ^ 2

/-- The coefficient defining the complete Sobolev lifespan is positive. -/
theorem regularisedBesselLocalCoefficient_pos
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    0 < regularisedBesselLocalCoefficient ρ ε hε k := by
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  unfold regularisedBesselLocalCoefficient
  linarith only [hC]

/-- The complete Sobolev local lifespan is positive. -/
theorem regularisedBesselLocalLifespan_pos
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    0 < regularisedBesselLocalLifespan ρ ε hε k b := by
  unfold regularisedBesselLocalLifespan
  have hbase : 0 < 16 * regularisedBesselLocalCoefficient ρ ε hε k *
      (1 + ‖b‖) := by
    have hcoeff := regularisedBesselLocalCoefficient_pos ρ ε hε k
    positivity
  exact sq_pos_of_pos (inv_pos.mpr hbase)

/-- The square root of the lifespan equals its positive inverse scale. -/
theorem regularisedBesselLocalLifespan_sqrt
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) :
    Real.sqrt (regularisedBesselLocalLifespan ρ ε hε k b) =
      (16 * regularisedBesselLocalCoefficient ρ ε hε k * (1 + ‖b‖))⁻¹ := by
  unfold regularisedBesselLocalLifespan
  rw [Real.sqrt_sq_eq_abs]
  have hcoeff := regularisedBesselLocalCoefficient_pos ρ ε hε k
  exact abs_of_pos (inv_pos.mpr (by positivity))

end CKN.Leray

end
