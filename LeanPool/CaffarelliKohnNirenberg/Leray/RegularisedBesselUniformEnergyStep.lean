/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselTensorQuadratic
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselClampedTensorPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLocalMap

/-!
# Uniform time step for complete Sobolev energy control

The physical L² energy bound fixes a positive time step on which the
complete Sobolev mild estimate can always be absorbed.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A time step depending on the physical L² bound and the regularized
tensor operator, independent of the current H²ᵏ norm. -/
@[expose]
def regularisedBesselUniformEnergyStep
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (B : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.exp 1) /
    (8 * (1 + regularisedBesselTensorConstant ρ ε hε k * B))) ^ 2

/-- The complete Sobolev energy time step is strictly positive under
a nonnegative physical L² bound. -/
theorem regularisedBesselUniformEnergyStep_pos
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    0 < regularisedBesselUniformEnergyStep ρ ε hε k B := by
  have hC := (regularisedBesselTensorMap_norm_le ρ ε hε k).1
  have hbase : 0 < 8 * (1 + regularisedBesselTensorConstant ρ ε hε k * B) := by
    have hmul := mul_nonneg hC hB
    positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.exp 1) :=
    Real.sqrt_pos.2 (by positivity)
  unfold regularisedBesselUniformEnergyStep
  exact sq_pos_of_pos (div_pos hsqrt hbase)

/-- The uniform energy time step makes the Abel coefficient at most
one half, independently of the complete Sobolev norm. -/
theorem regularisedBesselUniformEnergyStep_small
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    2 * ((regularisedBesselTensorConstant ρ ε hε k * B) /
      Real.sqrt (2 * Real.exp 1)) *
        Real.sqrt (regularisedBesselUniformEnergyStep ρ ε hε k B) ≤
      1 / 2 := by
  let D := regularisedBesselTensorConstant ρ ε hε k * B
  let S := Real.sqrt (2 * Real.exp 1)
  have hD : 0 ≤ D :=
    mul_nonneg (regularisedBesselTensorMap_norm_le ρ ε hε k).1 hB
  have hS : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hden : 0 < 8 * (1 + D) := by positivity
  have hsqrt : Real.sqrt (regularisedBesselUniformEnergyStep ρ ε hε k B) =
      S / (8 * (1 + D)) := by
    change Real.sqrt ((S / (8 * (1 + D))) ^ 2) = _
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hS hden)]
  rw [hsqrt]
  change 2 * (D / S) * (S / (8 * (1 + D))) ≤ 1 / 2
  have hDle : D / (4 * (1 + D)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + D))).2
    nlinarith only [hD]
  calc
    2 * (D / S) * (S / (8 * (1 + D))) =
      D / (4 * (1 + D)) := by field_simp; ring
    _ ≤ 1 / 4 := hDle
    _ ≤ 1 / 2 := by norm_num

end CKN.Leray

end
