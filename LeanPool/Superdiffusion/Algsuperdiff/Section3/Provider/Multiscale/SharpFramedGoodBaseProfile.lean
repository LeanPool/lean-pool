/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedMeanLayerProperties

/-!
# SharpFramedGoodBaseProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic good-mass base profile in the framed layer envelope

The good-cell part of `probeSharpFramedMeanLayerEnvelope` contains the
deterministic summand
`probeMeanGoodBaseConst d * vecNormSq p * probeSharpLayerMassEnvelope d n`.
This file sums that literal term over the Whitney-layer index and over the
coordinate basis.  The resulting bound is dimension-only.

No collar mass, wave term, random factor, depth aggregation, or cutoff block
carrier is treated here.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-- The literal deterministic good-mass base summand for one layer and one
coordinate. -/
def probeSharpGoodBaseLayer (d n : ℕ) (j : Fin d) : ℝ :=
  probeMeanGoodBaseConst d * vecNormSq (basisVec j) *
    probeSharpLayerMassEnvelope d n

/-- The dimension-only sum of one coordinate's deterministic good-mass base
layers. -/
def probeSharpGoodBaseCoordinateConst (d : ℕ) : ℝ :=
  9 * (d : ℝ) * probeMeanGoodBaseConst d

/-- The dimension-only sum after the finite coordinate trace. -/
def probeSharpGoodBaseConst (d : ℕ) : ℝ :=
  (d : ℝ) * probeSharpGoodBaseCoordinateConst d

theorem probeSharpGoodBaseLayer_nonneg
    (hd : 2 ≤ d) (n : ℕ) (j : Fin d) :
    0 ≤ probeSharpGoodBaseLayer d n j := by
  rw [probeSharpGoodBaseLayer]
  exact mul_nonneg
    (mul_nonneg (probeMeanGoodBaseConst_nonneg hd) (vecNormSq_nonneg _))
    (probeSharpLayerMassEnvelope_nonneg d n)

theorem probeSharpGoodBaseCoordinateConst_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpGoodBaseCoordinateConst d := by
  rw [probeSharpGoodBaseCoordinateConst]
  exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    (probeMeanGoodBaseConst_nonneg hd)

theorem probeSharpGoodBaseConst_nonneg
    (hd : 2 ≤ d) :
    0 ≤ probeSharpGoodBaseConst d := by
  rw [probeSharpGoodBaseConst]
  exact mul_nonneg (Nat.cast_nonneg d)
    (probeSharpGoodBaseCoordinateConst_nonneg hd)

private theorem three_rpow_neg_nat_eq (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℝ)) = ((1 : ℝ) / 3) ^ n := by
  rw [show -(n : ℝ) = (-1 : ℝ) * (n : ℝ) by ring,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  norm_num


private theorem tsum_probeSharpLayerMassEnvelope (d : ℕ) :
    ∑' n : ℕ, probeSharpLayerMassEnvelope d n = 9 * (d : ℝ) := by
  calc
    ∑' n : ℕ, probeSharpLayerMassEnvelope d n =
        6 * (d : ℝ) * ∑' n : ℕ, ((1 : ℝ) / 3) ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [probeSharpLayerMassEnvelope, three_rpow_neg_nat_eq]
    _ = 6 * (d : ℝ) * (1 - (1 : ℝ) / 3)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one (by norm_num)]
    _ = 9 * (d : ℝ) := by ring

/-- One coordinate's deterministic good-mass base layers sum to the explicit
dimension-only constant. -/
theorem tsum_probeSharpGoodBaseLayer_eq
    (d : ℕ) (j : Fin d) :
    ∑' n : ℕ, probeSharpGoodBaseLayer d n j =
      probeSharpGoodBaseCoordinateConst d := by
  rw [probeSharpGoodBaseCoordinateConst, ← tsum_probeSharpLayerMassEnvelope d]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  rw [probeSharpGoodBaseLayer, vecNormSq_basisVec]
  ring


end

end Algsuperdiff.Section3.Provider.Multiscale
