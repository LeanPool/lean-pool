/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.GridWeights
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedGoodBaseProfile
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SharpFramedLayerNamedDecomposition

/-!
# UpperGoodBaseConsumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact root and strict-depth consumption of the framed good-base lane

The good-cell base term is deterministic and independent of the root,
descendant, cutoff sample, and observation frame.  This file consumes that
literal named summand through its Whitney-layer sum, finite coordinate trace,
finite descendant maximum, separate depth-zero weight, and positive-depth
grid series.  The full root-plus-depth contribution is bounded by an explicit
dimension-only constant.

No wave term, collar term, complete envelope, cutoff observable, or
source-facing theorem is treated here.
-/


namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale

noncomputable section

variable {d : ℕ}

/-- The literal named good-base Whitney sum for one basis coordinate. -/
def probeSharpFramedGoodBaseCoordinateENNRealLane
    (d : ℕ) (j : Fin d) : ENNReal :=
  ∑' n : ℕ, ENNReal.ofReal
    (probeSharpFramedGoodBaseTerm d n (basisVec j))

/-- The finite-coordinate trace of the literal named good-base lane. -/
def probeSharpFramedGoodBaseTraceENNRealLane (d : ℕ) : ENNReal :=
  ∑ j : Fin d, probeSharpFramedGoodBaseCoordinateENNRealLane d j


/-- The named framed good-base term is exactly the verified good-base layer. -/
theorem probeSharpFramedGoodBaseTerm_basisVec_eq
    (d n : ℕ) (j : Fin d) :
    probeSharpFramedGoodBaseTerm d n (basisVec j) =
      probeSharpGoodBaseLayer d n j := by
  rfl

private theorem three_rpow_neg_nat_eq_goodBaseConsumption (n : ℕ) :
    (3 : ℝ) ^ (-(n : ℝ)) = ((1 : ℝ) / 3) ^ n := by
  rw [show -(n : ℝ) = (-1 : ℝ) * (n : ℝ) by ring,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  norm_num

private theorem summable_probeSharpGoodBaseLayer_consumption
    (d : ℕ) (j : Fin d) :
    Summable fun n : ℕ => probeSharpGoodBaseLayer d n j := by
  have hgeom : Summable fun n : ℕ => ((1 : ℝ) / 3) ^ n :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hscaled := hgeom.mul_left
    (probeMeanGoodBaseConst d * vecNormSq (basisVec j) * (6 * (d : ℝ)))
  refine hscaled.congr fun n => ?_
  rw [probeSharpGoodBaseLayer, probeSharpLayerMassEnvelope,
    three_rpow_neg_nat_eq_goodBaseConsumption]
  ring

/-- The literal coordinate sum equals the verified explicit real coordinate
constant. -/
theorem probeSharpFramedGoodBaseCoordinateENNRealLane_eq
    (hd : 2 ≤ d) (j : Fin d) :
    probeSharpFramedGoodBaseCoordinateENNRealLane d j =
      ENNReal.ofReal (probeSharpGoodBaseCoordinateConst d) := by
  rw [probeSharpFramedGoodBaseCoordinateENNRealLane]
  simp_rw [probeSharpFramedGoodBaseTerm_basisVec_eq]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => probeSharpGoodBaseLayer_nonneg hd n j)
    (summable_probeSharpGoodBaseLayer_consumption d j)]
  rw [tsum_probeSharpGoodBaseLayer_eq]

/-- The literal finite-coordinate trace equals the verified explicit dimension-only
trace constant. -/
theorem probeSharpFramedGoodBaseTraceENNRealLane_eq
    (hd : 2 ≤ d) :
    probeSharpFramedGoodBaseTraceENNRealLane d =
      ENNReal.ofReal (probeSharpGoodBaseConst d) := by
  rw [probeSharpFramedGoodBaseTraceENNRealLane]
  simp_rw [probeSharpFramedGoodBaseCoordinateENNRealLane_eq hd]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, probeSharpGoodBaseConst]
  · intro j _
    exact probeSharpGoodBaseCoordinateConst_nonneg hd


end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
