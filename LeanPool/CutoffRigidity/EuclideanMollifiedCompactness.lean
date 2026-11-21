/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanL2MollificationGeneral
public import LeanPool.CutoffRigidity.CompactZeroExtension

/-! # Actual compactness of mollified bounded-support L² families

Actual smooth convolution supplies uniform sup and Lipschitz bounds.
Arzelà--Ascoli and the proved continuous zero extension into ambient L²
then give compact closure. No Sobolev compactness theorem is assumed.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution Pointwise

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Common compact support proves actual mollified L² membership even for
measurable L² inputs without classical differentiability. -/
theorem bumpMollification_memLp_of_commonSupport (φ : ContDiffBump (0 : E))
    {f : E → ℝ} (hf : MemLp f 2 volume) {K : Set E} (hK : IsCompact K)
    (hsupp : ∀ x ∉ K, f x = 0) : MemLp (bumpMollification φ f) 2 volume := by
  have hK' : IsCompact (Metric.closedBall (0 : E) φ.rOut + K) := (isCompact_closedBall _ _).add hK
  exact continuous_commonSupport_memLp volume hK' hK'.measure_lt_top.ne
    (bumpMollification φ f) (bumpMollification_contDiff φ (hf.locallyIntegrable
      (by norm_num))).continuous
    (bumpMollification_eq_zero_off_add_support φ hsupp)

/-- Actual compact closure in Euclidean Lebesgue L² of every fixed-kernel
mollified L²-bounded family with one common compact support. -/
theorem isCompact_closure_bumpMollification_L2_family {ι : Type*}
    (φ : ContDiffBump (0 : E)) (f : ι → E → ℝ) (hf : ∀ i, MemLp (f i) 2 volume)
    {K : Set E} (hK : IsCompact K) (hsupp : ∀ i x, x ∉ K → f i x = 0)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ‖(hf i).toLp (f i)‖ ≤ M) :
    IsCompact (closure (Set.range (fun i =>
      (bumpMollification_memLp_of_commonSupport φ (hf i) hK (hsupp i)).toLp (bumpMollification φ (f
        i))))) := by
  let K' := Metric.closedBall (0 : E) φ.rOut + K
  have hK' : IsCompact K' := (isCompact_closedBall _ _).add hK
  let N := ‖(c1_compact_gradient_memLp (φ.contDiff_normed (n := 1)) φ.hasCompactSupport_normed).toLp
    (gradient (φ.normed volume))‖
  have hN : 0 ≤ N := norm_nonneg _
  let B := (‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ *
    ‖(bumpKernel_memLp φ).toLp (φ.normed volume)‖) * M
  let L := Real.toNNReal (N * M)
  have hcont (i : ι) : Continuous (bumpMollification φ (f i)) :=
    (bumpMollification_contDiff φ ((hf i).locallyIntegrable (by norm_num))).continuous
  have hs (i : ι) (x : E) (hx : x ∉ K') : bumpMollification φ (f i) x = 0 :=
    bumpMollification_eq_zero_off_add_support φ (hsupp i) x hx
  have hb (i : ι) (x : E) : |bumpMollification φ (f i) x| ≤ B := by
    exact ((bumpMollification_uniform_bounds φ (hf i) M (hbound i) x).1)
  have hl (i : ι) : LipschitzWith L (bumpMollification φ (f i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := (bumpMollification_lipschitzWith φ (hf i)).dist_le_mul x y
    change dist (bumpMollification φ (f i) x) (bumpMollification φ (f i) y) ≤
      max (N * ‖(hf i).toLp (f i)‖) 0 * dist x y at hh
    rw [max_eq_left (mul_nonneg hN (norm_nonneg _))] at hh
    change dist (bumpMollification φ (f i) x) (bumpMollification φ (f i) y) ≤ max (N * M) 0 * dist
      x y
    rw [max_eq_left (mul_nonneg hN hM)]
    exact hh.trans (by gcongr; exact hbound i)
  exact isCompact_closure_commonSupport_L2_family volume hK' hK'.measure_lt_top.ne
    (fun i => bumpMollification φ (f i)) hcont hs B L hb hl

end CutoffRigidity
