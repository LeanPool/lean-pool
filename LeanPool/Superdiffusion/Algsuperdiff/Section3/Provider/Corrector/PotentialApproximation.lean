/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.RealizationTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.StationaryStrip
public import LeanPool.HighContrastHomogenization.Support.Geometry.OriginCubeBoundaryPush
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.QuantitativeCutoff
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidal

/-!
# PotentialApproximation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the potential half of the local-approximation lemma

This file proves the cutoff core of part (i) of
`l.approximation.stationary.by.local`:

> **(i) Potential approximation.**  For every `L ∈ ℕ` there exists a family >
`{v_{K,L}}_{K ∈ ℕ}` with `v_{K,L} ∈ H¹₀(cu_K)` such that > `limsup_{K→∞} E[
‖∇v_{K,L} − p‖²_{L²(cu_K)} ] ≤^{−L} E[|p|²]`.

The paper's proof fixes `η_{K,L} ∈ C_c^∞(cu_K)` equal to `1` away from a
boundary strip of relative width `3^{−L}` and with `|∇η_{K,L}| ≤^{L−K}`, takes
a spatial primitive `φ` of `p` and sets `v_{K,L} := η_{K,L}(φ − (φ)_{cu_K})`.
The error splits as `∇v_{K,L} − p = (η_{K,L} − 1) p + (φ − (φ)_{cu_K})
∇η_{K,L}`, the first term being controlled by the strip volume
`e.boundary.strip.volume` and the second by the sublinearity of `φ`.

Here the primitive is taken from the *stationary* `L²` layer: `φ` is a
square-integrable random variable whose spatial realization is a smooth
primitive of the realization of `p`.  For such a primitive no mean subtraction
and no sublinearity input is needed: the second error term is bounded by
`‖∇η_{K,L}‖²_∞ E[φ²] ≍ 3^{2(L−K)} E[φ²]`, which already tends to `0` as `K → ∞`
at fixed `L` because `E[φ²]` is finite.

The cutoff is CoarseGraining's
`Homogenization.QuantitativeCubeCutoff.canonical` at the concentric ratios `ρ₁
= 1 − 3^{−L}/2` and `ρ₂ = 1 − 3^{−L}/4`; the strip fraction `1 − ρ₁ ^ d ≤ d ·
3^{−L}/2` comes from
`Algsuperdiff/Section3/Provider/Corrector/BoundaryStrip.lean`, so the paper's
`C` is chosen explicitly as `C = d` (design decision `D-6`).
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### The concentric ratios of the paper's cutoff -/

/-- Inner concentric ratio of the localization cutoff at scale `L`: the cutoff
equals `1` on the subcube of relative radius `1 − 3^{−L}/2`. -/
def cutoffInnerRatio (L : ℕ) : ℝ := 1 - (3 : ℝ) ^ (-(L : ℤ)) / 2

/-- Outer concentric ratio of the localization cutoff at scale `L`: the cutoff
is supported in the subcube of relative radius `1 − 3^{−L}/4`. -/
def cutoffOuterRatio (L : ℕ) : ℝ := 1 - (3 : ℝ) ^ (-(L : ℤ)) / 4

theorem three_zpow_neg_pos (L : ℕ) : 0 < (3 : ℝ) ^ (-(L : ℤ)) :=
  zpow_pos (by norm_num) _

theorem three_zpow_neg_le_one (L : ℕ) : (3 : ℝ) ^ (-(L : ℤ)) ≤ 1 := by
  apply zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 3)
  simp

theorem cutoffInnerRatio_pos (L : ℕ) : 0 < cutoffInnerRatio L := by
  have := three_zpow_neg_le_one L
  unfold cutoffInnerRatio
  linarith

theorem cutoffInnerRatio_nonneg (L : ℕ) : 0 ≤ cutoffInnerRatio L :=
  (cutoffInnerRatio_pos L).le

theorem cutoffInnerRatio_lt_cutoffOuterRatio (L : ℕ) :
    cutoffInnerRatio L < cutoffOuterRatio L := by
  have := three_zpow_neg_pos L
  unfold cutoffInnerRatio cutoffOuterRatio
  linarith

theorem cutoffOuterRatio_lt_one (L : ℕ) : cutoffOuterRatio L < 1 := by
  have := three_zpow_neg_pos L
  unfold cutoffOuterRatio
  linarith

theorem cutoffInnerRatio_le_one (L : ℕ) : cutoffInnerRatio L ≤ 1 :=
  le_of_lt ((cutoffInnerRatio_lt_cutoffOuterRatio L).trans (cutoffOuterRatio_lt_one L))

theorem cutoffOuterRatio_sub_cutoffInnerRatio (L : ℕ) :
    cutoffOuterRatio L - cutoffInnerRatio L = (3 : ℝ) ^ (-(L : ℤ)) / 4 := by
  unfold cutoffInnerRatio cutoffOuterRatio
  ring

/-- **`e.boundary.strip.volume`, scalar half at the chosen ratios.**  The strip
fraction of the localization cutoff at scale `L` in dimension `d` is at most
`d · 3^{−L} / 2`. -/
theorem one_sub_cutoffInnerRatio_pow_le (d L : ℕ) :
    1 - cutoffInnerRatio L ^ d ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 := by
  have hbern := one_sub_pow_le_mul_one_sub d (cutoffInnerRatio_nonneg L)
  have hrw : (1 : ℝ) - cutoffInnerRatio L = (3 : ℝ) ^ (-(L : ℤ)) / 2 := by
    unfold cutoffInnerRatio; ring
  rw [hrw] at hbern
  linarith

/-! ### The cutoff and its gradient bound -/

section Cutoff

variable {d : ℕ}

/-- The paper's cutoff `η_{K,L}`, defined as CoarseGraining's canonical
quantitative cube cutoff between the concentric ratios `cutoffInnerRatio L` and
`cutoffOuterRatio L`. -/
def approxCutoff (Q : TriadicCube d) (L : ℕ) :
    QuantitativeCubeCutoff Q (cutoffInnerRatio L) (cutoffOuterRatio L) :=
  QuantitativeCubeCutoff.canonical Q _ _ (cutoffInnerRatio_pos L)
    (cutoffInnerRatio_lt_cutoffOuterRatio L)

theorem approxCutoff_tsupport_subset (Q : TriadicCube d) (L : ℕ) :
    tsupport (approxCutoff Q L).toFun ⊆ openCubeSet Q := by
  refine subset_trans (closure_minimal ?_ (isClosed_scaledClosedCubeSet Q _))
    (scaledClosedCubeSet_subset_openCubeSet Q (cutoffOuterRatio_lt_one L))
  intro x hx
  exact fun i => le_of_lt ((approxCutoff Q L).support_subset hx i)

/-- The uniform gradient bound of the localization cutoff, `C(d) 3^{L−K}` in the
notation of the paper. -/
def gradBound (Q : TriadicCube d) (L : ℕ) : ℝ :=
  (d : ℝ) * (quantitativeCubeCutoffGradientConst d /
    ((cutoffOuterRatio L - cutoffInnerRatio L) * cubeRadius Q))

/-- The gradient of the localization cutoff, as a Euclidean vector. -/
def cutoffHilbertGrad (Q : TriadicCube d) (L : ℕ) (x : Vec d) : HilbertVec d :=
  HilbertVec.ofVec fun i => fderiv ℝ (approxCutoff Q L).toFun x (basisVec i)

theorem norm_basisVec_le_one (i : Fin d) : ‖(basisVec i : Vec d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases h : j = i
  · subst h; simp [basisVec]
  · simp [basisVec, h]

theorem norm_cutoffHilbertGrad_le (Q : TriadicCube d) (L : ℕ) (x : Vec d) :
    ‖cutoffHilbertGrad Q L x‖ ≤ gradBound Q L := by
  have hcoord : ‖(fun i => fderiv ℝ (approxCutoff Q L).toFun x (basisVec i) : Vec d)‖
      ≤ ‖fderiv ℝ (approxCutoff Q L).toFun x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    calc ‖fderiv ℝ (approxCutoff Q L).toFun x (basisVec i)‖
        ≤ ‖fderiv ℝ (approxCutoff Q L).toFun x‖ * ‖(basisVec i : Vec d)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ (approxCutoff Q L).toFun x‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_basisVec_le_one i) (norm_nonneg _)
      _ = ‖fderiv ℝ (approxCutoff Q L).toFun x‖ := mul_one _
  calc ‖cutoffHilbertGrad Q L x‖
      ≤ (d : ℝ) * ‖(fun i => fderiv ℝ (approxCutoff Q L).toFun x (basisVec i) : Vec d)‖ :=
        HilbertVec.norm_ofVec_le_mul_norm _
    _ ≤ (d : ℝ) * ‖fderiv ℝ (approxCutoff Q L).toFun x‖ :=
        mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg d)
    _ ≤ gradBound Q L :=
        mul_le_mul_of_nonneg_left ((approxCutoff Q L).gradient_bound x) (Nat.cast_nonneg d)

theorem gradBound_nonneg (Q : TriadicCube d) (L : ℕ) : 0 ≤ gradBound Q L :=
  le_trans (norm_nonneg _) (norm_cutoffHilbertGrad_le Q L 0)

theorem continuous_cutoffHilbertGrad (Q : TriadicCube d) (L : ℕ) :
    Continuous (cutoffHilbertGrad Q L) := by
  have hfderiv : Continuous fun x => fderiv ℝ (approxCutoff Q L).toFun x :=
    (approxCutoff Q L).smooth.continuous_fderiv (by simp)
  have hpi : Continuous fun x => (fun i => fderiv ℝ (approxCutoff Q L).toFun x (basisVec i) :
      Vec d) :=
    continuous_pi fun i => (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).continuous.comp hfderiv
  exact ((HilbertVec.continuousLinearEquivVec d).symm.continuous).comp hpi

/-- The gradient bound of the localization cutoff on the origin cube of scale
`K`, in the paper's explicit form `C(d) 3^{L−K}`. -/
theorem gradBound_originCube (d : ℕ) (K L : ℕ) :
    gradBound (originCube d (K : ℤ)) L
      = ((d : ℝ) * quantitativeCubeCutoffGradientConst d * 8 * (3 : ℝ) ^ L)
        * ((3 : ℝ) ^ K)⁻¹ := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(L : ℤ)) := three_zpow_neg_pos L
  have hK : (0 : ℝ) < (3 : ℝ) ^ K := by positivity
  have hrad : cubeRadius (originCube d (K : ℤ)) = (1 / 2 : ℝ) * (3 : ℝ) ^ K := by
    simp [cubeRadius, cubeScaleFactor, originCube, zpow_natCast]
  have hL : (3 : ℝ) ^ (-(L : ℤ)) = ((3 : ℝ) ^ L)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ L := by positivity
  rw [gradBound, cutoffOuterRatio_sub_cutoffInnerRatio, hrad, hL]
  field_simp
  ring

end Cutoff

/-! ### The local approximant and its error -/

section Approximant

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]

/-- The gradient of the paper's local test field
`v_{K,L} = η_{K,L} · φ`, written out by the product rule.  It is defined by this
formula for *every* sample, so that it is jointly measurable without any
smoothness assumption; whenever the realization of `φ` really is a smooth
primitive of the realization of `p` it is the gradient of an `H¹₀(cu_K)`
function (`isPotentialZeroTraceOn_localGradApprox`). -/
def localGradApprox (Q : TriadicCube d) (L : ℕ) (φ : Ω → ℝ) (p : Ω → HilbertVec d)
    (ω : Ω) : Vec d → Vec d :=
  fun x i => (approxCutoff Q L).toFun x * (realize p ω x).toVec i
    + realize φ ω x * fderiv ℝ (approxCutoff Q L).toFun x (basisVec i)

omit [MeasurableSpace Ω] in
/-- The approximation error `∇v_{K,L} − p`, decomposed exactly as in ABK26. -/
theorem ofVec_localGradApprox_sub_realize (Q : TriadicCube d) (L : ℕ)
    (φ : Ω → ℝ) (p : Ω → HilbertVec d) (ω : Ω) (x : Vec d) :
    HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x
      = ((approxCutoff Q L).toFun x - 1) • realize p ω x
        + realize φ ω x • cutoffHilbertGrad Q L x := by
  ext i
  simp [localGradApprox, cutoffHilbertGrad, HilbertVec.toVec]
  ring

omit [MeasurableSpace Ω] in
/-- The local test field is an honest zero-trace potential on the cube, i.e.
`v_{K,L} ∈ H¹₀(cu_K)` in the notation of the paper. -/
theorem isPotentialZeroTraceOn_localGradApprox (Q : TriadicCube d) (L : ℕ)
    {φ : Ω → ℝ} {p : Ω → HilbertVec d} {ω : Ω}
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (realize (d := d) φ ω))
    (hgrad : ∀ (x : Vec d) i,
      fderiv ℝ (realize (d := d) φ ω) x (basisVec i) = (realize p ω x).toVec i) :
    IsPotentialZeroTraceOn (openCubeSet Q) (localGradApprox Q L φ p ω) := by
  have hη := (approxCutoff Q L).smooth
  have hprod : ContDiff ℝ (⊤ : ℕ∞) fun y : Vec d => (approxCutoff Q L).toFun y * realize φ ω y :=
    hη.mul hsmooth
  have hsupp : HasCompactSupport fun y : Vec d => (approxCutoff Q L).toFun y * realize φ ω y :=
    (approxCutoff Q L).hasCompactSupport.mul_right
  have hsub : tsupport (fun y : Vec d => (approxCutoff Q L).toFun y * realize φ ω y)
      ⊆ openCubeSet Q :=
    subset_trans (closure_mono (Function.support_mul_subset_left _ _))
      (approxCutoff_tsupport_subset Q L)
  have hbase := isPotentialZeroTraceOn_of_contDiff (isOpen_openCubeSet Q) hprod hsupp hsub
  refine (show (fun (x : Vec d) i =>
      fderiv ℝ (fun y : Vec d => (approxCutoff Q L).toFun y * realize φ ω y) x
      (basisVec i)) = localGradApprox Q L φ p ω from ?_) ▸ hbase
  funext x i
  have h1 : HasFDerivAt (approxCutoff Q L).toFun (fderiv ℝ (approxCutoff Q L).toFun x) x :=
    (hη.differentiable (by simp) x).hasFDerivAt
  have h2 : HasFDerivAt (realize (d := d) φ ω) (fderiv ℝ (realize (d := d) φ ω) x) x :=
    (hsmooth.differentiable (by simp) x).hasFDerivAt
  show fderiv ℝ ((approxCutoff Q L).toFun * realize (d := d) φ ω) x (basisVec i) = _
  rw [(h1.mul h2).fderiv]
  simp [localGradApprox, hgrad x i]

omit [MeasurableSpace Ω] in
/-- **Pointwise error bound.**  On the cube the local approximation error is
controlled by the boundary strip and by the primitive, exactly as in the two
displays of ABK26. -/
theorem norm_sq_localGradApprox_sub_le (Q : TriadicCube d) (L : ℕ)
    (φ : Ω → ℝ) (p : Ω → HilbertVec d) (ω : Ω) {x : Vec d} (hx : x ∈ cubeSet Q) :
    ‖HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x‖ ^ 2
      ≤ 2 * (cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L)).indicator
            (fun y => ‖realize p ω y‖ ^ 2) x
        + 2 * gradBound Q L ^ 2 * ‖realize φ ω x‖ ^ 2 := by
  have hdec := ofVec_localGradApprox_sub_realize Q L φ p ω x
  have hgb := norm_cutoffHilbertGrad_le Q L x
  have hgb0 := gradBound_nonneg Q L
  have hsecond : ‖realize φ ω x • cutoffHilbertGrad Q L x‖
      ≤ ‖realize φ ω x‖ * gradBound Q L := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hgb (norm_nonneg _)
  by_cases hmem : x ∈ scaledClosedCubeSet Q (cutoffInnerRatio L)
  · have hone : (approxCutoff Q L).toFun x = 1 := (approxCutoff Q L).eq_one_on_inner x hmem
    have hind : (cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L)).indicator
        (fun y => ‖realize p ω y‖ ^ 2) x = 0 :=
      Set.indicator_of_notMem (fun h => h.2 hmem) _
    have hle : ‖HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x‖
        ≤ ‖realize φ ω x‖ * gradBound Q L := by
      rw [hdec, hone]
      simpa using hsecond
    rw [hind]
    nlinarith [hle, norm_nonneg (HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x),
      mul_nonneg (norm_nonneg (realize φ ω x)) hgb0]
  · have hxmem : x ∈ cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L) :=
      Set.mem_sdiff_of_mem hx hmem
    have hind : (cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L)).indicator
        (fun y => ‖realize p ω y‖ ^ 2) x = ‖realize p ω x‖ ^ 2 :=
      Set.indicator_of_mem hxmem _
    have hcut : ‖(approxCutoff Q L).toFun x - 1‖ ≤ 1 := by
      have h0 := (approxCutoff Q L).nonneg x
      have h1 := (approxCutoff Q L).le_one x
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfirst : ‖((approxCutoff Q L).toFun x - 1) • realize p ω x‖ ≤ ‖realize p ω x‖ := by
      rw [norm_smul]
      calc ‖(approxCutoff Q L).toFun x - 1‖ * ‖realize p ω x‖
          ≤ 1 * ‖realize p ω x‖ :=
            mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
        _ = ‖realize p ω x‖ := one_mul _
    have hle : ‖HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x‖
        ≤ ‖realize p ω x‖ + ‖realize φ ω x‖ * gradBound Q L := by
      rw [hdec]
      exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
    rw [hind]
    nlinarith [hle, norm_nonneg (HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x),
      mul_nonneg (norm_nonneg (realize φ ω x)) hgb0, norm_nonneg (realize p ω x),
      sq_nonneg (‖realize p ω x‖ - ‖realize φ ω x‖ * gradBound Q L)]

end Approximant

/-! ### The expected error at a fixed cube -/

section Estimate

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The boundary strip `Σ_{K,L}` of ABK26: the part of the cube on which the
localization cutoff may differ from `1`. -/
def boundaryStripSet (Q : TriadicCube d) (L : ℕ) : Set (Vec d) :=
  cubeSet Q \ scaledClosedCubeSet Q (cutoffInnerRatio L)

theorem boundaryStripSet_subset_cubeSet (Q : TriadicCube d) (L : ℕ) :
    boundaryStripSet Q L ⊆ cubeSet Q := Set.sdiff_subset

theorem measurableSet_boundaryStripSet (Q : TriadicCube d) (L : ℕ) :
    MeasurableSet (boundaryStripSet Q L) :=
  (measurableSet_cubeSet Q).diff (isClosed_scaledClosedCubeSet Q _).measurableSet

theorem volume_boundaryStripSet_ne_top (Q : TriadicCube d) (L : ℕ) :
    volume (boundaryStripSet Q L) ≠ ⊤ :=
  measure_ne_top_of_subset Set.sdiff_subset (volume_cubeSet_lt_top Q).ne

/-- **`e.boundary.strip.volume`.**  The strip volume is at most
`d · 3^{−L} / 2` times the volume of the cube
(ABK26, with the explicit constant `C = d`
of design decision `D-6`). -/
theorem volume_boundaryStripSet_toReal_le (Q : TriadicCube d) (L : ℕ) :
    (volume (boundaryStripSet Q L)).toReal
      ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * cubeVolume Q := by
  refine (volume_cubeSet_diff_scaledClosedCubeSet_toReal_le Q (cutoffInnerRatio_nonneg L)
    (cutoffInnerRatio_le_one L)).trans ?_
  exact mul_le_mul_of_nonneg_right (one_sub_cutoffInnerRatio_pow_le d L) (cubeVolume_nonneg Q)

/-- The expected squared error over a fixed cube, before normalization. -/
theorem integral_setIntegral_normSq_localGradApprox_sub_le (Q : TriadicCube d) (L : ℕ)
    {φ : Ω → ℝ} {p : Ω → HilbertVec d}
    (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ) :
    ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x‖ ^ 2) ∂μ
      ≤ 2 * ((volume (boundaryStripSet Q L)).toReal * ∫ ω, ‖p ω‖ ^ 2 ∂μ)
        + 2 * gradBound Q L ^ 2 * (cubeVolume Q * ∫ ω, ‖φ ω‖ ^ 2 ∂μ) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hSfin := volume_boundaryStripSet_ne_top Q L
  have hSmeas := measurableSet_boundaryStripSet Q L
  set G := gradBound Q L with hG
  -- the dominating observable
  have hdomint : Integrable (fun ω =>
      2 * (∫ x in boundaryStripSet Q L, ‖realize p ω x‖ ^ 2)
        + 2 * G ^ 2 * ∫ x in cubeSet Q, ‖realize φ ω x‖ ^ 2) μ :=
    ((integrable_setIntegral_normSq_realize hSfin hpm hp).const_mul 2).add
      ((integrable_setIntegral_normSq_realize hQfin hφm hφ).const_mul (2 * G ^ 2))
  have hmono : ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x‖ ^ 2) ∂μ
      ≤ ∫ ω, (2 * (∫ x in boundaryStripSet Q L, ‖realize p ω x‖ ^ 2)
        + 2 * G ^ 2 * ∫ x in cubeSet Q, ‖realize φ ω x‖ ^ 2) ∂μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hdomint ?_
    · exact integral_nonneg fun x => by positivity
    filter_upwards [ae_memLp_two_realize (μ := μ) hSfin hpm hp,
      ae_memLp_two_realize (μ := μ) hQfin hφm hφ,
      ae_memLp_two_realize (μ := μ) hQfin hpm hp] with ω hpS hφQ hpQ
    have hpSint : Integrable (fun x => ‖realize p ω x‖ ^ 2) (volume.restrict
        (boundaryStripSet Q L)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hpm ω).aestronglyMeasurable).1 hpS
    have hφQint : Integrable (fun x => ‖realize φ ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hφm ω).aestronglyMeasurable).1 hφQ
    have hindvol : Integrable ((boundaryStripSet Q L).indicator
        fun y => ‖realize p ω y‖ ^ 2) volume :=
      MeasureTheory.IntegrableOn.integrable_indicator hpSint hSmeas
    have hindint : Integrable ((boundaryStripSet Q L).indicator
        fun y => ‖realize p ω y‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      hindvol.mono_measure Measure.restrict_le_self
    have hbound : Integrable (fun x =>
        2 * (boundaryStripSet Q L).indicator (fun y => ‖realize p ω y‖ ^ 2) x
          + 2 * G ^ 2 * ‖realize φ ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
      (hindint.const_mul 2).add (hφQint.const_mul (2 * G ^ 2))
    have hinner : (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x‖ ^ 2)
        ≤ ∫ x in cubeSet Q,
            (2 * (boundaryStripSet Q L).indicator (fun y => ‖realize p ω y‖ ^ 2) x
              + 2 * G ^ 2 * ‖realize φ ω x‖ ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        hbound ?_
      refine (ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
      filter_upwards with x hx
      exact norm_sq_localGradApprox_sub_le Q L φ p ω hx
    refine hinner.trans (le_of_eq ?_)
    rw [integral_add (hindint.const_mul 2) (hφQint.const_mul (2 * G ^ 2)),
      integral_const_mul, integral_const_mul,
      setIntegral_indicator hSmeas,
      Set.inter_eq_self_of_subset_right (boundaryStripSet_subset_cubeSet Q L)]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add ((integrable_setIntegral_normSq_realize hSfin hpm hp).const_mul 2)
      ((integrable_setIntegral_normSq_realize hQfin hφm hφ).const_mul (2 * G ^ 2)),
    integral_const_mul, integral_const_mul,
    integral_setIntegral_normSq_realize hSfin hpm hp,
    integral_setIntegral_normSq_realize hQfin hφm hφ, volume_cubeSet_toReal]

omit [MeasurableConstVAdd (Vec d) Ω] in
/-- The approximation error is a strongly measurable field for every sample. -/
theorem stronglyMeasurable_localGradApprox_sub (Q : TriadicCube d) (L : ℕ)
    {φ : Ω → ℝ} {p : Ω → HilbertVec d}
    (hφm : StronglyMeasurable φ) (hpm : StronglyMeasurable p) (ω : Ω) :
    StronglyMeasurable
      (fun x => HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x) := by
  have hrw : (fun x => HilbertVec.ofVec (localGradApprox Q L φ p ω x) - realize p ω x)
      = fun x => ((approxCutoff Q L).toFun x - 1) • realize p ω x
        + realize φ ω x • cutoffHilbertGrad Q L x :=
    funext fun x => ofVec_localGradApprox_sub_realize Q L φ p ω x
  rw [hrw]
  refine StronglyMeasurable.add ?_ ?_
  · exact ((approxCutoff Q L).smooth.continuous.sub continuous_const).stronglyMeasurable.smul
      (stronglyMeasurable_realize hpm ω)
  · exact (stronglyMeasurable_realize hφm ω).smul
      (continuous_cutoffHilbertGrad Q L).stronglyMeasurable

end Estimate

section Main

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

end Main

section Sublinearity

variable {d : ℕ}

end Sublinearity

section SublinearityStationary

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

end SublinearityStationary

end

end Algsuperdiff.Section3.Provider.Corrector
