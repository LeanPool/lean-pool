/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusPlacedCutoffC2

/-!
# The velocity hypotheses of `lem:parametrix-error` at a placed cell

The proof of `lem:parametrix-error` uses exactly
two facts about the global velocity `u` near the selected cell:

* **agreement**: "the coefficients of the horizontal and background operators on `T²` agree wherever
  `χ_n ≠ 0`, since `supp u_n^loc ⊂ D(p_n, R_n/10)`".  This is the field `backgroundAgreement` of
  `TorusTwoSummandParametrix.TwoSummandParametrixData`;
* **vanishing on the transition regions**: "the horizontal velocity vanishes on
  the transition regions of both output cut-offs", which is what makes both commutators
  diffusion-only.  These are the fields `backgroundVanishes` and `outputVanishes`, i.e.
  `HorizontalCutoffCommutator.VelocityVanishesOnGradient` for `χ_n` and for `ψ_n`.

This module proves both from *geometric* hypotheses on the velocity alone, stated at the placed
cell `(p, R)` of `FastDynamo/Global/TorusPlacedCutoffC2.lean`:

* `∇ψ_n` vanishes on `D(p_n, R_n/3)` and off `D(p_n, R_n/2)`, and `∇χ_n` vanishes on
  `D(p_n, R_n/10)` and off `D(p_n, R_n/6)`, all four proved here on the plane and transported
  through the no-wrap periodization; hence `VelocityVanishesOnGradient` follows for both from the
  single predicate `TransverseVelocityLocalized p inner outer u`, "almost every torus point
  either carries vanishing transverse velocity, or has its canonical representative inside
  `D(p_n, inner)`, or has it outside `D(p_n, outer)`", with `inner ≤ R_n/10` and
  `R_n/2 ≤ outer`;
* the agreement field follows from "almost everywhere either `χ_n = 0` or the two velocities have
  the same transport, axial and stretching coefficients", and `χ_n = 0` exactly on
  `D(p_n, R_n/10)`.

What remains for the parameter chain is purely the placement geometry of §3.3 ("Disjoint placement
and added axial velocity profiles on `T²`"): `supp u_n^loc ⊂ D(p_n, R_n/10)` (the consequence of
`eq:local-support-in-buffer` stated right after it) and the pairwise disjointness of the buffer
discs, which together put every point where the transverse velocity is nonzero either inside
`D(p_n, R_n/10)` or outside `D(p_n, R_n/2)`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

namespace TorusPlacedCutoffC2

open ConstantCoefficientBackground
open HorizontalCutoffCommutator
open HorizontalCutoffMultiplier
open ParametrixCutoffs
open ParametrixExplicitCutoff
open PeriodicSecondOrderCutoffs
open SchwartzPeriodicCutoff
open TransverseSmoothBumpPeriodization
open TransverseVecMultiplierAlgebra

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-! ## Where the two output cut-offs have vanishing derivative -/

/-- `ψ_n` is constant on the open disc `D(p_n, R_n/3)`, so its derivative vanishes there. -/
theorem realProfileCoordinateDerivative_outputCutoff_eq_zero_of_lt_third
    {y : WholePlane} (hy : dist y p < R / 3) (j : Fin 2) :
    realProfileCoordinateDerivative (outputCutoff p R hR) j y = 0 := by
  have hmem : y ∈ Metric.ball p (outputBump p R hR).rIn := by
    have hrin : (outputBump p R hR).rIn = R / 3 := rfl
    rw [Metric.mem_ball, hrin]
    exact hy
  have hfd : fderiv ℝ (outputCutoff p R hR) y = 0 :=
    contDiffBump_fderiv_eq_zero_of_mem_ball (outputBump p R hR) hmem
  change fderiv ℝ (outputCutoff p R hR) y (wholePlaneBasis j) = 0
  rw [hfd]
  rfl

/-- `ψ_n` vanishes identically beyond radius `R_n/2`, so its derivative vanishes there. -/
theorem realProfileCoordinateDerivative_outputCutoff_eq_zero_of_half_lt
    {y : WholePlane} (hy : R / 2 < dist y p) (j : Fin 2) :
    realProfileCoordinateDerivative (outputCutoff p R hR) j y = 0 := by
  have hout : (outputBump p R hR).rOut < dist y p := hy
  have hfd : fderiv ℝ (outputCutoff p R hR) y = 0 :=
    contDiffBump_fderiv_eq_zero_of_rOut_lt_dist (outputBump p R hR) hout
  change fderiv ℝ (outputCutoff p R hR) y (wholePlaneBasis j) = 0
  rw [hfd]
  rfl

/-- The background bump is constant on the open disc `D(p_n, R_n/10)`, so its derivative
vanishes there; equivalently `∇χ_n = 0` there. -/
theorem realProfileCoordinateDerivative_backgroundBump_eq_zero_of_lt_tenth
    {y : WholePlane} (hy : dist y p < R / 10) (j : Fin 2) :
    realProfileCoordinateDerivative ((backgroundBump p R hR : WholePlane → ℝ)) j y = 0 := by
  have hmem : y ∈ Metric.ball p (backgroundBump p R hR).rIn := by
    have hrin : (backgroundBump p R hR).rIn = R / 10 := rfl
    rw [Metric.mem_ball, hrin]
    exact hy
  have hfd : fderiv ℝ ((backgroundBump p R hR : WholePlane → ℝ)) y = 0 :=
    contDiffBump_fderiv_eq_zero_of_mem_ball (backgroundBump p R hR) hmem
  change fderiv ℝ ((backgroundBump p R hR : WholePlane → ℝ)) y (wholePlaneBasis j) = 0
  rw [hfd]
  rfl

/-- The background bump vanishes identically beyond radius `R_n/6`, so `∇χ_n = 0` there. -/
theorem realProfileCoordinateDerivative_backgroundBump_eq_zero_of_sixth_lt
    {y : WholePlane} (hy : R / 6 < dist y p) (j : Fin 2) :
    realProfileCoordinateDerivative ((backgroundBump p R hR : WholePlane → ℝ)) j y = 0 := by
  have hout : (backgroundBump p R hR).rOut < dist y p := hy
  have hfd : fderiv ℝ ((backgroundBump p R hR : WholePlane → ℝ)) y = 0 :=
    contDiffBump_fderiv_eq_zero_of_rOut_lt_dist (backgroundBump p R hR) hout
  change fderiv ℝ ((backgroundBump p R hR : WholePlane → ℝ)) y (wholePlaneBasis j) = 0
  rw [hfd]
  rfl

/-! ## `VelocityVanishesOnGradient` for the two output cut-offs -/

/-- **The paper's localization of the transverse velocity relative to one cell**
(`eq:local-support-in-buffer` and its consequence `supp u_n^loc ⊂ D(p_n, R_n/10)`, together with
the pairwise disjointness of the buffer discs, §3.3): almost every torus point either
carries vanishing transverse velocity, or has its canonical representative inside the inner disc
`D(p_n, inner)` — the selected cell's own local-flow core — or outside the outer disc
`D(p_n, outer)` — where all the other cells' cores live, the buffer discs being disjoint.

The two radii are explicit because the two output cut-offs need different ones: `ψ_n` is already
constant on `D(p_n, R_n/3)` and vanishes off `D(p_n, R_n/2)`, whereas `χ_n` is constant only on
`D(p_n, R_n/10)` and off `D(p_n, R_n/6)`.  The *binding* requirement is therefore
`inner ≤ R_n/10`: the transverse velocity of the selected cell must live in the plateau of the
background cut-off. -/
def TransverseVelocityLocalized (p : WholePlane) (inner outer : ℝ)
    (u : TransverseRealW1Inf) : Prop :=
  ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
    (transverseW1InfComplexValueCoordLInf j.castSucc u) q = 0 ∨
      dist (wholePlaneIocRepresentative q) p < inner ∨
      outer < dist (wholePlaneIocRepresentative q) p

/-- **`outputVanishes`** (proof of `lem:parametrix-error`): a transverse velocity
localized inside `D(p_n, R_n/3)` and outside `D(p_n, R_n/2)` annihilates `∇ψ_n`. -/
theorem velocityVanishesOnGradient_outputMul
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (u : TransverseRealW1Inf) {inner outer : ℝ}
    (hinner : inner ≤ R / 3) (houter : R / 2 ≤ outer)
    (hu : TransverseVelocityLocalized p inner outer u) :
    VelocityVanishesOnGradient (outputMul p R hR) u := by
  intro j
  apply Lp.ext
  filter_upwards [scalarMulTransverseLInf_coe_ae
      (transverseW1InfComplexValueCoordLInf j.castSucc u) ((outputMul p R hR).gradient j),
    cutoff_gradient_ae_representative (outputSchwartz p R hR) j
      (nowrap_outputSchwartz_deriv p R hR hbox j),
    hu j, Lp.coeFn_zero (E := ℂ) (p := ∞) (μ := transverseMeasure)] with q hmul hgrad hcase hzero
  rw [hmul, hzero]
  have hgrad' : ((outputMul p R hR).gradient j : TransverseTorus → ℂ) q =
      (∂_{wholePlaneBasis j} (outputSchwartz p R hR))
        (wholePlaneIocRepresentative q) := hgrad
  rcases hcase with hvel | hdist
  · rw [hvel, zero_mul]
    rfl
  · have hzeroprofile :
        realProfileCoordinateDerivative (outputCutoff p R hR) j
          (wholePlaneIocRepresentative q) = 0 := by
      rcases hdist with hin | hout
      · exact realProfileCoordinateDerivative_outputCutoff_eq_zero_of_lt_third p R hR
          (by linarith) j
      · exact realProfileCoordinateDerivative_outputCutoff_eq_zero_of_half_lt p R hR
          (by linarith) j
    have hgradzero : ((outputMul p R hR).gradient j : TransverseTorus → ℂ) q = 0 := by
      rw [hgrad', outputSchwartz, lineDerivOp_realSchwartz_apply, hzeroprofile]
      norm_num
    rw [hgradzero, mul_zero]
    rfl

/-- **`backgroundVanishes`** (proof of `lem:parametrix-error`): a transverse velocity
localized inside `D(p_n, R_n/10)` and outside `D(p_n, R_n/6)` annihilates `∇χ_n`. -/
theorem velocityVanishesOnGradient_backgroundMul
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (u : TransverseRealW1Inf) {inner outer : ℝ}
    (hinner : inner ≤ R / 10) (houter : R / 6 ≤ outer)
    (hu : TransverseVelocityLocalized p inner outer u) :
    VelocityVanishesOnGradient (backgroundMul p R hR) u := by
  intro j
  apply Lp.ext
  filter_upwards [scalarMulTransverseLInf_coe_ae
      (transverseW1InfComplexValueCoordLInf j.castSucc u) ((backgroundMul p R hR).gradient j),
    Lp.coeFn_neg ((SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).gradient j),
    cutoff_gradient_ae_representative (backgroundSchwartz p R hR) j
      (nowrap_backgroundSchwartz_deriv p R hR hbox j),
    hu j, Lp.coeFn_zero (E := ℂ) (p := ∞) (μ := transverseMeasure)]
    with q hmul hneg hgrad hcase hzero
  rw [hmul, hzero]
  rcases hcase with hvel | hdist
  · rw [hvel, zero_mul]
    rfl
  · have hzeroprofile :
        realProfileCoordinateDerivative ((backgroundBump p R hR : WholePlane → ℝ)) j
          (wholePlaneIocRepresentative q) = 0 := by
      rcases hdist with hin | hout
      · exact realProfileCoordinateDerivative_backgroundBump_eq_zero_of_lt_tenth p R hR
          (by linarith) j
      · exact realProfileCoordinateDerivative_backgroundBump_eq_zero_of_sixth_lt p R hR
          (by linarith) j
    have hgradzero : ((backgroundMul p R hR).gradient j : TransverseTorus → ℂ) q = 0 := by
      change ((-(SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).gradient j :
        TransverseScalarLInf) : TransverseTorus → ℂ) q = 0
      rw [hneg]
      change -(((SchwartzPeriodicCutoff.cutoff (backgroundSchwartz p R hR)).gradient j :
        TransverseScalarLInf) : TransverseTorus → ℂ) q = 0
      rw [hgrad, backgroundSchwartz, lineDerivOp_realSchwartz_apply, hzeroprofile]
      norm_num
    rw [hgradzero, mul_zero]
    rfl

/-! ## The background agreement field -/

/-- **`backgroundAgreement`** (proof of `lem:parametrix-error`) in its analytic form:
if almost everywhere either the cut-off vanishes or the two velocities have the same transport,
axial and stretching coefficients, then the cut-off multiplies the two horizontal actions to the
same bounded map.  The diffusion term carries no velocity coefficient at all. -/
theorem stateMul_comp_horizontalInductionAction_congr
    (chi : HorizontalSecondOrderCutoff) (u v : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ)
    (hvalue : ∀ i : Fin 3, ∀ᵐ q ∂transverseMeasure,
      (chi.value : TransverseTorus → ℂ) q = 0 ∨
        (transverseW1InfComplexValueCoordLInf i u) q =
          (transverseW1InfComplexValueCoordLInf i v) q)
    (hderiv : ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
      (chi.value : TransverseTorus → ℂ) q = 0 ∨
        (transverseW1InfHorizontalDerivLInf j u) q =
          (transverseW1InfHorizontalDerivLInf j v) q) :
    chi.stateMul.comp (horizontalInductionAction u epsilon K) =
      chi.stateMul.comp (horizontalInductionAction v epsilon K) := by
  have hprod : ∀ i : Fin 3,
      scalarMulTransverseLInf chi.value (transverseW1InfComplexValueCoordLInf i u) =
        scalarMulTransverseLInf chi.value (transverseW1InfComplexValueCoordLInf i v) := by
    intro i
    apply Lp.ext
    filter_upwards [scalarMulTransverseLInf_coe_ae chi.value
        (transverseW1InfComplexValueCoordLInf i u),
      scalarMulTransverseLInf_coe_ae chi.value
        (transverseW1InfComplexValueCoordLInf i v), hvalue i] with q h1 h2 hc
    rw [h1, h2]
    rcases hc with hz | he
    · rw [hz, zero_mul, zero_mul]
    · rw [he]
  apply ContinuousLinearMap.ext
  intro h
  have htrans : ∀ j : Fin 2,
      scalarVectorMulTransverseVec (Fin 2) chi.value
          (scalarVectorMulTransverseC2 (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (transverseVecDerivFromH2 (Fin 2) j h)) =
        scalarVectorMulTransverseVec (Fin 2) chi.value
          (scalarVectorMulTransverseC2 (transverseW1InfComplexValueCoordLInf j.castSucc v)
            (transverseVecDerivFromH2 (Fin 2) j h)) := by
    intro j
    rw [← scalarVectorMulTransverseVec_mulLInf, ← scalarVectorMulTransverseVec_mulLInf,
      hprod j.castSucc]
  have haxial : scalarVectorMulTransverseVec (Fin 2) chi.value
        (scalarVectorMulTransverseC2 (transverseW1InfComplexValueCoordLInf 2 u)
          (transverseH2Embedding h)) =
      scalarVectorMulTransverseVec (Fin 2) chi.value
        (scalarVectorMulTransverseC2 (transverseW1InfComplexValueCoordLInf 2 v)
          (transverseH2Embedding h)) := by
    rw [← scalarVectorMulTransverseVec_mulLInf, ← scalarVectorMulTransverseVec_mulLInf,
      hprod 2]
  have hstretch : ∀ j : Fin 2,
      scalarVectorMulTransverseVec (Fin 2) chi.value
          (vectorScalarMulTransverseC2 (transverseW1InfHorizontalDerivLInf j u)
            (transverseCoordL2 j (transverseH2Embedding h))) =
        scalarVectorMulTransverseVec (Fin 2) chi.value
          (vectorScalarMulTransverseC2 (transverseW1InfHorizontalDerivLInf j v)
            (transverseCoordL2 j (transverseH2Embedding h))) := by
    intro j
    rw [scalarVectorMulTransverseVec_vectorScalarMulTransverseVec,
      scalarVectorMulTransverseVec_vectorScalarMulTransverseVec]
    apply Lp.ext
    filter_upwards [vectorScalarMulTransverseVec_coe_ae (ι := Fin 2)
        (transverseW1InfHorizontalDerivLInf j u)
        (scalarMulTransverse chi.value (transverseCoordL2 j (transverseH2Embedding h))),
      vectorScalarMulTransverseVec_coe_ae (ι := Fin 2)
        (transverseW1InfHorizontalDerivLInf j v)
        (scalarMulTransverse chi.value (transverseCoordL2 j (transverseH2Embedding h))),
      scalarMulTransverse_coe_ae chi.value (transverseCoordL2 j (transverseH2Embedding h)),
      hderiv j] with q h1 h2 h3 hc
    rw [h1, h2]
    rcases hc with hz | he
    · rw [h3, hz, zero_mul, zero_smul, zero_smul]
    · rw [he]
  change scalarVectorMulTransverseVec (Fin 2) chi.value
      (horizontalInductionAction u epsilon K h) =
    scalarVectorMulTransverseVec (Fin 2) chi.value (horizontalInductionAction v epsilon K h)
  rw [horizontalInductionAction_apply, horizontalInductionAction_apply]
  simp only [map_sub, map_add, map_smul, map_sum, htrans, haxial, hstretch]

/-- Where its canonical representative lies in `D(p_n, R_n/10)`, the placed background cut-off
vanishes. -/
theorem backgroundMul_value_eq_zero_ae
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    ∀ᵐ q ∂transverseMeasure, dist (wholePlaneIocRepresentative q) p ≤ R / 10 →
      ((backgroundMul p R hR).value : TransverseTorus → ℂ) q = 0 := by
  filter_upwards [backgroundMul_value_ae p R hR hbox] with q hq hd
  rw [hq, backgroundCutoff_eq_zero_of_dist_le p R hR hd]
  norm_num

/-- **`backgroundAgreement` at a placed cell** (proof of `lem:parametrix-error`):
the full and background coefficients need only agree off `D(p_n, R_n/10)`, which is exactly the
paper's `supp u_n^loc ⊂ D(p_n, R_n/10)` (the consequence of `eq:local-support-in-buffer`). -/
theorem backgroundMul_agreement
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    (u v : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ)
    (hvalue : ∀ i : Fin 3, ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
        (transverseW1InfComplexValueCoordLInf i u) q =
          (transverseW1InfComplexValueCoordLInf i v) q)
    (hderiv : ∀ j : Fin 2, ∀ᵐ q ∂transverseMeasure,
      dist (wholePlaneIocRepresentative q) p ≤ R / 10 ∨
        (transverseW1InfHorizontalDerivLInf j u) q =
          (transverseW1InfHorizontalDerivLInf j v) q) :
    (backgroundMul p R hR).stateMul.comp (horizontalInductionAction u epsilon K) =
      (backgroundMul p R hR).stateMul.comp (horizontalInductionAction v epsilon K) := by
  refine stateMul_comp_horizontalInductionAction_congr _ u v epsilon K ?_ ?_
  · intro i
    filter_upwards [hvalue i, backgroundMul_value_eq_zero_ae p R hR hbox] with q hc hz
    rcases hc with hd | he
    · exact Or.inl (hz hd)
    · exact Or.inr he
  · intro j
    filter_upwards [hderiv j, backgroundMul_value_eq_zero_ae p R hR hbox] with q hc hz
    rcases hc with hd | he
    · exact Or.inl (hz hd)
    · exact Or.inr he

end TorusPlacedCutoffC2

end

end FastDynamo
