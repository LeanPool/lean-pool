/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.ReducedInductionAdjoint
public import LeanPool.FastDynamo.Operator.FixedSectorLowerOrderDecay
public import LeanPool.FastDynamo.Operator.PointwiseResolvent

/-!
# The right half-plane resolvent of the reduced induction operator

Let `u` be a transversely divergence-free real `W^{1,∞}` velocity, `ε > 0` a
diffusivity, `K` an axial frequency, and write

`M_u := ‖transverseStretchingCoefficient u‖`,  `A := reducedInductionOperator u ε K`.

The energy identity of `FastDynamo/Global/ReducedInductionEnergyIdentity.lean`
puts the numerical range of `A` — and, by
`FastDynamo/Global/ReducedInductionAdjoint.lean`, that of the displayed formal
adjoint `A*` — inside the closed half-plane `{Re ν ≤ M_u}`.  This module turns
that one-sided information into a resolvent family on the open right
half-plane `{Re z > M_u}`, with the Hille–Yosida bound

`‖(z - A)⁻¹‖_{L² → L²} ≤ (Re z - M_u)⁻¹`.

The three analytic inputs are proved elsewhere in the library.

* The numerical-range separation gives the ambient pencil lower bound
  `(Re z - M_u) ‖ι d‖ ≤ ‖(z - A) d‖` and the same bound for `A*` at `star z`
  (`DomainOperator.ambient_norm_pencil_lower_of_numericalRange`).  Only
  `0 ≤ ε` is used here.
* A far positive-real reference point where *both* `A` and `A*` are invertible.
  For `A` this is the exponential-ray Neumann construction of
  `FastDynamo/Operator/FixedSectorLowerOrderDecay.lean`.  The same construction
  works verbatim for `A*`: the adjoint has the *same* diffusion pencil, and its
  lower-order part `(u⊥·∇⊥) + 2πiK u₃ + (∇⊥u)ᵀ` decays relative to the diffusion
  inverse exactly like the forward one, the transposed stretching matrix being
  an `L∞` multiplier composed with the `H² → L²` embedding.  This needs `0 < ε`.
  The reference point upgrades the `FormalAdjointPairing` of
  `FastDynamo/Global/ReducedInductionAdjoint.lean` to a
  maximal `IsAdjointRealization` and closes the graph of `A`
  (`DomainOperator.adjointRealization_and_closedGraph_of_formalAdjoint_reference`).
* Closed range plus dense range then give bijectivity of the pencil at every
  point of the half-plane, and the open mapping theorem supplies the bounded
  inverse together with the `(Re z - M_u)⁻¹` estimate
  (`DomainOperator.exists_singleton_resolvent_with_stateNorm_le`).

Finally the pointwise inverses are assembled into a single coherent continuous
family by `DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses`, following
the template of
`FastDynamo/Global/TorusBackgroundResolvent.lean`.  The real-ray
specialization `norm_stateResolvent_reducedInductionOperator_realRay_le` is the
form consumed by a Hille–Yosida generation theorem.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Half-plane numerical ranges and the two pencil lower bounds -/

/-- If `Re ν ≤ M` then every `z` is at distance at least `Re z - M` from `ν`. -/
private theorem sub_re_le_dist_of_re_le {z nu : ℂ} {M : ℝ} (hnu : nu.re ≤ M) :
    z.re - M ≤ dist z nu := by
  have hre : z.re - nu.re ≤ ‖z - nu‖ := by
    calc z.re - nu.re = (z - nu).re := by simp
      _ ≤ |(z - nu).re| := le_abs_self _
      _ ≤ ‖z - nu‖ := Complex.abs_re_le_norm _
  rw [dist_eq_norm]
  linarith

/-- **The numerical range of `A_{ε,K}` lies in the half-plane `{Re ν ≤ M_u}`.**
This is `re_inner_reducedInductionAction_le` read on unit ambient vectors. -/
theorem reducedInductionOperator_numericalRange_re_le
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) {nu : ℂ}
    (hnu : nu ∈ (reducedInductionOperator u ε K).numericalRange) :
    nu.re ≤ ‖transverseStretchingCoefficient u‖ := by
  obtain ⟨d, hd, rfl⟩ := hnu
  have h := re_inner_reducedInductionAction_le u hu ε hε K d
  have hd' : ‖transverseH2Embedding d‖ = 1 := hd
  rw [hd'] at h
  change (inner ℂ (transverseH2Embedding d)
    (reducedInductionAction u ε K d)).re ≤ _
  simpa using h

/-- **Ambient lower bound for the reduced induction pencil.**  For every `z` and
every `d` in the `H²` domain,

`(Re z - M_u) ‖ι d‖ ≤ ‖(z - A_{ε,K}) d‖`.

No hypothesis on `Re z` is needed: the inequality is vacuous when
`Re z ≤ M_u`.  This is the quantitative content of the energy competition of
`eq:energy-competition` at the level of the spectral pencil. -/
theorem reducedInductionOperator_ambient_norm_pencil_lower
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) (z : ℂ) (d : TransverseC3H2) :
    (z.re - ‖transverseStretchingCoefficient u‖) *
        ‖transverseH2Embedding d‖ ≤
      ‖(reducedInductionOperator u ε K).pencil z d‖ :=
  (reducedInductionOperator u ε K).ambient_norm_pencil_lower_of_numericalRange
    (fun _ hnu ↦ sub_re_le_dist_of_re_le
      (reducedInductionOperator_numericalRange_re_le u hu ε hε K hnu)) d

/-- **The numerical range of the displayed formal adjoint lies in the same
half-plane `{Re ν ≤ M_u}`**, by `re_inner_reducedInductionAdjointAction_le`. -/
theorem reducedInductionAdjointOperator_numericalRange_re_le
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) {nu : ℂ}
    (hnu : nu ∈ (reducedInductionAdjointOperator u ε K).numericalRange) :
    nu.re ≤ ‖transverseStretchingCoefficient u‖ := by
  obtain ⟨d, hd, rfl⟩ := hnu
  have h := re_inner_reducedInductionAdjointAction_le u hu ε hε K d
  have hd' : ‖transverseH2Embedding d‖ = 1 := hd
  rw [hd'] at h
  change (inner ℂ (transverseH2Embedding d)
    (reducedInductionAdjointAction u ε K d)).re ≤ _
  simpa using h

/-- **Ambient lower bound for the adjoint pencil**, identical to the forward one
because the two numerical ranges obey the same half-plane bound. -/
theorem reducedInductionAdjointOperator_ambient_norm_pencil_lower
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) (z : ℂ) (d : TransverseC3H2) :
    (z.re - ‖transverseStretchingCoefficient u‖) *
        ‖transverseH2Embedding d‖ ≤
      ‖(reducedInductionAdjointOperator u ε K).pencil z d‖ :=
  DomainOperator.ambient_norm_pencil_lower_of_numericalRange
    (reducedInductionAdjointOperator u ε K)
    (fun _ hnu ↦ sub_re_le_dist_of_re_le
      (reducedInductionAdjointOperator_numericalRange_re_le u hu ε hε K hnu)) d

/-- The conjugated form of the adjoint lower bound, which is the hypothesis
shape of `DomainOperator.denseRange_pencil_of_adjoint_lower`: the conjugate
point `star z` has the same real part as `z`. -/
theorem reducedInductionAdjointOperator_ambient_norm_pencil_lower_star
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) (z : ℂ) (d : TransverseC3H2) :
    (z.re - ‖transverseStretchingCoefficient u‖) *
        ‖transverseH2Embedding d‖ ≤
      ‖(reducedInductionAdjointOperator u ε K).pencil (star z) d‖ := by
  have h := reducedInductionAdjointOperator_ambient_norm_pencil_lower
    u hu ε hε K (star z) d
  simpa using h

/-! ## A far positive-real resolvent point for the displayed formal adjoint -/

/-- All first- and zeroth-order terms of the displayed formal adjoint action,
`(u⊥·∇⊥) + 2πiK u₃ + (∇⊥u)ᵀ`.  Only the signs and the transposed stretching
matrix distinguish it from `reducedInductionLowerOrder`. -/
def reducedInductionAdjointLowerOrder (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  reducedInductionTransport u + reducedInductionAxialTransport u K +
    reducedInductionStretchingTranspose u

/-- The adjoint pencil splits through the *same* diffusion pencil as the
forward one, with the adjoint lower-order part subtracted. -/
theorem reducedInductionAdjointPencil_eq_diffusionPencil_sub_lowerOrder
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ) :
    (reducedInductionAdjointOperator u ε K).pencil z =
      reducedInductionDiffusionPencil ε K z -
        reducedInductionAdjointLowerOrder u K := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [DomainOperator.pencil, reducedInductionAdjointOperator_embedding,
    reducedInductionAdjointOperator_op, reducedInductionAdjointAction,
    reducedInductionDiffusionPencil, reducedInductionAdjointLowerOrder,
    add_apply, sub_apply, smul_apply]
  module

/-- Triangle inequality for the three adjoint lower-order terms composed with a
common ambient-to-domain map. -/
theorem norm_reducedInductionAdjointLowerOrder_comp_le
    (u : TransverseRealW1Inf) (K : ℤ)
    (T : TransverseC3L2 →L[ℂ] TransverseC3H2) :
    ‖(reducedInductionAdjointLowerOrder u K).comp T‖ ≤
      ‖(reducedInductionTransport u).comp T‖ +
        ‖(reducedInductionAxialTransport u K).comp T‖ +
          ‖(reducedInductionStretchingTranspose u).comp T‖ := by
  have heq : (reducedInductionAdjointLowerOrder u K).comp T =
      (reducedInductionTransport u).comp T +
        (reducedInductionAxialTransport u K).comp T +
          (reducedInductionStretchingTranspose u).comp T := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact norm_add_le _ _

/-- The transposed stretching term is an `L∞` operator multiplier composed with
the `H² → L²` embedding, so it decays like the order-zero Fourier bound
`O(σ⁻¹)` along the positive exponential diffusion ray. -/
theorem tendsto_norm_reducedInductionStretchingTranspose_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(reducedInductionStretchingTranspose u).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards with t
    simp only [reducedInductionStretchingTranspose,
      reducedInductionDiffusionInverseRay, ContinuousLinearMap.comp_assoc]
    calc
      ‖(operatorMulL2 transverseMeasure
          (star (transverseStretchingCoefficient u))).comp
            (transverseH2Embedding.comp
              (reducedInductionDiffusionInverse ε (Real.exp t) K hε
                (Real.exp_pos t)))‖ ≤
          ‖operatorMulL2 transverseMeasure
            (star (transverseStretchingCoefficient u))‖ *
            ‖transverseH2Embedding.comp
              (reducedInductionDiffusionInverse ε (Real.exp t) K hε
                (Real.exp_pos t))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖operatorMulL2 transverseMeasure
            (star (transverseStretchingCoefficient u))‖ *
            (‖transverseC3FourierSynthesis‖ *
              ((Real.exp t)⁻¹ * ‖transverseC3FourierAnalysis‖)) := by
        gcongr
        exact norm_transverseH2Embedding_comp_reducedInductionDiffusionInverse_le
          ε (Real.exp t) K hε (Real.exp_pos t)
  · have h : Filter.Tendsto
        (fun t : ℝ ↦ ‖operatorMulL2 transverseMeasure
          (star (transverseStretchingCoefficient u))‖ *
          (‖transverseC3FourierSynthesis‖ *
            ((Real.exp t)⁻¹ * ‖transverseC3FourierAnalysis‖)))
        Filter.atTop
        (nhds (‖operatorMulL2 transverseMeasure
          (star (transverseStretchingCoefficient u))‖ *
          (‖transverseC3FourierSynthesis‖ *
            (0 * ‖transverseC3FourierAnalysis‖)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        (tendsto_exp_inverse_zero.mul tendsto_const_nhds))
    simpa using h

/-- The complete adjoint lower-order correction is relatively small far out on
the positive exponential diffusion ray.  The two transport terms reuse the
forward estimates verbatim; only the transposed stretching term needs its own estimate. -/
theorem tendsto_norm_reducedInductionAdjointLowerOrder_comp_diffusionInverseRay_zero
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun t : ℝ ↦ ‖(reducedInductionAdjointLowerOrder u K).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards with t
    exact norm_reducedInductionAdjointLowerOrder_comp_le u K
      (reducedInductionDiffusionInverseRay ε K hε t)
  · have h :=
      ((tendsto_norm_reducedInductionTransport_comp_diffusionInverseRay_zero
          u ε K hε).add
        (tendsto_norm_reducedInductionAxialTransport_comp_diffusionInverseRay_zero
          u ε K hε)).add
      (tendsto_norm_reducedInductionStretchingTranspose_comp_diffusionInverseRay_zero
        u ε K hε)
    simpa using h

/-- The Neumann threshold for the adjoint is eventually attained on the positive
exponential diffusion ray. -/
theorem eventually_norm_reducedInductionAdjointLowerOrder_comp_diffusionInverseRay_lt_one
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      ‖(reducedInductionAdjointLowerOrder u K).comp
        (reducedInductionDiffusionInverseRay ε K hε t)‖ < 1 :=
  (tendsto_order.1
    (tendsto_norm_reducedInductionAdjointLowerOrder_comp_diffusionInverseRay_zero
      u ε K hε)).2 (1 : ℝ) zero_lt_one

/-- A two-sided inverse of the diffusion pencil together with the Neumann
smallness condition for the adjoint lower-order part gives a resolvent of the
displayed formal adjoint at the same spectral point.  This is the exact
analogue of `reducedInductionHasResolventOnSingletonOfDiffusionInverse`, run
with the adjoint splitting. -/
def reducedInductionAdjointHasResolventOnSingletonOfDiffusionInverse
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ)
    (T₀ : TransverseC3L2 →L[ℂ] TransverseC3H2)
    (hleft : T₀.comp (reducedInductionDiffusionPencil ε K z) =
      ContinuousLinearMap.id ℂ TransverseC3H2)
    (hright : (reducedInductionDiffusionPencil ε K z).comp T₀ =
      ContinuousLinearMap.id ℂ TransverseC3L2)
    (hsmall : ‖(reducedInductionAdjointLowerOrder u K).comp T₀‖ < 1) :
    HasResolventOn (reducedInductionAdjointOperator u ε K) {z} := by
  have hunit : IsUnit (DomainOperator.boundedPerturbationCorrection
      (reducedInductionAdjointLowerOrder u K) T₀) :=
    DomainOperator.isUnit_boundedPerturbationCorrection_of_norm_lt_one
      (reducedInductionAdjointLowerOrder u K) T₀ hsmall
  have hpencil : (reducedInductionAdjointOperator u ε K).pencil z =
      reducedInductionDiffusionPencil ε K z -
        reducedInductionAdjointLowerOrder u K :=
    reducedInductionAdjointPencil_eq_diffusionPencil_sub_lowerOrder u ε K z
  refine (reducedInductionAdjointOperator u ε K).hasResolventOnSingleton z
    (DomainOperator.boundedPerturbedInverse
      (reducedInductionAdjointLowerOrder u K) T₀) ?_ ?_
  · rw [hpencil]
    exact DomainOperator.boundedPerturbedInverse_left_inv
      (reducedInductionDiffusionPencil ε K z)
      (reducedInductionAdjointLowerOrder u K) T₀ hleft hright hunit
  · rw [hpencil]
    exact DomainOperator.boundedPerturbedInverse_right_inv
      (reducedInductionDiffusionPencil ε K z)
      (reducedInductionAdjointLowerOrder u K) T₀ hright hunit

/-- Every sufficiently far point on the positive-real exponential ray is a
resolvent point of the displayed formal adjoint. -/
theorem eventually_hasResolventOn_reducedInductionAdjointOperator_expRay
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop,
      Nonempty (HasResolventOn (reducedInductionAdjointOperator u ε K)
        {((Real.exp t : ℝ) : ℂ)}) := by
  filter_upwards [
    eventually_norm_reducedInductionAdjointLowerOrder_comp_diffusionInverseRay_lt_one
      u ε K hε] with t ht
  refine ⟨reducedInductionAdjointHasResolventOnSingletonOfDiffusionInverse
    u ε K ((Real.exp t : ℝ) : ℂ)
    (reducedInductionDiffusionInverseRay ε K hε t) ?_ ?_ ht⟩
  · exact inverse_comp_reducedInductionDiffusionPencil ε (Real.exp t) K hε
      (Real.exp_pos t)
  · exact reducedInductionDiffusionPencil_comp_inverse ε (Real.exp t) K hε
      (Real.exp_pos t)

/-! ## Maximal adjoint realization and closed graph -/

/-- One common far positive-real reference point at which both the reduced
induction operator and its displayed formal adjoint are boundedly invertible.
It exists because both Neumann thresholds are eventually met on the same
exponential ray. -/
theorem exists_expRay_reference_resolvents
    (u : TransverseRealW1Inf) (ε : ℝ) (hε : 0 < ε) (K : ℤ) :
    ∃ t : ℝ,
      Nonempty (HasResolventOn (reducedInductionOperator u ε K)
          {((Real.exp t : ℝ) : ℂ)}) ∧
        Nonempty (HasResolventOn (reducedInductionAdjointOperator u ε K)
          {((Real.exp t : ℝ) : ℂ)}) :=
  ((eventually_hasResolventOn_reducedInductionOperator_expRay u ε K hε).and
    (eventually_hasResolventOn_reducedInductionAdjointOperator_expRay
      u ε K hε)).exists

/-- **The displayed formal adjoint is the Hilbert adjoint, and the
reduced induction operator is closed.**  The formal pairing of
`Global/ReducedInductionAdjoint.lean` plus
the common real reference point of `exists_expRay_reference_resolvents` supply
exactly the hypotheses of
`DomainOperator.adjointRealization_and_closedGraph_of_formalAdjoint_reference`;
no maximal-domain or closedness premise is assumed. -/
theorem reducedInductionOperator_isAdjointRealization_and_isClosedGraph
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) :
    (reducedInductionOperator u ε K).IsAdjointRealization
        (reducedInductionAdjointOperator u ε K) ∧
      (reducedInductionOperator u ε K).IsClosedGraph := by
  obtain ⟨t, ⟨hfwd⟩, ⟨hadj⟩⟩ := exists_expRay_reference_resolvents u ε hε K
  refine DomainOperator.adjointRealization_and_closedGraph_of_formalAdjoint_reference
    (reducedInductionOperator_formalAdjointPairing u hu ε K) hfwd
    (Set.mem_singleton _) ?_
  have hstar : star ((Real.exp t : ℝ) : ℂ) = ((Real.exp t : ℝ) : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal]
  rw [hstar]
  exact hadj.surjective_pencil (Set.mem_singleton _)

/-- The displayed formal adjoint realizes the Hilbert-space adjoint of the
reduced induction operator. -/
theorem reducedInductionOperator_isAdjointRealization
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) :
    (reducedInductionOperator u ε K).IsAdjointRealization
      (reducedInductionAdjointOperator u ε K) :=
  (reducedInductionOperator_isAdjointRealization_and_isClosedGraph
    u hu ε hε K).1

/-! ## The pointwise inverse on the coercive half-plane -/

/-- **Bijectivity of the pencil on the open right half-plane.**  For
`M_u < Re z` the map `z - A_{ε,K} : H² → L²` is a linear bijection: injectivity
from the ambient lower bound, surjectivity from the closed-graph and adjoint
criteria. -/
theorem reducedInductionOperator_pencil_bijective_of_lt_re
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    Function.Bijective ((reducedInductionOperator u ε K).pencil z) := by
  obtain ⟨hadjoint, hgraph⟩ :=
    reducedInductionOperator_isAdjointRealization_and_isClosedGraph u hu ε hε K
  have hd0 : 0 < z.re - ‖transverseStretchingCoefficient u‖ := sub_pos.mpr hz
  refine ⟨(reducedInductionOperator u ε K).pencil_injective_of_ambient_lower
      hd0 (reducedInductionOperator_ambient_norm_pencil_lower
        u hu ε hε.le K z), ?_⟩
  exact DomainOperator.surjective_pencil_of_isClosedGraph_of_ambient_lower_of_adjoint_lower
    (reducedInductionOperator u ε K) (reducedInductionAdjointOperator u ε K)
    hadjoint hgraph z _ _ hd0 hd0
    (reducedInductionOperator_ambient_norm_pencil_lower u hu ε hε.le K z)
    (reducedInductionAdjointOperator_ambient_norm_pencil_lower_star
      u hu ε hε.le K z)

/-- **The pointwise resolvent with the Hille–Yosida bound.**  At every `z` with
`M_u < Re z` the pencil has a bounded two-sided ambient-to-domain inverse whose
ambient state resolvent obeys `‖(z - A)⁻¹‖ ≤ (Re z - M_u)⁻¹`. -/
theorem exists_reducedInductionOperator_singleton_resolvent_of_lt_re
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) {z : ℂ}
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    ∃ h : HasResolventOn (reducedInductionOperator u ε K) {z},
      ‖h.stateResolvent z‖ ≤
        (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ := by
  obtain ⟨hadjoint, hgraph⟩ :=
    reducedInductionOperator_isAdjointRealization_and_isClosedGraph u hu ε hε K
  have hd0 : 0 < z.re - ‖transverseStretchingCoefficient u‖ := sub_pos.mpr hz
  have hlower := reducedInductionOperator_ambient_norm_pencil_lower
    u hu ε hε.le K z
  refine DomainOperator.exists_singleton_resolvent_with_stateNorm_le
    (reducedInductionOperator u ε K) hd0 hlower ?_ ?_
  · exact DomainOperator.isClosed_range_pencil_of_isClosedGraph_of_ambient_lower
      (reducedInductionOperator u ε K) hgraph z _ hd0 hlower
  · exact DomainOperator.denseRange_pencil_of_adjoint_lower
      (reducedInductionOperator u ε K)
      (reducedInductionAdjointOperator u ε K) hadjoint z _ hd0
      (reducedInductionAdjointOperator_ambient_norm_pencil_lower_star
        u hu ε hε.le K z)

/-! ## The coherent half-plane resolvent family -/

/-- The open coercive right half-plane `{z | M_u < Re z}` of the reduced
induction operator. -/
def reducedInductionRightHalfPlane (u : TransverseRealW1Inf) : Set ℂ :=
  {z | ‖transverseStretchingCoefficient u‖ < z.re}

/-- Membership in the coercive right half-plane is exactly the inequality
`M_u < Re z`. -/
@[simp] theorem mem_reducedInductionRightHalfPlane
    (u : TransverseRealW1Inf) (z : ℂ) :
    z ∈ reducedInductionRightHalfPlane u ↔
      ‖transverseStretchingCoefficient u‖ < z.re :=
  Iff.rfl

/-- **The Hille–Yosida bound holds for any chosen resolvent of the reduced
induction operator.**  Whatever two-sided inverse is used, the ambient state
resolvent at a point of the coercive half-plane obeys
`‖(z - A)⁻¹‖ ≤ (Re z - M_u)⁻¹`: the right-inverse equation turns the ambient
pencil lower bound into the stated operator-norm estimate.  Only `0 ≤ ε` is
used. -/
theorem norm_stateResolvent_reducedInductionOperator_le
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 ≤ ε) (K : ℤ) {S : Set ℂ}
    (h : HasResolventOn (reducedInductionOperator u ε K) S)
    {z : ℂ} (hzS : z ∈ S)
    (hz : ‖transverseStretchingCoefficient u‖ < z.re) :
    ‖h.stateResolvent z‖ ≤
      (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ := by
  have hd0 : 0 < z.re - ‖transverseStretchingCoefficient u‖ := sub_pos.mpr hz
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hd0.le) ?_
  intro x
  have hlower := reducedInductionOperator_ambient_norm_pencil_lower
    u hu ε hε K z (h.inv z x)
  have hright := DFunLike.congr_fun (h.right_inv z hzS) x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hright
  rw [hright] at hlower
  have hlower' : ‖transverseH2Embedding (h.inv z x)‖ *
      (z.re - ‖transverseStretchingCoefficient u‖) ≤ ‖x‖ := by
    rw [mul_comm]
    exact hlower
  calc
    ‖(h.stateResolvent z) x‖ = ‖transverseH2Embedding (h.inv z x)‖ := rfl
    _ ≤ ‖x‖ / (z.re - ‖transverseStretchingCoefficient u‖) :=
      (le_div_iff₀ hd0).2 hlower'
    _ = (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ * ‖x‖ := by
      rw [inv_mul_eq_div]

/-- **One coherent resolvent family on the whole coercive right half-plane**,
with the uniform Hille–Yosida bound `‖(z - A)⁻¹‖ ≤ (Re z - M_u)⁻¹`.  The
pointwise inverses of
`exists_reducedInductionOperator_singleton_resolvent_of_lt_re` are glued by the
rational propagation formula of
`DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses`, which also supplies
continuity of the family. -/
theorem exists_reducedInductionOperator_resolventOn_rightHalfPlane
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) :
    ∃ h : HasResolventOn (reducedInductionOperator u ε K)
        (reducedInductionRightHalfPlane u),
      ∀ z ∈ reducedInductionRightHalfPlane u,
        ‖h.stateResolvent z‖ ≤
          (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ := by
  have hbase : ‖transverseStretchingCoefficient u‖ <
      (((‖transverseStretchingCoefficient u‖ + 1 : ℝ) : ℂ)).re := by
    simp
  obtain ⟨h₀, -⟩ := exists_reducedInductionOperator_singleton_resolvent_of_lt_re
    u hu ε hε K hbase
  have hpoint : ∀ z ∈ reducedInductionRightHalfPlane u,
      ∃ T : TransverseC3L2 →L[ℂ] TransverseC3H2,
        T.comp ((reducedInductionOperator u ε K).pencil z) =
            ContinuousLinearMap.id ℂ TransverseC3H2 ∧
          ((reducedInductionOperator u ε K).pencil z).comp T =
            ContinuousLinearMap.id ℂ TransverseC3L2 := by
    intro z hz
    obtain ⟨hzres, -⟩ :=
      exists_reducedInductionOperator_singleton_resolvent_of_lt_re
        u hu ε hε K hz
    exact ⟨hzres.inv z, hzres.left_inv z (Set.mem_singleton _),
      hzres.right_inv z (Set.mem_singleton _)⟩
  refine ⟨DomainOperator.hasResolventOnOfPointwiseTwoSidedInverses
      (reducedInductionOperator u ε K)
      (((‖transverseStretchingCoefficient u‖ + 1 : ℝ) : ℂ))
      (h₀.inv (((‖transverseStretchingCoefficient u‖ + 1 : ℝ) : ℂ)))
      (h₀.left_inv _ (Set.mem_singleton _))
      (h₀.right_inv _ (Set.mem_singleton _))
      (reducedInductionRightHalfPlane u) hpoint, ?_⟩
  intro z hz
  exact norm_stateResolvent_reducedInductionOperator_le u hu ε hε.le K _ hz hz

/-- **The chosen half-plane resolvent of the reduced induction operator.**  This
is the `HasResolventOn` structure produced by
`exists_reducedInductionOperator_resolventOn_rightHalfPlane`. -/
def reducedInductionRightHalfPlaneResolvent
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) :
    HasResolventOn (reducedInductionOperator u ε K)
      (reducedInductionRightHalfPlane u) :=
  (exists_reducedInductionOperator_resolventOn_rightHalfPlane
    u hu ε hε K).choose

/-- **The Hille–Yosida bound for the chosen half-plane resolvent**:
`‖(z - A_{ε,K})⁻¹‖_{L² → L²} ≤ (Re z - M_u)⁻¹` at every point of the coercive
right half-plane. -/
theorem norm_stateResolvent_reducedInductionOperator_rightHalfPlane_le
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) {z : ℂ}
    (hz : z ∈ reducedInductionRightHalfPlane u) :
    ‖(reducedInductionRightHalfPlaneResolvent
        u hu ε hε K).stateResolvent z‖ ≤
      (z.re - ‖transverseStretchingCoefficient u‖)⁻¹ :=
  (exists_reducedInductionOperator_resolventOn_rightHalfPlane
    u hu ε hε K).choose_spec z hz

/-! ## The real ray consumed by Hille–Yosida -/

/-- Every real `λ > M_u` lies in the coercive right half-plane. -/
theorem ofReal_mem_reducedInductionRightHalfPlane
    (u : TransverseRealW1Inf) {lam : ℝ}
    (hlam : ‖transverseStretchingCoefficient u‖ < lam) :
    (lam : ℂ) ∈ reducedInductionRightHalfPlane u := by
  simpa using hlam

/-- **The real-ray form of the generation estimate.**  For every real
`λ > M_u` the reduced induction pencil `λ - A_{ε,K}` is bijective from the `H²`
domain onto `L²` and its ambient inverse obeys `‖(λ - A)⁻¹‖ ≤ (λ - M_u)⁻¹`.
This is the inequality a Hille–Yosida generation theorem consumes. -/
theorem norm_stateResolvent_reducedInductionOperator_realRay_le
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (ε : ℝ) (hε : 0 < ε) (K : ℤ) {lam : ℝ}
    (hlam : ‖transverseStretchingCoefficient u‖ < lam) :
    Function.Bijective
        ((reducedInductionOperator u ε K).pencil (lam : ℂ)) ∧
      ‖(reducedInductionRightHalfPlaneResolvent
          u hu ε hε K).stateResolvent (lam : ℂ)‖ ≤
        (lam - ‖transverseStretchingCoefficient u‖)⁻¹ := by
  have hre : (lam : ℂ).re = lam := Complex.ofReal_re lam
  constructor
  · exact reducedInductionOperator_pencil_bijective_of_lt_re u hu ε hε K
      (by rw [hre]; exact hlam)
  · have h := norm_stateResolvent_reducedInductionOperator_rightHalfPlane_le
      u hu ε hε K (ofReal_mem_reducedInductionRightHalfPlane u hlam)
    rwa [hre] at h

end

end FastDynamo
