/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.IdealWeakForm
public import LeanPool.FastDynamo.Dynamics.Flow.ParticleFlowProof
public import LeanPool.FastDynamo.Analysis.BoundedOperatorMultiplier
public import LeanPool.FastDynamo.Global.TorusGlobalVelocityDerivativeBridge

/-!
# The gradient of the velocity on the literal three-torus

The ideal induction equation `∂ₜB + (u·∇)B − (B·∇)u = 0` of the paper (§1.2, proof of
`cor:ideal-growth`) involves the gradient `∇u` of the velocity, an `L^∞` matrix field.  This module
reads it on the literal torus `Torus 3` through `literalFDeriv` (`IdealWeakForm.lean`) and
proves the properties of `∇u` at the velocity of the paper that the weak form uses.

## Contents

* `literalStretchLInf v`, `literalStretchL2 v` — the stretching `B ↦ (B·∇)v` as an `L^∞` symbol
  (zero when `∇v` is not essentially bounded) and as a bounded operator on `L²(T³; ℂ³)`.
* `IdealWeakIdentity v W s t φ ψ` — the weak identity with an `L²` test pair `(φ, ψ)`, `ψ` standing
  for `(v·∇)φ`.
* `hasFDerivAt_literalVelocity_lift`, `norm_literalFDeriv_literalVelocity_le`,
  `measurable_literalFDeriv_literalVelocity` — at the velocity of the paper the lift is
  differentiable everywhere, `∇u` is the Fréchet derivative of the lift, bounded by twice the
  Lipschitz bound of `lem:global-velocity`, and measurable.
* `sum_literalFDeriv_literalVelocity_diag` — `div u = 0` at every point.
* `continuous_literalFDeriv_literalVelocity_literalFlow` — `∇u` is continuous along every
  trajectory of the flow, although it is discontinuous at the accumulation circle.
* `literalStretchL2_coe_ae`, `norm_literalStretchL2_le` — `literalStretchL2 u` is pointwise
  multiplication by `∇u ⊗ ℂ`, of norm at most `12` times the Lipschitz bound.

`∇u` is the pointwise Jacobian of the everywhere differentiable lift of `u`, as in the paper.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-! ## The stretching operator and the weak identity, generic in the velocity -/

/-- The `L^∞` class of `x ↦ ∇v(x) ⊗ ℂ` (zero if it is not essentially bounded). -/
def literalStretchLInf (v : Torus 3 → R3) : Lp (C3 →L[ℂ] C3) ∞ (volume : Measure (Torus 3)) :=
  @dite _ (MemLp (fun x ↦ r3Complexify (literalFDeriv v x)) ∞ (volume : Measure (Torus 3)))
    (Classical.propDecidable _) (fun hmem ↦ hmem.toLp _) fun _ ↦ 0

/-- The stretching operator `B ↦ (B·∇)v` on `L²(T³; ℂ³)`. -/
def literalStretchL2 (v : Torus 3 → R3) : LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  operatorMulL2 (volume : Measure (Torus 3)) (literalStretchLInf v)

/-- The weak identity of the ideal induction equation with an `L²` test pair `(φ, ψ)`, where `ψ`
plays the role of `(v·∇)φ`:
`⟨W t, φ⟩ − ⟨W s, φ⟩ = ∫ₛᵗ ⟨(W τ·∇)v, φ⟩ + ⟨W τ, ψ⟩ dτ`, with the paper's pairing
`⟨B, φ⟩ = ∫ ⟪φ, B⟫`. -/
def IdealWeakIdentity (v : Torus 3 → R3) (W : ℝ → LiteralC3L2) (s t : ℝ)
    (φ ψ : LiteralC3L2) : Prop :=
  inner ℂ φ (W t) - inner ℂ φ (W s) =
    ∫ τ in s..t, (inner ℂ φ (literalStretchL2 v (W τ)) + inner ℂ ψ (W τ))

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- The lift of the velocity of the paper is the periodised velocity composed with the pair of
transverse coordinates. -/
theorem literalVelocity_lift_eq :
    (fun b : R3 ↦ literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
        (literalTorusPoint b)) =
      (parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed tau) ∘
        flowPairProjection := by
  funext b
  exact literalVelocity_literalTorusPoint h P angularSpeed axialSpeed tau b

/-- The lift of the velocity is differentiable at every point. -/
theorem differentiable_literalVelocity_lift (htau : 0 ≤ tau) :
    Differentiable ℝ fun b : R3 ↦ literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
      (literalTorusPoint b) := by
  rw [literalVelocity_lift_eq]
  exact (differentiable_parameterizedFullGlobalPeriodizedRealSource
    h P angularSpeed axialSpeed tau htau).comp flowPairProjection.differentiable

/-- **`∇u` is the Fréchet derivative of the lift of `u`**, at every point. -/
theorem hasFDerivAt_literalVelocity_lift (htau : 0 ≤ tau) (a : R3) :
    HasFDerivAt (fun b : R3 ↦ literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
        (literalTorusPoint b))
      (literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (literalTorusPoint a)) a := by
  rw [literalFDeriv_literalTorusPoint]
  exact (differentiable_literalVelocity_lift h P angularSpeed axialSpeed tau htau a).hasFDerivAt

/-- **The bound on `∇u`**: the lift of `u` is Lipschitz with twice the constant of
`lem:global-velocity`. -/
theorem norm_literalFDeriv_literalVelocity_le (htau : 0 ≤ tau) (x : Torus 3) :
    ‖literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) x‖ ≤
      2 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau := by
  have hnn := globalVelocityLipschitzBound_nonneg h P angularSpeed axialSpeed tau htau
  have hproj : LipschitzWith 1 flowPairProjection := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact norm_flowPairProjection_le _
  have hlip := (lipschitzWith_parameterizedFullGlobalPeriodizedRealSource
    h P angularSpeed axialSpeed tau htau).comp hproj
  have := norm_fderiv_le_of_lipschitz (x₀ := literalIocRepresentative x) ℝ hlip
  rw [← literalVelocity_lift_eq h P angularSpeed axialSpeed tau] at this
  have h2 : ((2 * Real.toNNReal (globalVelocityLipschitzBound h P angularSpeed axialSpeed tau) *
      1 : ℝ≥0) : ℝ) = 2 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau := by
    push_cast
    rw [Real.coe_toNNReal _ hnn, mul_one]
  rw [h2] at this
  exact this

/-- `∇u` is a measurable function on the torus. -/
theorem measurable_literalFDeriv_literalVelocity :
    Measurable (literalFDeriv (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))) :=
  (measurable_fderiv ℝ _).comp measurable_literalIocRepresentative

/-- **`div u = 0` at every point**: the trace of `∇u` vanishes (the lift does not depend on the
axial coordinate, and the transverse divergence of the periodised velocity vanishes). -/
theorem sum_literalFDeriv_literalVelocity_diag (htau : 0 ≤ tau) (x : Torus 3) :
    ∑ i : Fin 3, literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) x
        (EuclideanSpace.single i 1) i = 0 := by
  set a : R3 := literalIocRepresentative x with ha
  have hxa : x = literalTorusPoint a := (literalTorusPoint_literalIocRepresentative x).symm
  have hd := (differentiable_parameterizedFullGlobalPeriodizedRealSource
    h P angularSpeed axialSpeed tau htau (flowPairProjection a)).hasFDerivAt.comp a
    flowPairProjection.hasFDerivAt
  rw [hxa, literalFDeriv_literalTorusPoint, literalVelocity_lift_eq h P angularSpeed axialSpeed tau,
    hd.fderiv, Fin.sum_univ_three]
  have hdiv := fderiv_parameterizedFullGlobalPeriodizedRealSource_transverseDivergence
    h P angularSpeed axialSpeed tau htau (flowPairProjection a)
  have e0 : flowPairProjection (EuclideanSpace.single 0 (1 : ℝ)) = pairBasis 0 := by
    simp [pairBasis]
  have e1 : flowPairProjection (EuclideanSpace.single 1 (1 : ℝ)) = pairBasis 1 := by
    simp [pairBasis]
  have e2 : flowPairProjection (EuclideanSpace.single 2 (1 : ℝ)) = 0 := by
    simp
  simp only [ContinuousLinearMap.comp_apply, e0, e1, e2, map_zero, PiLp.zero_apply, add_zero]
  exact hdiv

/-- **`∇u` is continuous along every trajectory of the flow**, although it is discontinuous at
the accumulation circle: a trajectory either stays on the circle, or never meets it. -/
theorem continuous_literalFDeriv_literalVelocity_literalFlow (x : Torus 3) :
    Continuous fun s : ℝ ↦ literalFDeriv
      (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
      (literalFlow h P angularSpeed axialSpeed tau s x) := by
  set a : R3 := literalIocRepresentative x with ha
  have hxa : literalTorusPoint a = x := literalTorusPoint_literalIocRepresentative x
  have hpt : ∀ s : ℝ, literalFlow h P angularSpeed axialSpeed tau s x =
      literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau s a) := fun s ↦ by
    rw [literalTorusPoint_literalFlowLift, hxa]
  have hcast : ∀ y : R3, (fun j : Fin 2 ↦ literalTorusPoint y j.castSucc) =
      transverseTorusPoint (y 0, y 1) := literalTorusPoint_castSucc
  by_cases hacc : ∃ k : ℤ × ℤ, ((a 0 - k.1, a 1 - k.2) : ℝ × ℝ) = accumulationPoint
  · obtain ⟨k, hk⟩ := hacc
    have hfix : ∀ s : ℝ, literalFlow h P angularSpeed axialSpeed tau s x = x := fun s ↦ by
      refine literalFlow_eq_self_of_accumulationPoint h P angularSpeed axialSpeed tau s ?_
      have : (fun j : Fin 2 ↦ x j.castSucc) = transverseTorusPoint (a 0, a 1) := by
        rw [← hxa]
        exact hcast a
      rw [this, ← hk]
      exact transverseTorusPoint_sub_int (a 0, a 1) k.1 k.2
    simp_rw [hfix]
    exact continuous_const
  · have hne : ∀ (s : ℝ) (k : ℤ × ℤ),
        ((literalFlowLift h P angularSpeed axialSpeed tau s a 0 - k.1,
          literalFlowLift h P angularSpeed axialSpeed tau s a 1 - k.2) : ℝ × ℝ) ≠
          accumulationPoint := by
      intro s k hk
      set y := literalFlowLift h P angularSpeed axialSpeed tau s a with hy
      have hyfix : literalFlow h P angularSpeed axialSpeed tau (-s) (literalTorusPoint y) =
          literalTorusPoint y := by
        refine literalFlow_eq_self_of_accumulationPoint h P angularSpeed axialSpeed tau (-s) ?_
        rw [hcast y, ← hk]
        exact transverseTorusPoint_sub_int (y 0, y 1) k.1 k.2
      have hback : literalFlow h P angularSpeed axialSpeed tau (-s) (literalTorusPoint y) = x := by
        rw [hy, literalTorusPoint_literalFlowLift, ← hxa,
          literalFlow_neg_literalFlow h P angularSpeed axialSpeed tau]
      have hyx : literalTorusPoint y = x := hyfix.symm.trans hback
      apply hacc
      have h0 : transverseTorusPoint (a 0, a 1) = transverseTorusPoint (y 0, y 1) := by
        rw [← hcast a, ← hcast y, hxa, hyx]
      obtain ⟨m, n, hm, hn⟩ := exists_int_of_transverseTorusPoint_eq h0
      refine ⟨(m + k.1, n + k.2), ?_⟩
      rw [← hk]
      simp only [Prod.mk.injEq]
      push_cast
      constructor <;> linarith
    have hfun : (fun s : ℝ ↦ literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (literalFlow h P angularSpeed axialSpeed tau s x)) = fun s ↦
        fderiv ℝ (fun b : R3 ↦ literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
          (literalTorusPoint b)) (literalFlowLift h P angularSpeed axialSpeed tau s a) := by
      funext s
      rw [hpt s, literalFDeriv_literalTorusPoint]
    rw [hfun]
    have hcurve : Continuous fun s : ℝ ↦ literalFlowLift h P angularSpeed axialSpeed tau s a :=
      continuous_iff_continuousAt.2 fun s ↦
        (hasDerivAt_literalFlowLift h P angularSpeed axialSpeed tau s a).continuousAt
    refine continuous_iff_continuousAt.2 fun s ↦ ?_
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun b : R3 ↦ literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
        (literalTorusPoint b)) (literalFlowLift h P angularSpeed axialSpeed tau s a) := by
      rw [literalVelocity_lift_eq]
      exact (contDiffAt_parameterizedFullGlobalPeriodizedRealSource h P angularSpeed axialSpeed
        tau (x := flowPairProjection (literalFlowLift h P angularSpeed axialSpeed tau s a))
        (fun k ↦ hne s k)).comp _ flowPairProjection.contDiff.contDiffAt
    exact ContinuousAt.comp (g := fderiv ℝ _) (hcd.continuousAt_fderiv (by simp))
      hcurve.continuousAt

/-- The pointwise bound `‖∇u ⊗ ℂ‖ ≤ 12 · Lip`, in the form of membership in `L^∞`. -/
theorem memLp_top_literalStretch (htau : 0 ≤ tau) :
    MemLp (fun x ↦ r3Complexify (literalFDeriv (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) x)) ∞
      (volume : Measure (Torus 3)) := by
  refine memLp_top_of_bound ?_
    (6 * (2 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact (continuous_r3Complexify.measurable.comp
      (measurable_literalFDeriv_literalVelocity h P angularSpeed axialSpeed tau)
        ).aestronglyMeasurable
  · exact (norm_r3Complexify_le _).trans
      (mul_le_mul_of_nonneg_left
        (norm_literalFDeriv_literalVelocity_le h P angularSpeed axialSpeed tau htau x)
        (by norm_num))

/-- The class `literalStretchLInf u` is the pointwise field `∇u ⊗ ℂ`. -/
theorem literalStretchLInf_coe_ae (htau : 0 ≤ tau) :
    (literalStretchLInf (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) :
      Torus 3 → C3 →L[ℂ] C3) =ᵐ[volume] fun x ↦ r3Complexify (literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) x) := by
  rw [literalStretchLInf,
    dite_eq_left (memLp_top_literalStretch h P angularSpeed axialSpeed tau htau)]
  exact (memLp_top_literalStretch h P angularSpeed axialSpeed tau htau).coeFn_toLp

/-- **`literalStretchL2 u` is the pointwise stretching `B ↦ (B·∇)u`**. -/
theorem literalStretchL2_coe_ae (htau : 0 ≤ tau) (B : LiteralC3L2) :
    (literalStretchL2 (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) B :
      Torus 3 → C3) =ᵐ[volume]
      literalStretch (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (B : Torus 3 → C3) := by
  filter_upwards [operatorMulL2_coe_ae (volume : Measure (Torus 3))
      (literalStretchLInf (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))) B,
    literalStretchLInf_coe_ae h P angularSpeed axialSpeed tau htau] with x h1 h2
  rw [literalStretchL2, h1, h2]
  rfl

/-- **The norm of the stretching operator**: `‖literalStretchL2 u‖ ≤ 12 · Lip`. -/
theorem norm_literalStretchL2_le (htau : 0 ≤ tau) :
    ‖literalStretchL2 (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))‖ ≤
      12 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau := by
  have hnn := globalVelocityLipschitzBound_nonneg h P angularSpeed axialSpeed tau htau
  have hA : ‖literalStretchLInf (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))‖ ≤
        12 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau := by
    have hae : ∀ᵐ x : Torus 3 ∂(volume : Measure (Torus 3)),
        ‖(literalStretchLInf (literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) :
            Torus 3 → C3 →L[ℂ] C3) x‖ ≤
          12 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau := by
      filter_upwards [literalStretchLInf_coe_ae h P angularSpeed axialSpeed tau htau] with x hx
      rw [hx]
      calc _ ≤ 6 * ‖literalFDeriv (literalVelocity
              (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) x‖ :=
            norm_r3Complexify_le _
        _ ≤ 6 * (2 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau) :=
            mul_le_mul_of_nonneg_left
              (norm_literalFDeriv_literalVelocity_le h P angularSpeed axialSpeed tau htau x)
              (by norm_num)
        _ = _ := by ring
    have := Lp.norm_le_of_ae_bound (by linarith) hae
    simpa using this
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun B ↦ ?_
  exact (norm_operatorMulL2_apply_apply_le (volume : Measure (Torus 3)) _ B).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
