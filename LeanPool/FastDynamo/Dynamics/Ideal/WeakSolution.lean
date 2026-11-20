/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Flow.VariationalEquation
public import LeanPool.FastDynamo.Dynamics.Ideal.StrongContinuity
public import LeanPool.FastDynamo.Dynamics.Ideal.SolenoidalInvariance

/-!
# The Cauchy formula solves the ideal induction equation

The proof of `cor:ideal-growth` (Corollary 4.2) states that the Cauchy formula
`eq:ideal-cauchy-formula`, `(𝒯₀(t)B)(Φ_t a) = DΦ_t(a) B(a)`, solves the ideal induction
equation `∂ₜB + (u·∇)B − (B·∇)u = 0` in the weak sense.  This module proves it, in the weak
form `IsIdealWeakSolution` of `FastDynamo/Dynamics/IdealWeakForm.lean`, for every datum
`B ∈ L²(T³; ℂ³)` (the paper takes `B ∈ L²_σ`).

## The argument

For a test field `φ` and `B ∈ L²`, the change of variables `x = Φ_t(a)` (the flow preserves the
measure) and the Cauchy formula give
`∫ ⟪φ, 𝒯₀(t)B⟫ = ∫ ⟪φ(Φ_t a), DΦ_t(a) B(a)⟫ da`.  For every `a` the integrand is differentiable
in `t`: `t ↦ φ(Φ_t a)` has derivative `(u·∇)φ(Φ_t a)` (chain rule on the lift) and
`t ↦ DΦ_t(a)` has derivative `∇u(Φ_t a) DΦ_t(a)` (the variational equation
`eq:flow-variational-equation`, `hasDerivAt_flowFDeriv`).  The derivative is dominated by a
multiple of `‖B(a)‖` uniformly for `t` in a bounded interval, so the integral may be
differentiated under the integral sign; changing variables back,
`d/dt ∫ ⟪φ, 𝒯₀(t)B⟫ = ∫ ⟪φ, (𝒯₀(t)B·∇)u⟫ + ⟪(u·∇)φ, 𝒯₀(t)B⟫`.  This derivative is an `L²`
pairing of `𝒯₀(t)B`, hence continuous in `t` (`strongly_continuous_idealTransport`), and the
fundamental theorem of calculus gives the time-integrated weak identity.

## Contents

* `hasDerivAt_inner_literalFlow_flowFDerivC` — the pointwise derivative along a trajectory.
* `hasDerivAt_integral_inner_idealTransport` — the derivative of `t ↦ ∫ ⟪φ, 𝒯₀(t)B⟫`.
* `isIdealWeakSolution_idealTransport` — every orbit `t ↦ 𝒯₀(t)B`, `B ∈ L²`, is a weak solution
  on every `[−T, T]`.
* `isIdealSolutionGroup_idealGroup` — `𝒯₀` restricted to `L²_σ` is a solution group of the ideal
  induction equation.

The derivative is computed at every point and every time, with the pointwise Jacobian `∇u` of
the everywhere differentiable lift of the velocity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Interval

/-! ## Generic facts on the literal torus -/

/-- A function on the torus whose lift is continuous is bounded. -/
theorem exists_norm_le_of_continuous_lift {F : Type*} [NormedAddCommGroup F]
    {f : Torus 3 → F} (hf : Continuous fun a : R3 ↦ f (literalTorusPoint a)) :
    ∃ C, ∀ x : Torus 3, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_comp_literalIocRepresentative hf
  exact ⟨C, fun x ↦ by simpa using hC x⟩

/-- A function on the torus whose lift is continuous is measurable. -/
theorem measurable_of_continuous_lift {F : Type*} [TopologicalSpace F] [MeasurableSpace F]
    [BorelSpace F] {f : Torus 3 → F}
    (hf : Continuous fun a : R3 ↦ f (literalTorusPoint a)) : Measurable f := by
  have := hf.measurable.comp measurable_literalIocRepresentative
  simpa [Function.comp_def] using this

/-- The complexification `r3Complexify` of real endomorphisms of `ℝ³`, as a continuous
`ℝ`-linear map. -/
def r3ComplexifyCLM : (R3 →L[ℝ] R3) →L[ℝ] (C3 →L[ℂ] C3) :=
  LinearMap.mkContinuous
    { toFun := r3Complexify
      map_add' := fun M N ↦ by
        have := r3Complexify_sub (M + N) N
        rw [add_sub_cancel_right] at this
        rw [this, sub_add_cancel]
      map_smul' := fun c M ↦ by
        refine ContinuousLinearMap.ext fun v ↦ PiLp.ext fun i ↦ ?_
        rw [RingHom.id_apply, _root_.smul_apply, PiLp.smul_apply,
          r3Complexify_apply, r3Complexify_apply, Complex.real_smul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul]
        push_cast
        ring }
    6 fun M ↦ norm_r3Complexify_le M

/-- The pairing `∫ ⟪φ, g⟫` of an `L²` field with a representative of an `L²` class is their `L²`
inner product. -/
theorem integral_inner_eq_inner_toLp {φ : Torus 3 → C3} (hφ : MemLp φ 2 volume)
    {g : Torus 3 → C3} {f : LiteralC3L2} (hg : g =ᵐ[volume] f) :
    ∫ x, inner ℂ (φ x) (g x) = inner ℂ (hφ.toLp φ) f := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hφ.coeFn_toLp, hg] with x h1 h2
  rw [h1, h2]

/-- The pairing `x ↦ ⟪φ x, g x⟫` of an `L²` field with a representative of an `L²` class is
integrable. -/
theorem integrable_inner_of_ae_eq {φ : Torus 3 → C3} (hφ : MemLp φ 2 volume)
    {g : Torus 3 → C3} {f : LiteralC3L2} (hg : g =ᵐ[volume] f) :
    Integrable (fun x ↦ inner ℂ (φ x) (g x)) volume := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hφ.toLp φ) f).congr ?_
  filter_upwards [hφ.coeFn_toLp, hg] with x h1 h2
  rw [h1, h2]

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## Test fields at the velocity of the paper -/

/-- The advection `(u·∇)φ` of a test field is bounded. -/
theorem exists_norm_literalAdvection_le (htau : 0 ≤ tau) {φ : Torus 3 → C3}
    (hφ : IsIdealTestField φ) :
    ∃ C, ∀ x : Torus 3, ‖literalAdvection (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ x‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_comp_literalIocRepresentative (hφ.continuous_fderiv (by simp))
  obtain ⟨C₂, hC₂⟩ := exists_norm_le_of_continuous_lift
    (differentiable_literalVelocity_lift h P angularSpeed axialSpeed tau htau).continuous
  refine ⟨C₁ * C₂, fun x ↦ ?_⟩
  rw [literalAdvection]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hC₁ x) (hC₂ x) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ x)))

/-- The advection `(u·∇)φ` of a test field is measurable. -/
theorem aestronglyMeasurable_literalAdvection (htau : 0 ≤ tau) {φ : Torus 3 → C3}
    (hφ : IsIdealTestField φ) :
    AEStronglyMeasurable (literalAdvection (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ) volume := by
  have hD : AEStronglyMeasurable (fun x : Torus 3 ↦
      fderiv ℝ (fun a : R3 ↦ φ (literalTorusPoint a)) (literalIocRepresentative x)) volume :=
    ((hφ.continuous_fderiv (by simp)).measurable.comp
      measurable_literalIocRepresentative).aestronglyMeasurable
  have hu : AEStronglyMeasurable (literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) volume :=
    (measurable_of_continuous_lift
      (differentiable_literalVelocity_lift h P angularSpeed axialSpeed tau
        htau).continuous).aestronglyMeasurable
  exact Continuous.comp_aestronglyMeasurable₂
    (g := fun (L : R3 →L[ℝ] C3) (w : R3) ↦ L w) (continuous_fst.clm_apply continuous_snd) hD hu

/-! ## The derivative along a trajectory -/

/-- **The pointwise derivative.**  Along the trajectory of `a`, the pairing of a test field `φ`
with the transported vector `DΦ_t(a) v` has derivative
`⟪φ(Φ_t a), ∇u(Φ_t a) DΦ_t(a) v⟫ + ⟪(u·∇)φ(Φ_t a), DΦ_t(a) v⟫`, at every time. -/
theorem hasDerivAt_inner_literalFlow_flowFDerivC (htau : 0 ≤ tau) {φ : Torus 3 → C3}
    (hφ : IsIdealTestField φ) (a : Torus 3) (v : C3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℂ (φ (literalFlow h P angularSpeed axialSpeed tau s a))
        (flowFDerivC h P angularSpeed axialSpeed tau s a v))
      (inner ℂ (φ (literalFlow h P angularSpeed axialSpeed tau t a))
          (r3Complexify (literalFDeriv (literalVelocity
              (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
              (literalFlow h P angularSpeed axialSpeed tau t a))
            (flowFDerivC h P angularSpeed axialSpeed tau t a v)) +
        inner ℂ (literalAdvection (literalVelocity
            (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ
            (literalFlow h P angularSpeed axialSpeed tau t a))
          (flowFDerivC h P angularSpeed axialSpeed tau t a v)) t := by
  set b : R3 := literalIocRepresentative a with hb
  have hpt : ∀ s : ℝ, literalFlow h P angularSpeed axialSpeed tau s a =
      literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau s b) := fun s ↦ by
    rw [literalTorusPoint_literalFlowLift, hb, literalTorusPoint_literalIocRepresentative]
  have h1 : HasDerivAt (fun s : ℝ ↦ φ (literalFlow h P angularSpeed axialSpeed tau s a))
      (literalAdvection (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ
        (literalFlow h P angularSpeed axialSpeed tau t a)) t := by
    simp_rw [hpt]
    rw [literalAdvection_literalTorusPoint]
    exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_literalFlowLift h P angularSpeed axialSpeed tau t b)
  have h2 : HasDerivAt (fun s : ℝ ↦ flowFDerivC h P angularSpeed axialSpeed tau s a v)
      (r3Complexify (literalFDeriv (literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
          (literalFlow h P angularSpeed axialSpeed tau t a))
        (flowFDerivC h P angularSpeed axialSpeed tau t a v)) t := by
    have hL := (((ContinuousLinearMap.apply ℂ C3 v).restrictScalars ℝ).comp
      r3ComplexifyCLM).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_flowFDeriv h P angularSpeed axialSpeed tau htau t a)
    refine hL.congr_deriv ?_
    change r3Complexify ((literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (literalFlow h P angularSpeed axialSpeed tau t a)).comp
          (flowFDeriv h P angularSpeed axialSpeed tau t a)) v = _
    rw [r3Complexify_comp]
    rfl
  exact h1.inner ℂ h2

/-! ## The derivative of the pairing with a test field -/

/-- **The derivative of the pairing with a test field**: for `B ∈ L²` and a test field `φ`,
`d/dt ∫ ⟪φ, 𝒯₀(t)B⟫ = ∫ ⟪φ, (𝒯₀(t)B·∇)u⟫ + ⟪(u·∇)φ, 𝒯₀(t)B⟫` at every time.  The pairing is
pulled back along `Φ_t` with the Cauchy formula and differentiated under the integral sign. -/
theorem hasDerivAt_integral_inner_idealTransport (htau : 0 ≤ tau) {φ : Torus 3 → C3}
    (hφ : IsIdealTestField φ) (B : LiteralC3L2) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, inner ℂ (φ x)
        ((idealTransport h P angularSpeed axialSpeed tau t B : Torus 3 → C3) x))
      (∫ x, (inner ℂ (φ x) (literalStretch (literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
          (idealTransport h P angularSpeed axialSpeed tau t₀ B : Torus 3 → C3) x) +
        inner ℂ (literalAdvection (literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) φ x)
          ((idealTransport h P angularSpeed axialSpeed tau t₀ B : Torus 3 → C3) x))) t₀ := by
  set U := literalVelocity
    (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
  set Φ := literalFlow h P angularSpeed axialSpeed tau
  set V : ℝ → Torus 3 → C3 := fun t a ↦
    flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a)
  set F' : ℝ → Torus 3 → ℂ := fun t a ↦
    inner ℂ (φ (Φ t a)) (r3Complexify (literalFDeriv U (Φ t a)) (V t a)) +
      inner ℂ (literalAdvection U φ (Φ t a)) (V t a) with hF'
  -- the Cauchy formula and the change of variables `x = Φ_t a`
  have hcauchy : ∀ t : ℝ, ∀ᵐ a : Torus 3,
      (idealTransport h P angularSpeed axialSpeed tau t B : Torus 3 → C3) (Φ t a) = V t a :=
    fun t ↦ by
      filter_upwards [idealTransport_cauchy h P angularSpeed axialSpeed tau htau t B] with a ha
      refine PiLp.ext fun i ↦ ?_
      rw [ha i]
      exact (r3Complexify_apply _ _ i).symm
  have hmp := measurePreserving_literalFlow h P angularSpeed axialSpeed tau
  have hcov : ∀ (t : ℝ) (H : Torus 3 → ℂ), ∫ x, H x = ∫ a, H (Φ t a) := fun t H ↦
    ((hmp t).integral_comp
      ((fullFlowData h P angularSpeed axialSpeed tau).measurableEmbedding_literalFlow t) H).symm
  have hF : (fun t : ℝ ↦ ∫ x, inner ℂ (φ x)
      ((idealTransport h P angularSpeed axialSpeed tau t B : Torus 3 → C3) x)) =
      fun t ↦ ∫ a, inner ℂ (φ (Φ t a)) (V t a) := by
    funext t
    rw [hcov t]
    refine integral_congr_ae ?_
    filter_upwards [hcauchy t] with a ha
    rw [ha]
  have hF'eq : (∫ x, (inner ℂ (φ x) (literalStretch U
        (idealTransport h P angularSpeed axialSpeed tau t₀ B : Torus 3 → C3) x) +
      inner ℂ (literalAdvection U φ x)
        ((idealTransport h P angularSpeed axialSpeed tau t₀ B : Torus 3 → C3) x))) =
      ∫ a, F' t₀ a := by
    rw [hcov t₀]
    refine integral_congr_ae ?_
    filter_upwards [hcauchy t₀] with a ha
    rw [hF', literalStretch, ha]
  -- the bounds
  obtain ⟨Cφ, hCφ⟩ := exists_norm_le_of_continuous_lift hφ.continuous
  obtain ⟨Ca, hCa⟩ := exists_norm_literalAdvection_le h P angularSpeed axialSpeed tau htau hφ
  have hCφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 0)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa 0)
  have hL0 := globalVelocityLipschitzBound_nonneg h P angularSpeed axialSpeed tau htau
  set L := globalVelocityLipschitzBound h P angularSpeed axialSpeed tau
  set K := flowComplexDerivativeBound h P angularSpeed axialSpeed tau (|t₀| + 1) with hK
  have hK0 : 0 ≤ K := flowComplexDerivativeBound_nonneg h P angularSpeed axialSpeed tau htau _
  have hKs : ∀ s ∈ Metric.ball t₀ 1, ∀ a : Torus 3,
      ‖flowFDerivC h P angularSpeed axialSpeed tau s a‖ ≤ K := by
    intro s hs a
    refine (norm_flowFDerivC_le h P angularSpeed axialSpeed tau htau s a).trans ?_
    have hs' : |s| ≤ |(|t₀| + 1)| := by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have := abs_sub_abs_le_abs_sub s t₀
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |t₀| + 1)]
      linarith
    have hslope := flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau
    rw [hK, flowComplexDerivativeBound_eq, flowComplexDerivativeBound_eq]
    nlinarith
  have hVs : ∀ s ∈ Metric.ball t₀ 1, ∀ a : Torus 3,
      ‖V s a‖ ≤ K * ‖(B : Torus 3 → C3) a‖ := fun s hs a ↦
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hKs s hs a) (norm_nonneg _))
  set C := Cφ * (6 * (2 * L)) * K + Ca * K with hC
  have hbound : ∀ s ∈ Metric.ball t₀ 1, ∀ a : Torus 3,
      ‖F' s a‖ ≤ C * ‖(B : Torus 3 → C3) a‖ := by
    intro s hs a
    have hS : ‖r3Complexify (literalFDeriv U (Φ s a)) (V s a)‖ ≤
        6 * (2 * L) * (K * ‖(B : Torus 3 → C3) a‖) :=
      (norm_r3Complexify_apply_le _ _).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left
          (norm_literalFDeriv_literalVelocity_le h P angularSpeed axialSpeed tau htau _)
          (by norm_num)) (hVs s hs a) (norm_nonneg _) (by positivity))
    calc ‖F' s a‖ ≤ ‖φ (Φ s a)‖ * ‖r3Complexify (literalFDeriv U (Φ s a)) (V s a)‖ +
          ‖literalAdvection U φ (Φ s a)‖ * ‖V s a‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
      _ ≤ Cφ * (6 * (2 * L) * (K * ‖(B : Torus 3 → C3) a‖)) +
          Ca * (K * ‖(B : Torus 3 → C3) a‖) :=
          add_le_add (mul_le_mul (hCφ _) hS (norm_nonneg _) hCφ0)
            (mul_le_mul (hCa _) (hVs s hs a) (norm_nonneg _) hCa0)
      _ = C * ‖(B : Torus 3 → C3) a‖ := by rw [hC]; ring
  have hBint : Integrable (fun a : Torus 3 ↦ ‖(B : Torus 3 → C3) a‖) volume :=
    ((Lp.memLp B).integrable one_le_two).norm
  -- measurability
  have hφm : Measurable φ := measurable_of_continuous_lift hφ.continuous
  have happ : Continuous fun p : (C3 →L[ℂ] C3) × C3 ↦ p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hVm : ∀ t : ℝ, AEStronglyMeasurable (V t) volume := fun t ↦
    Continuous.comp_aestronglyMeasurable₂ (g := fun (M : C3 →L[ℂ] C3) (w : C3) ↦ M w) happ
      (measurable_flowFDerivC h P angularSpeed axialSpeed tau t).aestronglyMeasurable
      (Lp.aestronglyMeasurable B)
  have hFm : ∀ t : ℝ, AEStronglyMeasurable (fun a ↦ inner ℂ (φ (Φ t a)) (V t a)) volume :=
    fun t ↦ (hφm.comp (hmp t).measurable).aestronglyMeasurable.inner (hVm t)
  have hF'm : AEStronglyMeasurable (F' t₀) volume := by
    refine AEStronglyMeasurable.add ?_ ?_
    · refine (hφm.comp (hmp t₀).measurable).aestronglyMeasurable.inner ?_
      exact Continuous.comp_aestronglyMeasurable₂ (g := fun (M : C3 →L[ℂ] C3) (w : C3) ↦ M w)
        happ ((continuous_r3Complexify.measurable.comp
          ((measurable_literalFDeriv_literalVelocity h P angularSpeed axialSpeed tau).comp
            (hmp t₀).measurable)).aestronglyMeasurable) (hVm t₀)
    · exact ((aestronglyMeasurable_literalAdvection h P angularSpeed axialSpeed tau htau
        hφ).comp_measurePreserving (hmp t₀)).inner (hVm t₀)
  have hFint : Integrable (fun a ↦ inner ℂ (φ (Φ t₀ a)) (V t₀ a)) volume := by
    refine (hBint.const_mul (Cφ * K)).mono' (hFm t₀) (ae_of_all _ fun a ↦ ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul (hCφ _) (hVs t₀ (Metric.mem_ball_self one_pos) a) (norm_nonneg _) hCφ0
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t a ↦ inner ℂ (φ (Φ t a)) (V t a)) (F' := F')
    (bound := fun a ↦ C * ‖(B : Torus 3 → C3) a‖) (Metric.ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall hFm) hFint hF'm (ae_of_all _ fun a s hs ↦ hbound s hs a)
    (hBint.const_mul C) (ae_of_all _ fun a s _ ↦
      hasDerivAt_inner_literalFlow_flowFDerivC h P angularSpeed axialSpeed tau htau hφ a _ s)
  rw [hF, hF'eq]
  exact hD

/-! ## The weak solution and the solution group -/

/-- **The Cauchy formula solves the ideal induction equation** (proof of `cor:ideal-growth`):
for every `B ∈ L²(T³; ℂ³)` and every `T`, the orbit `t ↦ 𝒯₀(t)B` is a weak solution of
`∂ₜB + (u·∇)B − (B·∇)u = 0` on `[−T, T]`.  The paper states it for `B ∈ L²_σ`. -/
theorem isIdealWeakSolution_idealTransport (htau : 0 ≤ tau) (B : LiteralC3L2) (T : ℝ) :
    IsIdealWeakSolution (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)) T
      fun t ↦ idealTransport h P angularSpeed axialSpeed tau t B where
  continuousOn :=
    (strongly_continuous_idealTransport h P angularSpeed axialSpeed tau htau B).continuousOn
  weak φ hφ s _ t _ := by
    set U := literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
    set W : ℝ → LiteralC3L2 := fun τ ↦ idealTransport h P angularSpeed axialSpeed tau τ B
    have hφL : MemLp φ 2 volume := by
      obtain ⟨C, hC⟩ := exists_norm_le_of_continuous_lift hφ.continuous
      exact MemLp.of_bound (measurable_of_continuous_lift hφ.continuous).aestronglyMeasurable C
        (ae_of_all _ hC)
    have hadvL : MemLp (literalAdvection U φ) 2 volume := by
      obtain ⟨C, hC⟩ := exists_norm_literalAdvection_le h P angularSpeed axialSpeed tau htau hφ
      exact MemLp.of_bound
        (aestronglyMeasurable_literalAdvection h P angularSpeed axialSpeed tau htau hφ) C
        (ae_of_all _ hC)
    have hD : ∀ τ : ℝ, (∫ x, (inner ℂ (φ x) (literalStretch U (W τ : Torus 3 → C3) x) +
        inner ℂ (literalAdvection U φ x) ((W τ : Torus 3 → C3) x))) =
        inner ℂ (hφL.toLp φ) (literalStretchL2 U (W τ)) +
          inner ℂ (hadvL.toLp _) (W τ) := by
      intro τ
      have hS := (literalStretchL2_coe_ae h P angularSpeed axialSpeed tau htau (W τ)).symm
      have hW' : (W τ : Torus 3 → C3) =ᵐ[volume] (W τ : Torus 3 → C3) := ae_eq_refl _
      rw [integral_add (integrable_inner_of_ae_eq hφL hS) (integrable_inner_of_ae_eq hadvL hW'),
        integral_inner_eq_inner_toLp hφL hS, integral_inner_eq_inner_toLp hadvL hW']
    have hcontW : Continuous W :=
      strongly_continuous_idealTransport h P angularSpeed axialSpeed tau htau B
    have hcont : Continuous fun τ : ℝ ↦
        ∫ x, (inner ℂ (φ x) (literalStretch U (W τ : Torus 3 → C3) x) +
          inner ℂ (literalAdvection U φ x) ((W τ : Torus 3 → C3) x)) := by
      simp_rw [hD]
      exact (continuous_const.inner ((literalStretchL2 U).continuous.comp hcontW)).add
        (continuous_const.inner hcontW)
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun τ _ ↦ hasDerivAt_integral_inner_idealTransport h P angularSpeed axialSpeed tau htau
        hφ B τ) (hcont.intervalIntegrable s t)).symm

/-- **`𝒯₀` is a solution group of the ideal induction equation on `L²_σ`** (proof of
`cor:ideal-growth`): the group laws, and every orbit is a weak solution on every `[−T, T]`. -/
theorem isIdealSolutionGroup_idealGroup (htau : 0 ≤ tau) :
    IsIdealSolutionGroup (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
      (idealGroup h P angularSpeed axialSpeed tau) where
  group_zero := idealGroup_zero h P angularSpeed axialSpeed tau htau
  group_add := idealGroup_add h P angularSpeed axialSpeed tau htau
  weakSolution B T := by
    have hfun : (fun t ↦ ((idealGroup h P angularSpeed axialSpeed tau t B :
        literalSolenoidalSubspace) : LiteralC3L2)) =
        fun t ↦ idealTransport h P angularSpeed axialSpeed tau t (B : LiteralC3L2) :=
      funext fun t ↦ idealGroup_coe h P angularSpeed axialSpeed tau htau t B
    rw [hfun]
    exact isIdealWeakSolution_idealTransport h P angularSpeed axialSpeed tau htau B T

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
