/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Ideal.VelocityGradient
public import LeanPool.FastDynamo.Dynamics.Flow.FlowDerivative

/-!
# The variational equation of the particle flow

The proof of `cor:ideal-growth` (Corollary 4.2) uses that the derivative flow `DΦ_t` of the
particle flow solves the variational equation `eq:flow-variational-equation` (4.8),

```
  DΦ_t(a) = Id + ∫₀ᵗ (∇u)(Φ_s(a)) DΦ_s(a) ds,
```

where `∇u` is the Jacobian `Du` of the velocity.  The paper obtains it for almost every `a` from
the Cauchy–Lipschitz theorem and Rademacher's theorem.  Here it holds at **every** point and every
time: the derivative flow `flowFDeriv` is the Fréchet derivative of the periodic lift of the flow
at every point (`hasFDerivAt_literalFlowLift`), the lift of the velocity is differentiable at every
point (`differentiable_literalVelocity_lift`), and the equation follows by differentiating the
integral form of the ODE in the initial point, under the integral sign by dominated convergence.

## Contents

* `flowDeriv_apply_eq_add_integral` — the generic statement: if a flow `X` of a differentiable
  field `U` with bounded derivative has a Fréchet derivative `DX` in the initial point, bounded
  on bounded time intervals, then `DX t a w = w + ∫₀ᵗ DU(X s a) (DX s a w) ds`.
* `flowFDeriv_eq_one_add_integral` — `eq:flow-variational-equation` for the flow of the paper.
* `hasDerivAt_flowFDeriv` — its differential form `∂ₜ DΦ_t(x) = (∇u)(Φ_t x) DΦ_t(x)`.
* `flowFDeriv_apply_literalVelocity` — `DΦ_t(x) u(x) = u(Φ_t x)`, the derivative of the group law
  `Φ_t ∘ Φ_h = Φ_{t+h}` in `h` at `0`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Interval

/-! ## The generic statement -/

/-- **Differentiation of the integral equation of a flow in the initial point.**  Let `X` be a
flow of the field `U` on `ℝ³` (`∂ₜ X t a = U (X t a)`, `X 0 a = a`), where `U` is differentiable
with derivative bounded by `K`, and let `DX t a` be the Fréchet derivative of `X t` at `a`,
bounded uniformly in `a` for `t` in bounded intervals.  Then `DX` solves the variational equation
`DX t a w = w + ∫₀ᵗ DU(X s a) (DX s a w) ds`, for every `t`, `a` and `w`.

The proof differentiates `X t b = b + ∫₀ᵗ U (X s b) ds` at `b = a` in the direction `w`: the
difference quotients of the integrand converge pointwise by the chain rule and are dominated by
`K · C · ‖w‖` by the mean value inequality. -/
theorem flowDeriv_apply_eq_add_integral {U : R3 → R3} {X : ℝ → R3 → R3}
    {DX : ℝ → R3 → (R3 →L[ℝ] R3)} (hU : Differentiable ℝ U) {K : ℝ}
    (hUb : ∀ b : R3, ‖fderiv ℝ U b‖ ≤ K)
    (hX : ∀ (t : ℝ) (a : R3), HasDerivAt (fun s : ℝ ↦ X s a) (U (X t a)) t)
    (hX0 : ∀ a : R3, X 0 a = a)
    (hDX : ∀ (t : ℝ) (a : R3), HasFDerivAt (X t) (DX t a) a)
    (hDXb : ∀ T : ℝ, ∃ C : ℝ, ∀ t ∈ Set.uIcc 0 T, ∀ a : R3, ‖DX t a‖ ≤ C)
    (t : ℝ) (a w : R3) :
    DX t a w = w + ∫ s in (0 : ℝ)..t, fderiv ℝ U (X s a) (DX s a w) := by
  obtain ⟨C, hC⟩ := hDXb t
  have hK : 0 ≤ K := (norm_nonneg _).trans (hUb 0)
  have hXc : ∀ b : R3, Continuous fun s : ℝ ↦ X s b := fun b ↦
    continuous_iff_continuousAt.2 fun s ↦ (hX s b).continuousAt
  have hUXc : ∀ b : R3, Continuous fun s : ℝ ↦ U (X s b) := fun b ↦ hU.continuous.comp (hXc b)
  -- the integral form of the ODE
  have hint : ∀ b : R3, X t b = b + ∫ s in (0 : ℝ)..t, U (X s b) := by
    intro b
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hX s b)
      ((hUXc b).intervalIntegrable 0 t), hX0]
    abel
  -- the two mean value inequalities
  have hUlip : ∀ b c : R3, ‖U b - U c‖ ≤ K * ‖b - c‖ := fun b c ↦
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ ↦ hU x) (fun x _ ↦ hUb x)
      (mem_univ c) (mem_univ b)
  have hXlip : ∀ s ∈ uIcc 0 t, ∀ b c : R3, ‖X s b - X s c‖ ≤ C * ‖b - c‖ := fun s hs b c ↦
    convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ ↦ (hDX s x).hasFDerivWithinAt) (fun x _ ↦ hC s hs x) (mem_univ c) (mem_univ b)
  -- the difference quotients of the integrand
  set F : ℝ → ℝ → R3 := fun ε s ↦ ε⁻¹ • (U (X s (a + ε • w)) - U (X s a)) with hF
  have hquot : ∀ ε : ℝ, ε ≠ 0 →
      ε⁻¹ • (X t (a + ε • w) - X t a) = w + ∫ s in (0 : ℝ)..t, F ε s := by
    intro ε hε
    rw [hint (a + ε • w), hint a, hF, intervalIntegral.integral_smul,
      intervalIntegral.integral_sub ((hUXc _).intervalIntegrable 0 t)
        ((hUXc _).intervalIntegrable 0 t)]
    rw [show a + ε • w + (∫ s in (0 : ℝ)..t, U (X s (a + ε • w))) -
        (a + ∫ s in (0 : ℝ)..t, U (X s a)) =
        ε • w + ((∫ s in (0 : ℝ)..t, U (X s (a + ε • w))) - ∫ s in (0 : ℝ)..t, U (X s a)) by
      abel, smul_add, smul_smul, inv_mul_cancel₀ hε, one_smul]
  -- derivatives along the line `ε ↦ a + ε • w`
  have hline : ∀ s : ℝ, HasDerivAt (fun ε : ℝ ↦ X s (a + ε • w)) (DX s a w) 0 := by
    intro s
    have h1 : HasDerivAt (fun ε : ℝ ↦ a + ε • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
    have h2 : HasFDerivAt (X s) (DX s a) (a + (0 : ℝ) • w) := by
      rw [zero_smul, add_zero]
      exact hDX s a
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hpt : ∀ s : ℝ, Tendsto (fun ε ↦ F ε s) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ U (X s a) (DX s a w))) := by
    intro s
    have hUa : HasFDerivAt U (fderiv ℝ U (X s a)) (X s (a + (0 : ℝ) • w)) := by
      rw [zero_smul, add_zero]
      exact (hU _).hasFDerivAt
    have := (hUa.comp_hasDerivAt (0 : ℝ) (hline s)).tendsto_slope_zero
    simpa only [Function.comp_apply, zero_add, zero_smul, add_zero] using this
  have hLHS : Tendsto (fun ε : ℝ ↦ ε⁻¹ • (X t (a + ε • w) - X t a)) (𝓝[≠] 0)
      (𝓝 (DX t a w)) := by
    have := (hline t).tendsto_slope_zero
    simpa only [zero_add, zero_smul, add_zero] using this
  -- dominated convergence
  have hmeas : ∀ᶠ ε in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (F ε) (volume.restrict (Ι (0 : ℝ) t)) :=
    Eventually.of_forall fun ε ↦
      (show Continuous (F ε) from
        ((hUXc (a + ε • w)).sub (hUXc a)).const_smul ε⁻¹).aestronglyMeasurable
  have hbound : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) t →
      ‖F ε s‖ ≤ K * C * ‖w‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine ae_of_all _ fun s hs ↦ ?_
    have hε' : 0 < |ε| := abs_pos.2 hε
    have hs' : s ∈ uIcc 0 t := uIoc_subset_uIcc hs
    calc ‖F ε s‖ = |ε|⁻¹ * ‖U (X s (a + ε • w)) - U (X s a)‖ := by
          rw [hF, norm_smul, norm_inv, Real.norm_eq_abs]
      _ ≤ |ε|⁻¹ * (K * (C * ‖a + ε • w - a‖)) := by
          gcongr
          exact (hUlip _ _).trans (mul_le_mul_of_nonneg_left (hXlip s hs' _ _) hK)
      _ = K * C * ‖w‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
          field_simp
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[≠] (0 : ℝ)) (F := F)
    (f := fun s ↦ fderiv ℝ U (X s a) (DX s a w)) (fun _ ↦ K * C * ‖w‖) hmeas hbound
    intervalIntegrable_const (ae_of_all _ fun s _ ↦ hpt s)
  have hRHS : Tendsto (fun ε : ℝ ↦ ε⁻¹ • (X t (a + ε • w) - X t a)) (𝓝[≠] 0)
      (𝓝 (w + ∫ s in (0 : ℝ)..t, fderiv ℝ U (X s a) (DX s a w))) :=
    (tendsto_const_nhds.add hlim).congr'
      (eventually_mem_nhdsWithin.mono fun ε hε ↦ (hquot ε hε).symm)
  exact tendsto_nhds_unique hLHS hRHS

/-! ## The flow of the paper -/

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- The periodic lift of the flow is the identity at time `0`. -/
theorem literalFlowLift_zero (a : R3) :
    literalFlowLift h P angularSpeed axialSpeed tau 0 a = a := by
  have hpair := (fullFlowData h P angularSpeed axialSpeed tau).flow_zero (a 0, a 1)
  refine r3_ext ?_ ?_ ?_
  · rw [PeriodizedPlaneFlowData.literalFlowLift_apply_zero, hpair]
  · rw [PeriodizedPlaneFlowData.literalFlowLift_apply_one, hpair]
  · rw [PeriodizedPlaneFlowData.literalFlowLift_apply_two,
      (fullFlowData h P angularSpeed axialSpeed tau).shift_zero, add_zero]

/-- The derivative flow is bounded on every time interval `[0, T]` (or `[T, 0]`) by the bound at
the endpoint `T`. -/
theorem norm_flowFDeriv_le_of_mem_uIcc (htau : 0 ≤ tau) {T t : ℝ} (ht : t ∈ uIcc 0 T)
    (x : Torus 3) :
    ‖flowFDeriv h P angularSpeed axialSpeed tau t x‖ ≤
      flowDerivativeBound h P angularSpeed axialSpeed tau T := by
  have hle : ‖flowFDeriv h P angularSpeed axialSpeed tau t x‖ ≤
      flowDerivativeBound h P angularSpeed axialSpeed tau t :=
    (fullFlowData h P angularSpeed axialSpeed tau).norm_flowFDeriv_le
      (norm_fderiv_planePeriodizedTransverseFlow_le h P angularSpeed axialSpeed tau htau t)
      (norm_fderiv_planePeriodizedAxialShift_add_one_le h P angularSpeed axialSpeed tau htau t) x
  have habs : |t| ≤ |T| := by
    rcases mem_uIcc.1 ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans h1)]
      exact h1
    · rw [abs_of_nonpos h1, abs_of_nonpos (h0.trans h1)]
      linarith
  have hslope := flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau
  refine hle.trans ?_
  rw [flowDerivativeBound_eq, flowDerivativeBound_eq]
  have := mul_le_mul_of_nonneg_right habs hslope
  linarith

/-- The integrand of the variational equation is continuous in the time. -/
theorem continuous_literalFDeriv_comp_flowFDeriv (x : Torus 3) :
    Continuous fun s : ℝ ↦ (literalFDeriv (literalVelocity
        (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (literalFlow h P angularSpeed axialSpeed tau s x)).comp
      (flowFDeriv h P angularSpeed axialSpeed tau s x) :=
  (continuous_literalFDeriv_literalVelocity_literalFlow h P angularSpeed axialSpeed tau x).clm_comp
    (continuous_flowFDeriv_time h P angularSpeed axialSpeed tau x)

/-- **The variational equation** `eq:flow-variational-equation` (proof of `cor:ideal-growth`):
`DΦ_t(x) = Id + ∫₀ᵗ (∇u)(Φ_s x) DΦ_s(x) ds`, with `∇u` the Jacobian of the velocity read on the
periodic lift (`literalFDeriv`).  The paper states it for almost every point; here it holds at
every point `x` and every time `t`. -/
theorem flowFDeriv_eq_one_add_integral (htau : 0 ≤ tau) (t : ℝ) (x : Torus 3) :
    flowFDeriv h P angularSpeed axialSpeed tau t x =
      ContinuousLinearMap.id ℝ R3 +
        ∫ s in (0 : ℝ)..t, (literalFDeriv (literalVelocity
            (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
            (literalFlow h P angularSpeed axialSpeed tau s x)).comp
          (flowFDeriv h P angularSpeed axialSpeed tau s x) := by
  obtain ⟨a, rfl⟩ := literalTorusPoint_surjective x
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [add_apply, ContinuousLinearMap.intervalIntegral_apply
    ((continuous_literalFDeriv_comp_flowFDeriv h P angularSpeed axialSpeed tau _).intervalIntegrable
      0 t), ContinuousLinearMap.id_apply]
  have key := flowDeriv_apply_eq_add_integral
    (U := fun b : R3 ↦ literalVelocity
      (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
      (literalTorusPoint b))
    (X := literalFlowLift h P angularSpeed axialSpeed tau)
    (DX := fun s b ↦ flowFDeriv h P angularSpeed axialSpeed tau s (literalTorusPoint b))
    (differentiable_literalVelocity_lift h P angularSpeed axialSpeed tau htau)
    (K := 2 * globalVelocityLipschitzBound h P angularSpeed axialSpeed tau)
    (fun b ↦ by
      rw [← literalFDeriv_literalTorusPoint]
      exact norm_literalFDeriv_literalVelocity_le h P angularSpeed axialSpeed tau htau _)
    (hasDerivAt_literalFlowLift h P angularSpeed axialSpeed tau)
    (literalFlowLift_zero h P angularSpeed axialSpeed tau)
    (hasFDerivAt_literalFlowLift h P angularSpeed axialSpeed tau)
    (fun T ↦ ⟨flowDerivativeBound h P angularSpeed axialSpeed tau T, fun s hs b ↦
      norm_flowFDeriv_le_of_mem_uIcc h P angularSpeed axialSpeed tau htau hs _⟩) t a w
  rw [key]
  congr 1
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [← literalFDeriv_literalTorusPoint, literalTorusPoint_literalFlowLift]

/-- **The variational equation in differential form**: `t ↦ DΦ_t(x)` is differentiable at every
time, with derivative `(∇u)(Φ_t x) DΦ_t(x)`. -/
theorem hasDerivAt_flowFDeriv (htau : 0 ≤ tau) (t : ℝ) (x : Torus 3) :
    HasDerivAt (fun s : ℝ ↦ flowFDeriv h P angularSpeed axialSpeed tau s x)
      ((literalFDeriv (literalVelocity
          (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
          (literalFlow h P angularSpeed axialSpeed tau t x)).comp
        (flowFDeriv h P angularSpeed axialSpeed tau t x)) t := by
  have hfun : (fun s : ℝ ↦ flowFDeriv h P angularSpeed axialSpeed tau s x) = fun s : ℝ ↦
      ContinuousLinearMap.id ℝ R3 +
        ∫ σ in (0 : ℝ)..s, (literalFDeriv (literalVelocity
            (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
            (literalFlow h P angularSpeed axialSpeed tau σ x)).comp
          (flowFDeriv h P angularSpeed axialSpeed tau σ x) :=
    funext fun s ↦ flowFDeriv_eq_one_add_integral h P angularSpeed axialSpeed tau htau s x
  rw [hfun]
  exact ((continuous_literalFDeriv_comp_flowFDeriv h P angularSpeed axialSpeed tau x
    ).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

/-- **The derivative flow carries the velocity along the flow**: `DΦ_t(x) u(x) = u(Φ_t x)`, at
every point and every time.  It is the derivative in `h` at `h = 0` of the group law
`Φ_t(Φ_h x) = Φ_{t+h}(x)`, read on the periodic lift. -/
theorem flowFDeriv_apply_literalVelocity (t : ℝ) (x : Torus 3) :
    flowFDeriv h P angularSpeed axialSpeed tau t x
        (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
          x) =
      literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
        (literalFlow h P angularSpeed axialSpeed tau t x) := by
  obtain ⟨a, rfl⟩ := literalTorusPoint_surjective x
  have h0 := hasDerivAt_literalFlowLift h P angularSpeed axialSpeed tau 0 a
  have hD := hasFDerivAt_literalFlowLift h P angularSpeed axialSpeed tau t
    (literalFlowLift h P angularSpeed axialSpeed tau 0 a)
  have hleft := hD.comp_hasDerivAt (0 : ℝ) h0
  rw [literalFlowLift_zero] at hleft
  have hright : HasDerivAt
      (fun s : ℝ ↦ literalFlowLift h P angularSpeed axialSpeed tau t
        (literalFlowLift h P angularSpeed axialSpeed tau s a))
      (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)
        (literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau t a))) 0 := by
    have hcomp : (fun s : ℝ ↦ literalFlowLift h P angularSpeed axialSpeed tau t
        (literalFlowLift h P angularSpeed axialSpeed tau s a)) =
        fun s : ℝ ↦ literalFlowLift h P angularSpeed axialSpeed tau (t + s) a :=
      funext fun s ↦ (fullFlowData h P angularSpeed axialSpeed tau).literalFlowLift_comp t s a
    rw [hcomp]
    have := (hasDerivAt_literalFlowLift h P angularSpeed axialSpeed tau (t + 0) a).comp_const_add
      t 0
    simpa only [add_zero] using this
  rw [← literalTorusPoint_literalFlowLift]
  exact hleft.unique hright

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
