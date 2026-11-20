/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Ideal.CauchyOperator

/-!
# Strong continuity of the ideal Cauchy transport group

The `strongly_continuous` clause of `IsIdealInductionGroup`
(`FastDynamo/Dynamics/ParticleFlow.lean`) asks that `t ↦ 𝒯₀(t)B` be continuous in `L²` for every
datum `B`.  The paper proves it (the strong-continuity paragraph of the proof of
`cor:ideal-growth`) for smooth fields and extends it by density; this module takes a cheaper
route, which needs no smooth approximation of a solenoidal field:

1. **The substitution is strongly continuous.**  Composition with the backward flow,
   `flowCompL2 … t B = B ∘ Φ_{-t}`, is an isometry of `L²(T³; ℂ³)` for every `t`, and for a
   *continuous* datum `g` the composite `g ∘ Φ_{-t}` moves continuously in the supremum norm,
   because `Φ` is Lipschitz in the time uniformly in the point
   (`dist_literalFlow_le`, the descent of the plane estimates of
   `FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`) and `g` is uniformly continuous on the
   compact torus.  Continuous data are dense in `L²` (`ContinuousMap.toLp_denseRange`), and a
   uniform limit of continuous functions is continuous, so `t ↦ flowCompL2 … t B` is continuous
   for **every** `B` (`continuous_flowCompL2_apply`).

2. **The symbol is strongly continuous at the origin.**  Composing with `Φ_t` — again an isometry
   — turns the difference `𝒯₀(t)B - B ∘ Φ_{-t}` into the pointwise expression
   `DΦ_t(a)B(a) - B(a)`, in which the time enters *only* through the derivative flow at the fixed
   point `a`.  The paper's display in that paragraph, `∫ |DΦ_t(a)B(a) - B(Φ_t(a))|² da` for
   smooth `B`, compares with `B(Φ_t(a))` instead; splitting off the substitution (step 1) is
   what makes the argument cheap: `t ↦ DΦ_t(a)` is continuous for each fixed `a`
   (`continuous_flowFDerivC_time`) even though `DΦ_t` is discontinuous in `a`, and
   `norm_flowFDerivC_le` dominates the integrand by a multiple of `‖B‖²`, so dominated
   convergence applies (`tendsto_integral_norm_flowFDerivC_apply_sub`).

3. **The group law moves the origin.**  Steps 1 and 2 give `𝒯₀(t)B → B` as `t → 0`
   (`tendsto_idealTransport_zero`); `𝒯₀(t) = 𝒯₀(t - t₀) 𝒯₀(t₀)` then transports the statement to
   every `t₀` (`strongly_continuous_idealTransport`), which is the delivered clause.

The final statement is on the whole of `LiteralC3L2`; the restriction to
`literalSolenoidalSubspace` is performed by the assembly module, the corestriction of a
continuous map being continuous.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The flow is Lipschitz in the time, uniformly in the point -/

/-- **The uniform speed of the literal flow**: the larger of the transverse and the axial plane
speed bounds of `FastDynamo/Dynamics/Flow/PlaneFlow.lean`.  No hypothesis on `tau` enters: neither
plane bound has one. -/
def flowTimeSpeedBound : ℝ :=
  max (planeTransverseSpeedBound h P angularSpeed) (planeAxialSpeedBound h P axialSpeed tau)

/-- The transverse plane speed bound is at most the uniform flow speed bound. -/
theorem planeTransverseSpeedBound_le_flowTimeSpeedBound :
    planeTransverseSpeedBound h P angularSpeed ≤
      flowTimeSpeedBound h P angularSpeed axialSpeed tau := by
  rw [flowTimeSpeedBound]
  exact le_max_left _ _

/-- The axial plane speed bound is at most the uniform flow speed bound. -/
theorem planeAxialSpeedBound_le_flowTimeSpeedBound :
    planeAxialSpeedBound h P axialSpeed tau ≤
      flowTimeSpeedBound h P angularSpeed axialSpeed tau := by
  rw [flowTimeSpeedBound]
  exact le_max_right _ _

/-- The uniform flow speed bound is nonnegative. -/
theorem flowTimeSpeedBound_nonneg :
    0 ≤ flowTimeSpeedBound h P angularSpeed axialSpeed tau :=
  le_trans (planeTransverseSpeedBound_nonneg h P angularSpeed)
    (planeTransverseSpeedBound_le_flowTimeSpeedBound h P angularSpeed axialSpeed tau)

/-- The transverse torus flow is Lipschitz in the time, uniformly in the point: the descent of
`dist_planePeriodizedTransverseFlow_le` through the `1`-Lipschitz quotient map
`transverseTorusPoint`. -/
theorem dist_torusTransverseFlow_le (s t : ℝ) (y : TransverseTorus) :
    dist (torusTransverseFlow h P angularSpeed t y) (torusTransverseFlow h P angularSpeed s y) ≤
      planeTransverseSpeedBound h P angularSpeed * |t - s| := by
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [torusTransverseFlow_transverseTorusPoint, torusTransverseFlow_transverseTorusPoint]
  refine le_trans ?_ (dist_planePeriodizedTransverseFlow_le h P angularSpeed s t x)
  simpa using lipschitzWith_transverseTorusPoint.dist_le_mul
    (planePeriodizedTransverseFlow h P angularSpeed t x)
    (planePeriodizedTransverseFlow h P angularSpeed s x)

/-- The axial torus shear is Lipschitz in the time, uniformly in the point: the descent of
`abs_planePeriodizedAxialShift_sub_le`. -/
theorem abs_torusAxialShift_sub_le (s t : ℝ) (y : TransverseTorus) :
    |torusAxialShift h P axialSpeed tau t y - torusAxialShift h P axialSpeed tau s y| ≤
      planeAxialSpeedBound h P axialSpeed tau * |t - s| := by
  obtain ⟨x, rfl⟩ := transverseTorusPoint_surjective y
  rw [torusAxialShift_transverseTorusPoint, torusAxialShift_transverseTorusPoint]
  exact abs_planePeriodizedAxialShift_sub_le h P axialSpeed tau s t x

/-- **The literal flow is Lipschitz in the time, uniformly in the point**
(`‖Φ_t - Φ_s‖_∞ ≤ C |t - s|`, cf. the bound `‖Φ_t - id‖_∞ ≤ ‖u‖_∞ |t|` of
the strong-continuity paragraph of the proof of `cor:ideal-growth`).  The transverse coordinates
inherit the plane estimate through the `1`-Lipschitz quotient map, and the axial coordinate
through translation invariance of the circle distance and the `1`-Lipschitz coercion
`ℝ → UnitAddCircle`; the supremum metric of `Torus 3` therefore costs nothing beyond the
maximum of the two plane constants. -/
theorem dist_literalFlow_le (s t : ℝ) (x : Torus 3) :
    dist (literalFlow h P angularSpeed axialSpeed tau t x)
        (literalFlow h P angularSpeed axialSpeed tau s x) ≤
      flowTimeSpeedBound h P angularSpeed axialSpeed tau * |t - s| := by
  have hK : 0 ≤ flowTimeSpeedBound h P angularSpeed axialSpeed tau :=
    flowTimeSpeedBound_nonneg h P angularSpeed axialSpeed tau
  refine (dist_pi_le_iff (mul_nonneg hK (abs_nonneg _))).2 fun j ↦ ?_
  refine Fin.lastCases ?_ ?_ j
  · rw [literalFlow_apply_last, literalFlow_apply_last, dist_add_left]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right
      (planeAxialSpeedBound_le_flowTimeSpeedBound h P angularSpeed axialSpeed tau)
      (abs_nonneg (t - s)))
    refine le_trans (by
      simpa using lipschitzWith_unitAddCircle_coe.dist_le_mul
        (torusAxialShift h P axialSpeed tau t fun i : Fin 2 ↦ x i.castSucc)
        (torusAxialShift h P axialSpeed tau s fun i : Fin 2 ↦ x i.castSucc)) ?_
    rw [Real.dist_eq]
    exact abs_torusAxialShift_sub_le h P axialSpeed tau s t _
  · intro i
    rw [literalFlow_apply_castSucc, literalFlow_apply_castSucc]
    refine le_trans (dist_le_pi_dist _ _ i) ?_
    refine le_trans (dist_torusTransverseFlow_le h P angularSpeed s t _) ?_
    exact mul_le_mul_of_nonneg_right
      (planeTransverseSpeedBound_le_flowTimeSpeedBound h P angularSpeed axialSpeed tau)
      (abs_nonneg (t - s))

/-! ## The flow as a bundled continuous map, and its continuity in the time -/

/-- The literal flow at time `t` as a bundled continuous self-map of `Torus 3`. -/
def literalFlowCM (t : ℝ) : C(Torus 3, Torus 3) :=
  ⟨literalFlow h P angularSpeed axialSpeed tau t,
    continuous_literalFlow h P angularSpeed axialSpeed tau t⟩

/-- The bundled continuous map acts as the flow. -/
@[simp]
theorem literalFlowCM_apply (t : ℝ) (x : Torus 3) :
    literalFlowCM h P angularSpeed axialSpeed tau t x =
      literalFlow h P angularSpeed axialSpeed tau t x := rfl

/-- **Precomposition with the backward flow is continuous in the time on continuous data.**  The
supremum distance of `g ∘ Φ_{-t}` and `g ∘ Φ_{-t₀}` is controlled by the modulus of uniform
continuity of `g` on the compact torus evaluated at `C |t - t₀|`. -/
theorem continuous_comp_literalFlowCM (g : C(Torus 3, C3)) :
    Continuous fun t : ℝ ↦ g.comp (literalFlowCM h P angularSpeed axialSpeed tau (-t)) := by
  have hK : 0 ≤ flowTimeSpeedBound h P angularSpeed axialSpeed tau :=
    flowTimeSpeedBound_nonneg h P angularSpeed axialSpeed tau
  have hK1 : 0 < flowTimeSpeedBound h P angularSpeed axialSpeed tau + 1 := by linarith
  refine Metric.continuous_iff.2 fun t₀ ε hε ↦ ?_
  obtain ⟨delta, hdelta, hgd⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 2) (by positivity)
  refine ⟨delta / (flowTimeSpeedBound h P angularSpeed axialSpeed tau + 1), by positivity,
    fun t ht ↦ ?_⟩
  have hstep : dist (g.comp (literalFlowCM h P angularSpeed axialSpeed tau (-t)))
      (g.comp (literalFlowCM h P angularSpeed axialSpeed tau (-t₀))) ≤ ε / 2 := by
    refine (ContinuousMap.dist_le (by positivity)).2 fun x ↦ ?_
    refine le_of_lt (hgd ?_)
    have hb := dist_literalFlow_le h P angularSpeed axialSpeed tau (-t₀) (-t) x
    have habs : |(-t) - -t₀| = dist t t₀ := by
      rw [Real.dist_eq, show (-t) - -t₀ = -(t - t₀) by ring, abs_neg]
    rw [habs] at hb
    refine lt_of_le_of_lt hb ?_
    calc flowTimeSpeedBound h P angularSpeed axialSpeed tau * dist t t₀
        ≤ (flowTimeSpeedBound h P angularSpeed axialSpeed tau + 1) * dist t t₀ := by
          have := dist_nonneg (x := t) (y := t₀)
          nlinarith
      _ < (flowTimeSpeedBound h P angularSpeed axialSpeed tau + 1) *
            (delta / (flowTimeSpeedBound h P angularSpeed axialSpeed tau + 1)) :=
          by exact mul_lt_mul_of_pos_left ht hK1
      _ = delta := by field_simp
  linarith

/-! ## Composition with the backward flow as an operator on `L²` -/

/-- **Composition with the backward flow** `B ↦ B ∘ Φ_{-t}`, the second factor of the Cauchy
transport `idealTransport … t`.  It is an isometry of `L²(T³; ℂ³)` because the flow preserves the
volume. -/
def flowCompL2 (t : ℝ) : LiteralC3L2 →L[ℂ] LiteralC3L2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (literalFlow h P angularSpeed axialSpeed tau (-t))
    (measurePreserving_literalFlow h P angularSpeed axialSpeed tau (-t))).toContinuousLinearMap

/-- The almost everywhere representative of the substitution. -/
theorem flowCompL2_coe_ae (t : ℝ) (B : LiteralC3L2) :
    (flowCompL2 h P angularSpeed axialSpeed tau t B : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ (B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x) :=
  coeFn_compMeasurePreservingCLM
    (measurePreserving_literalFlow h P angularSpeed axialSpeed tau (-t)) B

/-- The almost everywhere representative of the substitution at a negated time, with the double
negation already removed. -/
theorem flowCompL2_neg_coe_ae (t : ℝ) (B : LiteralC3L2) :
    (flowCompL2 h P angularSpeed axialSpeed tau (-t) B : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ (B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau t x) := by
  have hrep := flowCompL2_coe_ae h P angularSpeed axialSpeed tau (-t) B
  rw [neg_neg] at hrep
  exact hrep

/-- The substitution is an isometry. -/
theorem norm_flowCompL2_apply (t : ℝ) (B : LiteralC3L2) :
    ‖flowCompL2 h P angularSpeed axialSpeed tau t B‖ = ‖B‖ :=
  norm_compMeasurePreservingCLM
    (measurePreserving_literalFlow h P angularSpeed axialSpeed tau (-t)) B

/-- At time zero the substitution is the identity. -/
theorem flowCompL2_zero (B : LiteralC3L2) :
    flowCompL2 h P angularSpeed axialSpeed tau 0 B = B := by
  refine Lp.ext ?_
  filter_upwards [flowCompL2_coe_ae h P angularSpeed axialSpeed tau 0 B] with x hx
  rw [hx, neg_zero, literalFlow_zero]

/-- On a continuous datum the substitution is precomposition of continuous maps. -/
theorem flowCompL2_toLp (t : ℝ) (g : C(Torus 3, C3)) :
    flowCompL2 h P angularSpeed axialSpeed tau t
        (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g) =
      ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
        (g.comp (literalFlowCM h P angularSpeed axialSpeed tau (-t))) := by
  refine Lp.ext ?_
  have h1 := flowCompL2_coe_ae h P angularSpeed axialSpeed tau t
    (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)
  have h2 := (quasiMeasurePreserving_literalFlow h P angularSpeed axialSpeed tau (-t)).ae
    (ContinuousMap.coeFn_toLp (E := C3) (p := 2) (volume : Measure (Torus 3)) (𝕜 := ℂ) g)
  have h3 := ContinuousMap.coeFn_toLp (E := C3) (p := 2) (volume : Measure (Torus 3)) (𝕜 := ℂ)
    (g.comp (literalFlowCM h P angularSpeed axialSpeed tau (-t)))
  filter_upwards [h1, h2, h3] with x hx hx2 hx3
  rw [hx, hx2, hx3]
  rfl

/-- **Step 1 of the strong-continuity argument**: the substitution is strongly continuous.
Continuous data are dense in `L²` (`ContinuousMap.toLp_denseRange`), on them the orbit is
continuous by `continuous_comp_literalFlowCM`, and the approximation is uniform in the time
because every
`flowCompL2 … t` is an isometry; a uniform limit of continuous functions is continuous. -/
theorem continuous_flowCompL2_apply (B : LiteralC3L2) :
    Continuous fun t : ℝ ↦ flowCompL2 h P angularSpeed axialSpeed tau t B := by
  refine continuous_of_uniform_approx_of_continuous ?_
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.1
    (ContinuousMap.toLp_denseRange C3 (volume : Measure (Torus 3)) ℂ (by simp)) B ε hε
  refine ⟨fun t : ℝ ↦ flowCompL2 h P angularSpeed axialSpeed tau t
    (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g), ?_, fun t ↦ hsub ?_⟩
  · have heq : (fun t : ℝ ↦ flowCompL2 h P angularSpeed axialSpeed tau t
        (ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ g)) =
        fun t : ℝ ↦ ContinuousMap.toLp 2 (volume : Measure (Torus 3)) ℂ
          (g.comp (literalFlowCM h P angularSpeed axialSpeed tau (-t))) := by
      funext t
      exact flowCompL2_toLp h P angularSpeed axialSpeed tau t g
    rw [heq]
    exact (ContinuousMap.toLp (E := C3) 2 (volume : Measure (Torus 3)) ℂ).continuous.comp
      (continuous_comp_literalFlowCM h P angularSpeed axialSpeed tau g)
  · rw [dist_eq_norm, ← ContinuousLinearMap.map_sub,
      norm_flowCompL2_apply h P angularSpeed axialSpeed tau t, ← dist_eq_norm]
    exact hg

/-! ## The symbol at the origin -/

/-- The pointwise bound of the dominated-convergence step: for `|t| ≤ 1` the difference between
the complexified derivative flow and the identity is bounded by the fixed constant
`flowComplexDerivativeBound … 1 + 1`, uniformly in the point and in the time. -/
theorem norm_flowFDerivC_apply_sub_le (htau : 0 ≤ tau) {t : ℝ} (ht : |t| ≤ 1)
    (a : Torus 3) (v : C3) :
    ‖flowFDerivC h P angularSpeed axialSpeed tau t a v - v‖ ≤
      (flowComplexDerivativeBound h P angularSpeed axialSpeed tau 1 + 1) * ‖v‖ := by
  have hslope : 0 ≤ flowLipschitzSlope h P angularSpeed axialSpeed tau :=
    flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau
  have hmono : flowComplexDerivativeBound h P angularSpeed axialSpeed tau t ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau 1 := by
    rw [flowComplexDerivativeBound_eq, flowComplexDerivativeBound_eq, abs_one]
    nlinarith [mul_le_mul_of_nonneg_right ht hslope]
  have hop := norm_flowFDerivC_le h P angularSpeed axialSpeed tau htau t a
  have happ : ‖flowFDerivC h P angularSpeed axialSpeed tau t a v‖ ≤
      flowComplexDerivativeBound h P angularSpeed axialSpeed tau 1 * ‖v‖ := by
    refine le_trans ((flowFDerivC h P angularSpeed axialSpeed tau t a).le_opNorm v) ?_
    exact mul_le_mul_of_nonneg_right (hop.trans hmono) (norm_nonneg v)
  calc ‖flowFDerivC h P angularSpeed axialSpeed tau t a v - v‖
      ≤ ‖flowFDerivC h P angularSpeed axialSpeed tau t a v‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ flowComplexDerivativeBound h P angularSpeed axialSpeed tau 1 * ‖v‖ + ‖v‖ := by linarith
    _ = (flowComplexDerivativeBound h P angularSpeed axialSpeed tau 1 + 1) * ‖v‖ := by ring

/-- **Step 2 of the strong-continuity argument**: the integral `∫ |DΦ_t(a)B(a) - B(a)|² da`
tends to zero as the time tends to zero.  The integrand converges pointwise because
`t ↦ DΦ_t(a)` is continuous at every fixed `a` (`continuous_flowFDerivC_time`) with
`DΦ_0 = id`, and it is dominated by a fixed multiple of `‖B‖²` by
`norm_flowFDerivC_apply_sub_le`. -/
theorem tendsto_integral_norm_flowFDerivC_apply_sub (htau : 0 ≤ tau) (B : LiteralC3L2) :
    Tendsto (fun t : ℝ ↦ ∫ a : Torus 3,
        ‖flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a) -
          (B : Torus 3 → C3) a‖ ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hbound : Integrable (fun a : Torus 3 ↦
      (flowComplexDerivativeBound h P angularSpeed axialSpeed tau 1 + 1) ^ 2 *
        ‖(B : Torus 3 → C3) a‖ ^ 2) (volume : Measure (Torus 3)) :=
    (integrable_sq_norm_literalC3L2 B).const_mul _
  have hmeas : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun a : Torus 3 ↦
      ‖flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a) -
        (B : Torus 3 → C3) a‖ ^ 2) (volume : Measure (Torus 3)) := by
    filter_upwards with t
    have hm := (aestronglyMeasurable_clm_apply_literalC3L2
      (measurable_flowFDerivC h P angularSpeed axialSpeed tau t) B).sub
      (Lp.aestronglyMeasurable B)
    exact (continuous_pow 2).comp_aestronglyMeasurable hm.norm
  have hdom : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ᵐ a : Torus 3,
      ‖‖flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a) -
        (B : Torus 3 → C3) a‖ ^ 2‖ ≤
      (flowComplexDerivativeBound h P angularSpeed axialSpeed tau 1 + 1) ^ 2 *
        ‖(B : Torus 3 → C3) a‖ ^ 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    have habs : |t| ≤ 1 := by
      have := Metric.mem_ball.1 ht
      rw [Real.dist_eq, sub_zero] at this
      exact this.le
    filter_upwards with a
    have hle := norm_flowFDerivC_apply_sub_le h P angularSpeed axialSpeed tau htau habs a
      ((B : Torus 3 → C3) a)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (flowFDerivC h P angularSpeed axialSpeed tau t a
      ((B : Torus 3 → C3) a) - (B : Torus 3 → C3) a), norm_nonneg ((B : Torus 3 → C3) a)]
  have hlim : ∀ᵐ a : Torus 3, Tendsto (fun t : ℝ ↦
      ‖flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a) -
        (B : Torus 3 → C3) a‖ ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
    filter_upwards with a
    have hap := (ContinuousLinearMap.apply ℂ C3 ((B : Torus 3 → C3) a)).continuous.comp
      (continuous_flowFDerivC_time h P angularSpeed axialSpeed tau a)
    have hc : Continuous fun t : ℝ ↦
        flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a) -
          (B : Torus 3 → C3) a := hap.sub continuous_const
    have hcn : Continuous fun t : ℝ ↦
        ‖flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a) -
          (B : Torus 3 → C3) a‖ ^ 2 := (continuous_pow 2).comp hc.norm
    have htend := hcn.tendsto (0 : ℝ)
    have hzero : ‖flowFDerivC h P angularSpeed axialSpeed tau 0 a ((B : Torus 3 → C3) a) -
        (B : Torus 3 → C3) a‖ ^ 2 = 0 := by
      rw [flowFDerivC_zero]
      simp
    rwa [hzero] at htend
  have hmain := tendsto_integral_filter_of_dominated_convergence _ hmeas hdom hbound hlim
  simpa using hmain

/-! ## Strong continuity -/

/-- The Cauchy transport differs from the plain substitution by the pointwise action of
`DΦ_t - id`, read after the measure-preserving change of variables `x = Φ_t(a)`.  This is the
analogue, for the transport minus the substitution, of the identity in
the strong-continuity paragraph of the proof of `cor:ideal-growth`. -/
theorem flowCompL2_neg_idealTransport_sub_coe_ae (htau : 0 ≤ tau) (t : ℝ) (B : LiteralC3L2) :
    (flowCompL2 h P angularSpeed axialSpeed tau (-t)
        (idealTransport h P angularSpeed axialSpeed tau t B -
          flowCompL2 h P angularSpeed axialSpeed tau t B) : Torus 3 → C3) =ᵐ[volume]
      fun a ↦ flowFDerivC h P angularSpeed axialSpeed tau t a ((B : Torus 3 → C3) a) -
        (B : Torus 3 → C3) a := by
  have h1 := flowCompL2_neg_coe_ae h P angularSpeed axialSpeed tau t
    (idealTransport h P angularSpeed axialSpeed tau t B -
      flowCompL2 h P angularSpeed axialSpeed tau t B)
  have h2 := (quasiMeasurePreserving_literalFlow h P angularSpeed axialSpeed tau t).ae
    (Lp.coeFn_sub (idealTransport h P angularSpeed axialSpeed tau t B)
      (flowCompL2 h P angularSpeed axialSpeed tau t B))
  have h3 := (quasiMeasurePreserving_literalFlow h P angularSpeed axialSpeed tau t).ae
    (idealTransport_coe_ae h P angularSpeed axialSpeed tau htau t B)
  have h4 := (quasiMeasurePreserving_literalFlow h P angularSpeed axialSpeed tau t).ae
    (flowCompL2_coe_ae h P angularSpeed axialSpeed tau t B)
  filter_upwards [h1, h2, h3, h4] with a ha hsub hT hC
  rw [ha, hsub]
  simp only [Pi.sub_apply]
  rw [hT, hC, idealSymbol_eq, literalFlow_neg_literalFlow]

/-- The squared distance between the Cauchy transport and the plain substitution, as the
integral `∫ |DΦ_t(a)B(a) - B(a)|² da`. -/
theorem sq_norm_idealTransport_sub_flowCompL2 (htau : 0 ≤ tau) (t : ℝ) (B : LiteralC3L2) :
    ‖idealTransport h P angularSpeed axialSpeed tau t B -
        flowCompL2 h P angularSpeed axialSpeed tau t B‖ ^ 2 =
      ∫ a : Torus 3, ‖flowFDerivC h P angularSpeed axialSpeed tau t a
        ((B : Torus 3 → C3) a) - (B : Torus 3 → C3) a‖ ^ 2 := by
  rw [← norm_flowCompL2_apply h P angularSpeed axialSpeed tau (-t)
      (idealTransport h P angularSpeed axialSpeed tau t B -
        flowCompL2 h P angularSpeed axialSpeed tau t B),
    sq_norm_literalC3L2_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [flowCompL2_neg_idealTransport_sub_coe_ae h P angularSpeed axialSpeed tau htau t B]
    with a ha
  rw [ha]

/-- The Cauchy transport and the plain substitution agree in the limit `t → 0`. -/
theorem tendsto_norm_idealTransport_sub_flowCompL2 (htau : 0 ≤ tau) (B : LiteralC3L2) :
    Tendsto (fun t : ℝ ↦ ‖idealTransport h P angularSpeed axialSpeed tau t B -
      flowCompL2 h P angularSpeed axialSpeed tau t B‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ ↦ ‖idealTransport h P angularSpeed axialSpeed tau t B -
      flowCompL2 h P angularSpeed axialSpeed tau t B‖ ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
    refine (tendsto_integral_norm_flowFDerivC_apply_sub h P angularSpeed axialSpeed tau htau
      B).congr fun t ↦ ?_
    exact (sq_norm_idealTransport_sub_flowCompL2 h P angularSpeed axialSpeed tau htau t B).symm
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  rw [Real.sqrt_zero] at hroot
  refine hroot.congr fun t ↦ ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- **Strong continuity at the origin**: `𝒯₀(t)B → B` in `L²` as `t → 0` (the strong-continuity
paragraph of the proof of `cor:ideal-growth`). -/
theorem tendsto_idealTransport_zero (htau : 0 ≤ tau) (B : LiteralC3L2) :
    Tendsto (fun t : ℝ ↦ idealTransport h P angularSpeed axialSpeed tau t B) (𝓝 (0 : ℝ))
      (𝓝 B) := by
  have hsub : Tendsto (fun t : ℝ ↦ idealTransport h P angularSpeed axialSpeed tau t B -
      flowCompL2 h P angularSpeed axialSpeed tau t B) (𝓝 (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_norm_idealTransport_sub_flowCompL2 h P angularSpeed axialSpeed tau htau B
  have hcomp : Tendsto (fun t : ℝ ↦ flowCompL2 h P angularSpeed axialSpeed tau t B) (𝓝 (0 : ℝ))
      (𝓝 B) := by
    have hc := (continuous_flowCompL2_apply h P angularSpeed axialSpeed tau B).tendsto (0 : ℝ)
    rwa [flowCompL2_zero] at hc
  have hsum := hsub.add hcomp
  rw [zero_add] at hsum
  refine hsum.congr fun t ↦ ?_
  abel

/-- **The `strongly_continuous` clause of `IsIdealInductionGroup`, on the whole of
`LiteralC3L2`** (the strong-continuity paragraph of the proof of `cor:ideal-growth`).
Continuity at a general time follows from continuity at the origin and the group law
`𝒯₀(t) = 𝒯₀(t - t₀) 𝒯₀(t₀)`. -/
theorem strongly_continuous_idealTransport (htau : 0 ≤ tau) (B : LiteralC3L2) :
    Continuous fun t : ℝ ↦ idealTransport h P angularSpeed axialSpeed tau t B := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  have hzero := tendsto_idealTransport_zero h P angularSpeed axialSpeed tau htau
    (idealTransport h P angularSpeed axialSpeed tau t₀ B)
  have hshift : Tendsto (fun t : ℝ ↦ t - t₀) (𝓝 t₀) (𝓝 (0 : ℝ)) := by
    have hc : Continuous fun t : ℝ ↦ t - t₀ := continuous_id.sub continuous_const
    simpa using hc.tendsto t₀
  have hcomp := hzero.comp hshift
  refine hcomp.congr fun t ↦ ?_
  change idealTransport h P angularSpeed axialSpeed tau (t - t₀)
      (idealTransport h P angularSpeed axialSpeed tau t₀ B) =
    idealTransport h P angularSpeed axialSpeed tau t B
  rw [← ContinuousLinearMap.comp_apply,
    ← idealTransport_add h P angularSpeed axialSpeed tau htau (t - t₀) t₀, sub_add_cancel]

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
