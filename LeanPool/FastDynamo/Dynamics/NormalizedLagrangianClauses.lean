/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.MainLagrangianClauses
public import LeanPool.FastDynamo.Dynamics.IdealWeakFormRescaling

/-!
# The dynamical clauses for the normalised velocity

Remark 1.6 of the paper (the remark after `rem:scope-intro`): for `uNorm = u / M`,
"the particle flow and ideal induction group for `uNorm` are the corresponding objects for `u`
evaluated at time `t / M`.  This preserves the ideal growth rate and the vanishing of
topological entropy."  This module proves that statement for the predicates of
`FastDynamo/Dynamics/ParticleFlow.lean`, for a general factor `c > 0` in place of `M⁻¹`, and
reads it at the constructed velocity.

## Contents

* `IsParticleFlow.timeRescale`, `IsIdealInductionGroup.timeRescale`: if `Φ` is the particle
  flow of `v` and `𝒯₀` the ideal induction group of `v` (the unique solution group of the ideal
  induction equation, given by the Cauchy formula with the derivative `DΦ`), then `t ↦ Φ_{ct}`
  is the particle flow of `c v` and, for `c ≠ 0`, `t ↦ 𝒯₀(ct)` the ideal induction group of
  `c v`, with the derivative `t ↦ DΦ_{ct}`.
* `MainTheoremDynamicalClauses.smul`, `MainLagrangianClauses.smul`: the dynamical clauses of
  `thm:main` and the bundle of `prop:particle-flow` and `cor:ideal-growth` survive `v ↦ c v`
  for `c > 0`; in the bundle the constant `C_L` becomes `(1 + c) C_L`.  The entropy clause is
  the same family of time maps re-indexed, and the rates are multiplied by `c`
  (`tendsto_inv_mul_comp_const_mul`), so they stay zero.
* `normalizedLiteralVelocity`: the normalised velocity `uNorm` on the literal three-torus, the
  axially independent extension of `M⁻¹` times the torus-side representative of
  `mainVelocity`; it represents `normalizedVelocity mainVelocity` almost everywhere
  (`transverseW1InfValue_normalizedVelocity_ae`) and equals `M⁻¹ • mainLiteralVelocity`.
* `isIdealInductionGroup_normalizedLiteralVelocity`: the flow and the ideal group of `uNorm` are
  `mainLiteralFlow` and `mainIdealGroup` at time `M⁻¹ t`; `normalizedLiteralFlow_unique`:
  that flow is the only particle flow of `uNorm`.
* `normalizedTheoremDynamical_holds`, `normalizedTheoremLagrangian_holds`: the two predicates
  at `uNorm`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter
open HorizontalMode

/-! ## Rates under time rescaling -/

/-- If `t⁻¹ f(t) → 0` as `t → ∞`, then `t⁻¹ f(c t) → 0` for every `c > 0`: the second
quotient is `c` times the first read at time `c t`. -/
theorem tendsto_inv_mul_comp_const_mul {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun t : ℝ ↦ t⁻¹ * f t) atTop (nhds 0)) :
    Tendsto (fun t : ℝ ↦ t⁻¹ * f (c * t)) atTop (nhds 0) := by
  have hcomp := (h.comp (tendsto_id.const_mul_atTop hc)).const_mul c
  rw [mul_zero] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply, id]
  field_simp

/-! ## The flow and the ideal group under time rescaling -/

/-- **The particle flow of `c v` is the particle flow of `v` at time `c t`.**  A lift `γ` of
the trajectory through `x` gives the lift `t ↦ γ(c t)`, whose derivative is
`c v(Φ_{ct}(x))` by the chain rule. -/
theorem IsParticleFlow.timeRescale {v : Torus 3 → R3} {Φ : ℝ → Torus 3 → Torus 3}
    (h : IsParticleFlow v Φ) (c : ℝ) : IsParticleFlow (c • v) (fun t ↦ Φ (c * t)) where
  initial x := by
    rw [mul_zero]
    exact h.initial x
  ode x := by
    obtain ⟨γ, hγ, hder⟩ := h.ode x
    refine ⟨fun t ↦ γ (c * t), fun t ↦ hγ (c * t), fun t ↦ ?_⟩
    have hcomp := (hder (c * t)).scomp t ((hasDerivAt_id t).const_mul c)
    rw [mul_one] at hcomp
    exact hcomp

/-- **The ideal induction group of `c v` is that of `v` at time `c t`** (`c ≠ 0`), with the
flow `t ↦ Φ_{ct}` and the derivative `t ↦ DΦ_{ct}`.  The clauses of `IsIdealInductionGroup`
other than the particle flow and the two solution-group clauses are statements at a single
time, or the group law and strong continuity, which are preserved by the linear
reparametrisation `t ↦ c t`.  The weak form is preserved by `IsIdealSolutionGroup.timeRescale`
(`FastDynamo/Dynamics/IdealWeakFormRescaling.lean`); for uniqueness, a solution group `𝒯'` of
`c v` gives the solution group `t ↦ 𝒯'(c⁻¹ t)` of `c⁻¹ (c v) = v`, which is `𝒯₀`, so
`𝒯'(t) = 𝒯₀(c t)`; the hypothesis `c ≠ 0` is used only in this step. -/
theorem IsIdealInductionGroup.timeRescale {v : Torus 3 → R3} {Φ : ℝ → Torus 3 → Torus 3}
    {DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3)}
    {T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace}
    (h : IsIdealInductionGroup v Φ DΦ T) (c : ℝ) (hc : c ≠ 0) :
    IsIdealInductionGroup (c • v) (fun t ↦ Φ (c * t)) (fun t ↦ DΦ (c * t))
      (fun t ↦ T (c * t)) where
  particleFlow := h.particleFlow.timeRescale c
  hasFDerivAt t := h.hasFDerivAt (c * t)
  measurePreserving t := h.measurePreserving (c * t)
  group_zero := by
    show T (c * 0) = _
    rw [mul_zero]
    exact h.group_zero
  group_add s t := by
    show T (c * (s + t)) = (T (c * s)).comp (T (c * t))
    rw [mul_add]
    exact h.group_add _ _
  strongly_continuous B :=
    (h.strongly_continuous B).comp (continuous_const.mul continuous_id)
  cauchy t B := h.cauchy (c * t) B
  solutionGroup := h.solutionGroup.timeRescale c
  unique T' hT' := by
    have hback := hT'.timeRescale c⁻¹
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hback
    funext t
    have ht := congrFun (h.unique _ hback) (c * t)
    simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at ht
    exact ht

/-- **The dynamical clauses of `thm:main` survive `v ↦ c v` for `c > 0`**: the time maps of
the rescaled flow are time maps of the original flow, so they are continuous and have zero
topological entropy, and the operator-norm rate of `t ↦ 𝒯₀(c t)` is `c` times that of `𝒯₀`,
hence zero. -/
theorem MainTheoremDynamicalClauses.smul {v : Torus 3 → R3} {c : ℝ} (hc : 0 < c)
    (h : MainTheoremDynamicalClauses v) : MainTheoremDynamicalClauses (c • v) := by
  obtain ⟨Φ, DΦ, T, hgroup, hcont, hent, hrate⟩ := h
  exact ⟨fun t ↦ Φ (c * t), fun t ↦ DΦ (c * t), fun t ↦ T (c * t),
    hgroup.timeRescale c hc.ne',
    fun t ↦ hcont (c * t), fun t ↦ hent (c * t),
    tendsto_inv_mul_comp_const_mul (f := fun t ↦ Real.log ‖T t‖) hc hrate⟩

/-- The linear factor `C_L (1 + |c t|)` at time `c t` is at most `(1 + c) C_L (1 + |t|)`. -/
theorem mul_one_add_abs_mul_le {CL c : ℝ} (hCL : 0 ≤ CL) (hc : 0 < c) (t : ℝ) :
    CL * (1 + |c * t|) ≤ (1 + c) * CL * (1 + |t|) := by
  rw [abs_mul, abs_of_pos hc]
  nlinarith [abs_nonneg t, mul_nonneg hCL (abs_nonneg t), mul_nonneg hCL hc.le]

/-- **`prop:particle-flow` and `cor:ideal-growth` survive `v ↦ c v` for `c > 0`**, with the
flow `t ↦ Φ_{ct}`, the ideal group `t ↦ 𝒯₀(ct)` and the constant `(1 + c) C_L` in place of
`C_L`: the linear bounds at time `c t` are linear in `t`
(`mul_one_add_abs_mul_le`), and the per-datum rate is multiplied by `c`. -/
theorem MainLagrangianClauses.smul {v : Torus 3 → R3} {c : ℝ} (hc : 0 < c)
    (h : MainLagrangianClauses v) : MainLagrangianClauses (c • v) := by
  obtain ⟨Φ, CL, hCL, hflow, hinv, hlip, hent, DΦ, T, hgroup, hbounds, hrate⟩ := h
  have hCL0 : 0 ≤ CL := zero_le_one.trans hCL
  refine ⟨fun t ↦ Φ (c * t), (1 + c) * CL,
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right hc.le) hCL,
    hflow.timeRescale c, fun t x ↦ ?_, fun t ↦ ?_, fun t ↦ hent (c * t),
    fun t ↦ DΦ (c * t), fun t ↦ T (c * t), hgroup.timeRescale c hc.ne', fun t B ↦ ?_,
    fun B hB ↦ ?_⟩
  · change Φ (c * -t) (Φ (c * t) x) = x
    rw [mul_neg]
    exact hinv (c * t) x
  · obtain ⟨L₁, L₂, h₁, h₂, hsum⟩ := hlip (c * t)
    refine ⟨L₁, L₂, h₁, ?_, hsum.trans (mul_one_add_abs_mul_le hCL0 hc t)⟩
    change LipschitzWith L₂ (Φ (c * -t))
    rw [mul_neg]
    exact h₂
  · obtain ⟨hlow, hup⟩ := hbounds (c * t) B
    have hkey := mul_one_add_abs_mul_le hCL0 hc t
    have hpos : 0 < CL * (1 + |c * t|) :=
      mul_pos (zero_lt_one.trans_le hCL) (by positivity)
    refine ⟨(div_le_div_of_nonneg_left (norm_nonneg B) hpos hkey).trans hlow,
      hup.trans (mul_le_mul_of_nonneg_right hkey (norm_nonneg B))⟩
  · exact tendsto_inv_mul_comp_const_mul (f := fun t ↦ Real.log (‖T t B‖ / ‖B‖)) hc
      (hrate B hB)

/-! ## The normalised velocity on the literal three-torus -/

/-- **The normalised velocity `uNorm = M⁻¹ u` on the literal three-torus**: the axially
independent extension of `M⁻¹` times the torus-side representative of `mainVelocity`, with
`M⁻¹ = velocityNormalizer mainVelocity`.  It represents
`normalizedVelocity mainVelocity` (`transverseW1InfValue_normalizedVelocity_ae`) as
`mainLiteralVelocity` represents `mainVelocity`. -/
def normalizedLiteralVelocity : Torus 3 → R3 :=
  literalVelocity (velocityNormalizer mainVelocity • mainVelocityTorusRepresentative)

/-- The value of the normalised velocity is represented almost everywhere by `M⁻¹` times the
torus-side representative of `mainVelocity`. -/
theorem transverseW1InfValue_normalizedVelocity_ae :
    (transverseW1InfValue (normalizedVelocity mainVelocity) : TransverseTorus → R3)
      =ᵐ[transverseMeasure]
        velocityNormalizer mainVelocity • mainVelocityTorusRepresentative := by
  rw [normalizedVelocity, map_smul]
  filter_upwards [MeasureTheory.Lp.coeFn_smul (velocityNormalizer mainVelocity)
      (transverseW1InfValue mainVelocity), transverseW1InfValue_mainVelocity_ae] with x h₁ h₂
  rw [h₁, Pi.smul_apply, h₂, Pi.smul_apply]

/-- The literal velocity of `uNorm` is `M⁻¹` times that of `u`. -/
theorem normalizedLiteralVelocity_eq :
    normalizedLiteralVelocity = velocityNormalizer mainVelocity • mainLiteralVelocity :=
  rfl

/-- **The flow and the ideal group of `uNorm` are those of `u` at time `M⁻¹ t`**
(Remark 1.6): `t ↦ Φ_{M⁻¹t}` with `Φ = mainLiteralFlow`, its derivative, and
`t ↦ 𝒯₀(M⁻¹t)` with `𝒯₀ = mainIdealGroup` satisfy `IsIdealInductionGroup` for
`normalizedLiteralVelocity`; in particular `t ↦ Φ_{M⁻¹t}` is a particle flow of `uNorm` and
`t ↦ 𝒯₀(M⁻¹t)` the only solution group of the ideal induction equation of `uNorm`. -/
theorem isIdealInductionGroup_normalizedLiteralVelocity :
    IsIdealInductionGroup normalizedLiteralVelocity
      (fun t ↦ mainLiteralFlow (velocityNormalizer mainVelocity * t))
      (fun t ↦ ScaleFamily.TorusCellPlacement.flowFDeriv globalSeedInterface.smoothingWidth
        mainParameterChoice.placement globalSeedInterface.angularSpeed
        globalSeedInterface.axialSpeed mainParameterChoice.tau
        (velocityNormalizer mainVelocity * t))
      (fun t ↦ mainIdealGroup (velocityNormalizer mainVelocity * t)) :=
  (ScaleFamily.TorusCellPlacement.isIdealInductionGroup_idealGroup
    globalSeedInterface.smoothingWidth mainParameterChoice.placement
    globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed mainParameterChoice.tau
    mainParameterChoice.tau_nonneg).timeRescale (velocityNormalizer mainVelocity)
    (velocityNormalizer_pos mainVelocity).ne'

/-- **The particle flow of `uNorm` is unique**, so it is *the* flow of `u` at time `M⁻¹ t`: any
particle flow `Φ'` of `normalizedLiteralVelocity` is `t ↦ mainLiteralFlow (M⁻¹ t)`.  Run at
time `M t`, `Φ'` is a particle flow of `M (M⁻¹ u) = u` (`IsParticleFlow.timeRescale`), hence
`mainLiteralFlow` by `mainLiteralFlow_unique`. -/
theorem normalizedLiteralFlow_unique {Φ' : ℝ → Torus 3 → Torus 3}
    (h : IsParticleFlow normalizedLiteralVelocity Φ') :
    Φ' = fun t ↦ mainLiteralFlow (velocityNormalizer mainVelocity * t) := by
  have hc := (velocityNormalizer_pos mainVelocity).ne'
  have hv : (velocityNormalizer mainVelocity)⁻¹ • normalizedLiteralVelocity =
      mainLiteralVelocity := by
    rw [normalizedLiteralVelocity_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hflow := h.timeRescale (velocityNormalizer mainVelocity)⁻¹
  rw [hv] at hflow
  have huniq := mainLiteralFlow_unique hflow
  funext t
  have ht := congrFun huniq (velocityNormalizer mainVelocity * t)
  simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at ht
  exact ht

/-- **The dynamical clauses of `thm:main` for the normalised velocity**:
`h_top(ΦNorm_t) = 0` for every `t` and `lim_{t → ∞} t⁻¹ log ‖𝒯Norm₀(t)‖ = 0`, at
`normalizedLiteralVelocity`. -/
theorem normalizedTheoremDynamical_holds :
    MainTheoremDynamicalClauses normalizedLiteralVelocity :=
  mainTheoremDynamical_holds.smul (velocityNormalizer_pos mainVelocity)

/-- **`prop:particle-flow` and `cor:ideal-growth` for the normalised velocity**, with the
constant `(1 + M⁻¹) C_L`. -/
theorem normalizedTheoremLagrangian_holds :
    MainLagrangianClauses normalizedLiteralVelocity :=
  mainTheoremLagrangian_holds.smul (velocityNormalizer_pos mainVelocity)

end

end FastDynamo
