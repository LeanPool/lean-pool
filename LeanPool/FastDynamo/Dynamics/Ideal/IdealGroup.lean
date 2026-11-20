/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Ideal.WeakSolutionUniqueness
public import LeanPool.FastDynamo.Dynamics.Ideal.SolenoidalInvariance
public import LeanPool.FastDynamo.Dynamics.Ideal.StrongContinuity
public import LeanPool.FastDynamo.Dynamics.Flow.ParticleFlowProof

/-!
# The ideal induction group of the constructed velocity

This module assembles the last conjunct of `MainLagrangianClauses`
(`FastDynamo/Dynamics/ParticleFlow.lean`) for the velocity
`literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)`:
the ideal induction equation of `cor:ideal-growth` has a solution group on `L²_σ(T³; ℂ³)`,
it is the only one, and it obeys the two-sided per-datum bounds
`‖B‖/(C_L(1+|t|)) ≤ ‖𝒯₀(t)B‖ ≤ C_L(1+|t|)‖B‖` and the per-datum zero growth rate.  The paper
states the bounds and the rate inside `cor:ideal-growth`.  The group is constructed by the
Cauchy formula as in the proof of `cor:ideal-growth`; that it solves the equation in the weak
sense of `FastDynamo/Dynamics/IdealWeakForm.lean` is `isIdealSolutionGroup_idealGroup`
(`.../Ideal/WeakSolution.lean`), and that every solution group equals it is
`IsIdealSolutionGroup.eq_idealGroup` (`.../Ideal/WeakSolutionUniqueness.lean`).

Everything analytic is proved in the modules imported here; this module is bookkeeping of three
kinds.

1. **The structure `IsIdealInductionGroup`.**  Its nine fields are discharged one by one by
   `FastDynamo/Dynamics/Flow/ParticleFlowProof.lean` (the ODE), `.../Flow/FlowDerivative.lean`
   (the everywhere-defined differential of the lift, which gives the `∀ᵐ` field from a `∀`),
   `.../Flow/MeasurePreserving.lean` (measure preservation),
   `.../Ideal/SolenoidalInvariance.lean` (the corestricted group `idealGroup` and its group law),
   `.../Ideal/StrongContinuity.lean` (continuity in `t`, transported to the subspace by
   `continuous_induced_rng`), `.../Ideal/CauchyOperator.lean` (the Cauchy formula
   `eq:ideal-cauchy-formula`), `.../Ideal/WeakSolution.lean` (the weak solution property) and
   `.../Ideal/WeakSolutionUniqueness.lean` (uniqueness of the solution group).

2. **One constant for two clauses.**  `MainLagrangianClauses` quantifies a *single* `C_L ≥ 1`
   that must serve both the Lipschitz clause `eq:linear-flow-lipschitz`, where
   `flowCL … = 4(1 + slope)` works, and the per-datum bounds of `cor:ideal-growth`,
   where the operator bound is `flowComplexDerivativeBound … t = 24(1 + |t| · slope)`.  The
   module therefore fixes
   `dynamicalCL … = 6 * flowCL … = 24(1 + slope)`, which dominates both:
   `flowComplexDerivativeBound … t ≤ dynamicalCL … (1 + |t|)` and
   `flowCL … ≤ dynamicalCL …`.  The Lipschitz clause is restated at the larger constant
   by monotonicity, so a consumer never has to mix the two.

3. **The rate.**  `t⁻¹ log(‖𝒯₀(t)B‖ / ‖B‖) → 0` is the squeeze between `± t⁻¹ log(C_L(1 + t))`
   of the last step of the proof of `cor:ideal-growth`, `tendsto_inv_mul_log_of_two_sided` of
   `FastDynamo/Analysis/LogLinearGrowth.lean`, applied to the two-sided bounds.

The delivered bundle is `existsIdealGroupClauses`, whose statement is character-for-character the
last conjunct of `MainLagrangianClauses` at `CL := dynamicalCL …`; the assembly module has
only to supply the four earlier clauses and pick the same constant.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## The single constant of `MainLagrangianClauses` -/

/-- **The constant `C_L`** (`prop:particle-flow` and `cor:ideal-growth`; the paper keeps it
out of `thm:main`), in the one
form that serves every clause at once:

```
  dynamicalCL … = 6 * flowCL … = 24 * (1 + flowLipschitzSlope …) .
```

The Lipschitz clause `eq:linear-flow-lipschitz` holds already with
`flowCL … = 4(1 + slope)` of `FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`, and the ideal
per-datum bounds of `cor:ideal-growth` need
`flowComplexDerivativeBound … t = 24(1 + |t| · slope)` divided by `1 + |t|`; the factor `6` is
exactly what lets one constant dominate both (`flowCL_le_dynamicalCL` and
`flowComplexDerivativeBound_le_dynamicalCL_mul` below). -/
def dynamicalCL : ℝ := 6 * flowCL h P angularSpeed axialSpeed tau

/-- **`C_L ≥ 1`**, the first clause of `MainLagrangianClauses` (`prop:particle-flow`). -/
theorem one_le_dynamicalCL (htau : 0 ≤ tau) :
    1 ≤ dynamicalCL h P angularSpeed axialSpeed tau := by
  have hCL := one_le_flowCL h P angularSpeed axialSpeed tau htau
  rw [dynamicalCL]
  linarith

/-- The constant is positive. -/
theorem dynamicalCL_pos (htau : 0 ≤ tau) :
    0 < dynamicalCL h P angularSpeed axialSpeed tau :=
  lt_of_lt_of_le zero_lt_one (one_le_dynamicalCL h P angularSpeed axialSpeed tau htau)

/-- The constant `dynamicalCL` dominates `flowCL`, so every Lipschitz statement proved with
`flowCL` survives the enlargement. -/
theorem flowCL_le_dynamicalCL (htau : 0 ≤ tau) :
    flowCL h P angularSpeed axialSpeed tau ≤
      dynamicalCL h P angularSpeed axialSpeed tau := by
  have hpos := flowCL_pos h P angularSpeed axialSpeed tau htau
  rw [dynamicalCL]
  linarith

/-- **The operator bound has the shape the per-datum bounds ask for**: the uniform bound
`flowComplexDerivativeBound` on the complexified differential
(`FastDynamo/Dynamics/Flow/FlowDerivative.lean`) is at most `C_L (1 + |t|)`, because
`24(1 + |t| s) ≤ 24(1 + s)(1 + |t|)` for `s, |t| ≥ 0` (the last step of the proof of
`cor:ideal-growth`). -/
theorem flowComplexDerivativeBound_le_dynamicalCL_mul (htau : 0 ≤ tau) (t : ℝ) :
    flowComplexDerivativeBound h P angularSpeed axialSpeed tau t ≤
      dynamicalCL h P angularSpeed axialSpeed tau * (1 + |t|) := by
  have hslope : 0 ≤ flowLipschitzSlope h P angularSpeed axialSpeed tau :=
    flowLipschitzSlope_nonneg h P angularSpeed axialSpeed tau htau
  rw [flowComplexDerivativeBound_eq, dynamicalCL, flowCL]
  nlinarith [abs_nonneg t, hslope]

/-- **The Lipschitz clause of `MainLagrangianClauses` at the enlarged constant**
(`eq:linear-flow-lipschitz`): the statement `exists_lipschitzWith_literalFlow` of
`FastDynamo/Dynamics/Flow/ParticleFlowProof.lean`, weakened from `flowCL` to
`dynamicalCL` so that the whole predicate can be instantiated at a single `C_L`. -/
theorem exists_lipschitzWith_literalFlow_dynamicalCL (htau : 0 ≤ tau) :
    ∀ t : ℝ, ∃ L₁ L₂ : NNReal,
      LipschitzWith L₁ (literalFlow h P angularSpeed axialSpeed tau t) ∧
        LipschitzWith L₂ (literalFlow h P angularSpeed axialSpeed tau (-t)) ∧
          (L₁ : ℝ) + (L₂ : ℝ) ≤ dynamicalCL h P angularSpeed axialSpeed tau * (1 + |t|) := by
  intro t
  obtain ⟨L₁, L₂, h₁, h₂, hsum⟩ :=
    exists_lipschitzWith_literalFlow h P angularSpeed axialSpeed tau htau t
  refine ⟨L₁, L₂, h₁, h₂, hsum.trans ?_⟩
  have habs : (0 : ℝ) ≤ 1 + |t| := by positivity
  have hmono := flowCL_le_dynamicalCL h P angularSpeed axialSpeed tau htau
  nlinarith

/-! ## The ideal induction group -/

/-- **The ideal induction group of the constructed velocity** (`cor:ideal-growth`):
the corestriction `idealGroup` of the Cauchy transport to `L²_σ(T³; ℂ³)` is the solution group
of the ideal induction equation of `literalVelocity (parameterizedFullGlobalRealTorusSource …)`,
with particle flow `literalFlow …` and differential `flowFDeriv …`.

The nine fields, in order:

* `particleFlow` — `isParticleFlow_literalFlow` (`.../Flow/ParticleFlowProof.lean`,
  `prop:particle-flow`, `eq:explicit-particle-flow`);
* `hasFDerivAt` — `hasFDerivAt_literalFlowLift` (`.../Flow/FlowDerivative.lean`) holds at
  **every** point of the cover, so the almost-everywhere clause (Rademacher, in the proof of
  `cor:ideal-growth`) is
  `Filter.Eventually.of_forall` of it, with the lift `literalFlowLift … t` supplied by
  `isLiteralTorusLift_literalFlow` (`.../Flow/TorusFlow.lean`);
* `measurePreserving` — `measurePreserving_literalFlow` (`.../Flow/MeasurePreserving.lean`,
  `det DΦ_t = 1`);
* `group_zero`, `group_add` — `idealGroup_zero`, `idealGroup_add`
  (`.../Ideal/SolenoidalInvariance.lean`);
* `strongly_continuous` — `strongly_continuous_idealTransport`
  (`.../Ideal/StrongContinuity.lean`) read through `idealGroup_coe` and lifted to
  the subspace by `continuous_induced_rng`, the topology of a submodule being the induced one;
* `cauchy` — `idealTransport_cauchy` (`.../Ideal/CauchyOperator.lean`) applied to the coerced
  datum, which *is* the field because `idealGroup_coe` is definitional
  (`eq:ideal-cauchy-formula`);
* `solutionGroup` — `isIdealSolutionGroup_idealGroup` (`.../Ideal/WeakSolution.lean`): every
  orbit is a weak solution, by the Cauchy formula differentiated along the flow;
* `unique` — `IsIdealSolutionGroup.eq_idealGroup` (`.../Ideal/WeakSolutionUniqueness.lean`):
  every solution group is `idealGroup`, by pulling the weak identity back along the flow and
  Grönwall's inequality.

The group laws, strong continuity, the Cauchy formula, the weak form and uniqueness are the
facts the paper establishes in the proof of `cor:ideal-growth`. -/
theorem isIdealInductionGroup_idealGroup (htau : 0 ≤ tau) :
    IsIdealInductionGroup
      (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
      (literalFlow h P angularSpeed axialSpeed tau)
      (flowFDeriv h P angularSpeed axialSpeed tau)
      (fun t : ℝ ↦ idealGroup h P angularSpeed axialSpeed tau t) where
  particleFlow := isParticleFlow_literalFlow h P angularSpeed axialSpeed tau
  hasFDerivAt := fun t ↦
    ⟨literalFlowLift h P angularSpeed axialSpeed tau t,
      isLiteralTorusLift_literalFlow h P angularSpeed axialSpeed tau t,
      Filter.Eventually.of_forall (hasFDerivAt_literalFlowLift h P angularSpeed axialSpeed tau t)⟩
  measurePreserving := fun t ↦ measurePreserving_literalFlow h P angularSpeed axialSpeed tau t
  group_zero := idealGroup_zero h P angularSpeed axialSpeed tau htau
  group_add := idealGroup_add h P angularSpeed axialSpeed tau htau
  strongly_continuous := by
    intro B
    refine continuous_induced_rng.2 ?_
    have hmain := strongly_continuous_idealTransport h P angularSpeed axialSpeed tau htau
      (B : LiteralC3L2)
    exact hmain.congr fun t ↦ (idealGroup_coe h P angularSpeed axialSpeed tau htau t B).symm
  cauchy := fun t B ↦ by
    rw [idealGroup_coe h P angularSpeed axialSpeed tau htau t B]
    exact idealTransport_cauchy h P angularSpeed axialSpeed tau htau t (B : LiteralC3L2)
  solutionGroup := isIdealSolutionGroup_idealGroup h P angularSpeed axialSpeed tau htau
  unique := fun _ hT' ↦ IsIdealSolutionGroup.eq_idealGroup h P angularSpeed axialSpeed tau htau hT'

/-- **The two-sided per-datum bounds of `cor:ideal-growth`** (proved in the last step of its
proof), in the shape `MainLagrangianClauses` states them, at `C_L := dynamicalCL …`:

```
  ‖B‖ / (C_L(1 + |t|)) ≤ ‖𝒯₀(t)B‖ ≤ C_L(1 + |t|) ‖B‖ .
```

The upper bound is `norm_idealGroup_apply_le`; the lower bound is
`norm_le_mul_norm_idealGroup` (both `.../Ideal/SolenoidalInvariance.lean`), read at `t` instead
of `-t` through `flowComplexDerivativeBound_neg` (the bound is even in the time).  Both are then
weakened to the single constant by `flowComplexDerivativeBound_le_dynamicalCL_mul`. -/
theorem norm_idealGroup_bounds (htau : 0 ≤ tau) (t : ℝ) (B : literalSolenoidalSubspace) :
    ‖B‖ / (dynamicalCL h P angularSpeed axialSpeed tau * (1 + |t|)) ≤
        ‖idealGroup h P angularSpeed axialSpeed tau t B‖ ∧
      ‖idealGroup h P angularSpeed axialSpeed tau t B‖ ≤
        dynamicalCL h P angularSpeed axialSpeed tau * (1 + |t|) * ‖B‖ := by
  have hCL := flowComplexDerivativeBound_le_dynamicalCL_mul h P angularSpeed axialSpeed tau
    htau t
  have hden : (0 : ℝ) < dynamicalCL h P angularSpeed axialSpeed tau * (1 + |t|) := by
    have hpos := dynamicalCL_pos h P angularSpeed axialSpeed tau htau
    have habs : (0 : ℝ) < 1 + |t| := by positivity
    positivity
  refine ⟨?_, ?_⟩
  · have hlow := norm_le_mul_norm_idealGroup h P angularSpeed axialSpeed tau htau t B
    rw [flowComplexDerivativeBound_neg] at hlow
    rw [div_le_iff₀ hden]
    nlinarith [norm_nonneg (idealGroup h P angularSpeed axialSpeed tau t B)]
  · have hup := norm_idealGroup_apply_le h P angularSpeed axialSpeed tau htau t B
    nlinarith [norm_nonneg B]

/-- **Every non-zero ideal solution has exponential growth rate zero** (the last sentence of
`cor:ideal-growth`): the two-sided bounds trap `‖𝒯₀(t)B‖ / ‖B‖` between `1/(C_L(1 + t))` and
`C_L(1 + t)` for `t > 0`, and `tendsto_inv_mul_log_of_two_sided` squeezes the rate to `0`. -/
theorem tendsto_inv_mul_log_norm_idealGroup (htau : 0 ≤ tau) (B : literalSolenoidalSubspace)
    (hB : B ≠ 0) :
    Filter.Tendsto
      (fun t : ℝ ↦ t⁻¹ * Real.log (‖idealGroup h P angularSpeed axialSpeed tau t B‖ / ‖B‖))
      Filter.atTop (nhds (0 : ℝ)) := by
  have hCL := dynamicalCL_pos h P angularSpeed axialSpeed tau htau
  have hnB : (0 : ℝ) < ‖B‖ := norm_pos_iff.2 hB
  refine tendsto_inv_mul_log_of_two_sided hCL (fun t ht ↦ ?_) fun t ht ↦ ?_
  · have hden : (0 : ℝ) < dynamicalCL h P angularSpeed axialSpeed tau * (1 + t) := by
      positivity
    have hlow := (norm_idealGroup_bounds h P angularSpeed axialSpeed tau htau t B).1
    rw [abs_of_nonneg ht.le, div_le_iff₀ hden] at hlow
    rw [div_le_div_iff₀ hden hnB, one_mul]
    linarith
  · have hup := (norm_idealGroup_bounds h P angularSpeed axialSpeed tau htau t B).2
    rw [abs_of_nonneg ht.le] at hup
    rw [div_le_iff₀ hnB]
    exact hup

/-- **The last conjunct of `MainLagrangianClauses`, delivered** (`cor:ideal-growth`, whose
group is the `𝒯₀` fixed in §1.2 before `thm:main`): at the witnesses
`DΦ := flowFDeriv …` and
`T := idealGroup … htau`, the ideal induction group exists (as the unique solution group),
obeys the two-sided bounds with
`C_L := dynamicalCL …` and has vanishing per-datum growth rate.

This is the statement the assembly module plugs into `MainLagrangianClauses` after supplying the
flow clauses (`isParticleFlow_literalFlow`, `forall_literalFlow_neg_literalFlow` and
`exists_lipschitzWith_literalFlow`, the last weakened to this constant by
`exists_lipschitzWith_literalFlow_dynamicalCL`) and the entropy clause. -/
theorem existsIdealGroupClauses (htau : 0 ≤ tau) :
    ∃ (DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3))
      (T : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace),
      IsIdealInductionGroup
        (literalVelocity (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau))
        (literalFlow h P angularSpeed axialSpeed tau) DΦ T ∧
      (∀ (t : ℝ) (B : literalSolenoidalSubspace),
        ‖B‖ / (dynamicalCL h P angularSpeed axialSpeed tau * (1 + |t|)) ≤ ‖T t B‖ ∧
          ‖T t B‖ ≤ dynamicalCL h P angularSpeed axialSpeed tau * (1 + |t|) * ‖B‖) ∧
      (∀ B : literalSolenoidalSubspace, B ≠ 0 →
        Filter.Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log (‖T t B‖ / ‖B‖))
          Filter.atTop (nhds (0 : ℝ))) :=
  ⟨flowFDeriv h P angularSpeed axialSpeed tau,
    fun t : ℝ ↦ idealGroup h P angularSpeed axialSpeed tau t,
    isIdealInductionGroup_idealGroup h P angularSpeed axialSpeed tau htau,
    norm_idealGroup_bounds h P angularSpeed axialSpeed tau htau,
    tendsto_inv_mul_log_norm_idealGroup h P angularSpeed axialSpeed tau htau⟩

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
