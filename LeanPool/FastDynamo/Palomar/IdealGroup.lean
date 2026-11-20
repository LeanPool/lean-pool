/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.IdealSymbol

/-!
# The ideal solution group in the terms of the Challenge statement

The library's ideal induction group of the theorem's velocity is `mainIdealGroup`, a group of
operators on its literal solenoidal subspace `literalSolenoidalSubspace`, which is the Challenge's
`L2σ` (`L2σ_eq_literalSolenoidalSubspace`).  Conjugation by the identification
`literalSolenoidalEquivL2σ` transports it to a group `challengeIdealGroup` of operators on `L2σ`
with the same operator norms.

## Contents

* `exists_isIdealInductionGroup_mainIdealGroup` — `mainIdealGroup` is the group of the library's
  bundle `IsIdealInductionGroup`, and its operator norm grows subexponentially.
* `challengeIdealGroup` — the transported group, with `coe_challengeIdealGroup_apply`.
* `challengeIdealGroup_zero`, `challengeIdealGroup_add`, `continuous_challengeIdealGroup_apply` —
  group laws and strong continuity.
* `tendsto_inv_mul_log_norm_challengeIdealGroup` — **I3**: `t⁻¹ log ‖T t‖ → 0`.
* `mFourierCoeff_challengeIdealGroup_sub`, `isIdealGroup_challengeIdealGroup` — **I1**: the
  orbits solve the Challenge's integrated equation
  `B̂ᵢ(t)(m) − B̂ᵢ(s)(m) = ∫ₛᵗ inductionRHS u 0 B(τ) m i dτ`.  The library's weak form, tested with
  the character `e_m eᵢ`, gives this identity from `0` to `s` with the advective right-hand side
  `((B·∇)u)^ᵢ(m) − 2πi ∑ⱼ mⱼ (uⱼBᵢ)^(m)` (`literalFourierCoeff_idealGroup_sub`); on `L²_σ` that
  right-hand side is `inductionRHS u 0` (`mFourierCoeff_literalStretchL2_sub_eq_inductionRHS`),
  which is continuous along orbits.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus Filter Topology HorizontalMode

/-- **The library's ideal group is the group of its ideal induction bundle.**  The ideal group
`mainIdealGroup` of the theorem's velocity is, together with a flow and its derivative, an
`IsIdealInductionGroup`, and `t⁻¹ log ‖mainIdealGroup t‖ → 0`. -/
theorem exists_isIdealInductionGroup_mainIdealGroup :
    ∃ (Φ : ℝ → Torus 3 → Torus 3) (DΦ : ℝ → Torus 3 → (R3 →L[ℝ] R3)),
      IsIdealInductionGroup mainLiteralVelocity Φ DΦ mainIdealGroup ∧
        Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log ‖mainIdealGroup t‖) atTop (𝓝 0) := by
  obtain ⟨Φ, DΦ, T, hT, hrate⟩ := hasVanishingIdealOperatorGrowthRate_mainLiteralVelocity
  have hT0 : mainIdealGroup = T := hT.unique _ isIdealSolutionGroup_mainIdealGroup
  subst hT0
  exact ⟨Φ, DΦ, hT, hrate⟩

/-- Every orbit of the library's ideal group is continuous. -/
theorem continuous_mainIdealGroup_apply_subspace (B : literalSolenoidalSubspace) :
    Continuous fun t : ℝ ↦ mainIdealGroup t B := by
  obtain ⟨Φ, DΦ, hT, -⟩ := exists_isIdealInductionGroup_mainIdealGroup
  exact hT.strongly_continuous B

/-- **The ideal group on the Challenge's `L²_σ`**: the library's `mainIdealGroup`, conjugated by
the identification `literalSolenoidalEquivL2σ` of its state space with `L2σ`. -/
def challengeIdealGroup (t : ℝ) : L2σ →L[ℂ] L2σ :=
  conjOp literalSolenoidalEquivL2σ (mainIdealGroup t)

/-- The transported group acts on the underlying fields as the library's group. -/
@[simp] theorem coe_challengeIdealGroup_apply (t : ℝ) (B : L2σ) :
    ((challengeIdealGroup t B : L2σ) : L2) =
      ((mainIdealGroup t (literalSolenoidalEquivL2σ.symm B) : literalSolenoidalSubspace) :
        LiteralC3L2) :=
  rfl

/-- `T 0 = id`. -/
theorem challengeIdealGroup_zero : challengeIdealGroup 0 = ContinuousLinearMap.id ℂ L2σ := by
  obtain ⟨Φ, DΦ, hT, -⟩ := exists_isIdealInductionGroup_mainIdealGroup
  rw [challengeIdealGroup, hT.group_zero, conjOp_id]

/-- `T (s + t) = T s ∘ T t`. -/
theorem challengeIdealGroup_add (s t : ℝ) :
    challengeIdealGroup (s + t) = (challengeIdealGroup s).comp (challengeIdealGroup t) := by
  obtain ⟨Φ, DΦ, hT, -⟩ := exists_isIdealInductionGroup_mainIdealGroup
  rw [challengeIdealGroup, hT.group_add, conjOp_comp]
  rfl

/-- Every orbit of the transported group is continuous. -/
theorem continuous_challengeIdealGroup_apply (B : L2σ) :
    Continuous fun t : ℝ ↦ challengeIdealGroup t B :=
  literalSolenoidalEquivL2σ.continuous.comp
    (continuous_mainIdealGroup_apply_subspace (literalSolenoidalEquivL2σ.symm B))

/-- The operator norms of the transported group are those of the library's group. -/
theorem norm_challengeIdealGroup (t : ℝ) : ‖challengeIdealGroup t‖ = ‖mainIdealGroup t‖ := by
  rw [challengeIdealGroup, norm_conjOp]

/-- **I3, the vanishing growth rate**: `t⁻¹ log ‖T t‖ → 0` as `t → ∞`. -/
theorem tendsto_inv_mul_log_norm_challengeIdealGroup :
    Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log ‖challengeIdealGroup t‖) atTop (𝓝 0) := by
  obtain ⟨Φ, DΦ, -, hrate⟩ := exists_isIdealInductionGroup_mainIdealGroup
  simpa only [norm_challengeIdealGroup] using hrate

/-- **I1, the integrated equation.**  Every orbit of the transported group solves the Challenge's
ideal induction equation in integrated form, at every frequency, component and pair of times. -/
theorem mFourierCoeff_challengeIdealGroup_sub (B : L2σ) (m : Fin 3 → ℤ) (i : Fin 3) (s t : ℝ) :
    mFourierCoeff (fun x ↦ (challengeIdealGroup t B : L2) x i) m -
        mFourierCoeff (fun x ↦ (challengeIdealGroup s B : L2) x i) m =
      ∫ τ in s..t, inductionRHS mainLiteralVelocity 0 ⇑(challengeIdealGroup τ B : L2) m i := by
  set f : ℝ → ℂ := fun τ ↦ inductionRHS mainLiteralVelocity 0 ⇑(challengeIdealGroup τ B : L2) m i
  have hf : Continuous f := by
    have e : f = fun τ ↦ idealInductionRHSCLM m i (challengeIdealGroup τ B : L2) :=
      funext fun τ ↦ (idealInductionRHSCLM_apply m i _).symm
    rw [e]
    exact (idealInductionRHSCLM m i).continuous.comp
      (continuous_subtype_val.comp (continuous_challengeIdealGroup_apply B))
  set X : ℝ → ℂ := fun r ↦ mFourierCoeff (fun x ↦ (challengeIdealGroup r B : L2) x i) m
  have h0 : ∀ r, X r - X 0 = ∫ τ in (0 : ℝ)..r, f τ := by
    intro r
    have h := ScaleFamily.TorusCellPlacement.literalFourierCoeff_idealGroup_sub
      globalSeedInterface.smoothingWidth mainParameterChoice.placement
      globalSeedInterface.angularSpeed globalSeedInterface.axialSpeed mainParameterChoice.tau
      mainParameterChoice.tau_nonneg (literalSolenoidalEquivL2σ.symm B) r m i
    simp only [literalFourierCoeff_eq_mFourierCoeff] at h
    refine h.trans (intervalIntegral.integral_congr fun τ _ ↦ ?_)
    refine (congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun j _ ↦ ?_)).trans
      (mFourierCoeff_literalStretchL2_sub_eq_inductionRHS m i (challengeIdealGroup τ B).2)
    exact congrArg _ (mFourierCoeff_literalComponentMul _ j _ m i)
  change X t - X s = _
  rw [show X t - X s = (X t - X 0) - (X s - X 0) by ring, h0 t, h0 s,
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]

/-- **I1.**  The transported group is a solution group of the ideal induction equation in the
sense of the Challenge statement. -/
theorem isIdealGroup_challengeIdealGroup :
    IsIdealGroup mainLiteralVelocity challengeIdealGroup where
  map_zero := challengeIdealGroup_zero
  map_add := challengeIdealGroup_add
  continuous := continuous_challengeIdealGroup_apply
  weak := mFourierCoeff_challengeIdealGroup_sub

end

end FastDynamo
