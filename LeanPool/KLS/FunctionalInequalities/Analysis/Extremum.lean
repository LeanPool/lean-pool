/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Finite maxima of upper semicontinuous extended-real functions

`exists_finite_maximum_of_upperSemicontinuous_linear_decay`: on a finite-dimensional real
inner-product space (dimension zero
included), an upper semicontinuous `G : E → EReal` that never takes `⊤`, takes a finite value
somewhere and satisfies a linear
decay `G x ≤ b − a‖x‖` with `a > 0` attains a finite global maximum. Values `⊥` elsewhere are
allowed and no maximizing point
is supplied. A generic tool, used for the attainment of the Legendre supremum
(`Analysis/Convex/Legendre/Variation/Attainment.lean`).
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

/-- Actual extended-real USC objectives with a finite witness and positive
linear decay attain a finite global maximum. Bottom values elsewhere and
dimension zero are allowed; no maximizing point is supplied. -/
theorem exists_finite_maximum_of_upperSemicontinuous_linear_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (G : E → EReal) (husc : UpperSemicontinuous G)
    (hnotTop : ∀ x : E, G x ≠ ⊤) (hfinite : ∃ x : E, G x ≠ ⊥)
    (a b : ℝ) (ha : 0 < a)
    (hdecay : ∀ x : E, G x ≤ ((b - a * ‖x‖ : ℝ) : EReal)) :
    ∃ x : E, G x ≠ ⊥ ∧ G x ≠ ⊤ ∧ ∀ z : E, G z ≤ G x := by
    let : ProperSpace E := FiniteDimensional.proper ℝ E
    obtain ⟨x₀, hx₀⟩ := hfinite
    let r : ℝ := (G x₀).toReal
    have hcoe : (r : EReal) = G x₀ := by
      dsimp [r]
      exact EReal.coe_toReal (hnotTop x₀) hx₀
    let R : ℝ := max ‖x₀‖ ((b - r) / a)
    have hR₁ : ‖x₀‖ ≤ R := by
      dsimp [R]
      exact le_max_left _ _
    have hR₂ : (b - r) / a ≤ R := by
      dsimp [R]
      exact le_max_right _ _
    have hx₀K : x₀ ∈ Metric.closedBall (0 : E) R := by
      apply (Metric.mem_closedBall).2
      simpa [dist_zero_right] using hR₁
    have hK : (Metric.closedBall (0 : E) R).Nonempty :=
      ⟨x₀, hx₀K⟩
    have hKcompact : IsCompact (Metric.closedBall (0 : E) R) :=
      ProperSpace.isCompact_closedBall 0 R
    have hUSCK : UpperSemicontinuousOn G (Metric.closedBall (0 : E) R) :=
      husc.upperSemicontinuousOn _
    obtain ⟨x, hxK, hxmax⟩ :=
      UpperSemicontinuousOn.exists_isMaxOn hK hKcompact hUSCK
    have hx₀_le : G x₀ ≤ G x :=
      (isMaxOn_iff.mp hxmax) x₀ hx₀K
    refine ⟨x, ne_bot_of_le_ne_bot hx₀ hx₀_le, hnotTop x, ?_⟩
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : E) R
    · exact (isMaxOn_iff.mp hxmax) z hz
    · have hnotnorm : ¬ ‖z‖ ≤ R := by
        intro hz'
        apply hz
        apply (Metric.mem_closedBall).2
        simpa [dist_zero_right] using hz'
      have hnorm : R < ‖z‖ := lt_of_not_ge hnotnorm
      have hdiv : (b - r) / a < ‖z‖ :=
        lt_of_le_of_lt hR₂ hnorm
      have hmul : b - r < ‖z‖ * a :=
        (div_lt_iff₀ ha).mp hdiv
      have hreal : b - a * ‖z‖ < r := by
        nlinarith [hmul]
      have hstrict : G z < G x₀ := by
        calc
          G z ≤ ((b - a * ‖z‖ : ℝ) : EReal) := hdecay z
          _ < (r : EReal) := (EReal.coe_lt_coe_iff).2 hreal
          _ = G x₀ := hcoe
      exact le_of_lt (hstrict.trans_le hx₀_le)

end FunctionalInequalities.Analysis
