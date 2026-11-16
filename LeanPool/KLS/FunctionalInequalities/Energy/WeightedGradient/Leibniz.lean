/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import LeanPool.KLS.FunctionalInequalities.Energy.WeightedGradient.Basic

/-!
# Product and chain rules on the weighted-gradient test class

`Basic.lean` proves that the weighted gradient `apply B g = B ∘ ∇g` is additive and homogeneous
`ν`-almost everywhere on the test class `IsTest ν B`, which is what makes the graph a submodule.
This module adds the two nonlinear rules, in the smallest test class in which they close:

* **Leibniz.** For two tests `g₁, g₂` the a.e. identity
  `∇(g₁ g₂) = g₁ ∇g₂ + g₂ ∇g₁` (`IsTest.apply_mul_ae`) needs only absolute continuity, because
  Rademacher's theorem gives joint differentiability `ν`-a.e. Membership of the product in the
  test class (`IsTest.mul`) additionally needs both factors to be **bounded**: an unbounded
  product of Lipschitz functions is not Lipschitz, and its weighted gradient need not be in `L²`.
* **Chain rule.** For `Φ : ℝ → ℝ` differentiable, `∇(Φ ∘ g) = Φ'(g) ∇g` a.e.
  (`IsTest.apply_comp_ae`); `Φ ∘ g` is again a test (`IsTest.comp`) when `Φ` is `C¹` with a
  bounded derivative and `Φ 0 = 0`, which is what keeps `Φ ∘ g` square integrable without
  assuming `g` bounded.

The corresponding operator values are `coeFn_operator_mul` and `coeFn_operator_comp`, stated as
a.e. identities for the representative of `T [g]`; they need the frontier hypothesis `hfr`,
exactly as `operator_apply` does.

Nothing here is a statement about the **closure** `Tbar` beyond its restriction to the test domain,
and nothing here concerns `Γ`, a semigroup or log-concavity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter InnerProductSpace
open scoped ContDiff

namespace FunctionalInequalities.Energy.WeightedGradient

open Energy.Euclidean FunctionalInequalities.Analysis.BakryEmery

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} {B : V →L[ℝ] V} {m : Measure V} [m.IsAddHaarMeasure]

/-! ### Elementary Lipschitz closure properties -/

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- A product of bounded Lipschitz real functions is Lipschitz. -/
theorem lipschitzWith_mul {g₁ g₂ : V → ℝ} {K₁ K₂ : NNReal} {M₁ M₂ : ℝ}
    (hK₁ : LipschitzWith K₁ g₁) (hK₂ : LipschitzWith K₂ g₂)
    (hb₁ : ∀ x, |g₁ x| ≤ M₁) (hb₂ : ∀ x, |g₂ x| ≤ M₂) :
    LipschitzWith (Real.toNNReal M₁ * K₂ + Real.toNNReal M₂ * K₁) fun x => g₁ x * g₂ x := by
  have hM₁ : (0 : ℝ) ≤ M₁ := le_trans (abs_nonneg _) (hb₁ 0)
  have hM₂ : (0 : ℝ) ≤ M₂ := le_trans (abs_nonneg _) (hb₂ 0)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hsplit : g₁ x * g₂ x - g₁ y * g₂ y = g₁ x * (g₂ x - g₂ y) + g₂ y * (g₁ x - g₁ y) := by
    ring
  have hd₁ : |g₁ x - g₁ y| ≤ (K₁ : ℝ) * dist x y := by
    simpa [Real.dist_eq] using hK₁.dist_le_mul x y
  have hd₂ : |g₂ x - g₂ y| ≤ (K₂ : ℝ) * dist x y := by
    simpa [Real.dist_eq] using hK₂.dist_le_mul x y
  have hmain : |g₁ x * g₂ x - g₁ y * g₂ y| ≤ (M₁ * K₂ + M₂ * K₁) * dist x y := by
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |g₁ x| * |g₂ x - g₂ y| ≤ M₁ * ((K₂ : ℝ) * dist x y) := by
      exact mul_le_mul (hb₁ x) hd₂ (abs_nonneg _) hM₁
    have h2 : |g₂ y| * |g₁ x - g₁ y| ≤ M₂ * ((K₁ : ℝ) * dist x y) := by
      exact mul_le_mul (hb₂ y) hd₁ (abs_nonneg _) hM₂
    calc |g₁ x| * |g₂ x - g₂ y| + |g₂ y| * |g₁ x - g₁ y|
        ≤ M₁ * ((K₂ : ℝ) * dist x y) + M₂ * ((K₁ : ℝ) * dist x y) := add_le_add h1 h2
      _ = (M₁ * K₂ + M₂ * K₁) * dist x y := by ring
  calc dist (g₁ x * g₂ x) (g₁ y * g₂ y) = |g₁ x * g₂ x - g₁ y * g₂ y| := Real.dist_eq _ _
    _ ≤ (M₁ * K₂ + M₂ * K₁) * dist x y := hmain
    _ = ((Real.toNNReal M₁ * K₂ + Real.toNNReal M₂ * K₁ : NNReal) : ℝ) * dist x y := by
        rw [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, Real.coe_toNNReal _ hM₁,
          Real.coe_toNNReal _ hM₂]

/-! ### The Leibniz rule -/

variable {g₁ g₂ g : V → ℝ}

omit [SecondCountableTopology V] in
/-- **Leibniz rule for the weighted gradient**, `ν`-almost everywhere:
`B ∇(g₁ g₂) = g₁ (B ∇g₂) + g₂ (B ∇g₁)`. Only absolute continuity and the two Lipschitz
witnesses are used; no boundedness and no `L²` membership. -/
theorem IsTest.apply_mul_ae (hac : (ν : Measure V) ≪ m)
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) :
    apply B (fun x => g₁ x * g₂ x) =ᵐ[(ν : Measure V)]
      fun x => g₁ x • apply B g₂ x + g₂ x • apply B g₁ x := by
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  filter_upwards [hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
      hK₁.locallyLipschitz m),
    hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
      hK₂.locallyLipschitz m)] with x hx₁ hx₂
  simp only [apply, gradient_mul hx₁ hx₂, map_add, map_smul]

/-- The product of two **bounded** tests is a test. -/
theorem IsTest.mul (hac : (ν : Measure V) ≪ m) {M₁ M₂ : ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂)
    (hb₁ : ∀ x, |g₁ x| ≤ M₁) (hb₂ : ∀ x, |g₂ x| ≤ M₂) :
    IsTest ν B fun x => g₁ x * g₂ x := by
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  have hlip : LipschitzWith (Real.toNNReal M₁ * K₂ + Real.toNNReal M₂ * K₁)
      fun x => g₁ x * g₂ x := lipschitzWith_mul hK₁ hK₂ hb₁ hb₂
  refine ⟨⟨_, hlip⟩, ?_, ?_⟩
  · refine MemLp.of_bound hlip.continuous.aestronglyMeasurable (M₁ * M₂) ?_
    filter_upwards with x
    have hM₂ : (0 : ℝ) ≤ M₂ := le_trans (abs_nonneg _) (hb₂ 0)
    calc ‖g₁ x * g₂ x‖ = |g₁ x| * |g₂ x| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ M₁ * M₂ := mul_le_mul (hb₁ x) (hb₂ x) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hb₁ 0))
  · have hbound : MemLp (fun x => M₁ * ‖apply B g₂ x‖ + M₂ * ‖apply B g₁ x‖) 2
        (ν : Measure V) :=
      (h₂.memLp_apply.norm.const_mul M₁).add (h₁.memLp_apply.norm.const_mul M₂)
    refine hbound.mono' (measurable_apply B _).aestronglyMeasurable ?_
    filter_upwards [IsTest.apply_mul_ae hac h₁ h₂] with x hx
    rw [hx]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
    · exact hb₁ x
    · exact hb₂ x

/-! ### The chain rule -/

omit [SecondCountableTopology V] in
/-- **Chain rule for the weighted gradient**, `ν`-almost everywhere:
`B ∇(Φ ∘ g) = Φ'(g) (B ∇g)` for a differentiable `Φ : ℝ → ℝ`. -/
theorem IsTest.apply_comp_ae (hac : (ν : Measure V) ≪ m) {Φ : ℝ → ℝ}
    (hΦ : Differentiable ℝ Φ) (h : IsTest ν B g) :
    apply B (fun x => Φ (g x)) =ᵐ[(ν : Measure V)]
      fun x => deriv Φ (g x) • apply B g x := by
  obtain ⟨K, hK⟩ := h.1
  filter_upwards [hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
    hK.locallyLipschitz m)] with x hx
  simp only [apply, gradient_comp (hΦ (g x)) hx, map_smul]

/-- A `C¹` function with a bounded derivative and `Φ 0 = 0` maps tests to tests. -/
theorem IsTest.comp (hac : (ν : Measure V) ≪ m) {Φ : ℝ → ℝ} {K : ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0) (hK : ∀ t, |deriv Φ t| ≤ K) (h : IsTest ν B g) :
    IsTest ν B fun x => Φ (g x) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable one_ne_zero
  have hΦlip : LipschitzWith (Real.toNNReal K) Φ := by
    refine lipschitzWith_of_nnnorm_deriv_le hΦd fun t => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hK0, Real.norm_eq_abs]
    exact hK t
  obtain ⟨L, hL⟩ := h.1
  refine ⟨⟨Real.toNNReal K * L, hΦlip.comp hL⟩, ?_, ?_⟩
  · refine (h.memLp.norm.const_mul K).mono'
      (hΦlip.comp hL).continuous.aestronglyMeasurable ?_
    filter_upwards with x
    have := hΦlip.dist_le_mul (g x) 0
    rw [Real.dist_eq, Real.dist_eq, hΦ0, sub_zero, sub_zero,
      Real.coe_toNNReal _ hK0] at this
    simpa [Real.norm_eq_abs] using this
  · refine (h.memLp_apply.norm.const_mul K).mono'
      (measurable_apply B _).aestronglyMeasurable ?_
    filter_upwards [IsTest.apply_comp_ae hac hΦd h] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs]
    gcongr
    exact hK (g x)

/-! ### The operator values -/

/-- The operator value of a product of bounded tests, as an a.e. identity of representatives. -/
theorem coeFn_operator_mul (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {M₁ M₂ : ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂)
    (hb₁ : ∀ x, |g₁ x| ≤ M₁) (hb₂ : ∀ x, |g₂ x| ≤ M₂) :
    (operator ν B hac ⟨_, toLp_mem_domain_operator ν B hac (h₁.mul hac h₂ hb₁ hb₂)⟩ :
        V → V) =ᵐ[(ν : Measure V)]
      fun x => g₁ x • apply B g₂ x + g₂ x • apply B g₁ x := by
  rw [operator_apply ν B hac hfr (h₁.mul hac h₂ hb₁ hb₂) _ rfl]
  filter_upwards [(h₁.mul hac h₂ hb₁ hb₂).memLp_apply.coeFn_toLp,
    IsTest.apply_mul_ae hac h₁ h₂] with x hx hy
  rw [hx, hy]

/-- The operator value of a composition, as an a.e. identity of representatives. -/
theorem coeFn_operator_comp (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {Φ : ℝ → ℝ} {K : ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0) (hK : ∀ t, |deriv Φ t| ≤ K) (h : IsTest ν B g) :
    (operator ν B hac ⟨_, toLp_mem_domain_operator ν B hac (h.comp hac hΦ hΦ0 hK)⟩ :
        V → V) =ᵐ[(ν : Measure V)] fun x => deriv Φ (g x) • apply B g x := by
  rw [operator_apply ν B hac hfr (h.comp hac hΦ hΦ0 hK) _ rfl]
  filter_upwards [(h.comp hac hΦ hΦ0 hK).memLp_apply.coeFn_toLp,
    IsTest.apply_comp_ae hac (hΦ.differentiable one_ne_zero) h] with x hx hy
  rw [hx, hy]

end FunctionalInequalities.Energy.WeightedGradient
