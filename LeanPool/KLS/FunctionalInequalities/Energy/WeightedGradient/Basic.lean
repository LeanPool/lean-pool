/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.L2.MeanVariance
public import LeanPool.KLS.FunctionalInequalities.Energy.CovarianceGradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.LinearPMap

/-!
# The weighted gradient as a partially defined operator on `L²(ν)`

Source: Blueprint `lem:covariance-core-closure`, the operator `T g = Σ^{1/2} ∇g` on globally
Lipschitz `L²(ν)` functions. Read `Energy.WeightedGradient.apply`, `Energy.WeightedGradient.IsTest`,
`Energy.WeightedGradient.graph`,
`KLS.LogConcave.weightedOperator`, its domain and value lemmas, and finally
`Energy.CovarianceGradient.relaxation_eq_ofLinearPMap`.

Following the certified `lem:covariance-test-core-density`, the square root is replaced by an
arbitrary continuous linear map `B : V →L[ℝ] V`; the Blueprint case is `B = Σ^{1/2}` and every
`B` gives the positive semidefinite `Σ = B† B`. A test is a globally Lipschitz `g ∈ L²(ν)` with
`B ∘ ∇g ∈ L²(ν; V)`. The graph `{([g], [B ∇g])}` is a submodule of `L²(ν) × L²(ν; V)` when `ν` is
absolutely continuous with respect to a Haar measure, because Rademacher's theorem makes the
gradient additive almost everywhere; it is the graph of a function when the frontier of the
support of `ν` is `ν`-null, because two Lipschitz representatives of one class then have almost
everywhere equal gradients. `KLS.LogConcave.weightedOperator` is the resulting `LinearPMap`.

The bridge theorem shows that, whenever `⟪Σ v, v⟫ = ‖B v‖²` for the covariance operator
`Σ = Covariance.operator ν`, the covariance relaxation of `CovarianceGradient/Basic.lean` equals
the sequential relaxation of the squared-norm pre-energy of this operator, so the generic
operator theorems of `Energy/Relaxation/LinearPMap.lean` apply to the affine covariance energy.

What this module does not claim: closability of the operator (proved in `Closable.lean` under
local density bounds), density of its domain, or any Poincaré statement. In dimension zero every
function is constant, the operator vanishes and its domain is all of `L²(ν)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities.Energy

open Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]


section Gradient

namespace WeightedGradient

omit [InnerProductSpace ℝ V] [CompleteSpace V] in
/-- Real scalar multiples of Lipschitz functions are Lipschitz. -/
theorem lipschitzWith_const_smul_real {g : V → ℝ} {K : NNReal} (hK : LipschitzWith K g) (c : ℝ) :
    LipschitzWith (‖c‖₊ * K) (c • g) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul,
    coe_nnnorm, Real.norm_eq_abs, mul_assoc]
  gcongr
  simpa [Real.dist_eq] using hK.dist_le_mul x y

/-- The gradient is additive at points where both functions are differentiable. -/
theorem gradient_add_of_differentiableAt {g₁ g₂ : V → ℝ} {x : V}
    (h₁ : DifferentiableAt ℝ g₁ x) (h₂ : DifferentiableAt ℝ g₂ x) :
    gradient (g₁ + g₂) x = gradient g₁ x + gradient g₂ x := by
  apply (toDual ℝ V).injective
  simp only [toDual_gradient, map_add]
  exact fderiv_add h₁ h₂

/-- The gradient commutes with real scalars at differentiability points. -/
theorem gradient_const_smul_of_differentiableAt {g : V → ℝ} {x : V} (c : ℝ)
    (h : DifferentiableAt ℝ g x) : gradient (c • g) x = c • gradient g x := by
  apply (toDual ℝ V).injective
  simp only [toDual_gradient, map_smul]
  exact fderiv_const_smul h c

/-- The weighted gradient `B ∘ ∇g`. -/
def apply (B : V →L[ℝ] V) (g : V → ℝ) (x : V) : V :=
  B (gradient g x)

end WeightedGradient

section Measurability

variable [MeasurableSpace V] [BorelSpace V]

namespace WeightedGradient

/-- The weighted gradient of any function is Borel measurable. -/
theorem measurable_apply (B : V →L[ℝ] V) (g : V → ℝ) :
    Measurable (apply B g) :=
  B.continuous.measurable.comp (LipschitzApproximation.measurable_gradient g)

end WeightedGradient

end Measurability

namespace WeightedGradient

/-- The weighted gradient of a constant vanishes. -/
@[simp]
theorem apply_const (B : V →L[ℝ] V) (c : ℝ) :
    apply B (fun _ ↦ c) = fun _ ↦ 0 := by
  funext x
  simp [apply, gradient_fun_const]

/-- The identity-weighted gradient is the gradient. -/
theorem apply_id (g : V → ℝ) :
    apply (ContinuousLinearMap.id ℝ V) g = gradient g := by
  funext x
  rfl

end WeightedGradient

end Gradient

section Operator

variable [MeasurableSpace V] (ν : ProbabilityMeasure V) (B : V →L[ℝ] V)

namespace WeightedGradient

/-- Test data for the weighted gradient operator: globally Lipschitz, square integrable, with
square-integrable weighted gradient. -/
def IsTest (g : V → ℝ) : Prop :=
  (∃ K : NNReal, LipschitzWith K g) ∧ MemLp g 2 (ν : Measure V) ∧
    MemLp (apply B g) 2 (ν : Measure V)

end WeightedGradient

namespace WeightedGradient.IsTest

variable {ν B} {g : V → ℝ}

theorem continuous (h : IsTest ν B g) : Continuous g := by
  obtain ⟨K, hK⟩ := h.1
  exact hK.continuous

theorem memLp (h : IsTest ν B g) : MemLp g 2 (ν : Measure V) := h.2.1

theorem memLp_apply (h : IsTest ν B g) :
    MemLp (Energy.WeightedGradient.apply B g) 2 (ν : Measure V) := h.2.2

theorem const (c : ℝ) : IsTest ν B (fun _ ↦ c) :=
  ⟨⟨0, LipschitzWith.const c⟩, memLp_const c, by
    rw [Energy.WeightedGradient.apply_const]
    exact memLp_const 0⟩

variable [BorelSpace V] [FiniteDimensional ℝ V] {m : Measure V} [m.IsAddHaarMeasure]

/-- Under absolute continuity, the weighted gradient is additive `ν`-almost everywhere. -/
theorem apply_add_ae (hac : (ν : Measure V) ≪ m) {g₁ g₂ : V → ℝ} (h₁ : IsTest ν B g₁)
    (h₂ : IsTest ν B g₂) :
    Energy.WeightedGradient.apply B g₁ + Energy.WeightedGradient.apply B g₂ =ᵐ[(ν : Measure V)]
      Energy.WeightedGradient.apply B (g₁ + g₂) := by
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  filter_upwards [hac.ae_le
      (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hK₁.locallyLipschitz m),
    hac.ae_le
      (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hK₂.locallyLipschitz
        m)] with
    x hx₁ hx₂
  simp only [Pi.add_apply, Energy.WeightedGradient.apply,
    Energy.WeightedGradient.gradient_add_of_differentiableAt hx₁ hx₂, map_add]

/-- Under absolute continuity, the weighted gradient is homogeneous `ν`-almost everywhere. -/
theorem apply_smul_ae (hac : (ν : Measure V) ≪ m) (c : ℝ) (h : IsTest ν B g) :
    c • Energy.WeightedGradient.apply B g =ᵐ[(ν : Measure V)]
      Energy.WeightedGradient.apply B (c • g) := by
  obtain ⟨K, hK⟩ := h.1
  filter_upwards [hac.ae_le
      (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hK.locallyLipschitz
        m)] with
    x hx
  simp only [Pi.smul_apply, Energy.WeightedGradient.apply,
    Energy.WeightedGradient.gradient_const_smul_of_differentiableAt c hx, map_smul]


theorem add (hac : (ν : Measure V) ≪ m) {g₁ g₂ : V → ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) : IsTest ν B (g₁ + g₂) := by
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  exact ⟨⟨K₁ + K₂, hK₁.add hK₂⟩, h₁.memLp.add h₂.memLp,
    (h₁.memLp_apply.add h₂.memLp_apply).ae_eq
      (apply_add_ae hac h₁ h₂)⟩

theorem smul (hac : (ν : Measure V) ≪ m) (c : ℝ) (h : IsTest ν B g) : IsTest ν B (c • g) := by
  obtain ⟨K, hK⟩ := h.1
  exact
    ⟨⟨‖c‖₊ * K, Energy.WeightedGradient.lipschitzWith_const_smul_real hK c⟩,
      h.memLp.const_smul c, (h.memLp_apply.const_smul c).ae_eq (apply_smul_ae hac c h)⟩

end WeightedGradient.IsTest

variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : Measure V} [m.IsAddHaarMeasure]

namespace WeightedGradient

/-- The graph `{([g], [B ∇g]) : g test}` of the weighted gradient in `L²(ν) × L²(ν; V)`. It is
a submodule because Rademacher's theorem makes the gradient linear `ν`-almost everywhere. -/
def graph (hac : (ν : Measure V) ≪ m) :
    Submodule ℝ (Lp ℝ 2 (ν : Measure V) × Lp V 2 (ν : Measure V)) where
  carrier := {p | ∃ (g : V → ℝ) (h : IsTest ν B g),
    p = (h.memLp.toLp g, h.memLp_apply.toLp (apply B g))}
  zero_mem' := by
    refine ⟨fun _ ↦ 0, IsTest.const 0, ?_⟩
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_zero]
      symm
      rw [Lp.eq_zero_iff_ae_eq_zero]
      filter_upwards [MemLp.coeFn_toLp (IsTest.const (ν := ν) (B := B) 0).memLp]
        with x hx
      rw [hx]
      rfl
    · simp only [Prod.snd_zero]
      symm
      rw [Lp.eq_zero_iff_ae_eq_zero]
      filter_upwards [MemLp.coeFn_toLp (IsTest.const (ν := ν) (B := B) 0).memLp_apply]
        with x hx
      rw [hx]
      simp
  add_mem' := by
    rintro p₁ p₂ ⟨g₁, h₁, rfl⟩ ⟨g₂, h₂, rfl⟩
    refine ⟨g₁ + g₂, h₁.add hac h₂, Prod.ext ?_ ?_⟩
    · exact (MemLp.toLp_add h₁.memLp h₂.memLp).symm
    · simp only [Prod.snd_add]
      rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (IsTest.apply_add_ae hac h₁ h₂)
  smul_mem' := by
    rintro c p ⟨g, h, rfl⟩
    refine ⟨c • g, h.smul hac c, Prod.ext ?_ ?_⟩
    · exact (MemLp.toLp_const_smul c h.memLp).symm
    · simp only [Prod.smul_snd]
      rw [← MemLp.toLp_const_smul]
      exact MemLp.toLp_congr _ _ (IsTest.apply_smul_ae hac c h)

omit [SecondCountableTopology V] in
theorem mem_graph_iff (hac : (ν : Measure V) ≪ m)
    (p : Lp ℝ 2 (ν : Measure V) × Lp V 2 (ν : Measure V)) :
    p ∈ graph ν B hac ↔ ∃ (g : V → ℝ) (h : IsTest ν B g),
      p = (h.memLp.toLp g, h.memLp_apply.toLp (apply B g)) :=
  Iff.rfl

/-- When the frontier of the support is `ν`-null, the graph contains no pair `(0, y)` with
`y ≠ 0`: two Lipschitz representatives of the zero class have almost everywhere zero gradient. -/
theorem graph_snd_eq_zero (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    ∀ p ∈ graph ν B hac, p.1 = 0 → p.2 = 0 := by
  rintro p ⟨g, h, rfl⟩ h0
  simp only at h0 ⊢
  have hg : g =ᵐ[(ν : Measure V)] fun _ ↦ 0 := by
    have := (Lp.eq_zero_iff_ae_eq_zero.mp h0)
    exact (h.memLp.coeFn_toLp.symm.trans this)
  have hgrad := gradient_ae_eq_of_ae_eq hfr h.continuous continuous_const hg
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [h.memLp_apply.coeFn_toLp, hgrad] with x hx hgx
  rw [hx]
  simp [apply, hgx, gradient_fun_const]

/-- The weighted gradient operator `g ↦ B ∘ ∇g` as a partially defined linear map on `L²(ν)`
with values in `L²(ν; V)`. -/
def operator (hac : (ν : Measure V) ≪ m) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  (graph ν B hac).toLinearPMap

/-- The graph of the operator is the test graph. -/
theorem graph_operator (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    (operator ν B hac).graph = graph ν B hac :=
  Submodule.toLinearPMap_graph_eq _ (graph_snd_eq_zero ν B hac hfr)

section OperatorDomain

omit [SecondCountableTopology V]
/-- The domain consists exactly of the classes of globally Lipschitz `L²` functions with
square-integrable weighted gradient. -/
theorem mem_domain_operator_iff (hac : (ν : Measure V) ≪ m) (f : Lp ℝ 2 (ν : Measure V)) :
    f ∈ (operator ν B hac).domain ↔
      ∃ (g : V → ℝ) (h : IsTest ν B g), f = h.memLp.toLp g := by
  change f ∈ (graph ν B hac).map (LinearMap.fst ℝ _ _) ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨p, ⟨g, h, rfl⟩, rfl⟩
    exact ⟨g, h, rfl⟩
  · rintro ⟨g, h, rfl⟩
    exact ⟨_, ⟨g, h, rfl⟩, rfl⟩

/-- Every test class lies in the domain. -/
theorem toLp_mem_domain_operator (hac : (ν : Measure V) ≪ m) {g : V → ℝ}
    (h : IsTest ν B g) : h.memLp.toLp g ∈ (operator ν B hac).domain :=
  (mem_domain_operator_iff ν B hac _).mpr ⟨g, h, rfl⟩

end OperatorDomain

/-- The operator sends the class of a test to the class of its weighted gradient. -/
theorem operator_apply (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {g : V → ℝ}
    (h : IsTest ν B g) {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∈ (operator ν B hac).domain) (hfg : f = h.memLp.toLp g) :
    operator ν B hac ⟨f, hf⟩ = h.memLp_apply.toLp (apply B g) := by
  symm
  rw [LinearPMap.image_iff hf, graph_operator ν B hac hfr]
  exact ⟨g, h, by rw [hfg]⟩

end WeightedGradient

namespace CovarianceGradient

open WeightedGradient

omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance density is the squared weighted gradient. -/
theorem density_eq_norm_sq
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    density ν g = fun x ↦ ‖apply B g x‖ ^ 2 := by
  funext x
  exact hB _

omit [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance tests are exactly the gradient tests. -/
theorem weightedTest_iff_exists_test
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    IsTest ν B g ↔ ∃ f : Test ν, f.toFun = g := by
  have hmeas : AEStronglyMeasurable (apply B g) (ν : Measure V) :=
    (measurable_apply B g).aestronglyMeasurable
  constructor
  · rintro ⟨hK, h2, hBg⟩
    refine ⟨⟨g, hK, h2, ?_⟩, rfl⟩
    rw [density_eq_norm_sq ν B hB]
    exact (memLp_two_iff_integrable_sq_norm hmeas).mp hBg
  · rintro ⟨f, rfl⟩
    refine ⟨f.lipschitz, f.memLp_two, ?_⟩
    rw [memLp_two_iff_integrable_sq_norm hmeas, ← density_eq_norm_sq ν B hB]
    exact f.integrable

end CovarianceGradient

namespace CovarianceGradient.Test

open WeightedGradient

omit [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- With `⟪Σ v, v⟫ = ‖B v‖²`, the covariance energy of a test is the squared `L²` norm of its
weighted gradient. -/
theorem coe_energy_eq_norm_sq
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2)
    (f : Energy.CovarianceGradient.Test ν) (h : IsTest ν B f.toFun) :
    (f.energy : ℝ) = ‖h.memLp_apply.toLp (apply B f.toFun)‖ ^ 2 := by
  rw [coe_energy, L2.norm_toLp_sq,
    Energy.CovarianceGradient.density_eq_norm_sq ν B hB]

end CovarianceGradient.Test

namespace CovarianceGradient

open WeightedGradient

/-- The covariance relaxation is the sequential relaxation of the squared-norm pre-energy of the
weighted gradient operator, whenever `⟪Σ v, v⟫ = ‖B v‖²`. -/
theorem relaxation_eq_ofLinearPMap (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) :
    relaxation ν =
      (PreEnergy.ofLinearPMap (operator ν B hac)).sequentialRelaxation := by
  ext x
  apply le_antisymm
  · refine (PreEnergy.ofLinearPMap (operator ν B hac)).sequentialRelaxation_comp_le
      (preEnergy ν) id continuous_id ?_ x
    intro t
    let t' : (operator ν B hac).domain := t
    obtain ⟨g, h, hg⟩ := (mem_domain_operator_iff ν B hac t').mp t'.2
    obtain ⟨f, rfl⟩ := (weightedTest_iff_exists_test ν B hB g).mp h
    refine ⟨f, ?_, le_of_eq ?_⟩
    · change f.toL2 = (t' : Lp ℝ 2 (ν : Measure V))
      rw [hg]
      rfl
    · apply NNReal.eq
      change (f.energy : ℝ) =
        ((‖operator ν B hac ⟨(t' : Lp ℝ 2 (ν : Measure V)), t'.2⟩‖₊ ^ 2 : NNReal) : ℝ)
      rw [Test.coe_energy_eq_norm_sq ν B hB f h, operator_apply ν B hac hfr h t'.2 hg]
      push_cast
      rfl
  · refine (preEnergy ν).sequentialRelaxation_comp_le
      (PreEnergy.ofLinearPMap (operator ν B hac)) id continuous_id ?_ x
    intro f
    have h : IsTest ν B f.toFun :=
      (weightedTest_iff_exists_test ν B hB f.toFun).mpr ⟨f, rfl⟩
    have hmem : f.toL2 ∈ (operator ν B hac).domain :=
      toLp_mem_domain_operator ν B hac h
    refine ⟨⟨f.toL2, hmem⟩, rfl, le_of_eq ?_⟩
    apply NNReal.eq
    change ((‖operator ν B hac ⟨f.toL2, hmem⟩‖₊ ^ 2 : NNReal) : ℝ) = (f.energy : ℝ)
    rw [Test.coe_energy_eq_norm_sq ν B hB f h, operator_apply ν B hac hfr h hmem rfl]
    push_cast
    rfl

end CovarianceGradient

end Operator

section ZeroDimension

variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (ν : ProbabilityMeasure V) (B : V →L[ℝ] V) {m : Measure V} [m.IsAddHaarMeasure]

namespace WeightedGradient

section SubsingletonOperator

omit [SecondCountableTopology V]
/-- In dimension zero the weighted gradient operator vanishes identically. -/
theorem operator_apply_eq_zero_of_subsingleton [Subsingleton V]
    (hac : (ν : Measure V) ≪ m) (f : (operator ν B hac).domain) :
    operator ν B hac f = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact Eventually.of_forall fun x ↦ Subsingleton.elim _ _

/-- In dimension zero every `L²` class is constant, hence a test: the domain is everything. -/
theorem domain_operator_eq_top_of_subsingleton [Subsingleton V]
    (hac : (ν : Measure V) ≪ m) : (operator ν B hac).domain = ⊤ := by
  rw [eq_top_iff]
  intro f _
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (ν : Measure V)
  refine (mem_domain_operator_iff ν B hac f).mpr ⟨fun _ ↦ f x₀, IsTest.const _, ?_⟩
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (IsTest.const (ν := ν) (B := B) (f x₀)).memLp]
    with x hx
  rw [hx]
  exact congrArg f (Subsingleton.elim x x₀)

end SubsingletonOperator

end WeightedGradient

end ZeroDimension

end FunctionalInequalities.Energy
