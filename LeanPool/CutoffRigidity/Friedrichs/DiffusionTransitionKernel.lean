/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Adapted from CutoffRigidity/Riemann/DiffKer2.lean through DiffKer5.lean for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.DiffusionConservativity
public import LeanPool.CutoffRigidity.Friedrichs.TransitionKernel
import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSupport

/-! # Transition kernels of the weighted Friedrichs semigroup

This construction takes positive-time continuous representatives as input. It realizes the
operators as Markov kernels and transports their composition and invariance laws.
-/

public section

open Bundle MeasureTheory ProbabilityTheory
open scoped ContDiff Manifold NNReal

namespace CutoffRigidity.Riemann.Diff

open CutCur L2Kernel

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The regularity input for obtaining a kernel from the weighted L² semigroup. -/
abbrev HasContinuousDiffusion : Prop :=
  ∀ t : ℝ≥0, t ≠ 0 → HasContinuousRepresentatives ((diffFormData F hV hμ).semigroup t)

variable (regular : HasContinuousDiffusion F hV hμ)

/-- The transition kernel given by continuous representatives at positive time and identity at
zero. -/
noncomputable def diffusionTransitionKernel (t : ℝ≥0) : Kernel M M := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  let : μ.IsOpenPosMeasure := isOpenPosMeasure_of_weighted F hV hμ
  exact if ht : t = 0 then Kernel.id else
    (regular t ht).kernel (diffusion_semigroup_nonneg F hV hμ t)

/-- Zero time gives the identity kernel. -/
@[simp] theorem diffusionTransitionKernel_zero :
    diffusionTransitionKernel F hV hμ regular 0 = Kernel.id := by
  simp [diffusionTransitionKernel]

/-- Positive-time transitions are absolutely continuous with respect to weighted volume. -/
theorem diffusionTransitionKernel_ac {t : ℝ≥0} (ht : t ≠ 0) (x : M) :
    diffusionTransitionKernel F hV hμ regular t x ≪ μ := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  let : μ.IsOpenPosMeasure := isOpenPosMeasure_of_weighted F hV hμ
  rw [diffusionTransitionKernel, dite_eq_right ht]
  exact (regular t ht).kernel_ac _ x

/-- Integrating an L² vector against a positive-time transition recovers the continuous output. -/
theorem diffusionTransitionKernel_integral {t : ℝ≥0} (ht : t ≠ 0) (x : M) (u : M →₂[μ] ℝ) :
    Integrable (u : M → ℝ) (diffusionTransitionKernel F hV hμ regular t x) ∧
      (∫ y, u y ∂diffusionTransitionKernel F hV hμ regular t x) =
        (regular t ht).representative u x := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  let : μ.IsOpenPosMeasure := isOpenPosMeasure_of_weighted F hV hμ
  rw [diffusionTransitionKernel, dite_eq_right ht]
  exact (regular t ht).kernel_integral _ x u

/-- The transition kernels satisfy the Chapman–Kolmogorov composition law. -/
theorem diffusionTransitionKernel_add (s t : ℝ≥0) :
    diffusionTransitionKernel F hV hμ regular (s + t) =
      diffusionTransitionKernel F hV hμ regular t ∘ₖ diffusionTransitionKernel F hV hμ regular s :=
  by
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
    let : μ.IsOpenPosMeasure := isOpenPosMeasure_of_weighted F hV hμ
    by_cases hs : s = 0
    · subst s
      rw [zero_add, diffusionTransitionKernel_zero, Kernel.comp_id]
    by_cases ht : t = 0
    · subst t
      rw [add_zero, diffusionTransitionKernel_zero, Kernel.id_comp]
    have hst : s + t ≠ 0 := fun heq => hs (add_eq_zero.mp heq).1
    simp only [diffusionTransitionKernel, dite_eq_right hs, dite_eq_right ht, dite_eq_right hst]
    exact (regular t ht).kernel_comp_eq (regular s hs) (regular (s + t) hst)
      ((diffFormData F hV hμ).semigroup_add s t) _ _ _

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- Every transition of the conservative weighted semigroup is a probability kernel. -/
theorem diffusionTransitionKernel_markov (t : ℝ≥0) :
    IsMarkovKernel (diffusionTransitionKernel F hV hμ regular t) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  let : μ.IsOpenPosMeasure := isOpenPosMeasure_of_weighted F hV hμ
  by_cases ht : t = 0
  · subst t
    rw [diffusionTransitionKernel_zero]
    infer_instance
  rw [diffusionTransitionKernel, dite_eq_right ht]
  exact (regular t ht).kernel_markov _ (diffusion_semigroup_one F hV hμ t)

/-- Weighted volume is invariant under every transition. -/
theorem diffusionTransitionKernel_invariant (t : ℝ≥0) :
    μ.bind (diffusionTransitionKernel F hV hμ regular t) = μ := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  let : μ.IsOpenPosMeasure := isOpenPosMeasure_of_weighted F hV hμ
  by_cases ht : t = 0
  · subst t
    rw [diffusionTransitionKernel_zero]
    ext A hA
    rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
    simp [Kernel.id_apply, hA]
  rw [diffusionTransitionKernel, dite_eq_right ht]
  exact (regular t ht).kernel_invariant _ (diffusion_semigroup_preserves_integral F hV hμ t)

end CutoffRigidity.Riemann.Diff
