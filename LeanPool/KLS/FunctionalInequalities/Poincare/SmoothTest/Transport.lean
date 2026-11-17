/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Transport interfaces for `lem:poincare-finite-tensorization`

A coordinate projection has an isometric adjoint; this gives exact gradient energy
preservation when the projection preserves the probability law.

Source: local helpers for the repository's smooth finite-energy test domain. These are not
separately stated BGL propositions, and no identification with a closed Dirichlet domain is used.
The Mathlib sources at the pinned v4.33.0 commit are
[gradient calculus](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Gradient/Basic.lean),
[adjoints](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Adjoint.lean),
[L² transport](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean),
[integral transport](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean),
and [variance](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Moments/Variance.lean).
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ContDiff


namespace FunctionalInequalities.Poincare.SmoothTest

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

section CoordinateLift

variable (q : E →L[ℝ] F)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `C∞` regularity of a test lifted along a continuous linear projection.
Source: local helper from Mathlib's `ContDiff.comp` and continuous-linear-map smoothness. -/
theorem contDiff_comp_projection {f : F → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (f ∘ q) :=
  hf.comp q.contDiff

/-- The gradient chain rule uses the Hilbert adjoint.
Source: local helper from `HasFDerivAt.comp`, `toDual_gradient`, and
`ContinuousLinearMap.adjoint_inner_left` in Mathlib. -/
theorem gradient_comp_projection {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (q x)) :
    gradient (f ∘ q) x = q.adjoint (gradient f (q x)) := by
  have hcomp : HasFDerivAt (f ∘ q) ((fderiv ℝ f (q x)).comp q) x :=
    hf.hasFDerivAt.comp x q.hasFDerivAt
  have hkey : (fderiv ℝ f (q x)).comp q
      = InnerProductSpace.toDual ℝ E (q.adjoint (gradient f (q x))) := by
    ext h
    rw [ContinuousLinearMap.comp_apply, ← toDual_gradient,
      InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_apply_apply,
      ContinuousLinearMap.adjoint_inner_left]
  have hgrad : HasGradientAt (f ∘ q) (q.adjoint (gradient f (q x))) x := by
    rw [hasGradientAt_iff_hasFDerivAt, ← hkey]
    exact hcomp
  exact hgrad.gradient

/-- The norm identity needed for coordinate energy; no division by dimension.
Source: local consequence of `gradient_comp_projection` and the isometric-adjoint hypothesis. -/
theorem norm_gradient_comp_projection {f : F → ℝ} {x : E}
    (hq : Isometry q.adjoint) (hf : DifferentiableAt ℝ f (q x)) :
    ‖gradient (f ∘ q) x‖ ^ 2 = ‖gradient f (q x)‖ ^ 2 := by
  rw [gradient_comp_projection q hf, hq.norm_map_of_map_zero (map_zero _)]

variable [MeasurableSpace E] [MeasurableSpace F]
  {ρ : Measure E} {μ : Measure F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- L² lifting retains its explicit L² hypothesis.
Source: local specialization of Mathlib's `MemLp.comp_measurePreserving`. -/
theorem memLp_comp_projection (hmap : MeasurePreserving q ρ μ)
    {f : F → ℝ} (hf : MemLp f 2 μ) : MemLp (f ∘ q) 2 ρ :=
  hf.comp_measurePreserving hmap

/-- Finite gradient energy is transported with explicit integrability evidence.
Source: local helper from `norm_gradient_comp_projection` and Mathlib's
`MeasurePreserving.integrable_comp_of_integrable`. -/
theorem integrable_gradient_comp_projection (hq : Isometry q.adjoint)
    (hmap : MeasurePreserving q ρ μ) {f : F → ℝ} (hf : Admissible μ f) :
    Integrable (fun x ↦ ‖gradient (f ∘ q) x‖ ^ 2) ρ := by
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  have h1 : Integrable ((fun y ↦ ‖gradient f y‖ ^ 2) ∘ q) ρ :=
    hmap.integrable_comp_of_integrable hf.energy_integrable
  refine h1.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (norm_gradient_comp_projection q hq (hdiff _)).symm

/-- Source: local helper assembling `contDiff_comp_projection`, `memLp_comp_projection`, and
`integrable_gradient_comp_projection` for the repository's `Admissible` class. -/
theorem Admissible.comp_projection (hq : Isometry q.adjoint)
    (hmap : MeasurePreserving q ρ μ) {f : F → ℝ} (hf : Admissible μ f) :
    Admissible ρ (f ∘ q) :=
  ⟨contDiff_comp_projection q hf.smooth', memLp_comp_projection q hmap hf.memLp_two,
    integrable_gradient_comp_projection q hq hmap hf⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- Source: local specialization of Mathlib's `MeasurePreserving.variance_fun_comp`, retaining
the factor test's L² hypothesis. -/
theorem variance_comp_projection (hmap : MeasurePreserving q ρ μ)
    {f : F → ℝ} (hf : MemLp f 2 μ) : variance (f ∘ q) ρ = variance f μ := by
  simpa [Function.comp_def] using
    hmap.variance_fun_comp hf.aestronglyMeasurable.aemeasurable

/-- Source: local helper combining `norm_gradient_comp_projection` with Mathlib's `integral_map`;
`Admissible` supplies the required finite-energy hypothesis. -/
theorem energy_comp_projection (hq : Isometry q.adjoint)
    (hmap : MeasurePreserving q ρ μ) {f : F → ℝ} (hf : Admissible μ f) :
    energy ρ (f ∘ q) = energy μ f := by
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  have hint : AEStronglyMeasurable (fun y ↦ ‖gradient f y‖ ^ 2) (ρ.map q) := by
    rw [hmap.map_eq]
    exact hf.energy_integrable.aestronglyMeasurable
  rw [energy, energy, ← hmap.map_eq,
    integral_map hmap.measurable.aemeasurable hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    norm_gradient_comp_projection q hq (hdiff _))

end CoordinateLift

section IsometryTransport

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  (e : E ≃ₗᵢ[ℝ] F) (μ : Measure E) [IsProbabilityMeasure μ]

omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
private theorem measurePreserving_isometryEquiv :
    MeasurePreserving (⇑e) μ (μ.map e) :=
  ⟨e.continuous.measurable, rfl⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem isometry_adjoint_isometryEquiv :
    Isometry (e : E →L[ℝ] F).adjoint := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact e.symm.isometry

/-- The forward test transport along a linear isometry equivalence. -/
private theorem admissible_comp_isometryEquiv {f : F → ℝ}
    (hf : Admissible (μ.map e) f) : Admissible μ (f ∘ e) :=
  have : IsProbabilityMeasure (μ.map ⇑e) :=
    (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).2 inferInstance
  Admissible.comp_projection (e : E →L[ℝ] F) (isometry_adjoint_isometryEquiv e)
    (measurePreserving_isometryEquiv e μ) hf

/-- Exact test-domain correspondence for a linear isometry equivalence.
Source: local consequence of `Admissible.comp_projection` in both directions and
Mathlib's `LinearIsometryEquiv.adjoint_eq_symm`; this is not a change of test domain. -/
theorem admissible_map_linearIsometryEquiv_iff {f : F → ℝ} :
    Admissible (μ.map e) f ↔ Admissible μ (f ∘ e) := by
  constructor
  · exact admissible_comp_isometryEquiv e μ
  · intro h
    have hprob : IsProbabilityMeasure (μ.map ⇑e) :=
      (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).2 inferInstance
    have hmm : (μ.map ⇑e).map ⇑e.symm = μ := by
      rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
      have hco : ⇑e.symm ∘ ⇑e = id := funext fun x ↦ e.symm_apply_apply x
      rw [hco, Measure.map_id]
    have h' : Admissible ((μ.map ⇑e).map ⇑e.symm) (f ∘ ⇑e) := by rwa [hmm]
    have h2 := admissible_comp_isometryEquiv e.symm (μ.map ⇑e) h'
    have hfe : (f ∘ ⇑e) ∘ ⇑e.symm = f := funext fun y ↦ by
      simp [Function.comp]
    rwa [hfe] at h2

omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
/-- Source: local helper from Mathlib's `MeasurePreserving.variance_fun_comp` for the law pushed
forward by the linear isometry equivalence. -/
theorem variance_map_linearIsometryEquiv {f : F → ℝ} (hf : MemLp f 2 (μ.map e)) :
    variance f (μ.map e) = variance (f ∘ e) μ := by
  simpa [Function.comp_def] using
    ((measurePreserving_isometryEquiv e μ).variance_fun_comp
      hf.aestronglyMeasurable.aemeasurable).symm

/-- Source: local consequence of `energy_comp_projection` and Mathlib's
`LinearIsometryEquiv.adjoint_eq_symm`, with the `Admissible` finite-energy hypothesis. -/
theorem energy_map_linearIsometryEquiv {f : F → ℝ} (hf : Admissible (μ.map e) f) :
    energy (μ.map e) f = energy μ (f ∘ e) :=
  have : IsProbabilityMeasure (μ.map ⇑e) :=
    (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).2 inferInstance
  (energy_comp_projection (e : E →L[ℝ] F) (isometry_adjoint_isometryEquiv e)
    (measurePreserving_isometryEquiv e μ) hf).symm

/-- Source: local consequence of the admissibility, variance, and energy transport identities
above, applied to the repository's fixed-constant `Holds` definition. -/
theorem holds_map_linearIsometryEquiv_iff {C : ℝ} :
    Holds (μ.map e) C ↔ Holds μ C := by
  have hprob : IsProbabilityMeasure (μ.map ⇑e) :=
    (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).2 inferInstance
  constructor
  · intro h
    refine ⟨inferInstance, h.constant_nonneg, fun g hg ↦ ?_⟩
    have hgid : (g ∘ ⇑e.symm) ∘ ⇑e = g := funext fun x ↦ by
      simp [Function.comp]
    have hgF : Admissible (μ.map ⇑e) (g ∘ ⇑e.symm) := by
      apply (admissible_map_linearIsometryEquiv_iff e μ).mpr
      rwa [hgid]
    have hv := h.variance_le hgF
    rw [variance_map_linearIsometryEquiv e μ hgF.memLp_two,
      energy_map_linearIsometryEquiv e μ hgF, hgid] at hv
    exact hv
  · intro h
    refine ⟨hprob, h.constant_nonneg, fun f hf ↦ ?_⟩
    rw [variance_map_linearIsometryEquiv e μ hf.memLp_two,
      energy_map_linearIsometryEquiv e μ hf]
    exact h.variance_le ((admissible_map_linearIsometryEquiv_iff e μ).mp hf)

/-- Source: local consequence of `holds_map_linearIsometryEquiv_iff`, `constant_le`, and
`le_constant`; the extended infimum requires no attaining finite constant. -/
theorem constant_map_linearIsometryEquiv : optimalConstant (μ.map e) = optimalConstant μ := by
  apply le_antisymm
  · exact le_constant fun C hC ↦
      constant_le ((holds_map_linearIsometryEquiv_iff e μ).mpr hC)
  · exact le_constant fun C hC ↦
      constant_le ((holds_map_linearIsometryEquiv_iff e μ).mp hC)

end IsometryTransport

section ScalingTransport

variable [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem gradient_comp_smul (f : E → ℝ) (r : ℝ) (x : E) :
    gradient (fun y : E => f (r • y)) x = r • gradient f (r • x) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [toDual_gradient, map_smul, fderiv_comp_smul]

/-- Scaling a probability law scales its smooth-test Poincaré constant by
the squared scale, including the zero scale. -/
theorem Holds.map_smul {μ : Measure E} {C : ℝ} (h : Holds μ C) (r : ℝ) :
    Holds (μ.map (fun x : E => r • x)) (r ^ 2 * C) := by
  have := h.probability
  let q : E → E := fun x => r • x
  have hq : Measurable q := by fun_prop
  let hmap : MeasurePreserving q μ (μ.map q) := ⟨hq, rfl⟩
  refine ⟨(Measure.isProbabilityMeasure_map_iff hq.aemeasurable).2 inferInstance,
    mul_nonneg (sq_nonneg r) h.constant_nonneg, ?_⟩
  intro f hf
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  have hlift : Admissible μ (fun x => f (q x)) := by
    have hbase : Integrable (fun x => ‖gradient f (q x)‖ ^ 2) μ :=
      hmap.integrable_comp_of_integrable hf.energy_integrable
    refine ⟨hf.smooth'.comp (by fun_prop : ContDiff ℝ ∞ q),
      hf.memLp_two.comp_measurePreserving hmap, ?_⟩
    refine (hbase.const_mul (r ^ 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    change r ^ 2 * ‖gradient f (r • x)‖ ^ 2 =
      ‖gradient (fun y : E => f (r • y)) x‖ ^ 2
    rw [gradient_comp_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hv := h.variance_le hlift
  have hvar : variance (fun x => f (q x)) μ = variance f (μ.map q) :=
    hmap.variance_fun_comp hf.smooth'.continuous.aemeasurable
  have henergy : energy μ (fun x => f (q x)) = r ^ 2 * energy (μ.map q) f := by
    rw [energy, energy, ← hmap.map_eq,
      integral_map hq.aemeasurable (by
        rw [hmap.map_eq]
        exact hf.energy_integrable.aestronglyMeasurable),
      ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ‖gradient (fun y : E => f (r • y)) x‖ ^ 2 =
        r ^ 2 * ‖gradient f (r • x)‖ ^ 2
      rw [gradient_comp_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hvar, henergy] at hv
  convert hv using 1
  ring

end ScalingTransport

variable [MeasurableSpace E]

/-- Empty products and zero-dimensional Hilbert factors have a valid constant zero.
Source: local consequence of constant tests on a subsingleton and Mathlib's
`variance_eq_integral`, rather than a separate assertion in the cited tensorization theorem. -/
theorem holds_zero_of_subsingleton [Subsingleton E]
    (μ : Measure E) [IsProbabilityMeasure μ] : Holds μ 0 := by
  refine ⟨inferInstance, le_refl 0, fun f hf ↦ ?_⟩
  have hconst : f = fun _ ↦ f 0 := funext fun x ↦ congrArg f (Subsingleton.elim x 0)
  rw [zero_mul, hconst]
  have hvar : variance (fun _ ↦ f 0) μ = 0 := by
    rw [variance_eq_integral aemeasurable_const]
    simp
  rw [hvar]

/-- Source: local consequence of `holds_zero_of_subsingleton` and `constant_le`, with
nonnegativity supplied by the `ENNReal` codomain. -/
theorem constant_eq_zero_of_subsingleton [Subsingleton E]
    (μ : Measure E) [IsProbabilityMeasure μ] : optimalConstant μ = 0 := by
  apply le_antisymm
  · have h0 : Holds μ ((0 : NNReal) : ℝ) := by
      simpa using holds_zero_of_subsingleton μ
    simpa using constant_le h0
  · exact _root_.zero_le

end FunctionalInequalities.Poincare.SmoothTest
