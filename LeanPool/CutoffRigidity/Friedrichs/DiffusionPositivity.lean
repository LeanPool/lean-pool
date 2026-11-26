/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.DiffusionForm
public import LeanPool.CutoffRigidity.Friedrichs.FormContraction
public import LeanPool.CutoffRigidity.Friedrichs.FunctionalCalculusSemigroup
import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedGradientRegularity
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule

/-! # Smooth contractions and positivity of the weighted diffusion resolvent -/

@[expose] public section

open Bundle Filter MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal Topology

namespace CutoffRigidity.Riemann.Diff

open CutCur

/-- A smooth nondecreasing `1`-Lipschitz function `τ` with `τ 0 = 0`, `τ s = s` for `s ≥ 0` and
`τ s > s` for `s < 0`.  (Then `τ s - s` is a nonnegative smooth approximation of the negative part
which is strictly positive on `(-∞, 0)`.) -/
theorem exists_posContraction : ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧ τ 0 = 0 ∧
    (∀ s, |deriv τ s| ≤ 1) ∧ (∀ s, 0 ≤ s → τ s = s) ∧ (∀ s, s ≤ τ s) ∧
    ∀ s, s < 0 → s < τ s := by
  obtain ⟨bound, hbound⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  let B := max bound 1
  have hBpos : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hB (s : ℝ) : |deriv Real.smoothTransition s| ≤ B :=
    (Real.norm_eq_abs _ ▸ hbound s).trans (le_max_left _ _)
  set τ : ℝ → ℝ := fun s => s + (1 - Real.smoothTransition (1 + s)) / B with hτ
  have hsm : ContDiff ℝ ∞ τ := by
    refine contDiff_id.add ?_
    exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (contDiff_const.add contDiff_id))).div_const B
  have hder : ∀ s, deriv τ s = 1 - deriv Real.smoothTransition (1 + s) / B := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
    have transition := (Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
    have h2 := (transition _).hasDerivAt.comp s h1
    have h3 : HasDerivAt (fun s : ℝ => s + (1 - Real.smoothTransition (1 + s)) / B)
        (1 + (-(deriv Real.smoothTransition (1 + s) * 1)) / B) s :=
      (hasDerivAt_id s).add ((h2.const_sub 1).div_const B)
    simp only [hτ]
    rw [h3.deriv]
    ring
  have hd0 (s : ℝ) : 0 ≤ deriv Real.smoothTransition s :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hdB : ∀ s, deriv Real.smoothTransition s ≤ B := fun s => (le_abs_self _).trans (hB s)
  refine ⟨τ, hsm, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hτ, Real.smoothTransition.one]
  · intro s
    rw [hder s]
    have h1 : deriv Real.smoothTransition (1 + s) / B ≤ 1 := by
      rw [div_le_one hBpos]; exact hdB _
    have h2 : 0 ≤ deriv Real.smoothTransition (1 + s) / B := div_nonneg (hd0 _) hBpos.le
    rw [abs_of_nonneg (by linarith)]
    linarith
  · intro s hs
    simp [hτ, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 1 + s)]
  · intro s
    have := Real.smoothTransition.le_one (1 + s)
    simp only [hτ]
    have : 0 ≤ (1 - Real.smoothTransition (1 + s)) / B := div_nonneg (by linarith) hBpos.le
    linarith
  · intro s hs
    have := Real.smoothTransition.lt_one_of_lt_one (x := 1 + s) (by linarith)
    simp only [hτ]
    have : 0 < (1 - Real.smoothTransition (1 + s)) / B := div_pos (by linarith) hBpos
    linarith

section Lift
variable {M : Type} [MeasurableSpace M]

theorem lipschitzWith_of_deriv_le {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h1 : ∀ s, |deriv τ s| ≤ 1) :
    LipschitzWith 1 τ := by
  apply lipschitzWith_of_nnNorm_deriv_le (hτ.differentiable (by simp))
  intro s
  have := h1 s
  rw [← NNReal.coe_le_coe]
  simpa using this

/-- The action of a smooth normal contraction on `L²(μ)`. -/
noncomputable def liftLp {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) : (M →₂[μ] ℝ) → (M →₂[μ] ℝ) :=
  (lipschitzWith_of_deriv_le hτ h1).compLp h0

theorem liftLp_norm_sub_le {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (u v : M →₂[μ] ℝ) :
    ‖liftLp hτ h0 h1 u - liftLp hτ h0 h1 v‖ ≤ 1 * ‖u - v‖ := by
  have := (lipschitzWith_of_deriv_le hτ h1).norm_compLp_sub_le h0 u v
  unfold liftLp
  simpa using this

theorem liftLp_norm_le {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (u : M →₂[μ] ℝ) : ‖liftLp hτ h0 h1 u‖ ≤ ‖u‖ := by
  have := (lipschitzWith_of_deriv_le hτ h1).norm_compLp_le h0 u
  unfold liftLp
  simpa using this

theorem coeFn_liftLp {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (u : M →₂[μ] ℝ) :
    (liftLp hτ h0 h1 u : M → ℝ) =ᵐ[μ] fun x => τ (u x) :=
  (lipschitzWith_of_deriv_le hτ h1).coeFn_compLp h0 u


end Lift

section Concrete

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

variable {μ : Measure M} [IsFiniteMeasure μ]

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
/-- Chain rule for the gradient with a smooth real function. -/
private theorem mgrad_comp_real {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ}
    (hf : MSmooth F f) (x : M) :
    mgrad F (θ ∘ f) x = deriv θ (f x) • mgrad F f x := by
  simp only [mgrad_eq_mgradient]
  exact TauCeti.Manifold.mgradient_comp_deriv (hθ.differentiable (by simp) _)
    ((hf x).mdifferentiableAt (by simp))

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
private theorem carre_comp_self {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) {f : M → ℝ} (hf : MSmooth F f)
    (x : M) : carre F (θ ∘ f) (θ ∘ f) x = deriv θ (f x) ^ 2 * carre F f f x := by
  simp only [carre, mgrad_comp_real F hθ hf, real_inner_smul_left, real_inner_smul_right]
  ring

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
/-- **Stability of `𝒟` under smooth normal contractions**: `θ ∘ f ∈ 𝒟` and
`Γ(θ∘f) = θ'(f)² Γ(f) ≤ Γ(f)`. -/
theorem normalContraction_stable (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (h0 : θ 0 = 0)
    (h1 : ∀ s, |deriv θ s| ≤ 1) (f : M → ℝ) (hf : f ∈ testSub F M) :
    θ ∘ f ∈ testSub F M ∧ ∀ x, carre F (θ ∘ f) (θ ∘ f) x ≤ carre F f f x := by
  refine ⟨⟨hθ.contMDiff.comp hf.1, hf.2.comp_left h0⟩, fun x => ?_⟩
  rw [carre_comp_self F hθ hf.1]
  have h2 : deriv θ (f x) ^ 2 ≤ 1 := by
    simpa only [pow_two] using abs_le_one_iff_mul_self_le_one.mp (h1 (f x))
  exact mul_le_of_le_one_left (carre_nonneg F f x) h2

omit [MeasurableSpace F] [BorelSpace F] in
private theorem integrable_carre (a b : testSub F M) :
    Integrable (fun x => carre F (a : M → ℝ) (b : M → ℝ) x) μ := by
  have hs : MSmooth F (carre F (a : M → ℝ) (b : M → ℝ)) := WReg.msmooth_carre a.2.1 b.2.1
  exact hs.continuous.integrable_of_hasCompactSupport (hasCompactSupport_carre F _ a.2.2)

/-- The test function `τ ∘ a`. -/
def compTest {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0) (a : testSub F M) : testSub F M :=
  ⟨τ ∘ (a : M → ℝ), ⟨hτ.contMDiff.comp a.2.1, a.2.2.comp_left h0⟩⟩

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M ↦ TangentSpace 𝓘(ℝ, F) x)] in
private theorem liftLp_testToL2 {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (a : testSub F M) :
    liftLp (μ := μ) hτ h0 h1 (testToL2 F μ a) = testToL2 F μ (compTest F hτ h0 a) := by
  apply Lp.ext
  filter_upwards [coeFn_liftLp hτ h0 h1 (testToL2 F μ a), coeFn_testToL2 F μ a,
    coeFn_testToL2 F μ (compTest F hτ h0 a)] with x h1 h2 h3
  rw [h1, h3, h2]
  rfl

variable {V : M → ℝ} (hV : MSmooth F V)
  (hμ : IsWeightedVolume F μ V)

theorem liftLp_mem_D {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (f : (diffFormData F hV hμ).Dom) :
    ∃ g : (diffFormData F hV hμ).Dom,
      (diffFormData F hV hμ).emb g = liftLp hτ h0 h1 ((diffFormData F hV hμ).emb f) := by
  change (diffFormData F hV hμ).D at f
  obtain ⟨_, a, rfl⟩ := f
  exact ⟨⟨testToL2 F μ (compTest F hτ h0 a), _, rfl⟩, (liftLp_testToL2 F hτ h0 h1 a).symm⟩

theorem liftLp_en_le {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (f g : (diffFormData F hV hμ).Dom)
    (hg : (diffFormData F hV hμ).emb g = liftLp hτ h0 h1 ((diffFormData F hV hμ).emb f)) :
    inner ℝ ((diffFormData F hV hμ).opA g) ((diffFormData F hV hμ).emb g) ≤
      inner ℝ ((diffFormData F hV hμ).opA f) ((diffFormData F hV hμ).emb f) := by
  change (diffFormData F hV hμ).D at f
  obtain ⟨_, a, rfl⟩ := f
  have hg' : g = ⟨testToL2 F μ (compTest F hτ h0 a), _, rfl⟩ :=
    Subtype.ext (hg.trans (liftLp_testToL2 F hτ h0 h1 a))
  have e1 := en_diffFormData F hV hμ (compTest F hτ h0 a) (compTest F hτ h0 a)
  have e2 := en_diffFormData F hV hμ a a
  have e3 : ∫ x, carre F (compTest F hτ h0 a : M → ℝ) (compTest F hτ h0 a : M → ℝ) x ∂μ ≤
      ∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ := by
    refine integral_mono (integrable_carre F (μ := μ) (compTest F hτ h0 a) (compTest F hτ h0 a))
      (integrable_carre F (μ := μ) a a) (fun x => ?_)
    have := (normalContraction_stable F τ hτ h0 h1 (a : M → ℝ) a.2).2 x
    exact this
  subst g
  exact e1.le.trans (e3.trans e2.ge)

/-- The Friedrichs resolvent of the nonnegative weighted diffusion operator preserves positivity. -/
theorem diffusion_resolvent_nonneg {parameter : ℝ} (hparameter : 0 < parameter)
    (g : M →₂[μ] ℝ) (hg : 0 ≤ᵐ[μ] g) :
    0 ≤ᵐ[μ] (diffFormData F hV hμ).resolvent parameter g := by
  obtain ⟨τ, hτ, hzero, hderiv, _, hle, hlt⟩ := exists_posContraction
  let S := diffFormData F hV hμ
  let transform := liftLp (μ := μ) hτ hzero hderiv
  let u := S.resolvent parameter g
  have hcontinuous : Continuous transform :=
    ((lipschitzWith_of_deriv_le hτ hderiv).lipschitzWith_compLp hzero).continuous
  have hcore (f : S.Dom) : ∃ v : S.Dom, S.emb v = transform (S.emb f) ∧
      inner ℝ (S.opA v) (S.emb v) ≤ inner ℝ (S.opA f) (S.emb f) := by
    obtain ⟨v, hv⟩ := liftLp_mem_D F hV hμ hτ hzero hderiv f
    exact ⟨v, hv, liftLp_en_le F hV hμ hτ hzero hderiv f v hv⟩
  have hforce : 0 ≤ inner ℝ g (transform u - u) := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hg, Lp.coeFn_sub (transform u) u, coeFn_liftLp hτ hzero hderiv u]
      with x hx hsub hcomp
    rw [hsub, Pi.sub_apply, hcomp]
    exact mul_nonneg (sub_nonneg.mpr (hle (u x))) hx
  have hfixed : transform u = u :=
    S.resolvent_fixed_of_comparison hcontinuous hcore hparameter g
      (liftLp_norm_le hτ hzero hderiv u) hforce
  change 0 ≤ᵐ[μ] u
  filter_upwards [coeFn_liftLp hτ hzero hderiv u] with x hx
  change 0 ≤ u x
  change transform u x = τ (u x) at hx
  rw [hfixed] at hx
  exact le_of_not_gt fun hneg ↦ (hlt (u x) hneg).ne hx

omit [EMetricSpace M] [BorelSpace M] [IsFiniteMeasure μ] in
/-- Nonnegativity almost everywhere is a closed condition in the real `L²` norm. -/
private theorem isClosed_ae_nonneg :
    IsClosed {u : M →₂[μ] ℝ | 0 ≤ᵐ[μ] u} := by
  have eq : {u : M →₂[μ] ℝ | 0 ≤ᵐ[μ] u} = {u | Lp.posPart u = u} := by
    ext u
    change (0 ≤ᵐ[μ] u) ↔ Lp.posPart u = u
    constructor
    · intro h
      apply Lp.ext
      filter_upwards [h, Lp.coeFn_posPart u] with x hx hpart
      exact hpart.trans (max_eq_left hx)
    · intro h
      filter_upwards [Lp.coeFn_posPart u] with x hx
      rw [h] at hx
      exact hx.symm ▸ le_max_right (u x) 0
  rw [eq]
  exact isClosed_eq Lp.continuous_posPart continuous_id

/-- Euler convergence transfers positivity from the weighted resolvents to the semigroup. -/
theorem diffusion_semigroup_nonneg (time : ℝ≥0) (g : M →₂[μ] ℝ) (hg : 0 ≤ᵐ[μ] g) :
    0 ≤ᵐ[μ] (diffFormData F hV hμ).semigroup time g := by
  let S := diffFormData F hV hμ
  apply cfcSemigroup_mapsTo S.R_unitOp {u : M →₂[μ] ℝ | 0 ≤ᵐ[μ] u} isClosed_ae_nonneg _ time hg
  intro parameter hparameter u hu
  change 0 ≤ᵐ[μ] (parameter • S.resolvent parameter u : M →₂[μ] ℝ)
  filter_upwards [diffusion_resolvent_nonneg F hV hμ hparameter u hu,
    Lp.coeFn_smul parameter (S.resolvent parameter u)] with x hx hsmul
  rw [hsmul]
  exact mul_nonneg hparameter.le hx

end Concrete

end CutoffRigidity.Riemann.Diff
