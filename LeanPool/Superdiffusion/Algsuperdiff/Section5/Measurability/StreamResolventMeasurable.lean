/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.ResolventFamilyMeasurable

/-!
# From measurable cube resolvents to stream transition laws

The analytic minimal resolvent is a countable supremum of cube resolvents,
with positive and negative parts supplying its real-valued version.
-/

@[expose] public section



namespace Algsuperdiff.Section5.Measurability

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field
open DivergenceFormProcess.Form
open HCPolySupport MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d] (M : ABKModel d)

omit [NeZero d] in
private theorem measurable_c0_family_eval {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → C₀(Vec d, ℝ))
    (hF : ∀ x, Measurable fun omega => F omega x) :
    Measurable fun p : Ω × Vec d => F p.1 p.2 := by
  have hjoint : Measurable (Function.uncurry fun x omega => F omega x) :=
    measurable_uncurry_of_continuous_of_measurable (fun omega => (F omega).continuous) hF
  exact hjoint.comp measurable_swap

theorem measurable_streamResolvent_of_cube
    (hcube : ∀ (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f)
      (D : ℝ) (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d),
      Measurable fun omega : FullSample d M.gamma =>
        (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent mu f hf hfD m x)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    Measurable fun p : FullSample d M.gamma × Vec d =>
      (streamWholeSpaceResolvent M p.1).toContractiveResolvent.operator mu f p.2 := by
  have hminimal : ∀ (g : Vec d → ℝ) (hg : Measurable g)
      (D : ℝ) (hgD : ∀ x, |g x| ≤ D) (x : Vec d),
      Measurable fun omega : FullSample d M.gamma =>
        (streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent mu g hg hgD x := by
    intro g hg D hgD x
    change Measurable fun omega : FullSample d M.gamma =>
      ⨆ m, ENNReal.ofReal
        ((streamWholeSpaceAnalyticData M omega).analyticCubeResolvent mu g hg hgD m x)
    exact Measurable.iSup fun m => ENNReal.measurable_ofReal.comp
      (hcube mu g hg D hgD m x)
  have hreal : ∀ (g : Vec d → ℝ) (hg : Measurable g)
      (D : ℝ) (hgD : ∀ x, |g x| ≤ D) (x : Vec d),
      Measurable fun omega : FullSample d M.gamma =>
        (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal mu g hg hgD x := by
    intro g hg D hgD x
    unfold WholeSpaceAnalyticData.analyticMinimalResolventReal
    exact (hminimal _ _ _ _ x).ennreal_toReal.sub (hminimal _ _ _ _ x).ennreal_toReal
  have hpoint : ∀ x : Vec d, Measurable fun omega : FullSample d M.gamma =>
      (streamWholeSpaceResolvent M omega).toContractiveResolvent.operator mu f x := by
    intro x
    have hf : ∀ y, |f y| ≤ ‖f‖ := fun y => by
      rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF y
    simp only [streamWholeSpaceResolvent,
      streamAnalyticMinimalPositiveC0ContractiveResolvent_operator,
      WholeSpaceAnalyticData.analyticMinimalC0ResolventOfVanishing_apply]
    exact hreal f f.continuous.measurable ‖f‖ hf x
  exact measurable_c0_family_eval
    (fun omega => (streamWholeSpaceResolvent M omega).toContractiveResolvent.operator mu f)
    hpoint

theorem measurable_streamTransition_of_cube
    (hcube : ∀ (mu : PositiveShift) (f : Vec d → ℝ) (hf : Measurable f)
      (D : ℝ) (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d),
      Measurable fun omega : FullSample d M.gamma =>
        (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent mu f hf hfD m x)
    (t : NNReal) :
    Measurable fun p : FullSample d M.gamma × Vec d =>
      (streamWholeSpaceResolvent M p.1).kernelSemigroup t p.2 :=
  measurable_kernelSemigroup_family (streamWholeSpaceResolvent M)
    (measurable_streamResolvent_of_cube M hcube) t

end
end Algsuperdiff.Section5.Measurability
