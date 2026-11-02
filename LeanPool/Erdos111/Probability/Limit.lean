/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Basic
public import LeanPool.Erdos111.Probability.Kolmogorov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Limits of sign laws along an ultrafilter

Probability laws on `V → Bool` are compact in the following sense: along any ultrafilter,
the finite-dimensional marginals of a family of laws converge, and Kolmogorov extension
turns the limits into one law. Every property that is a closed condition on finitely many
coordinates, holding eventually along the ultrafilter, then holds for the limit. In
particular `Rooted`, `SameOn` and `TraceBound` pass to the limit.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Erdos111

variable {V : Type*}

/-- Along an ultrafilter, laws on a finite type converge setwise to a limit measure. -/
theorem exists_tendsto_measure_of_finite {α X : Type*} [Finite X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (F : Ultrafilter α) (π : α → Measure X) :
    ∃ ρ : Measure X, ∀ S : Set X, Tendsto (fun a => π a S) F (𝓝 (ρ S)) := by
  have := Fintype.ofFinite X
  have hlim : ∀ x : X, ∃ m, Tendsto (fun a => π a {x}) F (𝓝 m) := fun x => by
    obtain ⟨m, -, hm⟩ := isCompact_univ.ultrafilter_le_nhds (F.map fun a => π a {x}) (by simp)
    exact ⟨m, hm⟩
  choose m hm using hlim
  refine ⟨Measure.sum fun x => m x • Measure.dirac x, fun S => ?_⟩
  have hS : MeasurableSet S := S.toFinite.measurableSet
  have h : ∀ a, π a S = ∑ x, π a {x} * Measure.dirac x S := fun a => by
    conv_lhs => rw [← Measure.sum_smul_dirac (π a)]
    simp
  simp only [h, Measure.sum_apply _ hS, tsum_fintype, Measure.smul_apply, smul_eq_mul]
  exact tendsto_finsetSum _ fun x _ =>
    ENNReal.Tendsto.mul_const (hm x) (Or.inr (measure_ne_top _ _))

/-- Along an ultrafilter, sign laws have a limit law: the integral of every finite-valued
function of finitely many coordinates converges to its integral under the limit. -/
theorem exists_limit {α : Type*} (F : Ultrafilter α) (ν : α → Measure (V → Bool))
    [∀ a, IsProbabilityMeasure (ν a)] :
    ∃ μ : Measure (V → Bool), IsProbabilityMeasure μ ∧
      ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
        Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)) := by
  classical
  choose P hP using fun J : Finset V =>
    exists_tendsto_measure_of_finite F (fun a => (ν a).map J.restrict)
  have hprob : ∀ J, IsProbabilityMeasure (P J) := fun J => by
    have h : ∀ a, (ν a).map J.restrict Set.univ = 1 := fun a => by
      rw [Measure.map_apply (Finset.measurable_restrict J) .univ, Set.preimage_univ, measure_univ]
    refine ⟨tendsto_nhds_unique (hP J Set.univ) ?_⟩
    simp only [h]
    exact tendsto_const_nhds
  have hproj : IsProjectiveMeasureFamily (α := fun _ : V => Bool) P := by
    intro I J hJI
    ext S hS
    rw [Measure.map_apply (Finset.measurable_restrict₂ (X := fun _ : V => Bool) hJI) hS]
    refine tendsto_nhds_unique (hP J S) ?_
    convert hP I (Finset.restrict₂ (π := fun _ : V => Bool) hJI ⁻¹' S) using 2 with a
    rw [Measure.map_apply (Finset.measurable_restrict _) hS,
      Measure.map_apply (Finset.measurable_restrict _)
        (Finset.measurable_restrict₂ (X := fun _ : V => Bool) hJI hS),
      ← Set.preimage_comp, Finset.restrict₂_comp_restrict]
  obtain ⟨μ, hμprob, hμ⟩ := exists_isProjectiveLimit_bool P hproj
  refine ⟨μ, hμprob, fun J f hf hfin => ?_⟩
  -- `f` factors through the coordinates in `J`
  obtain ⟨g, hg, hfg⟩ : ∃ g : (J → Bool) → ℝ≥0∞, (∀ y, g y ≠ ∞) ∧
      ∀ ω, f ω = g (J.restrict ω) :=
    ⟨fun y => f fun i => if h : i ∈ J then y ⟨i, h⟩ else false, fun _ => hfin _,
      fun ω => hf fun i hi => by simp [Finset.mem_coe.1 hi]⟩
  have hint : ∀ ρ : Measure (V → Bool), ∫⁻ ω, f ω ∂ρ = ∑ y, g y * ρ.map J.restrict {y} :=
    fun ρ => by
      simp only [hfg]
      rw [← lintegral_map (measurable_of_finite g) (Finset.measurable_restrict J),
        lintegral_fintype]
  simp only [hint, hμ J]
  exact tendsto_finsetSum _ fun y _ => ENNReal.Tendsto.const_mul (hP J {y}) (Or.inr (hg y))

/-- A bound on the integral of a finite-valued function of finitely many coordinates that
holds eventually along the ultrafilter holds for the limit law. -/
theorem lintegral_le_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {J : Finset V} {f : (V → Bool) → ℝ≥0∞} (hf : DependsOn f J) (hfin : ∀ ω, f ω ≠ ∞)
    {c : ℝ≥0∞} (h : ∀ᶠ a in F, ∫⁻ ω, f ω ∂ν a ≤ c) : ∫⁻ ω, f ω ∂μ ≤ c :=
  le_of_tendsto (hμ J f hf hfin) h

/-- `J` over `N` passes to the limit law. -/
theorem rooted_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {G : SimpleGraph V} {C : ℝ≥0} {N : Set V}
    (h : ∀ P : Pattern V, P.IsOver G N →
      ∀ᶠ a in F, ∫⁻ τ, (extCost P.S P.E τ : ℝ≥0∞) ∂ν a ≤ C * P.S.card) :
    Rooted G C N μ := fun P hP =>
  lintegral_le_of_tendsto hμ (J := P.R)
    (fun _ _ hxy => congrArg _ (extCost_dependsOn hP.edges_inside hxy))
    (fun _ => ENNReal.natCast_ne_top _) (h P hP)

/-- The mass of a measurable set determined by finitely many coordinates converges to its
mass under the limit law. -/
theorem tendsto_measure_of_dependsOn {α : Type*} {F : Ultrafilter α}
    {ν : α → Measure (V → Bool)} {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {J : Finset V} {s : Set (V → Bool)} (hs : MeasurableSet s) (hsJ : DependsOn (· ∈ s) J) :
    Tendsto (fun a => ν a s) F (𝓝 (μ s)) := by
  classical
  have hf : DependsOn (s.indicator (1 : (V → Bool) → ℝ≥0∞)) J := fun x y hxy => by
    simp only [Set.indicator_apply, show x ∈ s ↔ y ∈ s from iff_of_eq (hsJ hxy), Pi.one_apply]
  have := hμ J _ hf fun ω => by by_cases hω : ω ∈ s <;> simp [hω]
  simpa only [lintegral_indicator_one hs] using this

/-- Agreement of finite marginals on `A` with a fixed law passes to the limit law. -/
theorem sameOn_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {A : Set V} {ρ : Measure (V → Bool)} (h : ∀ᶠ a in F, SameOn A ρ (ν a)) :
    SameOn A ρ μ := by
  intro J hJ
  ext S hS
  have hm : MeasurableSet (J.restrict ⁻¹' S) :=
    Finset.measurable_restrict (X := fun _ : V => Bool) J hS
  rw [Measure.map_apply (Finset.measurable_restrict J) hS,
    Measure.map_apply (Finset.measurable_restrict J) hS]
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_)
    (tendsto_measure_of_dependsOn hμ hm (J := J) fun x y hxy => ?_)
  · filter_upwards [h] with a ha
    rw [← Measure.map_apply (Finset.measurable_restrict J) hS, ha J hJ,
      Measure.map_apply (Finset.measurable_restrict J) hS]
  · have : J.restrict x = J.restrict y := funext fun i => hxy i i.2
    simp only [Set.mem_preimage, this]

/-- A trace bound that holds eventually along the ultrafilter holds for the limit law. -/
theorem traceBound_of_tendsto {α : Type*} {F : Ultrafilter α} {ν : α → Measure (V → Bool)}
    {μ : Measure (V → Bool)}
    (hμ : ∀ (J : Finset V) (f : (V → Bool) → ℝ≥0∞), DependsOn f J → (∀ ω, f ω ≠ ∞) →
      Tendsto (fun a => ∫⁻ ω, f ω ∂ν a) F (𝓝 (∫⁻ ω, f ω ∂μ)))
    {C : ℝ≥0} {v : V} {T : Set V} (h : ∀ᶠ a in F, TraceBound C (ν a) v T) :
    TraceBound C μ v T := by
  classical
  intro B hB
  refine le_of_tendsto (tendsto_finsetSum _ fun u _ =>
    tendsto_measure_of_dependsOn hμ (J := {u, v})
      (measurableSet_eq_fun (measurable_pi_apply u) (measurable_pi_apply v))
      fun x y hxy => ?_) ?_
  · change (x u = x v) = (y u = y v)
    rw [hxy u (by simp), hxy v (by simp)]
  · filter_upwards [h] with a ha using ha B hB

end Erdos111
