/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Connected.Basic

/-!
# Local integrability of nontrivial plurisubharmonic functions

The good locus records both almost-everywhere finiteness and integrability on
an actual open neighborhood. A finite center starts this locus. At every PSH
germ the locus contains its limit points: positive measure supplies a finite
nearby center, and the ball submean estimate controls a neighborhood of the
limit point. Connectedness then propagates local integrability.

The argument uses the disc neighborhood of each individual PSH germ. It does
not assume that all local germs already satisfy a global disc criterion.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- Points with an open neighborhood on which the potential is finite almost
everywhere and its real representative is integrable. -/
def pshIntegrabilityLocus (u : E → EReal) (μ : Measure E) : Set E :=
  {x | ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
    (∀ᵐ y ∂μ.restrict V, u y ≠ ⊤ ∧ u y ≠ ⊥) ∧
    IntegrableOn (fun y => (u y).toReal) V μ}

theorem isOpen_pshIntegrabilityLocus (u : E → EReal) (μ : Measure E) :
    IsOpen (pshIntegrabilityLocus u μ) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨V, hV, hxV, hae, hI⟩
  exact mem_of_superset (hV.mem_nhds hxV)
    (fun y hy => ⟨V, hV, hy, hae, hI⟩)

variable [BorelSpace E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable [FiniteDimensional ℝ E] {u : E → EReal} {x : E}

/-- A PSH germ with finite value controls a neighborhood in the actual
almost-everywhere finite and integrable sense. -/
theorem PlurisubharmonicAt.mem_pshIntegrabilityLocus
    (hu : PlurisubharmonicAt u x) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hx : u x ≠ ⊥) : x ∈ pshIntegrabilityLocus u μ := by
  obtain ⟨W, hW, hxW, huW⟩ := hu
  obtain ⟨R, hR, hB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hxW)
  have hball := huW.ae_finite_and_integrableOn_ball μ x hR hB hx
  exact ⟨ball x R, isOpen_ball, mem_ball_self hR, hball.1, hball.2.1⟩

theorem PlurisubharmonicAt.integrableAtFilter_toReal
    (hu : PlurisubharmonicAt u x) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hx : u x ≠ ⊥) : IntegrableAtFilter (fun y => (u y).toReal) (𝓝 x) μ := by
  obtain ⟨V, hV, hxV, _, hI⟩ := hu.mem_pshIntegrabilityLocus μ hx
  exact ⟨V, hV.mem_nhds hxV, hI⟩

/-- At every PSH germ, the good locus contains its limit points. A nearby
finite center is obtained from positive measure, not from upper semicontinuity. -/
theorem PlurisubharmonicAt.mem_pshIntegrabilityLocus_of_mem_closure
    (hu : PlurisubharmonicAt u x) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hx : x ∈ closure (pshIntegrabilityLocus u μ)) :
    x ∈ pshIntegrabilityLocus u μ := by
  obtain ⟨W, hW, hxW, huW⟩ := hu
  obtain ⟨R, hR, hB⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hxW)
  obtain ⟨z, hzG, hxz⟩ := Metric.mem_closure_iff.mp hx (R / 4) (by positivity)
  obtain ⟨V, hV, hzV, hae, _⟩ := hzG
  have hzB : z ∈ ball x (R / 4) := by
    simpa only [mem_ball, dist_comm] using hxz
  have hpos : 0 < μ (V ∩ ball x (R / 4)) :=
    (hV.inter isOpen_ball).measure_pos μ ⟨z, hzV, hzB⟩
  have hae' : ∀ᵐ y ∂μ.restrict (V ∩ ball x (R / 4)), u y ≠ ⊤ ∧ u y ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hae
  obtain ⟨y, hy, hfin⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae (μ := μ) hpos.ne' hae'
  have hyx : dist y x < R / 4 := hy.2
  have hxB : x ∈ ball y (R / 2) := by
    rw [mem_ball, dist_comm]
    linarith
  have hyB : closedBall y (R / 2) ⊆ W := by
    intro w hw
    apply hB
    rw [mem_closedBall] at hw ⊢
    have htriangle := dist_triangle w y x
    linarith
  have hball := huW.ae_finite_and_integrableOn_ball μ y (by positivity) hyB hfin.2
  exact ⟨ball y (R / 2), isOpen_ball, hxB, hball.1, hball.2.1⟩

/-- One finite point propagates the good locus throughout a preconnected set
of PSH germs. The set need not itself be open. -/
theorem PlurisubharmonicOn.subset_pshIntegrabilityLocus {U : Set E}
    (hu : PlurisubharmonicOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hU : IsPreconnected U) (hne : ∃ a ∈ U, u a ≠ ⊥) :
    U ⊆ pshIntegrabilityLocus u μ := by
  obtain ⟨a, haU, ha⟩ := hne
  apply hU.subset_of_closure_inter_subset (isOpen_pshIntegrabilityLocus u μ)
    ⟨a, haU, (hu a haU).mem_pshIntegrabilityLocus μ ha⟩
  rintro x ⟨hxG, hxU⟩
  exact (hu x hxU).mem_pshIntegrabilityLocus_of_mem_closure μ hxG

/-- A nontrivial PSH potential is locally integrable on every preconnected
domain of its ambient germs. -/
theorem PlurisubharmonicOn.locallyIntegrableOn_toReal {U : Set E}
    (hu : PlurisubharmonicOn u U) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hU : IsPreconnected U) (hne : ∃ a ∈ U, u a ≠ ⊥) :
    LocallyIntegrableOn (fun x => (u x).toReal) U μ := by
  intro x hx
  obtain ⟨V, hV, hxV, _, hI⟩ := hu.subset_pshIntegrabilityLocus μ hU hne hx
  exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), hI⟩

end SGPT.Foundations.Analysis
