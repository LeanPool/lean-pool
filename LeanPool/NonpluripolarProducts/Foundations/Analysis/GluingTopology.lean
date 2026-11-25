/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# The topological part of the gluing argument

The upstream source credits a gluing argument from a draft of the
transcendental Nakamaye manuscript. The lemmas concern collar agreement and
the selection of a finite continuous branch near a pole of an upper
semicontinuous function.
[Upstream Lean source](https://github.com/MingchenXia/SGPT-lean/blob/76cbff42fbefc4c953a0ea0ba5b6948ac20c69b3/SGPT/Foundations/Analysis/GluingTopology.lean).
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis

variable {X : Type*} [TopologicalSpace X]

/-- Strict separation of a USC branch and an LSC branch persists locally. -/
theorem eventually_lt_of_semicontinuous {A : Type*} [LinearOrder A]
    [DenselyOrdered A] {f g : X → A} {x : X}
    (hg : UpperSemicontinuousAt g x) (hf : LowerSemicontinuousAt f x)
    (h : g x < f x) : ∀ᶠ y in 𝓝 x, g y < f y := by
  obtain ⟨c, hgc, hcf⟩ := exists_between h
  filter_upwards [hg c hgc, hf c hcf] with y hgy hfy
  exact hgy.trans hfy

/-- At a pole, an upper semicontinuous extended-real branch is eventually
strictly below a finite continuous branch. -/
theorem eventually_lt_real_of_eq_bot {g : X → EReal} {f : X → ℝ} {x : X}
    (hg : UpperSemicontinuousAt g x) (hbot : g x = ⊥)
    (hf : ContinuousAt f x) : ∀ᶠ y in 𝓝 x, g y < (f y : EReal) := by
  apply eventually_lt_of_semicontinuous hg
    (continuous_coe_real_ereal.continuousAt.comp hf).lowerSemicontinuousAt
  simp [hbot]

/-- This is the local branch equality used to deduce smoothness in gluing. -/
theorem eventually_max_eq_real_of_eq_bot {g : X → EReal} {f : X → ℝ} {x : X}
    (hg : UpperSemicontinuousAt g x) (hbot : g x = ⊥)
    (hf : ContinuousAt f x) :
    (fun y => max (f y : EReal) (g y)) =ᶠ[𝓝 x] (fun y => (f y : EReal)) := by
  filter_upwards [eventually_lt_real_of_eq_bot hg hbot hf] with y hy
  exact max_eq_left hy.le

section Collar

variable {A : Type*} [LinearOrder A]

/-- Local maximum on `U`, equal to the global branch outside `U`. -/
noncomputable def gluedMax (U : Set X) (f g : X → A) (x : X) : A := by
  classical
  exact if x ∈ U then max (f x) (g x) else g x

omit [TopologicalSpace X] in
theorem gluedMax_eq_max {U : Set X} {f g : X → A} {x : X} (hx : x ∈ U) :
    gluedMax U f g x = max (f x) (g x) := by
  simp [gluedMax, hx]

omit [TopologicalSpace X] in
/-- The collar inequality makes the two formulae agree, including at poles. -/
theorem gluedMax_eq_global {U U' : Set X} {f g : X → A}
    (hcollar : ∀ x ∈ U \ U', f x ≤ g x) {x : X} (hx : x ∉ U') :
    gluedMax U f g x = g x := by
  classical
  by_cases hxU : x ∈ U
  · simp [gluedMax, hxU, max_eq_right (hcollar x ⟨hxU, hx⟩)]
  · simp [gluedMax, hxU]

theorem gluedMax_eventually_eq_max {U : Set X} {f g : X → A}
    (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    gluedMax U f g =ᶠ[𝓝 x] (fun y => max (f y) (g y)) := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact gluedMax_eq_max hy

/-- A smaller neighborhood whose closure lies inside `U` supplies an open
collar on which the glued function is the global branch. -/
theorem gluedMax_eventually_eq_global {U U' : Set X} {f g : X → A}
    (hclosure : closure U' ⊆ U) (hcollar : ∀ x ∈ U \ U', f x ≤ g x)
    {x : X} (hx : x ∉ U) : gluedMax U f g =ᶠ[𝓝 x] g := by
  have hx' : x ∈ (closure U')ᶜ := fun hc => hx (hclosure hc)
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
  exact gluedMax_eq_global hcollar (fun h => hy (subset_closure h))

/-- Every point has one of the two local descriptions used by the analytic
maximum-stability argument. -/
theorem gluedMax_local {U U' : Set X} {f g : X → A}
    (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hcollar : ∀ x ∈ U \ U', f x ≤ g x) (x : X) :
    (x ∈ U ∧ gluedMax U f g =ᶠ[𝓝 x] (fun y => max (f y) (g y))) ∨
      gluedMax U f g =ᶠ[𝓝 x] g := by
  by_cases hx : x ∈ U
  · exact Or.inl ⟨hx, gluedMax_eventually_eq_max hU hx⟩
  · exact Or.inr (gluedMax_eventually_eq_global hclosure hcollar hx)

/-- Upper semicontinuity survives the collar gluing. Positivity of currents
requires the separate analytic maximum principle. -/
theorem gluedMax_upperSemicontinuous {U U' : Set X} {f g : X → A}
    (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hcollar : ∀ x ∈ U \ U', f x ≤ g x)
    (hf : ∀ x ∈ U, UpperSemicontinuousAt f x) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous (gluedMax U f g) := by
  intro x c hc
  by_cases hx : x ∈ U
  · rw [gluedMax_eq_max (f := f) (g := g) hx] at hc
    obtain ⟨hfc, hgc⟩ := max_lt_iff.mp hc
    filter_upwards [gluedMax_eventually_eq_max (f := f) (g := g) hU hx,
      hf x hx c hfc, hg x c hgc]
      with y hy hfy hgy
    rw [hy]
    exact max_lt hfy hgy
  · have hgc : g x < c := by simpa [gluedMax, hx] using hc
    filter_upwards [gluedMax_eventually_eq_global hclosure hcollar hx, hg x c hgc]
      with y hy hgy
    simpa only [hy] using hgy

end Collar

/-- The actual patched function selects its finite continuous branch near a
pole in the inner region. The conclusion is an equality of germs. -/
theorem gluedMax_eventually_eq_real {U : Set X} {f : X → ℝ} {g : X → EReal}
    (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (hg : UpperSemicontinuousAt g x) (hbot : g x = ⊥)
    (hf : ContinuousAt f x) :
    gluedMax U (fun y => (f y : EReal)) g =ᶠ[𝓝 x] (fun y => (f y : EReal)) :=
  (gluedMax_eventually_eq_max hU hx).trans
    (eventually_max_eq_real_of_eq_bot hg hbot hf)

end SGPT.Foundations.Analysis
