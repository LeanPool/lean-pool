/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Regions

/-!
# Parameter endpoints of trace steps

The trace definition in XII, page 243, divides a period of the curve
at its visits to vertices. This file records that each sequence of
steps has the stated endpoint images and nondecreasing parameter
bounds. It also proves uniqueness of the next vertex parameter: a
normal region segment cannot contain another vertex visit.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A sequence of trace steps has the claimed endpoint images, both
endpoints in the original vertex set, and nondecreasing parameter
bounds. This follows by removing the first two edges at each step. -/
theorem traceSteps_parameters {S : Type*} [TopologicalSpace S]
    {Γ K : Drawing S} {f : ℝ → S} {a b : ℝ} {u v : S}
    (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W) :
    a ≤ b ∧ f a = u ∧ u ∈ Γ.V ∧ f b = v ∧ v ∈ Γ.V := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    obtain ⟨rfl, hfu, hu⟩ := hW
    exact ⟨le_rfl, hfu, hu, hfu, hu⟩
  | cons hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv =>
      rw [hrestcase] at hW
      exact hW.elim
    | cons hlink' rest =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, _, _, r, hr, _, _, _, _, hrest⟩ := hW
      obtain ⟨hcb, _, _, hfb, hv⟩ := traceSteps_parameters rest hrest
      exact ⟨hac.le.trans hcb, hfa, hu, hfb, hv⟩
termination_by W.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- The next vertex parameter of a region segment is unique. A smaller
candidate would place a vertex in the open region segment of the other
candidate, which normality excludes. -/
theorem next_vertex_parameter_unique {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {f : ℝ → S} {a c c' : ℝ}
    (hac : a < c) (hac' : a < c')
    (hc : f c ∈ Γ.V) (hc' : f c' ∈ Γ.V)
    {r r' : Set S} (hr : r ∈ Γ.R) (hr' : r' ∈ Γ.R)
    (hf : ∀ t ∈ Ioo a c, f t ∈ r) (hf' : ∀ t ∈ Ioo a c', f t ∈ r') : c = c' := by
  apply le_antisymm
  · by_contra hle
    have hlt : c' < c := lt_of_not_ge hle
    exact region_subset hr (hf c' ⟨hac', hlt⟩) (Γ.V_subset_U hc')
  · by_contra hle
    have hlt : c < c' := lt_of_not_ge hle
    exact region_subset hr' (hf' c ⟨hac, hlt⟩) (Γ.V_subset_U hc)

end GraphMinor.GM12
