/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.Minor.Model
import LeanPool.GraphMinor.GM12.Section4Model
import LeanPool.GraphMinor.GM12.Section4ModelBack
import LeanPool.GraphMinor.GM12.Section4ModelComposition
import LeanPool.GraphMinor.Minor.Basic

/-!
# Preserving control while merging branches

For XII (4.2), page 249, compose a target minor model with the controlled
model. A new branch is a union of old branches. It contains at least one
old branch, so it cannot lie on a small side of order below the new
vertex count. That count is at most the old vertex count because the
target model has disjoint nonempty branches.
-/

public section

namespace GraphMinor.GM12

open Set Graph Hypergraph

/-- The contraction and deletion steps of XII (4.2), page 249, given a
model of the target minor. Each new branch contains an old branch. -/
theorem controlsMinor_of_target_model {α β γ δ γ' δ' : Type*}
    {G : Graph α β} (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {L : Graph γ δ} {L' : Graph γ' δ'}
    {ηv : γ → Set γ'} {ηe : δ → δ'} (hm : IsMinorModel L L' ηv ηe)
    (hV' : L'.vertexSet.Finite) {θ : ℕ}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hc : ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L') :
    ControlsMinor (Hypergraph.ofGraph G hV hE) θ T L := by
  obtain ⟨a, b, hmodel, hcard, hcontrol⟩ := controlsMinor_has_minorModel hV hE hc
  have hcount := minorModel_vertex_ncard_le hm hV'
  apply controlsMinor_of_minorModel hV hE (minorModel_comp hm hmodel) (hcount.trans hcard)
  intro A B hAB ho v hv hsub
  obtain ⟨w, hw⟩ := hm.vertex_nonempty v hv
  apply hcontrol A B hAB (ho.trans_le hcount) w (hm.vertex_subset v hv hw)
  intro x hx
  exact hsub (mem_iUnion₂.mpr ⟨w, hw, hx⟩)

end GraphMinor.GM12
