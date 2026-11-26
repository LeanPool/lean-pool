/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73RealPath
public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM11.Walks
public import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM12.Section2RegionPathDeformation
import LeanPool.GraphMinor.GM11.LocalCone
import LeanPool.GraphMinor.GM11.PathClasses
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# A region visit deforms to prescribed spoke paths

For the representativity step of XII (7.3), page 261, use the trace
of a normal curve in the new radial drawing. On each region visit,
the entry comparison deforms the original segment to its two
spokes. A line is simply connected, so those spoke paths can be
replaced by any prescribed parametrizations with the same ends.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- One region interval of a trace is homotopic to its two
prescribed edge paths. This is the local trace-to-path comparison
used for representativity in XII (7.3), page 261. -/
theorem region_visit_homotopic_to_edge_paths
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ K : Drawing S} (hK : PreRad (PaintingOrDrawing.drawing Γ) K)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c)
    {u v w : S} (hfa : f a = u) (hfc : f c = v)
    (hu : u ∈ Γ.V) (hv : v ∈ Γ.V)
    {r e e' : Set S} (hr : r ∈ Γ.R) (hw : w ∈ r)
    (h₁ : K.toGraph.IsLink e u w) (h₂ : K.toGraph.IsLink e' w v)
    (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (hleave : LeavesLike f a c e r u w) (henter : EntersLike f a c e' r v w)
    (q : ∀ g x y, K.toGraph.IsLink g x y → Path x y)
    (hq : ∀ g x y (h : K.toGraph.IsLink g x y), range (q g x y h) ⊆ closure g) :
    ((realIntervalPath f hf a c).cast hfa.symm hfc.symm).Homotopic
      ((q e u w h₁).trans (q e' w v h₂)) := by
  let γ := (realIntervalPath f hf a c).cast hfa.symm hfc.symm
  let P : Path (⟨u, mem_univ u⟩ : (univ : Set S)) ⟨v, mem_univ v⟩ := {
    toFun := fun t => ⟨γ t, mem_univ _⟩
    continuous_toFun := γ.continuous.subtype_mk _
    source' := Subtype.ext γ.source
    target' := Subtype.ext γ.target }
  have huE : u ∉ e := fun hx => (h₁.1.2.1 hx).2 h₁.2.1
  have hwE : w ∉ e := fun hx => (h₁.1.2.1 hx).2 h₁.2.2.1
  have hvE' : v ∉ e' := fun hx => (h₂.1.2.1 hx).2 h₂.2.2.1
  have hwE' : w ∉ e' := fun hx => (h₂.1.2.1 hx).2 h₂.2.1
  have huw : u ≠ w := fun h => region_subset hr (h ▸ hw) (Γ.V_subset_U hu)
  have hvw : v ≠ w := fun h => region_subset hr (h ▸ hw) (Γ.V_subset_U hv)
  obtain ⟨α, β, _, _, hαrange, hβrange, _, _, hhom⟩ :=
    region_path_homotopic_to_spokes (hK.1.2 r hr) (subset_univ _) (mem_univ u) (mem_univ v)
      hw huE hwE huw hvE' hwE' hvw hf hac hfa hfc hfr hleave henter P (fun _ => rfl)
  have hhomS := hhom.map (⟨Subtype.val, continuous_subtype_val⟩ : C((univ : Set S), S))
  change γ.Homotopic ((α.trans β.symm).map continuous_subtype_val) at hhomS
  rw [Path.map_trans, ← Path.map_symm] at hhomS
  have hα : (α.map continuous_subtype_val).Homotopic (q e u w h₁) := by
    obtain ⟨p, _, _⟩ := isLine_closure h₁.1 huw h₁.2.2.2
    apply GM11.IsSimplyConnectedSet.flat (GM11.IsLine.isSimplyConnected (L := closure e) ⟨p⟩)
    · intro t
      exact hαrange.subset (mem_range_self t)
    · intro t
      exact hq e u w h₁ (mem_range_self t)
  have hβ : (β.map continuous_subtype_val).symm.Homotopic (q e' w v h₂) := by
    obtain ⟨p, _, _⟩ := isLine_closure h₂.1 hvw.symm h₂.2.2.2
    apply GM11.IsSimplyConnectedSet.flat (GM11.IsLine.isSimplyConnected (L := closure e') ⟨p⟩)
    · intro t
      change (β (σ t)).val ∈ closure e'
      exact hβrange.subset (mem_range_self (σ t))
    · intro t
      exact hq e' w v h₂ (mem_range_self t)
  exact hhomS.trans (hα.hcomp hβ)

end GraphMinor.GM12
