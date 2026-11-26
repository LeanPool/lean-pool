/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Walks
public import Mathlib.Topology.Homotopy.Path
import LeanPool.GraphMinor.GM12.Section73WalkPointSets
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.PathClasses
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Paths realizing radial walks

For the representativity step of XII (7.3), page 261, realize each
edge of a radial walk by a path in its closure and concatenate these
paths. The resulting path stays in the walk drawing. A short closed
walk lies in its simply connected inside, by XI (8.5), so the path
is null-homotopic. This will pass through the star-collapse map.
-/

public section

namespace GraphMinor.GM12

open Set Topology Graph Surface GM11

/-- A loopless drawing admits paths parametrizing every oriented
edge closure. These realize the radial edges in XII (7.3). -/
theorem exists_edge_paths
    {S : Type*} [TopologicalSpace S] {K : Drawing S}
    (hloopless : ∀ e x y, K.toGraph.IsLink e x y → x ≠ y) :
    ∃ p : ∀ e x y, K.toGraph.IsLink e x y → Path x y,
      ∀ e x y (h : K.toGraph.IsLink e x y), range (p e x y h) = closure e := by
  classical
  have hex : ∀ e x y (h : K.toGraph.IsLink e x y),
      ∃ p : Path x y, range p = closure e := by
    intro e x y h
    obtain ⟨p, hp0, hp1⟩ := isLine_closure h.1 (hloopless e x y h) h.2.2.2
    let q : Path x y := {
      toFun := fun t => (p t).val
      continuous_toFun := continuous_subtype_val.comp p.continuous
      source' := hp0
      target' := hp1 }
    refine ⟨q, ?_⟩
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact (p t).property
    · intro hz
      exact ⟨p.symm ⟨z, hz⟩, congrArg Subtype.val (p.apply_symm_apply ⟨z, hz⟩)⟩
  choose p hp using hex
  exact ⟨p, hp⟩

/-- Realize a graph walk using prescribed paths for its oriented
edges. This is a parametrization of the walks in XII (7.3), page 261. -/
@[expose] noncomputable def walkPath
    {S E : Type*} [TopologicalSpace S] {G : Graph S E}
    (p : ∀ e x y, G.IsLink e x y → Path x y) {a b : S} : GraphWalk G a b → Path a b
  | .nil _ => Path.refl _
  | .cons (u := x) (v := y) (e := e) h W => (p e x y h).trans (walkPath p W)

/-- Realizing a concatenated walk agrees up to homotopy with
concatenating its realized paths. -/
theorem walkPath_append_homotopic
    {S E : Type*} [TopologicalSpace S] {G : Graph S E}
    (p : ∀ e x y, G.IsLink e x y → Path x y)
    {a b c : S} (W : GraphWalk G a b) (W' : GraphWalk G b c) :
    (walkPath p (W.append W')).Homotopic ((walkPath p W).trans (walkPath p W')) := by
  induction W with
  | nil h => exact (Path.Homotopic.refl_trans (walkPath p W')).symm
  | @cons x y z e h W ih =>
    exact ((Path.Homotopic.refl (p e x y h)).hcomp (ih W')).trans
      (Path.Homotopic.trans_assoc (p e x y h) (walkPath p W) (walkPath p W')).symm

/-- Edge paths in their closures realize the walk within its point
set. This controls the paths used in XII (7.3), page 261. -/
theorem range_walkPath_subset
    {S : Type*} [TopologicalSpace S] [T2Space S] {K : Drawing S}
    (p : ∀ e x y, K.toGraph.IsLink e x y → Path x y)
    (hp : ∀ e x y (h : K.toGraph.IsLink e x y), range (p e x y h) ⊆ closure e)
    {a b : S} (W : GraphWalk K.toGraph a b) :
    range (walkPath p W) ⊆ (walkDrawing K W).U := by
  induction W with
  | nil h =>
    change range (Path.refl _) ⊆ _
    rw [Path.refl_range]
    exact (walkDrawing_nil_points h).symm.subset
  | @cons x y z e h W ih =>
    change range ((p e x y h).trans (walkPath p W)) ⊆ _
    rw [Path.trans_range, walkDrawing_cons_points]
    exact union_subset_union (hp e x y h) ih

/-- A path realizing a short closed walk of a slope is
null-homotopic. Its range lies in `ins(W)`, which is simply connected
by XI (8.5). This supplies the old-walk step for the representativity
argument in XII (7.3), page 261. -/
theorem walkPath_homotopic_refl_of_short_slope
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope K k ins)
    (p : ∀ e x y, K.toGraph.IsLink e x y → Path x y)
    (hp : ∀ e x y (h : K.toGraph.IsLink e x y), range (p e x y h) ⊆ closure e)
    {a : S} (W : GraphWalk K.toGraph a a) (hshort : W.length < k) :
    (walkPath p W).Homotopic (Path.refl a) := by
  have hrest := (GM11.theorem_8_5_proof hS hs W hshort).1
  have hpoints : ∀ t, walkPath p W t ∈ insWalk ins K W := fun t =>
    Or.inl (range_walkPath_subset p hp W (mem_range_self t))
  have ha : a ∈ insWalk ins K W := by simpa using hpoints 0
  exact GM11.IsSimplyConnectedSet.flat hrest.isSimplyConnected
    (walkPath p W) (Path.refl a) hpoints (fun _ => ha)

end GraphMinor.GM12
