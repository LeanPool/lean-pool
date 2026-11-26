/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkPaths
public import LeanPool.GraphMinor.GM12.Section73WalkSubstitution
import LeanPool.GraphMinor.GM11.LocalCone
import LeanPool.GraphMinor.GM11.PathClasses

/-!
# Homotopy of realized lifted walks

For the representativity step of XII (7.3), page 261, realize a new
walk by paths in its edge closures. Realize each old replacement
path as well. After the collapse, its range lies in the new edge
closure, a line. The two paths are therefore homotopic with fixed
ends. Concatenating these homotopies compares the whole walks.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Apply a continuous map to a path when its two ends are fixed.
This retains the original endpoint types in the homotopy comparison
for XII (7.3). -/
@[expose] def mapPathFixed
    {S : Type*} [TopologicalSpace S] (f : C(S, S)) {a b : S}
    (ha : f a = a) (hb : f b = b) (p : Path a b) : Path a b :=
  (p.map f.continuous).cast ha.symm hb.symm

private theorem mapPathFixed_refl
    {S : Type*} [TopologicalSpace S] (f : C(S, S)) {a : S} (ha : f a = a) :
    mapPathFixed f ha ha (Path.refl a) = Path.refl a := by
  ext t
  exact ha

private theorem mapPathFixed_trans
    {S : Type*} [TopologicalSpace S] (f : C(S, S)) {a b c : S}
    (ha : f a = a) (hb : f b = b) (hc : f c = c) (p : Path a b) (q : Path b c) :
    mapPathFixed f ha hc (p.trans q) =
      (mapPathFixed f ha hb p).trans (mapPathFixed f hb hc q) := by
  unfold mapPathFixed
  rw [Path.map_trans, Path.cast_trans _ _ ha.symm hb.symm hc.symm]

private theorem mapPathFixed_homotopic
    {S : Type*} [TopologicalSpace S] (f : C(S, S)) {a b : S}
    (ha : f a = a) (hb : f b = b) {p q : Path a b} (hpq : p.Homotopic q) :
    (mapPathFixed f ha hb p).Homotopic (mapPathFixed f ha hb q) :=
  (hpq.map f).pathCast ha.symm hb.symm

open Classical in
/-- The realized lifted walk maps to a path homotopic to the
realized new walk, with the exact length increase in XII (7.3),
page 261. Edge images lie in lines, so their endpoint-preserving
homotopies concatenate. -/
theorem exists_closed_walk_path_lift
    {S : Type*} [TopologicalSpace S] [T2Space S] {J K : Drawing S} {v : S}
    (f : C(S, S)) (hfix : ∀ x ∈ J.V, f x = x) (hV : J.V ⊆ K.V)
    (hloopless : ∀ e x y, J.toGraph.IsLink e x y → x ≠ y)
    (hline : ∀ e ∈ J.E, IsLine (closure e))
    (p : ∀ e x y, K.toGraph.IsLink e x y → Path x y)
    (hp : ∀ e x y (h : K.toGraph.IsLink e x y), range (p e x y h) ⊆ closure e)
    (q : ∀ e x y, J.toGraph.IsLink e x y → Path x y)
    (hq : ∀ e x y (h : J.toGraph.IsLink e x y), range (q e x y h) ⊆ closure e)
    (hpaths : ∀ e x y, J.toGraph.IsLink e x y →
      ∃ P : GraphWalk K.toGraph x y,
        P.length = (if x = v ∨ y = v then 2 else 1) ∧
        f '' (walkDrawing K P).U = closure e)
    {a : S} (W : GraphWalk J.toGraph a a) :
    let hfa : f a = a := hfix a (W.mem_vertexSet_of_mem_support W.start_mem_support)
    ∃ W' : GraphWalk K.toGraph a a,
      W'.length = W.length + 2 * walkVertexCount v W ∧
      (mapPathFixed f hfa hfa (walkPath p W')).Homotopic (walkPath q W) := by
  let I : S → ℕ := fun x => if x = v then 1 else 0
  have hlift : ∀ {x y : S} (Q : GraphWalk J.toGraph x y) (hx : x ∈ J.V) (hy : y ∈ J.V),
      ∃ Q' : GraphWalk K.toGraph x y,
        (Q'.length + I x = Q.length + 2 * walkVertexCount v Q + I y) ∧
        (mapPathFixed f (hfix x hx) (hfix y hy) (walkPath p Q')).Homotopic (walkPath q Q) := by
    intro x y Q
    induction Q with
    | nil h =>
      intro hx hy
      refine ⟨.nil (hV h), by rfl, ?_⟩
      change (mapPathFixed f (hfix _ hx) (hfix _ hx) (Path.refl _)).Homotopic (Path.refl _)
      rw [mapPathFixed_refl]
    | @cons x y z e h Q ih =>
      intro hx hz
      have hy : y ∈ J.V := h.2.2.1
      obtain ⟨P, hP, hPimage⟩ := hpaths e x y h
      obtain ⟨Q', hQlen, hQhom⟩ := ih hy hz
      have hedge : (mapPathFixed f (hfix x hx) (hfix y hy) (walkPath p P)).Homotopic (q e x y h)
        := by
        apply GM11.IsSimplyConnectedSet.flat (GM11.IsLine.isSimplyConnected (hline e h.1))
        · intro t
          apply hPimage.subset
          exact ⟨walkPath p P t, range_walkPath_subset p hp P (mem_range_self t), rfl⟩
        · intro t
          exact hq e x y h (mem_range_self t)
      refine ⟨P.append Q', ?_, ?_⟩
      · exact replacement_append_length (h := h) (hloopless e x y h) hP hQlen
      · have happend := mapPathFixed_homotopic f (hfix x hx) (hfix z hz)
          (walkPath_append_homotopic p P Q')
        rw [mapPathFixed_trans f (hfix x hx) (hfix y hy) (hfix z hz)] at happend
        exact happend.trans (hedge.hcomp hQhom)
  have ha : a ∈ J.V := W.mem_vertexSet_of_mem_support W.start_mem_support
  obtain ⟨W', hWlen, hWhom⟩ := hlift W ha ha
  exact ⟨W', Nat.add_right_cancel hWlen, hWhom⟩

end GraphMinor.GM12
