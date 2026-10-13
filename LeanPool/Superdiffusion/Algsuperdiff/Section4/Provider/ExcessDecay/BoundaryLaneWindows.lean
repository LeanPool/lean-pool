/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorGeometry

/-!
# BoundaryLaneWindows

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The truncated comparison windows of the boundary lane, and the choice `y := x`

The §4.3 boundary regime works on the *truncated* windows

```text
  W_j := (x + □_{n-j}) ∩ □_m ,        V := W_2 = (x + □_{n-2}) ∩ □_m ,
```

which are the windows of `l.excess.decay.good.scales` read through the replacement draft's
item 2 (the lemma `l.comparison.reduction`).  This
module proves their geometry and the one statement the draft calls the *window choice*.

## The window choice

The printed proof asks for a point `y ∈ □_m` with **both**

```text
  y + □_{n-2} ⊆ (z + □_n) ∩ □_m       and      (x + □_{n-2}) ∩ □_m ⊆ y + □_{n-2} ,
```

and the graph records the gap: "the existence of `y` with BOTH inclusions is
asserted with no construction, and in the boundary case the two requirements
pull against each other" — indeed the first inclusion is *false* at a boundary
point `x`, because the full cube `y + □_{n-2}` then leaves `□_m`.

The draft's correction is `y := x` together with the move of the
comparison function onto the truncated window: the pair of requirements
becomes

```text
  V = (x + □_{n-2}) ∩ □_m ⊆ (z + □_n) ∩ □_m       and      W_2 = V ,
```

and both are then immediate from `x ∈ (z + □_{n-3}) ∩ □_m`.  That is
`truncatedWindow_subset_of_windowChoice` and `truncatedWindow_two_eq_V` below;
`windowChoice_y_eq_x` packages the pair.

## What is not done here

Nothing analytic: no harmonic function, no excess, no Caccioppoli estimate.  In
particular this module does **not** provide the volume-ratio (`window sandwich`)
constant `K_vol` of the draft's §0 — only the qualitative positivity of the
window volume, which is what the excess normalizers need to be finite.

## References

* ABK26, `l.excess.decay.good.scales`, (windows).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. A general inclusion for translated origin cubes -/

/-! ## 2. The truncated windows -/

/-- **The truncated window** `(x + □_k) ∩ □_m` of the §4.3 boundary regime, in the
frozen theorem's own carrier shape (a translation *image* of an origin cube,
intersected with the domain cube). -/
def truncatedWindow (x : Vec d) (m k : ℤ) : Set (Vec d) :=
  ((fun y => x + y) '' openCubeSet (originCube d k)) ∩
    openCubeSet (originCube d m)

theorem truncatedWindow_eq_inter_openCubeAtScale (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k =
      openCubeAtScale x k ∩ openCubeSet (originCube d m) := by
  rw [truncatedWindow, openCubeAtScale_eq_image_add]

theorem truncatedWindow_subset_translate (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k ⊆ (fun y => x + y) '' openCubeSet (originCube d k) :=
  Set.inter_subset_left

theorem truncatedWindow_subset_domain (x : Vec d) (m k : ℤ) :
    truncatedWindow x m k ⊆ openCubeSet (originCube d m) :=
  Set.inter_subset_right

/-- The truncated windows are nested in the scale. -/
theorem truncatedWindow_mono (x : Vec d) (m : ℤ) {k l : ℤ} (hkl : k ≤ l) :
    truncatedWindow x m k ⊆ truncatedWindow x m l := by
  refine Set.inter_subset_inter_left _ ?_
  rintro p ⟨y, hy, rfl⟩
  exact ⟨y, openCubeSet_originCube_subset_of_le hkl hy, rfl⟩

/-- The centre of a truncated window lies in it, as soon as it lies in the
domain cube. -/
theorem mem_truncatedWindow_self {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) : x ∈ truncatedWindow x m k :=
  ⟨⟨0, zero_mem_openCubeSet_originCube d k, by simp⟩, hx⟩

theorem truncatedWindow_nonempty {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) :
    (truncatedWindow x m k).Nonempty :=
  ⟨x, mem_truncatedWindow_self k hx⟩

/-! ## 3. The windows are open bounded convex domains -/

/-- The intersection of two open bounded convex domains is one. -/
theorem isOpenBoundedConvexDomain_inter {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hV : IsOpenBoundedConvexDomain V) :
    IsOpenBoundedConvexDomain (U ∩ V) := by
  obtain ⟨R, hRpos, hR⟩ := hU.isBoundedDomain
  exact ⟨hU.isOpen.inter hV.isOpen, ⟨R, hRpos, fun y hy i => hR y hy.1 i⟩,
    hU.convex.inter hV.convex⟩

theorem isOpenBoundedConvexDomain_truncatedWindow (x : Vec d) (m k : ℤ) :
    IsOpenBoundedConvexDomain (truncatedWindow x m k) := by
  refine isOpenBoundedConvexDomain_inter ?_ (isOpenBoundedConvexDomain_openCubeSet _)
  rw [image_add_eq_translateSet]
  exact (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet x

theorem isOpen_truncatedWindow (x : Vec d) (m k : ℤ) :
    IsOpen (truncatedWindow x m k) :=
  (isOpenBoundedConvexDomain_truncatedWindow x m k).isOpen

theorem convex_truncatedWindow (x : Vec d) (m k : ℤ) :
    Convex ℝ (truncatedWindow x m k) :=
  (isOpenBoundedConvexDomain_truncatedWindow x m k).convex

theorem volume_truncatedWindow_lt_top (x : Vec d) (m k : ℤ) :
    MeasureTheory.volume (truncatedWindow x m k) < ⊤ :=
  (isOpenBoundedConvexDomain_truncatedWindow x m k).volume_lt_top

/-- A truncated window centred in the domain cube has positive volume: it is a
nonempty open set. -/
theorem volume_truncatedWindow_pos {x : Vec d} {m : ℤ} (k : ℤ)
    (hx : x ∈ openCubeSet (originCube d m)) :
    0 < MeasureTheory.volume (truncatedWindow x m k) :=
  (isOpen_truncatedWindow x m k).measure_pos MeasureTheory.volume
    (truncatedWindow_nonempty k hx)

/-! ## 4. The window choice `y := x` -/

/-- The printed hypothesis `x ∈ (z + □_j) ∩ □_m` in its difference form. -/
theorem sub_mem_openCubeSet_of_mem_truncatedWindow {j m : ℤ} {x z : Vec d}
    (hx : x ∈ truncatedWindow z m j) :
    x - z ∈ openCubeSet (originCube d j) := by
  obtain ⟨y0, hy0mem, hy0⟩ := hx.1
  have hxy : x - z = y0 := by
    rw [← hy0]
    exact add_sub_cancel_left z y0
  rwa [hxy]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
