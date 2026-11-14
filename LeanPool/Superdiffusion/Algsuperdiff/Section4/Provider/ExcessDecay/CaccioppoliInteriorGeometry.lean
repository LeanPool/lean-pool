/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Definitions

/-!
# CaccioppoliInteriorGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior-regime geometry of the coarse-grained Caccioppoli window

The frozen §4.3 anchor's second conjunct (the *frontier-empty* clause) is gated
on

```text
  ((z + □_{n+2}) image) ∩ frontier (□_m) = ∅ .
```

This module turns that gate into the two geometric facts the coarse-grained
Caccioppoli step needs, and matches the window triple of ABK26's
`l.coarse.grained.Caccioppoli.RHS` to CoarseGraining's own `caccioppoliCoreSet`.

## What the gate buys

`image_add_openCubeSet_subset_of_frontier_inter_empty`: the translated parent
cube is *contained* in `□_m`.  The proof is topological, not coordinatewise: the
translated open cube is convex, hence preconnected; the complement of
`frontier □_m` is the disjoint union of the open set `□_m` and the open set
`(closure □_m)ᶜ`; a preconnected set inside that union which meets `□_m` lies in
`□_m`.  It meets `□_m` because `z ∈ □_m` and `0 ∈ □_{n+2}`.

## The Caccioppoli window triple is CoarseGraining's own

```text
  caccioppoliCoreSet Q x = openCubeSet Q ∩ openCubeAtScale x (Q.scale - 2) .
```

## Carrier convention (resolution A4)

Every cube is an *origin* cube; a window centred at `z` is realized by
translating the sample.  The geometry lemmas below therefore appear twice: once
for the untranslated image `(fun y => z + y) '' □_k` used by the frozen
statement, and once for the shifted centre `w = x - z` used by the translated
frame in which the Caccioppoli is applied.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`.
* ABK26, `e.energy.bound.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. Translations: images and `translateSet` -/

/-- The frozen statement's translated window is CoarseGraining's `translateSet`. -/
theorem image_add_eq_translateSet (z : Vec d) (S : Set (Vec d)) :
    (fun y => z + y) '' S = translateSet z S := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [add_comm]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [add_comm]⟩

/-- CoarseGraining's `openCubeAtScale` at a real centre is the frozen statement's
translated origin cube. -/
theorem openCubeAtScale_eq_image_add (z : Vec d) (m : ℤ) :
    openCubeAtScale z m = (fun y => z + y) '' openCubeSet (originCube d m) := by
  rw [image_add_eq_translateSet, openCubeAtScale_eq_translateSet z m,
    openCubeAtScale_zero_eq_openCubeSet_originCube]

/-! ## 2. The gate: a preconnected set off the frontier stays inside -/

/-- **A preconnected set which meets an open set and misses its frontier lies
inside it.**  The complement of `frontier U` is the disjoint union of the two
open sets `U` (for open `U`, `interior U = U`) and `(closure U)ᶜ`. -/
theorem subset_of_isPreconnected_of_frontier_inter_empty {S U : Set (Vec d)}
    (hS : IsPreconnected S) (hU : IsOpen U) (hne : (S ∩ U).Nonempty)
    (hfr : S ∩ frontier U = ∅) : S ⊆ U := by
  have hdisj : Disjoint U (closure U)ᶜ :=
    Set.disjoint_left.mpr fun a ha hna => hna (subset_closure ha)
  have hsub : S ⊆ U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hcl : y ∈ closure U
    · refine Or.inl ?_
      have hyfr : y ∉ frontier U := by
        intro hmem
        exact (Set.eq_empty_iff_forall_notMem.1 hfr y) ⟨hy, hmem⟩
      have hint : y ∈ interior U := by
        by_contra hnint
        exact hyfr ⟨hcl, hnint⟩
      rwa [hU.interior_eq] at hint
    · exact Or.inr hcl
  exact hS.subset_left_of_subset_union hU isClosed_closure.isOpen_compl hdisj hsub hne

/-- The centre of an origin cube lies in it. -/
theorem zero_mem_openCubeSet_originCube (d : ℕ) (m : ℤ) :
    (0 : Vec d) ∈ openCubeSet (originCube d m) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h3 : (0 : ℝ) < 3 ^ m := zpow_pos (by norm_num) m
  refine ⟨?_, ?_⟩ <;> simp only [Pi.zero_apply] <;> linarith only [h3]

/-- **The interior gate gives the full parent cube.**

If `z ∈ □_m` and the translated parent cube `z + □_k` misses `frontier □_m`,
then `z + □_k ⊆ □_m`.  This is the inclusion the frozen theorem's
frontier-empty clause supplies to the interior Caccioppoli application, and it
is what makes the Dirichlet locus of that application empty. -/
theorem image_add_openCubeSet_subset_of_frontier_inter_empty {k m : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m))
    (hfr : ((fun y => z + y) '' openCubeSet (originCube d k)) ∩
        frontier (openCubeSet (originCube d m)) = ∅) :
    (fun y => z + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d m) := by
  have hconv : Convex ℝ ((fun y => z + y) '' openCubeSet (originCube d k)) := by
    rw [image_add_eq_translateSet]
    exact ((isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet z).convex
  have hmem : z ∈ (fun y => z + y) '' openCubeSet (originCube d k) :=
    ⟨0, zero_mem_openCubeSet_originCube d k, by simp⟩
  exact subset_of_isPreconnected_of_frontier_inter_empty hconv.isPreconnected
    (isOpen_openCubeSet (originCube d m)) ⟨z, hmem, hz⟩ hfr

/-! ## 3. The two-scale window triple -/

/-- Origin cubes are nested in their scale. -/
theorem openCubeSet_originCube_subset_of_le {k l : ℤ} (hkl : k ≤ l) :
    openCubeSet (originCube d k) ⊆ openCubeSet (originCube d l) := by
  intro y hy
  rw [mem_openCubeSet_originCube_iff] at hy ⊢
  intro i
  have hmono : (3 : ℝ) ^ k ≤ 3 ^ l := zpow_le_zpow_right₀ (by norm_num) hkl
  exact ⟨by linarith only [(hy i).1, hmono], by linarith only [(hy i).2, hmono]⟩

/-- If the two-scale core window already sits inside the outer cube,
CoarseGraining's `caccioppoliCoreSet` **is** that window. -/
theorem caccioppoliCoreSet_eq_of_subset {Q : TriadicCube d} {x : Vec d}
    (hx : openCubeAtScale x (Q.scale - 2) ⊆ openCubeSet Q) :
    caccioppoliCoreSet Q x = openCubeAtScale x (Q.scale - 2) := by
  rw [caccioppoliCoreSet, Set.inter_eq_right.mpr hx]

/-- **The shifted child centre lies in the parent cube.**

From the frozen theorem's geometry binder, the shifted centre `w = x - z` lies
in `□_{n+1}`, hence in `□_{n+2}`: CoarseGraining's Caccioppoli hypothesis `x ∈
openCubeSet Q` holds in the translated frame. -/
theorem sub_mem_openCubeSet_succ_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hsub : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    x - z ∈ openCubeSet (originCube d (n + 1)) := by
  have hxmem : x ∈ (fun y => x + y) '' openCubeSet (originCube d n) :=
    ⟨0, zero_mem_openCubeSet_originCube d n, by simp⟩
  obtain ⟨y0, hy0mem, hy0⟩ := (hsub hxmem).1
  have hxy : x - z = y0 := by
    rw [← hy0]
    exact add_sub_cancel_left z y0
  rwa [hxy]

/-- **A window centred in `□_{n+1}` of scale at most `n+1` sits in `□_{n+2}`.**

The one geometric estimate behind both the Dirichlet patch inclusion (`k = n+1`)
and the core identity (`k = n`) of the two-scale window triple. -/
theorem image_add_openCubeSet_subset_succ_succ {k n : ℤ} {w : Vec d}
    (hw : w ∈ openCubeSet (originCube d (n + 1))) (hk : k ≤ n + 1) :
    (fun y => w + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d (n + 2)) := by
  have hstep1 : (3 : ℝ) ^ (n + 2) = 3 ^ (n + 1) * 3 := by
    have hn : n + 2 = n + 1 + 1 := by ring
    rw [hn, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hk3 : (3 : ℝ) ^ k ≤ 3 ^ (n + 1) := zpow_le_zpow_right₀ (by norm_num) hk
  have hpos : (0 : ℝ) < 3 ^ (n + 1) := zpow_pos (by norm_num) _
  rintro p ⟨y, hy, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hw hy ⊢
  intro i
  have h1 := hw i
  have h2 := hy i
  rw [hstep1]
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply] <;>
    linarith only [h1.1, h1.2, h2.1, h2.2, hk3, hpos]

/-- **The Dirichlet patch of the translated frame sits inside the parent.**

Under the frozen theorem's geometry binder, the Caccioppoli localization patch
`(x - z) + □_{n+1}` is a subset of `□_{n+2}`: the interior regime's hypothesis. -/
theorem openCubeAtScale_patch_subset_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hsub : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    openCubeAtScale (x - z) (n + 1) ⊆ openCubeSet (originCube d (n + 2)) := by
  rw [openCubeAtScale_eq_image_add]
  exact image_add_openCubeSet_subset_succ_succ
    (sub_mem_openCubeSet_succ_of_anchorGeometry hsub) le_rfl

/-- **The Caccioppoli core is the translated child cube.**

Under the frozen theorem's geometry binder, read in the translated frame at the
outer cube `□_{n+2}` and the shifted centre `w = x - z`,

```text
  caccioppoliCoreSet (□_{n+2}) (x - z) = (x - z) + □_n ,
``` -/
theorem caccioppoliCoreSet_eq_image_add_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hsub : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    caccioppoliCoreSet (originCube d (n + 2)) (x - z) =
      (fun y => (x - z) + y) '' openCubeSet (originCube d n) := by
  have hscale : (originCube d (n + 2)).scale - 2 = n := by
    simp only [originCube]
    ring
  have hcore : (fun y => (x - z) + y) '' openCubeSet (originCube d n) ⊆
      openCubeSet (originCube d (n + 2)) :=
    image_add_openCubeSet_subset_succ_succ
      (sub_mem_openCubeSet_succ_of_anchorGeometry hsub) (by linarith only [])
  have hkey : openCubeAtScale (x - z) ((originCube d (n + 2)).scale - 2) =
      (fun y => (x - z) + y) '' openCubeSet (originCube d n) := by
    rw [hscale, openCubeAtScale_eq_image_add]
  rw [caccioppoliCoreSet_eq_of_subset (by rw [hkey]; exact hcore), hkey]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
