/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryLaneWindows

/-!
# BoundaryCoveringGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The well-placed cube of the boundary covering step

ABK26's Step 2 applies the *boundary* coarse-grained Caccioppoli inequality on
a truncated window `(x+□_{n+1}) ∩ □_m` and concludes an energy bound on
`(x+□_n) ∩ □_m`, "after a simple covering argument".  CoarseGraining's theorem,
however, lives on a **cube**: an outer triadic cube `Q`, a Dirichlet patch
`openCubeAtScale x (Q.scale-1)`, and the core `caccioppoliCoreSet Q x = □_Q ∩
openCubeAtScale x (Q.scale-2)`.

This module constructs that cube and proves the three inclusions the
application needs.

## The construction

With `hm := 3^m/2`, `hk := 3^k/2` and the *gap* `A := hm - hk ≥ 0` (this is where
`k ≤ m` enters), the centre is the coordinatewise clamp

```text
  c_i := max (-A) (min A (x_i)) ,        c := wellPlacedCentre x m k .
```

Clamping is exactly "anchor on the met faces": in a coordinate where the window
stays well inside `□_m` the cube is centred at `x_i`, and in a coordinate where
the window reaches a face the cube slides until its own face coincides with that
face of `□_m`.  Consequently

* `c + □_k ⊆ □_m` — the cube never leaves the domain (so the equation holds on
  it, and the Dirichlet locus of the application is contained in `∂□_m`);
* `(x+□_j) ∩ □_m ⊆ c + □_k` for every `j ≤ k` — the cube covers the window,
  patch included;
* `(x+□_j) ∩ □_m ⊆ c + caccioppoliCoreSet (□_k^{origin}) (x-c)` for `j ≤ k-2` —
  in the translated frame (A4: the *sample* is translated, every cube is an
  origin cube) the anchor's window sits inside CoarseGraining's Caccioppoli
  core.

## What is not done here

No measure theory (that is `BoundaryCoveringVolume`) and no analysis: this
module contains only inclusions of sets.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; boundary application.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. Membership in a translated set -/

/-- A point lies in the translate `c + S` exactly when its back-translate lies
in `S`. -/
theorem mem_image_add_iff {c p : Vec d} {S : Set (Vec d)} :
    p ∈ (fun y => c + y) '' S ↔ p - c ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [add_sub_cancel_left]
  · intro h
    refine ⟨p - c, h, ?_⟩
    change c + (p - c) = p
    abel

/-! ## 2. The well-placed centre -/

/-- The clamping gap `3^m/2 - 3^k/2` of the well-placed cube. -/
def wellPlacedHalfGap (m k : ℤ) : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k

/-- **The centre of the well-placed cube**: the coordinatewise clamp of `x` into
the set of centres whose cube of side `3^k` still fits inside `□_m`. -/
def wellPlacedCentre (x : Vec d) (m k : ℤ) : Vec d :=
  fun i => max (-wellPlacedHalfGap m k) (min (wellPlacedHalfGap m k) (x i))

theorem wellPlacedHalfGap_nonneg {m k : ℤ} (hkm : k ≤ m) :
    0 ≤ wellPlacedHalfGap m k := by
  have h : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m := zpow_le_zpow_right₀ (by norm_num) hkm
  rw [wellPlacedHalfGap]
  linarith only [h]

theorem neg_wellPlacedHalfGap_le_wellPlacedCentre (x : Vec d) (m k : ℤ) (i : Fin d) :
    -wellPlacedHalfGap m k ≤ wellPlacedCentre x m k i :=
  le_max_left _ _

theorem wellPlacedCentre_le_wellPlacedHalfGap {m k : ℤ} (hkm : k ≤ m) (x : Vec d)
    (i : Fin d) : wellPlacedCentre x m k i ≤ wellPlacedHalfGap m k :=
  max_le (by linarith only [wellPlacedHalfGap_nonneg hkm]) (min_le_left _ _)

/-! ## 3. The cube stays inside the domain -/

/-- **The well-placed cube never leaves `□_m`.**  This is what makes the printed
"the equation holds on the covering cube" legitimate, and it forces the
Dirichlet locus of the Caccioppoli application into `∂□_m`. -/
theorem image_add_wellPlacedCentre_subset_openCubeSet {m k : ℤ} (x : Vec d)
    (hkm : k ≤ m) :
    (fun y => wellPlacedCentre x m k + y) '' openCubeSet (originCube d k) ⊆
      openCubeSet (originCube d m) := by
  intro p hp
  rw [mem_image_add_iff, mem_openCubeSet_originCube_iff] at hp
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hlow := neg_wellPlacedHalfGap_le_wellPlacedCentre x m k i
  have hhigh := wellPlacedCentre_le_wellPlacedHalfGap hkm x i
  have hi := hp i
  rw [wellPlacedHalfGap] at hlow hhigh
  simp only [Pi.sub_apply] at hi
  exact ⟨by linarith only [hi.1, hlow], by linarith only [hi.2, hhigh]⟩

/-! ## 4. The cube covers the truncated window -/

/-- The coordinate computation behind the covering inclusion: the three clamp
regimes (`x_i` below the gap, inside the gap, above the gap). -/
private theorem coord_sub_wellPlacedCentre_bound {m k j : ℤ} {x : Vec d} {i : Fin d}
    {y : ℝ} (hkm : k ≤ m) (hjk : j ≤ k)
    (hj1 : -(1 / 2 : ℝ) * (3 : ℝ) ^ j < y - x i)
    (hj2 : y - x i < (1 / 2 : ℝ) * (3 : ℝ) ^ j)
    (hm1 : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < y)
    (hm2 : y < (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    -(1 / 2 : ℝ) * (3 : ℝ) ^ k < y - wellPlacedCentre x m k i ∧
      y - wellPlacedCentre x m k i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  have hjk3 : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hjk
  have hA : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hAdef : wellPlacedHalfGap m k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  have hAu : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
    rw [← hAdef]
    exact hA
  rcases le_total (x i) (-wellPlacedHalfGap m k) with h1 | h1
  · have hc : wellPlacedCentre x m k i = -wellPlacedHalfGap m k := by
      rw [wellPlacedCentre, min_eq_right (h1.trans (by linarith only [hA]))]
      exact max_eq_left h1
    have h1u : x i ≤ -((1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k) := by
      rw [← hAdef]
      exact h1
    rw [hc, hAdef]
    exact ⟨by linarith only [hm1], by linarith only [hj2, h1u, hjk3]⟩
  · rcases le_total (x i) (wellPlacedHalfGap m k) with h2 | h2
    · have hc : wellPlacedCentre x m k i = x i := by
        rw [wellPlacedCentre, min_eq_right h2]
        exact max_eq_right h1
      rw [hc]
      exact ⟨by linarith only [hj1, hjk3], by linarith only [hj2, hjk3]⟩
    · have hc : wellPlacedCentre x m k i = wellPlacedHalfGap m k := by
        rw [wellPlacedCentre, min_eq_left h2]
        exact max_eq_right (by linarith only [h2, hA])
      have h2u : (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ x i := by
        rw [← hAdef]
        exact h2
      rw [hc, hAdef]
      exact ⟨by linarith only [hj1, h2u, hjk3], by linarith only [hm2]⟩

/-- **The well-placed cube covers the truncated window.**

For every scale `j ≤ k` the anchor's window `(x+□_j) ∩ □_m` lies inside the
translated cube `c + □_k`.  At `j = k-1` this is the covering of the Caccioppoli
Dirichlet patch; at `j = k-2` it is the covering of the energy window. -/
theorem truncatedWindow_subset_image_add_wellPlacedCentre {m k j : ℤ} (x : Vec d)
    (hkm : k ≤ m) (hjk : j ≤ k) :
    truncatedWindow x m j ⊆
      (fun y => wellPlacedCentre x m k + y) '' openCubeSet (originCube d k) := by
  intro p hp
  have hpx : p - x ∈ openCubeSet (originCube d j) :=
    sub_mem_openCubeSet_of_mem_truncatedWindow hp
  have hpm : p ∈ openCubeSet (originCube d m) := truncatedWindow_subset_domain x m j hp
  rw [mem_openCubeSet_originCube_iff] at hpx hpm
  rw [mem_image_add_iff, mem_openCubeSet_originCube_iff]
  intro i
  have hj := hpx i
  simp only [Pi.sub_apply] at hj ⊢
  exact coord_sub_wellPlacedCentre_bound hkm hjk hj.1 hj.2 (hpm i).1 (hpm i).2

/-! ## 5. The window sits in CoarseGraining's Caccioppoli core -/

theorem scale_originCube (d : ℕ) (k : ℤ) : (originCube d k).scale = k := by
  simp only [originCube]

/-- **The covering inclusion in CoarseGraining's own window shape.**

In the translated frame the anchor's window `(x+□_j) ∩ □_m` with `j ≤ k-2` is
contained in `caccioppoliCoreSet (□_k) (x-c)`, the core of CoarseGraining's
boundary coarse Caccioppoli inequality at the outer cube `□_k` and centre
`x-c`.  Together with `image_add_wellPlacedCentre_subset_openCubeSet` this is
the geometric content of the printed "simple covering argument". -/
theorem truncatedWindow_subset_image_add_caccioppoliCoreSet {m k j : ℤ} (x : Vec d)
    (hkm : k ≤ m) (hjk : j ≤ k - 2) :
    truncatedWindow x m j ⊆
      (fun y => wellPlacedCentre x m k + y) ''
        caccioppoliCoreSet (originCube d k) (x - wellPlacedCentre x m k) := by
  intro p hp
  have hcube : p - wellPlacedCentre x m k ∈ openCubeSet (originCube d k) := by
    have h := truncatedWindow_subset_image_add_wellPlacedCentre x hkm
      (by linarith only [hjk] : j ≤ k) hp
    rwa [mem_image_add_iff] at h
  have hpx : p - x ∈ openCubeSet (originCube d j) :=
    sub_mem_openCubeSet_of_mem_truncatedWindow hp
  have hpatch : p - wellPlacedCentre x m k ∈
      openCubeAtScale (x - wellPlacedCentre x m k) ((originCube d k).scale - 2) := by
    rw [scale_originCube, openCubeAtScale_eq_image_add, mem_image_add_iff]
    have hsub : p - wellPlacedCentre x m k - (x - wellPlacedCentre x m k) = p - x := by
      abel
    rw [hsub]
    exact openCubeSet_originCube_subset_of_le hjk hpx
  rw [mem_image_add_iff]
  exact ⟨hcube, hpatch⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay
