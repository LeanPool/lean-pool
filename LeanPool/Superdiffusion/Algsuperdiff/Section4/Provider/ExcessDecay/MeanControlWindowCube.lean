/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringGeometry

/-!
# MeanControlWindowCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The mean comparison, step 1: a boundary-flush cube inside the anchor's own
window

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## The geometric obstruction this module removes

The mean comparison asks for a bound on the scalar

```text
  S = |⨍_{c+□_{n+2}} (u − h)| ,    c = wellPlacedCentre x m (n+2) ,
```

on the boundary branch `(z+□_{n+2}) ∩ ∂□_m ≠ ∅`.  The only extra information
the boundary branch carries is the *zero trace of `u − h` on `∂□_m`*, so any
producer must reach `∂□_m` from the cube it works on.  The covering cube of the
anchor's own centre `x` does **not** reach it: the branch is a statement about
`z`, and `x` is only known to lie in `z + □_{n+1}`, so `x` can sit a distance
`3^{n+1}/2` short of the clamp level and `wellPlacedCentre x m (n+2) + □_{n+2}`
can then be strictly interior to `□_m`.

This module produces the cube that does reach it, from the anchor's **own**
binders and with **no new construction**: the same `wellPlacedCentre` clamp,
applied to `z` instead of `x`.  Writing

```text
  K := wellPlacedCentre z m (n+2) + □_{n+2} ,
```

three facts are proved.

* `K ⊆ □_m` (`image_add_wellPlacedCentre_subset_openCubeSet`, reused): the
  equation, the Caccioppoli and the coarse-graining envelope are all available
  on `K`.
* `K ⊆ (z+□_{n+3}) ∩ □_m` (`image_add_wellPlacedCentre_z_subset_anchorWindow`):
  `K` sits inside the frozen window `W'`, so every quantity read on `K` is
  transportable to the frozen first and fifth legs by the `3^d` measure ratio.
* **`K` is flush against `∂□_m`** (`wellPlacedCentre_flush`,
  `faceLevel_sub_lt_of_mem_wellPlacedCube`): on the boundary branch there are a
  coordinate `i` and a sign `σ = ±1` with

  ```text
    σ · (wellPlacedCentre z m (n+2))ᵢ + ½·3^{n+2} = ½·3^m ,
  ```

  i.e. the `σeᵢ` face of `K` lies *exactly* in the frontier hyperplane of `□_m`,
  and consequently every point of `K` is within `3^{n+2}` of that hyperplane.

The last item is what the funded coarse-grained boundary Poincaré needs and what
the `x`-centred covering cube cannot supply: `u − h` has zero trace on the face,
so a comparator on `K` that shares `u`'s boundary data agrees with the datum `h`
there.  The `n+3 ≤ m` binder of the frozen statement is what makes the
`(n+2)` clamp legitimate (`n + 2 ≤ m` suffices, and is implied).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. Coordinates of a translated open cube -/

/-- Membership in a translated open triadic cube, coordinatewise. -/
theorem mem_image_add_openCubeSet_coord_iff {j : ℤ} {z y : Vec d} :
    y ∈ (fun y' => z + y') '' openCubeSet (originCube d j) ↔
      ∀ i, (-(1 / 2 : ℝ)) * (3 : ℝ) ^ j < y i - z i ∧
        y i - z i < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  rw [mem_image_add_iff, mem_openCubeSet_originCube_iff]
  constructor
  · intro h i
    have hi := h i
    simp only [Pi.sub_apply] at hi
    exact hi
  · intro h i
    have hi := h i
    simp only [Pi.sub_apply]
    exact hi

/-! ## 2. The negated interior gate, in clamp normal form -/

/-- **The boundary branch, quantitatively.**

If the parent cube `z + □_j` meets the frontier of `□_m`, then in some
coordinate `i` and some direction `σ = ±1` the centre `z` already exceeds the
clamp level `wellPlacedHalfGap m j = ½·3^m − ½·3^j` of the well-placed cube of
side `3^j`.  This is exactly the hypothesis under which the clamp saturates, so
it is the bridge from the anchor's negated gate to a boundary-flush cube. -/
theorem overhang_of_boundaryBranch {j m : ℤ} {z : Vec d}
    (hfr : (((fun y' => z + y') '' openCubeSet (originCube d j)) ∩
      frontier (openCubeSet (originCube d m))) ≠ ∅) :
    ∃ (i : Fin d) (σ : ℝ), (σ = 1 ∨ σ = -1) ∧ wellPlacedHalfGap m j < σ * z i := by
  classical
  obtain ⟨p, hpcube, hpfr⟩ := Set.nonempty_iff_ne_empty.mpr hfr
  have hpout : p ∉ openCubeSet (originCube d m) := by
    rw [(isOpen_openCubeSet (originCube d m)).frontier_eq] at hpfr
    exact hpfr.2
  have hp : ∃ i, ¬((-(1 / 2 : ℝ)) * (3 : ℝ) ^ m < p i ∧
      p i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
    by_contra hcon
    push Not at hcon
    exact hpout (mem_openCubeSet_originCube_iff.mpr fun i => hcon i)
  obtain ⟨i, hi⟩ := hp
  obtain ⟨hlo, hhi⟩ := mem_image_add_openCubeSet_coord_iff.mp hpcube i
  rw [wellPlacedHalfGap]
  rcases not_and_or.mp hi with hcase | hcase
  · push Not at hcase
    exact ⟨i, -1, Or.inr rfl, by simp only [neg_mul, one_mul]; linarith only [hcase, hlo]⟩
  · push Not at hcase
    exact ⟨i, 1, Or.inl rfl, by simp only [one_mul]; linarith only [hcase, hhi]⟩

/-! ## 3. The clamp saturates: the cube is flush against the frontier -/

/-- **The flush face.**

If the centre `z` exceeds the clamp level in the direction `σeᵢ`, then the
well-placed centre of side `3^k` saturates the clamp in that coordinate:
`σ·cᵢ = wellPlacedHalfGap m k`. -/
theorem wellPlacedCentre_flush {m k : ℤ} (hkm : k ≤ m) {z : Vec d} {i : Fin d} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hover : wellPlacedHalfGap m k < σ * z i) :
    σ * wellPlacedCentre z m k i = wellPlacedHalfGap m k := by
  have hA : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  simp only [wellPlacedCentre]
  rcases hσ with h | h <;> subst h
  · have hz : wellPlacedHalfGap m k ≤ z i := by
      have := hover
      simp only [one_mul] at this
      exact this.le
    rw [min_eq_left hz, max_eq_right (by linarith only [hA]), one_mul]
  · have hz : z i ≤ -wellPlacedHalfGap m k := by
      have := hover
      simp only [neg_mul, one_mul] at this
      linarith only [this]
    rw [min_eq_right (by linarith only [hz, hA]), max_eq_left hz]
    ring

/-- **The flush face, at the frontier level.**  The `σeᵢ` face of the well-placed
cube `wellPlacedCentre z m k + □_k` lies exactly in the frontier hyperplane
`{σ yᵢ = ½·3^m}` of `□_m`. -/
theorem wellPlacedCentre_faceLevel {m k : ℤ} (hkm : k ≤ m) {z : Vec d} {i : Fin d}
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hover : wellPlacedHalfGap m k < σ * z i) :
    σ * wellPlacedCentre z m k i + (1 / 2 : ℝ) * (3 : ℝ) ^ k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  rw [wellPlacedCentre_flush hkm hσ hover, wellPlacedHalfGap]
  ring

/-! ## 4. The flush cube sits inside the frozen window -/

/-- The well-placed centre of `z` never moves `z` by as much as a half side. -/
theorem abs_wellPlacedCentre_sub_lt {m k : ℤ} (hkm : k ≤ m) {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (i : Fin d) :
    |wellPlacedCentre z m k i - z i| < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  have hA : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hgap : wellPlacedHalfGap m k = (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
    rfl
  obtain ⟨hzlo, hzhi⟩ := mem_openCubeSet_originCube_iff.mp hz i
  simp only [wellPlacedCentre]
  rw [abs_lt]
  rcases le_or_gt (z i) (wellPlacedHalfGap m k) with h1 | h1
  · rw [min_eq_right h1]
    rcases le_or_gt (-wellPlacedHalfGap m k) (z i) with h2 | h2
    · rw [max_eq_right h2]
      have hkpos : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
      constructor <;> linarith only [hkpos]
    · rw [max_eq_left h2.le]
      constructor <;> linarith only [h2, hzlo, hgap]
  · rw [min_eq_left h1.le, max_eq_right (by linarith only [hA])]
    constructor <;> linarith only [h1, hzhi, hgap]

/-- **The flush cube lies in the frozen window.**

`wellPlacedCentre z m (n+2) + □_{n+2} ⊆ (z+□_{n+3}) ∩ □_m`: every quantity read
on the flush cube transports to the frozen clause's own window at the `3^d`
measure ratio. -/
theorem image_add_wellPlacedCentre_z_subset_anchorWindow {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} (hz : z ∈ openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre z m (n + 2) + y) '' openCubeSet (originCube d (n + 2)) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
  intro p hp
  refine ⟨?_, image_add_wellPlacedCentre_subset_openCubeSet z hnm hp⟩
  rw [mem_image_add_openCubeSet_coord_iff]
  intro i
  obtain ⟨hlo, hhi⟩ := mem_image_add_openCubeSet_coord_iff.mp hp i
  have hc := abs_wellPlacedCentre_sub_lt hnm hz i
  rw [abs_lt] at hc
  have h3 : (3 : ℝ) ^ (n + 3) = 3 * (3 : ℝ) ^ (n + 2) := by
    rw [show n + 3 = (n + 2) + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (n + 2) := zpow_pos (by norm_num) _
  constructor
  · linarith only [hlo, hc.1, h3, hpos]
  · linarith only [hhi, hc.2, h3, hpos]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
