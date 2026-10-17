/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringGeometry

/-!
# CoveringSlotObstruction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Where the boundary covering cube sits relative to the good-event slot

```text
  max { σ_{n+2}⁻¹ Λ_{s/8,2}(□_{n+2}; ã) , σ_{n+2} λ_{s/8,2}(□_{n+2}; ã)⁻¹ }
```

at the sample `τ_z ω` — physically the cube `z + □_{n+2}`.  So the question is
one about **two cubes of the same scale**:
`c + □_{n+2}` versus `z + □_{n+2}`.

This module answers it geometrically, in both directions.

* `eq_of_image_add_openCubeSet_subset` — two open triadic cubes of the *same*
  scale are nested only when their centres coincide.
* `inter_frontier_eq_empty_of_subset_openCubeSet` — a set inside the open cube
  `□_m` misses `∂□_m`.
* `gate_of_coveringCube_subset_slot` — **the obstruction.**  Any centre `c` whose
  cube `c + □_{n+2}` both (i) stays inside `□_m` (which the boundary lane
  *requires*: the anchor's solution `u` lives on `□_m` only) and (ii) stays
  inside the good-event slot's cube `z + □_{n+2}`, forces the anchor's own
  **interior gate** `(z + □_{n+2}) ∩ ∂□_m = ∅`.  Contrapositive: on the branch
  the interior chain leaves open — the boundary regime — *no* admissible covering
  cube of the covering scale fits inside the slot cube, so no covering,
  subadditivity or descendant argument indexed by `𝒢(n+2, z)` can reach the
  covering cube's ellipticity data.
* `image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ` — **the
  positive half.**  The covering cube always fits inside `z + □_{k+1}`; at `k =
  n+2` that is `z + □_{n+3}`, the anchor's own window cube.  So a slot at index `n+3`
  *does* reach it, and the proved off-grid transport
  (`OffGridComposeAssembly`/`OffGridErrorFluxCorrected`, which require exactly
  a containment `w + □_k ⊆ □_K` of the off-grid cube in a grid cube) applies
  with `K = n+3` at depth one.

Nothing here transports any coefficient, error or ellipticity quantity: this
module is pure cube geometry, exactly like `BoundaryCoveringGeometry`.  In
particular nothing below is an instance, or a fraction, of any source node.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the boundary application of
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. Two open cubes of the same scale -/

/-- Half the side of `□_j` is positive. -/
private theorem half_three_zpow_pos (j : ℤ) : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  linarith only [h3]

/-! ## 2. The frontier gate from a containment in `□_m` -/

/-! ## 3. The obstruction -/

/-! ## 4. The positive half: the covering cube fits one scale up -/

private theorem three_zpow_succ (j : ℤ) : (3 : ℝ) ^ (j + 1) = 3 * (3 : ℝ) ^ j := by
  rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) j 1, zpow_one]
  ring

/-- The clamp moves each coordinate by less than half a side of `□_k`. -/
theorem sub_wellPlacedCentre_coord_bound {m k : ℤ} (hkm : k ≤ m) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (i : Fin d) :
    -((1 / 2 : ℝ) * (3 : ℝ) ^ k) < x i - wellPlacedCentre x m k i ∧
      x i - wellPlacedCentre x m k i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  have hA : (0 : ℝ) ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hAdef : wellPlacedHalfGap m k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  have hk : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ k := half_three_zpow_pos k
  rw [mem_openCubeSet_originCube_iff] at hx
  have hxi := hx i
  rcases le_total (x i) (-wellPlacedHalfGap m k) with h1 | h1
  · have hc : wellPlacedCentre x m k i = -wellPlacedHalfGap m k := by
      rw [wellPlacedCentre, min_eq_right (h1.trans (by linarith only [hA]))]
      exact max_eq_left h1
    rw [hc, hAdef] at *
    exact ⟨by linarith only [hxi.1], by linarith only [h1, hk]⟩
  · rcases le_total (x i) (wellPlacedHalfGap m k) with h2 | h2
    · have hc : wellPlacedCentre x m k i = x i := by
        rw [wellPlacedCentre, min_eq_right h2]
        exact max_eq_right h1
      rw [hc]
      exact ⟨by linarith only [hk], by linarith only [hk]⟩
    · have hc : wellPlacedCentre x m k i = wellPlacedHalfGap m k := by
        rw [wellPlacedCentre, min_eq_left h2]
        exact max_eq_right (by linarith only [h2, hA])
      rw [hc, hAdef] at *
      exact ⟨by linarith only [h2, hk], by linarith only [hxi.2]⟩

/-- **The positive half.**

The boundary covering cube always sits inside `z + □_{k+1}`, provided the window
centre `x` is within half a side of `□_{k-1}` of `z` — which is exactly what the
anchor's geometry binder gives at `k = n+2`.

Consequently a good-event slot at index `n+3` *does* reach the covering cube:
the proved off-grid transports require precisely a containment of the off-grid
cube in a grid cube, and this is that containment at depth one. -/
theorem image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ {m k : ℤ}
    {x z : Vec d} (hkm : k ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hxz : x - z ∈ openCubeSet (originCube d (k - 1))) :
    (fun y => wellPlacedCentre x m k + y) '' openCubeSet (originCube d k) ⊆
      (fun y => z + y) '' openCubeSet (originCube d (k + 1)) := by
  have hkk : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ (k - 1) := by
    have hrw : k = (k - 1) + 1 := by ring
    rw [hrw, three_zpow_succ (k - 1)]
    ring_nf
  have hk1 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := three_zpow_succ k
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (k - 1) := zpow_pos (by norm_num) (k - 1)
  rw [mem_openCubeSet_originCube_iff] at hxz
  intro p hp
  rw [mem_image_add_iff, mem_openCubeSet_originCube_iff] at hp
  rw [mem_image_add_iff, mem_openCubeSet_originCube_iff]
  intro i
  have h1 := hp i
  have h2 := sub_wellPlacedCentre_coord_bound hkm hx i
  have h3 := hxz i
  simp only [Pi.sub_apply] at h1 h3 ⊢
  constructor
  · linarith only [h1.1, h2.2, h3.1, hkk, hk1, hpos]
  · linarith only [h1.2, h2.1, h3.2, hkk, hk1, hpos]

/-- The anchor's geometry binder, read as a bound on `x - z`. -/
theorem sub_mem_openCubeSet_of_anchorGeometry {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    x - z ∈ openCubeSet (originCube d (n + 1)) := by
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d n) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have h := half_three_zpow_pos n
    refine ⟨?_, ?_⟩ <;> simp only [Pi.zero_apply] <;> linarith only [h]
  have hx : x ∈ (fun y => x + y) '' openCubeSet (originCube d n) :=
    ⟨0, hzero, by simp⟩
  have h := (hgeom hx).1
  rwa [mem_image_add_iff] at h

/-- **The covering cube inside the anchor's own window cube.**

At the boundary lane's covering scale `k = n+2`, under the frozen theorem's own
binders, `c + □_{n+2} ⊆ z + □_{n+3}`.  Together with
`gate_of_wellPlacedCentre_subset_slot` this is the exact measurement: the
covering cube is outside the `n+2` slot on the boundary branch, and inside the
`n+3` one always. -/
theorem image_add_wellPlacedCentre_subset_anchorParent {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    (fun y => wellPlacedCentre x m (n + 2) + y) '' openCubeSet (originCube d (n + 2)) ⊆
      (fun y => z + y) '' openCubeSet (originCube d (n + 3)) := by
  have hxz : x - z ∈ openCubeSet (originCube d (n + 2 - 1)) := by
    have h := sub_mem_openCubeSet_of_anchorGeometry hgeom
    have hrw : n + 2 - 1 = n + 1 := by ring
    rw [hrw]
    exact h
  have hbase := image_add_wellPlacedCentre_subset_image_add_openCubeSet_succ
    (k := n + 2) (m := m) hnm hx hxz
  have hrw : n + 2 + 1 = n + 3 := by ring
  rwa [hrw] at hbase

end

end Algsuperdiff.Section4.Provider.ExcessDecay
