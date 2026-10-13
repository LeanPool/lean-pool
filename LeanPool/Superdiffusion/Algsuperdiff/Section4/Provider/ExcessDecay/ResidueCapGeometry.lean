/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealCaccioppoliGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoveringSlotObstruction

/-!
# ResidueCapGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three geometric hinges of the boundary cap chain, verified at the flush
# sub-cube `K'`

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## What is proved

`ResidueAbsorption.exists_flushSubCube_not_subset_anchorGeometry` shows that
the flush scale-`n` sub-cube `K' = flushSubCentre z m n i σ + □_n` provably
fails the anchor's geometry binder `x + □_n ⊆ (z+□_{n+1}) ∩ □_m` on a genuine
`3·3^n`-wide far-range of the boundary branch.  That block is a statement about
*binders*.  This module measures what the proved boundary cap chain actually
consumes from that binder, and discharges each item at `K'` from the anchor's
own `(n+3, z)` frame instead.

Three hinges — and only three — carry `hgeom` through the whole chain:

```text
  (W)  wellPlacedCentre x m (n+2) + □_{n+2} ⊆ (z+□_{n+3}) ∩ □_m
       (`image_add_wellPlacedCentre_subset_anchorWindow`;  the window
        transports `BoundaryTransports`, `BoundaryGradH`,
        the parent-`L²` pricing and the energy legs use nothing else)
  (P)  translateSet (wellPlacedCentre x m (n+2) − z) (cubeSet □_{n+2})
         ⊆ cubeSet □_{n+3}
       (`translateSet_cubeSet_coveringCube_subset_anchorParent`;  the covering
        cube's error/ellipticity caps use nothing else)
  (C)  translateSet (x − z) (cubeSet □_n) ⊆ cubeSet □_{n+3}
       (`translateSet_cubeSet_subset_of_anchorGeometry` composed with the half-open
        nesting;  the child cube's error/ellipticity caps use nothing else)
```

At `x := flushSubCentre z m n i σ`, (W) is already proved
(`SealCaccioppoliGeometry.outer_subset_anchorWindow_flushSubCentre` item 4),
and (P), (C) are proved here.  The margin is real, not tight: the flush
sub-centre sits at `|c'ᵢ − zᵢ| ≤ 8.5·3^n` against the `13·3^n` the `(n+3)`
frame allows, and the clamp defining the covering centre cannot increase that
distance (§1).

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. The clamp cannot move a centre away from a nearby reference point -/

/-- **The covering clamp, measured against a reference point.**

`wellPlacedCentre a m k` is the coordinatewise clamp of `a` into
`[−A, A]`, `A = ½3^m − ½3^k`.  If a reference point `b` lies in `□_m` and `aᵢ` is
within `D` of `bᵢ` for some `D ≥ ½3^k`, then the clamped coordinate is still
within `D` of `bᵢ`: clamping either does nothing, or moves `aᵢ` towards the
origin and therefore towards `b`, and the residual is at most the clamp gap
`½3^k`. -/
theorem abs_wellPlacedCentre_sub_le {m k : ℤ} (hkm : k ≤ m) {a b : Vec d} {D : ℝ}
    (i : Fin d) (hb : b ∈ openCubeSet (originCube d m))
    (hD : (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ D) (hab : |a i - b i| ≤ D) :
    |wellPlacedCentre a m k i - b i| ≤ D := by
  have hAdef : wellPlacedHalfGap m k =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m - (1 / 2 : ℝ) * (3 : ℝ) ^ k := rfl
  have hA0 : 0 ≤ wellPlacedHalfGap m k := wellPlacedHalfGap_nonneg hkm
  have hAnn : -wellPlacedHalfGap m k ≤ wellPlacedHalfGap m k := by
    linarith only [hA0]
  rw [mem_openCubeSet_originCube_iff] at hb
  have hb1 := (hb i).1
  have hb2 := (hb i).2
  have hab1 : -D ≤ a i - b i := (abs_le.mp hab).1
  have hab2 : a i - b i ≤ D := (abs_le.mp hab).2
  have hshow : wellPlacedCentre a m k i =
      max (-wellPlacedHalfGap m k) (min (wellPlacedHalfGap m k) (a i)) := rfl
  rcases le_total (a i) (-wellPlacedHalfGap m k) with h1 | h1
  · have hc : wellPlacedCentre a m k i = -wellPlacedHalfGap m k := by
      rw [hshow, min_eq_right (h1.trans hAnn), max_eq_left h1]
    rw [hc]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith only [h1, hab1, hAdef]
    · rw [hAdef]
      linarith only [hb1, hD]
  · rcases le_total (a i) (wellPlacedHalfGap m k) with h2 | h2
    · have hc : wellPlacedCentre a m k i = a i := by
        rw [hshow, min_eq_right h2, max_eq_right h1]
      rw [hc]
      exact hab
    · have hc : wellPlacedCentre a m k i = wellPlacedHalfGap m k := by
        rw [hshow, min_eq_left h2, max_eq_right hAnn]
      rw [hc]
      refine abs_le.mpr ⟨?_, ?_⟩
      · rw [hAdef]
        linarith only [hb2, hD]
      · linarith only [h2, hab2, hAdef]

/-! ## 2. The flush sub-centre's displacement from the anchor centre `z` -/

/-- Half the side of the `(n+2)` cube, in units of `3^n`. -/
private theorem half_three_zpow_add_two (n : ℤ) :
    (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 2) = (9 / 2 : ℝ) * (3 : ℝ) ^ n := by
  rw [three_zpow_add_two n]
  ring

/-- Half the side of the `(n+3)` cube, in units of `3^n`. -/
private theorem half_three_zpow_add_three (n : ℤ) :
    (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 3) = (27 / 2 : ℝ) * (3 : ℝ) ^ n := by
  have h : (3 : ℝ) ^ (n + 3) = 27 * (3 : ℝ) ^ n := by
    rw [show n + 3 = n + 2 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0),
      three_zpow_add_two n]
    ring
  rw [h]
  ring

/-- **The flush sub-centre stays within `8.5·3^n` of `z`.**

`c' = wellPlacedCentre z m (n+2)` pushed by `½(3^{n+2} − 3^n) = 4·3^n` in the
`σeᵢ` direction: the clamp contributes at most `½3^{n+2} = 4.5·3^n` and the push
exactly `4·3^n`. -/
theorem abs_flushSubCentre_sub_le {n m : ℤ} (hnm : n + 2 ≤ m) {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (r : Fin d) :
    |flushSubCentre z m n i σ r - z r| ≤ (17 / 2 : ℝ) * (3 : ℝ) ^ n := by
  have hclamp := sub_wellPlacedCentre_coord_bound (k := n + 2) hnm hz r
  have h92 := half_three_zpow_add_two n
  have hx := flushSubCentre_apply z m n i σ r
  have h9 := three_zpow_add_two n
  refine abs_le.mpr ⟨?_, ?_⟩ <;> by_cases hr : r = i
  · rw [ite_eq_left hr] at hx
    rcases hσ with h | h <;> subst h <;>
      linarith only [hx, hclamp.1, hclamp.2, h92, h9]
  · rw [ite_eq_right hr, add_zero] at hx
    linarith only [hx, hclamp.1, hclamp.2, h92]
  · rw [ite_eq_left hr] at hx
    rcases hσ with h | h <;> subst h <;>
      linarith only [hx, hclamp.1, hclamp.2, h92, h9]
  · rw [ite_eq_right hr, add_zero] at hx
    linarith only [hx, hclamp.1, hclamp.2, h92]

/-- **The flush sub-centre lies in `□_m`.** -/
theorem flushSubCentre_mem_openCubeSet {n m : ℤ} (hnm : n + 2 ≤ m) (z : Vec d)
    (i : Fin d) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    flushSubCentre z m n i σ ∈ openCubeSet (originCube d m) :=
  image_add_wellPlacedCentre_subset_openCubeSet z hnm
    (flushSubCentre_mem_flushCube z i hσ)

/-! ## 3. Hinge (C): the child cube inside the `(n+3)` parent, half-open -/

/-- **Hinge (C) at `K'`.**

`K' − z + □_n ⊆ □_{n+3}` in the half-open realizations: `8.5·3^n + 0.5·3^n =
9·3^n` against the available `13.5·3^n`.  This is the containment the proved
off-grid transport
`OffGridErrorFluxCorrected.ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot`
consumes, read at the root `□_{n+3}`. -/
theorem translateSet_cubeSet_flushSubCube_subset_anchorParent {n m : ℤ}
    (hnm : n + 2 ≤ m) {z : Vec d} (hz : z ∈ openCubeSet (originCube d m))
    (i : Fin d) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    translateSet (flushSubCentre z m n i σ - z) (cubeSet (originCube d n)) ⊆
      cubeSet (originCube d (n + 3)) := by
  have h27 := half_three_zpow_add_three n
  rintro p ⟨y, hy, rfl⟩
  rw [mem_cubeSet_originCube_iff] at hy ⊢
  intro r
  have hyr := hy r
  have hdisp := abs_flushSubCentre_sub_le hnm hz i hσ r
  have hd1 := (abs_le.mp hdisp).1
  have hd2 := (abs_le.mp hdisp).2
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.sub_apply] <;>
    linarith only [hyr.1, hyr.2, hd1, hd2, h27]

/-! ## 4. Hinge (P): the covering cube of `K'` inside the `(n+3)` parent -/

/-- **Hinge (P) at `K'`.**

The covering centre `wellPlacedCentre c' m (n+2)` is still within `8.5·3^n` of
`z` (§1, at `D = 8.5·3^n ≥ 4.5·3^n = ½3^{n+2}`), so the covering cube's
half-open realization sits inside `□_{n+3}`: `8.5·3^n + 4.5·3^n = 13·3^n`
against the available `13.5·3^n`.  This is the containment
`BoundaryCoveringSlot.ae_coveringCubeError_le_representative` consumes. -/
theorem translateSet_cubeSet_flushCoveringCube_subset_anchorParent {n m : ℤ}
    (hnm : n + 2 ≤ m) {z : Vec d} (hz : z ∈ openCubeSet (originCube d m))
    (i : Fin d) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    translateSet (wellPlacedCentre (flushSubCentre z m n i σ) m (n + 2) - z)
        (cubeSet (originCube d (n + 2))) ⊆
      cubeSet (originCube d (n + 3)) := by
  have h27 := half_three_zpow_add_three n
  have h92 := half_three_zpow_add_two n
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  rintro p ⟨y, hy, rfl⟩
  rw [mem_cubeSet_originCube_iff] at hy ⊢
  intro r
  have hyr := hy r
  have hD : (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 2) ≤ (17 / 2 : ℝ) * (3 : ℝ) ^ n := by
    linarith only [h92, hpos]
  have hdisp : |wellPlacedCentre (flushSubCentre z m n i σ) m (n + 2) r - z r| ≤
      (17 / 2 : ℝ) * (3 : ℝ) ^ n :=
    abs_wellPlacedCentre_sub_le (by omega) r hz hD
      (abs_flushSubCentre_sub_le hnm hz i hσ r)
  have hd1 := (abs_le.mp hdisp).1
  have hd2 := (abs_le.mp hdisp).2
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.sub_apply] <;>
    linarith only [hyr.1, hyr.2, hd1, hd2, h27, h92]

/-! ## 5. The covering centre of `K'` is the anchor's own flush centre -/

/-- **The clamp collapses the flush push.**

`wellPlacedCentre (flushSubCentre z m n i σ) m (n+2) = wellPlacedCentre z m (n+2)`
on the boundary branch.  Off the `i`-axis the flush sub-centre already *is* the
clamped anchor centre, and the clamp is idempotent; on the `i`-axis the overhang
`wellPlacedHalfGap m (n+2) < σ zᵢ` puts both `zᵢ` and the pushed coordinate
strictly beyond the clamp gap on the same side, so both clamp to `σ·A`. -/
theorem wellPlacedCentre_flushSubCentre {n m : ℤ} (hnm : n + 2 ≤ m) {z : Vec d}
    {i : Fin d} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hover : wellPlacedHalfGap m (n + 2) < σ * z i) :
    wellPlacedCentre (flushSubCentre z m n i σ) m (n + 2) =
      wellPlacedCentre z m (n + 2) := by
  have hA0 : 0 ≤ wellPlacedHalfGap m (n + 2) := wellPlacedHalfGap_nonneg hnm
  have h9 := three_zpow_add_two n
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  funext r
  by_cases hr : r = i
  · subst hr
    have hc : flushSubCentre z m n r σ r =
        wellPlacedCentre z m (n + 2) r + σ * (((3 : ℝ) ^ (n + 2) - (3 : ℝ) ^ n) / 2) :=
      flushSubCentre_apply_self z m n r σ
    show max (-wellPlacedHalfGap m (n + 2))
        (min (wellPlacedHalfGap m (n + 2)) (flushSubCentre z m n r σ r)) =
      max (-wellPlacedHalfGap m (n + 2))
        (min (wellPlacedHalfGap m (n + 2)) (z r))
    rcases hσ with h | h
    · subst h
      rw [one_mul] at hover
      have hz1 : wellPlacedCentre z m (n + 2) r = wellPlacedHalfGap m (n + 2) := by
        show max (-wellPlacedHalfGap m (n + 2))
            (min (wellPlacedHalfGap m (n + 2)) (z r)) = _
        rw [min_eq_left hover.le, max_eq_right (by linarith only [hA0])]
      rw [hz1, one_mul] at hc
      rw [min_eq_left (by linarith only [hc, h9, hpos]),
        min_eq_left hover.le]
    · subst h
      have hzneg : z r < -wellPlacedHalfGap m (n + 2) := by
        have : (-1 : ℝ) * z r = -(z r) := by ring
        rw [this] at hover
        linarith only [hover]
      have hz1 : wellPlacedCentre z m (n + 2) r = -wellPlacedHalfGap m (n + 2) := by
        show max (-wellPlacedHalfGap m (n + 2))
            (min (wellPlacedHalfGap m (n + 2)) (z r)) = _
        rw [min_eq_right (by linarith only [hzneg, hA0]), max_eq_left hzneg.le]
      rw [hz1] at hc
      rw [min_eq_right (by linarith only [hc, h9, hpos, hA0]),
        min_eq_right (by linarith only [hzneg, hA0]),
        max_eq_left (by linarith only [hc, h9, hpos]),
        max_eq_left hzneg.le]
  · have hc : flushSubCentre z m n i σ r = wellPlacedCentre z m (n + 2) r :=
      flushSubCentre_apply_of_ne z m n σ hr
    show max (-wellPlacedHalfGap m (n + 2))
        (min (wellPlacedHalfGap m (n + 2)) (flushSubCentre z m n i σ r)) =
      wellPlacedCentre z m (n + 2) r
    rw [hc]
    exact congrFun (wellPlacedCentre_wellPlacedCentre hnm z) r

/-! ## 6. Hinge (W) and the frame containments, collected at `K'` -/

/-- See `SealCaccioppoliGeometry.outer_subset_anchorWindow_flushSubCentre`. -/
theorem image_add_flushCoveringCube_subset_anchorWindow {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} (hz : z ∈ openCubeSet (originCube d m)) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ((fun y => wellPlacedCentre (flushSubCentre z m n i σ) m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2))) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) :=
  outer_subset_anchorWindow_flushSubCentre hnm hz i hσ

/-- **The flush sub-cube's own frame containment**, in the `translateSet`
spelling the coarse-graining composition consumes. -/
theorem translateSet_flushSubCube_subset_openCubeSet {n m : ℤ} (hnm : n + 2 ≤ m)
    (z : Vec d) (i : Fin d) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    translateSet (flushSubCentre z m n i σ) (openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m) := by
  rw [← image_add_eq_translateSet]
  exact flushSubCube_subset_openCubeSet hnm z i hσ

end

end Algsuperdiff.Section4.Provider.ExcessDecay
