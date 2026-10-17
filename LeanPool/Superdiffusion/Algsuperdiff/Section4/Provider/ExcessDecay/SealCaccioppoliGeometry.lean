/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanControlWindowCube

/-!
# SealCaccioppoliGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Route (b) of the S4.3 boundary lane: the geometric containment machine-check

## What is at stake

Route (b) wants to price the gradient of the anchor's solution on the
boundary-flush cube

```text
  K := wellPlacedCentre z m (n+2) + □_{n+2}       (`MeanControlWindowCube`)
```

by a *single* application of a boundary Caccioppoli estimate whose **outer**
window still sits inside the frozen first-leg window

```text
  W' := ((z + □_{n+3}) ∩ □_m) .
```

Each proved boundary Caccioppoli A has a *core* set (where the energy is read)
and an *outer* set (where the `L²` right-hand side is read).  A single
application prices `K` iff `core ⊇ K` **and** `outer ⊆ W'`.

## The configuration table (proved here)

Write `x'` for the centre the A is entered at and `k` for its outer scale.

* `BoundaryOuterAssembly.exists_boundaryWindowEnergy_le_dirichletDatum at scale
  `k`: core `truncatedWindow x' m (k-2) = (x'+□_{k-2}) ∩ □_m`, outer
  `wellPlacedCentre x' m k + □_k`.
  - `core ⊇ K` forces `n + 4 ≤ k`
    (`add_four_le_of_flushCube_subset_truncatedWindow`).
  - `outer ⊆ W'` forces `k ≤ n + 3`
    (`scale_le_of_image_add_subset_anchorWindow`).
  - Hence **no** `k` works at all: `no_single_boundaryOuterAssembly_application`.
  - `k = n+2`: core (`not_flushCube_subset_truncatedWindow_core`); outer, and
    this is the pivotal positive fact
    (`image_add_wellPlacedCentre_flush_subset_anchorWindow`).
  - `k = n+3`: core (same lemma, `n+3 < n+4`); outer, and for a second,
    independent reason — equal side lengths force the outer centre to be `z`
    itself (`centre_eq_of_image_add_openCubeSet_subset`) and on the boundary
    branch `z + □_{n+3} ⊄ □_m`
    (`not_image_add_openCubeSet_subset_of_boundaryBranch`); the two combine in
    `not_exists_outer_at_scale_add_three`.
  - `k = n+4`: core at `x' = wellPlacedCentre z m (n+2)`
    (`flushCube_subset_truncatedWindow_self`); outer
    (`not_image_add_subset_anchorWindow_of_add_four_le`).
* `CoarseAssemblyDatum.exists_boundaryWindowEnergy_rebased_le_dirichletDatum:
  core `x + □_n` (an untruncated scale-`n` cube), outer `wellPlacedCentre x m
  (n+2) + □_{n+2}`.
  - `core ⊇ K`: `not_flushCube_subset_image_add_openCubeSet_of_lt` at `j = n <
    n + 2`.
  - `outer ⊆ W'` whenever the entry centre lies in `K`, again by
    `image_add_wellPlacedCentre_flush_subset_anchorWindow`.
* the raw `BoundaryOuterCaccioppoli` form at a `TriadicCube` of scale `k`:
  core `caccioppoliCoreSet (originCube d k) x' = □_k ∩ (x' + □_{k-2})`, outer
  `□_k`, both read in a translated frame `c + ·`.
  - `core ⊇ K` forces `n + 4 ≤ k`
    (`add_four_le_of_flushCube_subset_image_add_caccioppoliCoreSet`), so the
    raw form reproduces exactly the same obstruction.

The single positive fact, and the only one, is the outer inclusion at `k =
n+2`; the core is then two triadic scales too small.  With the read window
taken to be `K` itself, route (b) therefore cannot be closed by one application
of any proved boundary Caccioppoli A.

## Shrinking the read window to the flush scale-`n` sub-cube

The obstruction is entirely caused by insisting that the read window be `K`.
Take instead the scale-`n` sub-cube of `K` that shares `K`'s flush `σeᵢ` face,

```text
  K' := x' + □_n ,     x' := wellPlacedCentre z m (n+2) + σ·½(3^{n+2} − 3^n)·eᵢ ,
```

with `(i, σ)` the coordinate and sign of
`MeanControlWindowCube.overhang_of_boundaryBranch` (`flushSubCentre`).  Then
all four requirements hold at once, at the outer scale `k = n+2`:

* `x' ∈ K` — `flushSubCentre_mem_flushCube` (the displacement is
  `4·3^n < ½·3^{n+2} = 4.5·3^n`, strictly);
* `K' ⊆ K ⊆ □_m` — `flushSubCube_subset_flushCube`,
  `flushSubCube_subset_openCubeSet`, and `K' ⊆ W'`
  (`flushSubCube_subset_anchorWindow`);
* `K'` is flush at the same face — `flushSubCentre_faceLevel`,
  `flushSubCentre_faceLevel_signed`;
* the assembly **fits exactly** at `k = n+2`
  (`flushSubCube_boundaryOuterAssembly_fits`): its core is
  `truncatedWindow x' m (k-2) = truncatedWindow x' m n = K'` — an *equality*,
  since `K' ⊆ □_m` (`truncatedWindow_eq_flushSubCube`) — and its outer window
  `wellPlacedCentre x' m (n+2) + □_{n+2}` is inside `W'` by the pivotal
  positive theorem instantiated at this `x'`
  (`outer_subset_anchorWindow_flushSubCentre`).

So the configuration table for `K'` has one row: read window `K'` (scale `n`),
`k = n+2`, core `= K'` exactly, outer `⊆ W'`.  Every row above is a statement
about the read window `K` (scale `n+2`) and stays exactly as proved; those rows
are what force the smaller read window.

## The pivotal positive theorem, in words

The clamp `wellPlacedCentre · m k` is coordinatewise 1-Lipschitz
(`abs_wellPlacedCentre_sub_wellPlacedCentre_le`) and fixes its own image
(`wellPlacedCentre_wellPlacedCentre`).  So for `x' ∈ K`, with
`cz := wellPlacedCentre z m (n+2)` and `c' := wellPlacedCentre x' m (n+2)`,

```text
  |c'_i - cz_i| ≤ |x'_i - cz_i| < ½·3^{n+2} ,   |cz_i - z_i| < ½·3^{n+2} ,
```

hence `|c'_i - z_i| < 3^{n+2}` and every `y ∈ c' + □_{n+2}` obeys
`|y_i - z_i| < ½·3^{n+2} + 3^{n+2} = ½·3^{n+3}` — the requirement, strictly.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2 (boundary cubes).
* CoarseGraining, `Homogenization/Book/Ch03/Definitions.lean`
  (`caccioppoliCoreSet`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 0. Two elementary translation identities -/

/-! ## 2. The clamp is 1-Lipschitz and idempotent -/

/-- **The well-placed centre is coordinatewise 1-Lipschitz.**  It is the
composition of the two clamps `min A ·` and `max (-A) ·`, each of which is. -/
theorem abs_wellPlacedCentre_sub_wellPlacedCentre_le (m k : ℤ) (x z : Vec d)
    (i : Fin d) :
    |wellPlacedCentre x m k i - wellPlacedCentre z m k i| ≤ |x i - z i| := by
  have hminself : |wellPlacedHalfGap m k - wellPlacedHalfGap m k| = 0 := by
    rw [sub_self, abs_zero]
  have hmaxself : |(-wellPlacedHalfGap m k) - (-wellPlacedHalfGap m k)| = 0 := by
    rw [sub_self, abs_zero]
  have hmin := abs_min_sub_min_le_max (wellPlacedHalfGap m k) (x i)
    (wellPlacedHalfGap m k) (z i)
  rw [hminself, max_eq_right (abs_nonneg (x i - z i))] at hmin
  have hmax := abs_max_sub_max_le_max (-wellPlacedHalfGap m k)
    (min (wellPlacedHalfGap m k) (x i)) (-wellPlacedHalfGap m k)
    (min (wellPlacedHalfGap m k) (z i))
  rw [hmaxself, max_eq_right
    (abs_nonneg (min (wellPlacedHalfGap m k) (x i) -
      min (wellPlacedHalfGap m k) (z i)))] at hmax
  simp only [wellPlacedCentre]
  exact le_trans hmax hmin

/-- **The clamp fixes its own image.**  A clamped point already lies between
`-A` and `A`, so clamping it again changes nothing. -/
theorem wellPlacedCentre_wellPlacedCentre {m k : ℤ} (hkm : k ≤ m) (z : Vec d) :
    wellPlacedCentre (wellPlacedCentre z m k) m k = wellPlacedCentre z m k := by
  funext i
  have hlo : -wellPlacedHalfGap m k ≤ wellPlacedCentre z m k i :=
    neg_wellPlacedHalfGap_le_wellPlacedCentre z m k i
  have hhi : wellPlacedCentre z m k i ≤ wellPlacedHalfGap m k :=
    wellPlacedCentre_le_wellPlacedHalfGap hkm z i
  change max (-wellPlacedHalfGap m k)
      (min (wellPlacedHalfGap m k) (wellPlacedCentre z m k i)) =
    wellPlacedCentre z m k i
  rw [min_eq_right hhi, max_eq_right hlo]

/-! ## 3. The pivotal positive theorem -/

/-- **The outer window of the `k = n+2` entry sits inside the frozen window.**

Let `z ∈ □_m`, `n + 2 ≤ m`, and let `x'` lie in the boundary-flush cube
`K = wellPlacedCentre z m (n+2) + □_{n+2}`.  Then the well-placed covering cube
of `x'` at the *same* scale `n+2` is contained in
`W' = (z + □_{n+3}) ∩ □_m`.

This is the one configuration in which a proved boundary Caccioppoli A reads
its `L²` right-hand side inside the frozen first-leg window. -/
theorem image_add_wellPlacedCentre_flush_subset_anchorWindow {n m : ℤ}
    (hnm : n + 2 ≤ m) {z x' : Vec d} (hz : z ∈ openCubeSet (originCube d m))
    (hx' : x' ∈ (fun y => wellPlacedCentre z m (n + 2) + y) ''
      openCubeSet (originCube d (n + 2))) :
    (fun y => wellPlacedCentre x' m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
  intro p hp
  refine ⟨?_, image_add_wellPlacedCentre_subset_openCubeSet x' hnm hp⟩
  rw [mem_image_add_openCubeSet_coord_iff]
  intro i
  obtain ⟨hplo, hphi⟩ := mem_image_add_openCubeSet_coord_iff.mp hp i
  obtain ⟨hxlo, hxhi⟩ := mem_image_add_openCubeSet_coord_iff.mp hx' i
  have hxabs : |x' i - wellPlacedCentre z m (n + 2) i| <
      (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 2) :=
    abs_lt.mpr ⟨by linarith only [hxlo], by linarith only [hxhi]⟩
  have hlip := abs_wellPlacedCentre_sub_wellPlacedCentre_le m (n + 2) x'
    (wellPlacedCentre z m (n + 2)) i
  rw [wellPlacedCentre_wellPlacedCentre hnm z] at hlip
  obtain ⟨hclo, hchi⟩ := abs_lt.mp (lt_of_le_of_lt hlip hxabs)
  obtain ⟨hzlo, hzhi⟩ := abs_lt.mp (abs_wellPlacedCentre_sub_lt hnm hz i)
  have h3 : (3 : ℝ) ^ (n + 3) = 3 * (3 : ℝ) ^ (n + 2) := by
    rw [show n + 3 = (n + 2) + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  exact ⟨by linarith only [hplo, hclo, hzlo, h3],
    by linarith only [hphi, hchi, hzhi, h3]⟩

/-! ## 4. The refutations -/

/-! ## 5. The flush scale-`n` sub-cube, and the exact fit at `k = n+2` -/

/-- **The centre of the flush scale-`n` sub-cube `K'`.**

The centre of the boundary-flush cube `K = wellPlacedCentre z m (n+2) + □_{n+2}`
pushed by `½(3^{n+2} − 3^n)` in the `σeᵢ` direction, so that `K' = x' + □_n` is
the scale-`n` slab of `K` sharing `K`'s `σeᵢ` face. -/
def flushSubCentre (z : Vec d) (m n : ℤ) (i : Fin d) (σ : ℝ) : Vec d :=
  fun r => wellPlacedCentre z m (n + 2) r +
    (if r = i then σ * (((3 : ℝ) ^ (n + 2) - (3 : ℝ) ^ n) / 2) else 0)

theorem flushSubCentre_apply (z : Vec d) (m n : ℤ) (i : Fin d) (σ : ℝ) (r : Fin d) :
    flushSubCentre z m n i σ r = wellPlacedCentre z m (n + 2) r +
      (if r = i then σ * (((3 : ℝ) ^ (n + 2) - (3 : ℝ) ^ n) / 2) else 0) := rfl

theorem flushSubCentre_apply_self (z : Vec d) (m n : ℤ) (i : Fin d) (σ : ℝ) :
    flushSubCentre z m n i σ i =
      wellPlacedCentre z m (n + 2) i + σ * (((3 : ℝ) ^ (n + 2) - (3 : ℝ) ^ n) / 2) := by
  rw [flushSubCentre_apply, ite_eq_left (rfl : i = i)]

theorem flushSubCentre_apply_of_ne (z : Vec d) (m n : ℤ) {i r : Fin d} (σ : ℝ)
    (hr : r ≠ i) :
    flushSubCentre z m n i σ r = wellPlacedCentre z m (n + 2) r := by
  rw [flushSubCentre_apply, ite_eq_right hr, add_zero]

/-- The scale identity `3^{n+2} = 9·3^n`, used throughout this section. -/
theorem three_zpow_add_two (n : ℤ) : (3 : ℝ) ^ (n + 2) = 9 * (3 : ℝ) ^ n := by
  rw [show n + 2 = n + 1 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0),
    zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- ** The shrunken centre lies in the flush cube `K`.**

Its displacement from `K`'s centre is `4·3^n`, strictly below the half side
`½·3^{n+2} = 4.5·3^n`.  This is what feeds the pivotal positive theorem. -/
theorem flushSubCentre_mem_flushCube {n m : ℤ} (z : Vec d) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    flushSubCentre z m n i σ ∈
      (fun y => wellPlacedCentre z m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2)) := by
  rw [mem_image_add_openCubeSet_coord_iff]
  intro r
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have h9 := three_zpow_add_two n
  have hx := flushSubCentre_apply z m n i σ r
  by_cases hr : r = i
  · rw [ite_eq_left hr] at hx
    rcases hσ with h | h <;> subst h <;>
      exact ⟨by linarith only [hx, hpos, h9], by linarith only [hx, hpos, h9]⟩
  · rw [ite_eq_right hr, add_zero] at hx
    exact ⟨by linarith only [hx, hpos, h9], by linarith only [hx, hpos, h9]⟩

/-- ** `K' ⊆ K`.**  The scale-`n` slab sits inside the scale-`(n+2)` cube: `4·3^n +
½·3^n = 4.5·3^n = ½·3^{n+2}`, strictly. -/
theorem flushSubCube_subset_flushCube {n m : ℤ} (z : Vec d) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ((fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n)) ⊆
      ((fun y => wellPlacedCentre z m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2))) := by
  intro p hp
  rw [mem_image_add_openCubeSet_coord_iff] at hp ⊢
  intro r
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have h9 := three_zpow_add_two n
  have hpr := hp r
  have hx := flushSubCentre_apply z m n i σ r
  by_cases hr : r = i
  · rw [ite_eq_left hr] at hx
    rcases hσ with h | h <;> subst h <;>
      exact ⟨by linarith only [hpr.1, hpr.2, hx, hpos, h9],
        by linarith only [hpr.1, hpr.2, hx, hpos, h9]⟩
  · rw [ite_eq_right hr, add_zero] at hx
    exact ⟨by linarith only [hpr.1, hpr.2, hx, hpos, h9],
      by linarith only [hpr.1, hpr.2, hx, hpos, h9]⟩

/-- ** `K' ⊆ □_m`.** -/
theorem flushSubCube_subset_openCubeSet {n m : ℤ} (hnm : n + 2 ≤ m) (z : Vec d)
    (i : Fin d) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ((fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n)) ⊆
      openCubeSet (originCube d m) :=
  (flushSubCube_subset_flushCube z i hσ).trans
    (image_add_wellPlacedCentre_subset_openCubeSet z hnm)

theorem flushSubCube_subset_anchorWindow {n m : ℤ} (hnm : n + 2 ≤ m) {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ((fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n)) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) :=
  (flushSubCube_subset_flushCube z i hσ).trans
    (image_add_wellPlacedCentre_z_subset_anchorWindow hnm hz)

/-- ** `K'` is flush at the same face as `K`.**

The `σeᵢ` face of `K' = x' + □_n` lies exactly in the frontier hyperplane
`{σ y_i = ½·3^m}` of `□_m`, in the same normal form as
`MeanControlWindowCube.wellPlacedCentre_faceLevel`. -/
theorem flushSubCentre_faceLevel {n m : ℤ} (hnm : n + 2 ≤ m) {z : Vec d}
    {i : Fin d} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hover : wellPlacedHalfGap m (n + 2) < σ * z i) :
    σ * flushSubCentre z m n i σ i + (1 / 2 : ℝ) * (3 : ℝ) ^ n =
      (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  have hface := wellPlacedCentre_faceLevel hnm hσ hover
  have h9 := three_zpow_add_two n
  rw [flushSubCentre_apply_self]
  rcases hσ with h | h <;> subst h <;> linarith only [hface, h9]

theorem flushSubCentre_faceLevel_signed {n m : ℤ} (hnm : n + 2 ≤ m) {z : Vec d}
    {i : Fin d} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hover : wellPlacedHalfGap m (n + 2) < σ * z i) :
    flushSubCentre z m n i σ i + σ * ((3 : ℝ) ^ n / 2) =
      σ * ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  have hlevel := flushSubCentre_faceLevel hnm hσ hover
  rcases hσ with h | h <;> subst h <;> linarith only [hlevel]

/-- **(core) The assembly's energy window at `k = n+2` IS `K'`.**

`truncatedWindow x' m n = (x' + □_n) ∩ □_m = x' + □_n = K'`, an equality
because `K' ⊆ □_m`.  No covering loss is incurred on the left-hand side. -/
theorem truncatedWindow_eq_flushSubCube {n m : ℤ} (hnm : n + 2 ≤ m) (z : Vec d)
    (i : Fin d) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    truncatedWindow (flushSubCentre z m n i σ) m n =
      (fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n) := by
  change ((fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n)) ∩
      openCubeSet (originCube d m) =
    (fun y => flushSubCentre z m n i σ + y) '' openCubeSet (originCube d n)
  exact Set.inter_eq_left.mpr (flushSubCube_subset_openCubeSet hnm z i hσ)

/-- **(outer) The assembly's outer window at `k = n+2` is inside `W'`.**

The pivotal positive theorem, instantiated at the shrunken centre. -/
theorem outer_subset_anchorWindow_flushSubCentre {n m : ℤ} (hnm : n + 2 ≤ m)
    {z : Vec d} (hz : z ∈ openCubeSet (originCube d m)) (i : Fin d) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ((fun y => wellPlacedCentre (flushSubCentre z m n i σ) m (n + 2) + y) ''
        openCubeSet (originCube d (n + 2))) ⊆
      (((fun y => z + y) '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) :=
  image_add_wellPlacedCentre_flush_subset_anchorWindow hnm hz
    (flushSubCentre_mem_flushCube z i hσ)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
