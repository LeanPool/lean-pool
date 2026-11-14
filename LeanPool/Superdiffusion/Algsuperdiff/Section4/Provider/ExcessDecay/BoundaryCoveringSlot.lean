/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorPrefactor
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoveringSlotObstruction
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ReindexSlot

/-!
# BoundaryCoveringSlot

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary lane's covering cube, read at the slot `n+3`

`CoveringSlotObstruction` measured exactly this: on the
boundary branch the covering cube `c + □_{n+2}`, `c = wellPlacedCentre x m
(n+2)`, **leaves** the `n+2` good-event slot's cube, and **always** sits inside
the `n+3` one.  The frozen general clause puts its slot at
`n+3` precisely so that this positive half is usable.  This module cashes
it in, at the level the boundary Caccioppoli step consumes.

Three steps, each proved elsewhere and composed here:

1. **the half-open containment** — `CoveringSlotObstruction`'s open-cube
   containment `c + □_{n+2} ⊆ z + □_{n+3}` re-derived in the *half-open*
   realization the off-grid transports require (the margin is ample: the centre
   moves by less than `6·3^n` and the half-open child reaches `4.5·3^n`, against
   the parent's `13.5·3^n`);
2. **the off-grid transport at depth `1`** — `OffGridErrorFluxCorrected`'s root
   transport at `K = □_{n+3}`, `P = □_{n+2}`, so the depth factor is a single
   `3^{u·1}`, i.e. `3^{s/8} ≤ 3^{1/8} < 1.15`;
3. **the good event at the `n+3` slot** — `ReindexSlot`'s `(n+3)` caps, read at
   `L ≥ n+3` (the frozen binder `n + 3 ≤ m ≤ L`).

**No antisymmetric-shift conversion is used**: nothing below converts `Λ` or `λ`
by the antisymmetric-shift invariance.  The whole chain runs at the `(n+3)`
family `parentRebasedFamily M L (n+3) c z ω` — the covering cube's own frame
*at the parent's constant* — which is the family `InteriorRebase` builds and the
one the equation transports to for free.

**The `q = 1` ingredients are supplied here**, at the covering cube:
`CaccioppoliInteriorPrefactor`'s constant-`1` comparisons `Λ_{u,1} ≤ Λ_{u/2,2}`
and `λ_{u,1}^{-1} ≤ λ_{u/2,2}^{-1}` turn the `q = 2` ratio cap into the `q = 1`
ingredients `Λ_{u,1}`, `λ_{u,1}^{-1}` and `Θ` that
`caccioppoliWithRHSPrefactor` reads.

## What this does *not* do

It does not prove the boundary clause.  The boundary lane still needs its
analytic half (the trace-measure Poincaré and the Stampacchia step), the
boundary energy assembly at this family, and the `L²`/window transport onto the
general clause's window.  Nothing below is an instance, or a fraction, of any
source node.

## References

* ABK26, `e.mathcalE.stability.applied`; the boundary application of
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The half-open containment of the covering cube in the `n+3` parent -/

/-- Displacement control places the clamped covering cube in its anchor parent. -/
theorem translateSet_cubeSet_coveringCube_subset_anchorParent_of_sub {n m : ℤ}
    {x z : Vec d} (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hw : x - z ∈ openCubeSet (originCube d (n + 1))) :
    translateSet (wellPlacedCentre x m (n + 2) - z) (cubeSet (originCube d (n + 2))) ⊆
      cubeSet (originCube d (n + 3)) := by
  rw [mem_openCubeSet_originCube_iff] at hw
  have h1 : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := by
    rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have h2 : (3 : ℝ) ^ (n + 2) = 3 ^ n * 9 := by
    have hn : n + 2 = n + 1 + 1 := by ring
    rw [hn, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), h1]
    ring
  have h3 : (3 : ℝ) ^ (n + 3) = 3 ^ n * 27 := by
    have hn : n + 3 = n + 2 + 1 := by ring
    rw [hn, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), h2]
    ring
  have hpos : (0 : ℝ) < 3 ^ n := zpow_pos (by norm_num) n
  rintro p ⟨y, hy, rfl⟩
  rw [mem_cubeSet_originCube_iff] at hy ⊢
  intro i
  have hyi := hy i
  have hwi := hw i
  have hci := sub_wellPlacedCentre_coord_bound hnm hx i
  simp only [Pi.sub_apply] at hwi
  rw [h1] at hwi
  rw [h2] at hyi hci
  rw [h3]
  refine ⟨?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.sub_apply] <;>
    linarith only [hyi.1, hyi.2, hwi.1, hwi.2, hci.1, hci.2, hpos]

/-- **The covering cube inside the `n+3` parent, half-open.** -/
theorem translateSet_cubeSet_coveringCube_subset_anchorParent {n m : ℤ} {x z : Vec d}
    (hnm : n + 2 ≤ m) (hx : x ∈ openCubeSet (originCube d m))
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    translateSet (wellPlacedCentre x m (n + 2) - z) (cubeSet (originCube d (n + 2))) ⊆
      cubeSet (originCube d (n + 3)) := by
  exact translateSet_cubeSet_coveringCube_subset_anchorParent_of_sub hnm hx
    (sub_mem_openCubeSet_of_anchorGeometry hgeom)

/-! ## 2. The off-grid transport at depth one -/

/-- The scale gap of the `n+3` parent/covering pair, as a natural number. -/
private theorem originCube_scale_gap_one (n : ℤ) :
    ((originCube d (n + 3)).scale - (originCube d (n + 2)).scale).toNat = 1 := by
  have h : (originCube d (n + 3)).scale - (originCube d (n + 2)).scale = 1 := by
    simp only [originCube]
    ring
  rw [h]
  rfl

/-- **The covering cube's coarse-graining error against the general clause's
representative.**

At every index `t` strictly above the good-event index `s/8` and at most `1/2`,
the covering cube's `q = 2` error at the `(n+3)` re-based family is bounded by
the frozen clause's own `fluxCorrectedErrorRepresentative M L (n+3) ⟨s/8⟩`,
with the **depth-one** factor `3^{s/8}` (at most `3^{1/8} < 1.15`). -/
theorem ae_coveringCubeError_le_representative_gapThree [NeZero d] (M : ABKModel d)
    (L n m : ℤ) (z : Vec d) {s t : ℝ} (hs : 0 < s) (hst : s / 8 < t) (ht : t ≤ 1 / 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d,
        translateSet (wellPlacedCentre x m (n + 2) - z) (cubeSet (originCube d (n + 2))) ⊆
            cubeSet (originCube d (n + 3)) →
        Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) t .infinity (.finite 2)
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d t (s / 8)) *
            ((3 : ℝ) ^ (s / 8) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  have hbase := (GoodEvents.measurePreserving_translateCutoffSample M
      z).quasiMeasurePreserving.ae
    (ae_offGridErrorFunctional_le_fluxCorrectedErrorFunctionalAtRoot
      M L (n + 3) (originCube d (n + 3))
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))
      (by linarith only [hs] : (0 : ℝ) < s / 8) hst ht)
  filter_upwards [hbase] with omega hall
  intro x hhinge
  have hstep := hall (wellPlacedCentre x m (n + 2) - z) (originCube d (n + 2))
    (originCube d (n + 3)) hhinge
  rw [originCube_scale_gap_one (d := d) n,
    fluxCorrectedErrorFunctionalAtRoot_eq_representative M L (n + 3)
      ⟨s / 8, by linarith only [hs]⟩] at hstep
  have hexp : (s / 8 * ((1 : ℕ) : ℝ)) = s / 8 := by
    push_cast
    ring
  rw [hexp] at hstep
  rwa [homogenizationErrorOnCube_parentRebasedFamily_eq_offGrid M L (n + 3) (n + 2)
    (wellPlacedCentre x m (n + 2)) z omega (by linarith only [hs, hst] : (0 : ℝ) < t)
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3)))]


theorem ae_coveringCubeError_le_representative [NeZero d] (M : ABKModel d)
    (L n m : ℤ) (z : Vec d) {s t : ℝ} (hs : 0 < s) (hst : s / 8 < t) (ht : t ≤ 1 / 2) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ x : Vec d, n + 2 ≤ m → x ∈ openCubeSet (originCube d m) →
        (fun y => x + y) '' openCubeSet (originCube d n) ⊆
            ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
              openCubeSet (originCube d m) →
        Ch02.HomogenizationErrorOnCube (originCube d (n + 2)) t .infinity (.finite 2)
            (parentRebasedFamily M L (n + 3) (wellPlacedCentre x m (n + 2)) z omega)
            (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 3))) ≤
          Real.sqrt (offGridStabilityConst d t (s / 8)) *
            ((3 : ℝ) ^ (s / 8) *
              fluxCorrectedErrorRepresentative M L (n + 3)
                ⟨s / 8, by linarith only [hs]⟩
                (Cutoff.translateCutoffSample z omega)) := by
  filter_upwards [ae_coveringCubeError_le_representative_gapThree M L n m z hs hst ht]
    with omega herror
  intro x hnm hx hgeom
  exact herror x (translateSet_cubeSet_coveringCube_subset_anchorParent hnm hx hgeom)

/-! ## 3. The covering cube's ellipticity data, capped on the good event -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
