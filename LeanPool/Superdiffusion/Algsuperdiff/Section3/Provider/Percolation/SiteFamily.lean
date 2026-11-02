/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CutoffSampleRange
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.SupMeasurability

/-!
# SiteFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The scale-resolved bad-event family of `l.percolation.bad.clusters`

The aggregate extended bad event `B^*(z + square_j)` is **not** finite range at
any fixed range: its oscillation part `B_osc` is a union over *all* shells
`L > j`, and the shell `j_L` has range `3^L`.  The manuscript therefore never
feeds `B^*` itself into the abstract percolation lemma
`l.percolation.bound.general` (ABK26); it feeds a
*two-indexed* family, the scale-`L` bad events of the proof of
`l.percolation.bad.clusters` (ABK26):

```
B_0(z + cu_{m-h})   = ⋃_{i=0}^{9} ⋃_{z'} B_loc(z' + cu_{m-h-i})
B_L(z + cu_{m-h})   = ⋃_{i=0}^{9} ⋃_{z'} B_{osc, m-h-i+L}(z' + cu_{m-h-i})   (L ≥ 1)
```

with `B^*(z + cu_{m-h}) ⊆ ⋃_{L ∈ N_0} B_L(z + cu_{m-h})`.

This module defines that family as `badScaleEvent`, proves the manuscript's
inclusion, and proves the *locality* half of the independence requirement of
`l.percolation.bound.general` for every positive level: the level-`l` event of
a cube of scale `j` is measurable for the integral-local sigma-field of the
shells of index at most `j + l` on a ball of radius `3^j` around the cube's
base point.  Independence at the matching separation is then the proved cutoff
range lemma.

## Range constants (disclosed)

* `cubeTreeRegion Q` — the union of the closed cubes of the nine-generation
  descendant tree of `Q` — is contained in `Metric.closedBall (cubeBasePoint Q)
  (3 ^ Q.scale)`, i.e. in the closed sup-ball of radius `3^j` (twice the closed
  cube `z + \bar{square}_j`).  The factor `2` is the crude bound
  `dist(z', z) + 3^{j-i}/2 ≤ 3^j/2 + 3^j/2`; it is not optimized.
* `badScaleEvent M Q (l+1)` reads only shells of index `≤ Q.scale + l + 1`.
* Consequently two cubes whose `3^{Q.scale}`-balls are separated by `√d ·
  3^{Q.scale + l + 1}` in the *Euclidean* norm carry independent level-`≤ l+1`
  information.  The `√d` is the ℓ∞-to-Euclidean conversion already built into
  `indep_lowerShellLocalSigma_of_cutoff_separation`; it is the literal
  hypothesis shape of the proved lemma and is not weakened here.

## Main definitions

* `cubeTreeRegion`: the spatial region read by the whole descendant tree.
* `badScaleEvent`: the manuscript's `B_L(z + cu_{m-h})`.
* `cutoffShellLocalSigma`: the cutoff-sample sigma-field of the integral-local
  information in `U` of every shell of index at most `n`.

## Main results

* `badExtended_subset_iUnion_badScaleEvent`: the manuscript's own inclusion.
* `measurableSet_badScaleEvent_succ_cutoffShellLocal`: locality of every
  positive level.
* `closedBall_cubeBasePoint_subset_cubeTreeRegion`,
  `shellCoordinateLocalSigma_le_cutoffShellLocalSigma`: the two containments
  that turn the range constants above into locality statements.

## References

* ABK26, `e.bad.cluster.def` and `l.percolation.bad.clusters`.
* ABK26, `l.percolation.bound.general`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The spatial region of the nine-generation descendant tree -/

/-- The union of the closed cubes of the nine-generation triadic descendant
tree of `Q`.  This is exactly the region whose shell data the extended bad
event `B^*(z + square_j)` reads. -/
def cubeTreeRegion (Q : TriadicCube d) : Set (Vec d) :=
  ⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
    Metric.closedBall (cubeBasePoint R) ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale)


theorem closedBall_cubeBasePoint_subset_cubeTreeRegion {Q R : TriadicCube d}
    {i : ℕ} (hi : i ∈ Finset.range 10)
    (hR : R ∈ descendantsAtScale Q (Q.scale - (i : ℤ))) :
    Metric.closedBall (cubeBasePoint R) ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale) ⊆
      cubeTreeRegion Q := by
  refine Set.Subset.trans (Set.subset_biUnion_of_mem (u := fun R : TriadicCube d =>
    Metric.closedBall (cubeBasePoint R) ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale)) hR) ?_
  exact Set.subset_biUnion_of_mem (u := fun i : ℕ =>
    ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
      Metric.closedBall (cubeBasePoint R) ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale)) hi


/-! ## The manuscript's scale-resolved bad events -/

/-- The manuscript's `B_L(z + cu_{m-h})` (ABK26), at the cube `Q = z +
cu_{m-h}`.  Level `0` collects the local ellipticity failures of the whole
nine-generation tree; level `l + 1` collects, for each tree member `R`, the
single-shell oscillation event of `e.BoscL.def` at shell index `R.scale + l +
1`. -/
def badScaleEvent (M : ABKModel d) (Q : TriadicCube d) :
    ℕ → Set (CutoffSample d)
  | 0 => ⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
      badLoc M R
  | (l + 1) => ⋃ i ∈ Finset.range 10, ⋃ R ∈ descendantsAtScale Q (Q.scale - (i : ℤ)),
      badOscAt M R (R.scale + ((l : ℤ) + 1))

theorem measurableSet_badScaleEvent (M : ABKModel d) (Q : TriadicCube d) (l : ℕ) :
    MeasurableSet (badScaleEvent M Q l) := by
  cases l with
  | zero =>
      exact Finset.measurableSet_biUnion _ fun i _ =>
        Finset.measurableSet_biUnion _ fun R _ => measurableSet_badLoc M R
  | succ l =>
      exact Finset.measurableSet_biUnion _ fun i _ =>
        Finset.measurableSet_biUnion _ fun R _ =>
          measurableSet_badOscAt M R (R.scale + ((l : ℤ) + 1))

/-- **The manuscript's own scale resolution of the extended bad event** (ABK26).
Nothing is added: the inclusion is `e.Bosc.decomp` applied inside each member of
the nine-generation tree. -/
theorem badExtended_subset_iUnion_badScaleEvent (M : ABKModel d)
    (Q : TriadicCube d) :
    badExtended M Q ⊆ ⋃ l : ℕ, badScaleEvent M Q l := by
  intro omega homega
  obtain ⟨i, hi, homega⟩ := Set.mem_iUnion₂.1 homega
  obtain ⟨R, hR, homega⟩ := Set.mem_iUnion₂.1 homega
  rcases homega with hosc | hloc
  · obtain ⟨L, homega⟩ := Set.mem_iUnion.1 hosc
    obtain ⟨hL, homega⟩ := Set.mem_iUnion.1 homega
    refine Set.mem_iUnion.2 ⟨(L - R.scale - 1).toNat + 1, ?_⟩
    have hindex : R.scale + (((L - R.scale - 1).toNat : ℤ) + 1) = L := by
      have : ((L - R.scale - 1).toNat : ℤ) = L - R.scale - 1 := Int.toNat_of_nonneg (by omega)
      omega
    refine Set.mem_iUnion₂.2 ⟨i, hi, Set.mem_iUnion₂.2 ⟨R, hR, ?_⟩⟩
    rw [hindex]
    exact homega
  · exact Set.mem_iUnion.2 ⟨0, Set.mem_iUnion₂.2 ⟨i, hi, Set.mem_iUnion₂.2 ⟨R, hR, hloc⟩⟩⟩

/-! ## The cutoff-sample local sigma-fields -/

/-- The cutoff-sample sigma-field carrying the integral-local information in
`U` of every shell of index at most `n`. -/
abbrev cutoffShellLocalSigma (n : ℤ) (U : Set (Vec d)) :
    MeasurableSpace (CutoffSample d) :=
  (lowerShellLocalSigma n U).comap Subtype.val

/-- A single shell of index at most `n` is carried by the lower-shell local
sigma-field at `n`. -/
theorem shellCoordinateLocalSigma_le_cutoffShellLocalSigma {L n : ℤ} (hLn : L ≤ n)
    (U : Set (Vec d)) :
    shellCoordinateLocalSigma (d := d) L U ≤ cutoffShellLocalSigma (d := d) n U := by
  refine le_trans (le_of_eq ?_) (MeasurableSpace.comap_mono
    (le_iSup (fun r : ℕ => (ShellField.lihLocalSigma U).comap
      (fun omega : ShellSeq d => omega (n - (r : ℤ)))) (n - L).toNat))
  have hidx : n - (((n - L).toNat : ℤ)) = L := by
    have : (((n - L).toNat : ℤ)) = n - L := Int.toNat_of_nonneg (by omega)
    omega
  rw [MeasurableSpace.comap_comp]
  simp only [Function.comp_def, hidx]

/-- **Locality of every positive level of the site family.**  The level-`l + 1`
bad event of the cube `Q` is measurable for the integral-local information of
the shells of index at most `Q.scale + l + 1` in the tree region of `Q`. -/
theorem measurableSet_badScaleEvent_succ_cutoffShellLocal (M : ABKModel d)
    (Q : TriadicCube d) (l : ℕ) {U : Set (Vec d)} (hU : cubeTreeRegion Q ⊆ U) :
    MeasurableSet[cutoffShellLocalSigma (Q.scale + (l : ℤ) + 1) U]
      (badScaleEvent M Q (l + 1)) := by
  let : MeasurableSpace (CutoffSample d) :=
    cutoffShellLocalSigma (Q.scale + (l : ℤ) + 1) U
  refine Finset.measurableSet_biUnion _ fun i hi => ?_
  refine Finset.measurableSet_biUnion _ fun R hR => ?_
  have hscale : R.scale = Q.scale - (i : ℤ) :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hshell : R.scale + ((l : ℤ) + 1) ≤ Q.scale + (l : ℤ) + 1 := by omega
  have hregion : Metric.closedBall (cubeBasePoint R)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale) ⊆ U :=
    (closedBall_cubeBasePoint_subset_cubeTreeRegion hi hR).trans hU
  exact shellCoordinateLocalSigma_le_cutoffShellLocalSigma hshell U _
    (measurableSet_badOscAt_shellLocal M R (R.scale + ((l : ℤ) + 1)) hregion)

/-! ## The independence input -/


end

end Algsuperdiff.Section3.Provider.Percolation
