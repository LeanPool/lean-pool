/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.BoundaryDistance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.ClusterGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.LayerDensity

/-!
# ClusterLayerConstraint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `l.bad.clusters.geometry`, clause (1): the layer constraint

This module proves the **layer constraint** of ABK26's Lemma
`l.bad.clusters.geometry` for the closure-touching neighborhood `𝒩(𝒞)` of a
connected component `𝒞` of the bad family:

* `whitneyNeighborhood_layer_index_close` — any two cubes of `𝒩(𝒞)` occupy
  equal or neighbouring Whitney layers;
* `whitneyNeighborhood_finite_and_mem_leastLayer_or_succ` — consequently `𝒩(𝒞)`
  is **finite** and contained in its least occupied layer together with that
  layer's successor, which is the manuscript's `𝒩(𝒞) ⊆ 𝒲(□_m,n-1) ∪ 𝒲(□_m,n) ∪
  𝒲(□_m,n+1)` read at the least occupied layer ("in particular, every
  2-connected component intersects at most two consecutive layers").

Only the **deterministic geometric layer** is delivered: as in the manuscript,
the statements are conditional on avoidance of the bad-cluster diameter failure,
carried by the binder `havoid` below.  No probability estimate is used.

## The avoidance binder

`havoid` is shaped exactly on the conclusion of the proved distance-two
machinery,

```lean
havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
  (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ))
```

which is `e.diameter.deterministic` in the cube-side units of
`Percolation.badClusterDiam`.  It is discharged verbatim by the proved
`Percolation.badClusterDiam_lt_of_hsep_le` at `hs:= Percolation.hsep M m E b
omega`, since `h_n ≥ h_hat_sep` for every `n` (`hsep_le_whitneyScaleSeq`); this is
the concrete corollary
`badFamily_whitneyNeighborhood_finite_and_mem_leastLayer_or_succ` at the end of
the module.  In the abstract helper, `havoid` remains an explicit conditional A
obligation; the concrete corollary discharges it from the manuscript's
`p.minimal.scale.separation` input rather than adding it to a source-facing
statement.

## The proof, and where each ingredient lives

1. *"Cubes in layer `n` lie at distance of order `3^{m-n}` from `∂□_m`; cubes
   in layers differing by two or more occupy disjoint regions, so adjacent
   cubes come from consecutive layers."* —
   `two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers` and
   `whitneyLayer_index_close_of_cubeTouch` of `BoundaryDistance`, at the
   dimension-free `c = 2/3`.
2. *"`□` is a descendant of `□` within `< 9` generations, so `𝓑(□)` forces
   `𝓑^*(□)`; adjacent cubes lift to identical or adjacent cubes at scale
   `3^{m-n_min-h_{n_min}}`."* (the diameter display) — `IsWhitneyLift` and
   the dictionary below, with the generation count supplied by the proved
   `whitneyDepth_sub_lt_ten` and the site adjacency proved as
   `Percolation.Connected₂` (distance two).
3. *"Applying `e.diameter.deterministic` with `h = n_min + h_{n_min}` …
   choosing `k₀` large enough that `4·3^{-(1-b)k₀} < c`."* (as corrected) —
   the proved gate `four_mul_three_rpow_whitneyDepth_lt_two_thirds` at `k₀ ≥
   3`.

The core induction runs along the chain relation of the component and carries
the lifted site path with it, so that at the first cube that would reach layer
`n_min + 2` the diameter bound and the layer separation collide.

## The two readings of `𝒩(𝒥)`

`whitneyNeighborhood` is the *cubewise* reading `∃ □' ∈ 𝒥, dist(□,□') = 0`,
which for an infinite `𝒥` is strictly smaller than the printed
`dist(□, ⋃𝒥) = 0`.  The finiteness delivered here proves the local comparison:
`𝒩(𝒞)` is
finite, hence so is `𝒞`, and on a finite family the two readings coincide
(`whitneyNeighborhood_eq_whitneyNeighborhoodDist_of_finite`, applied to the
component in `whitneyNeighborhood_eq_dist_reading`).

## References

* ABK26, `l.bad.clusters.geometry`.
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The least occupied Whitney layer -/

/-- The set of Whitney layers a family occupies. -/
def whitneyLayerIndices (m : ℤ) (hn : ℕ → ℕ) (J : Set (TriadicCube d)) : Set ℕ :=
  {n | ∃ Q ∈ J, Q ∈ whitneyLayer m hn n}

/-- The least Whitney layer a family occupies (`n_min`). -/
def leastWhitneyLayer (m : ℤ) (hn : ℕ → ℕ) (J : Set (TriadicCube d)) : ℕ :=
  sInf (whitneyLayerIndices m hn J)

theorem leastWhitneyLayer_le_of_mem {m : ℤ} {hn : ℕ → ℕ} {J : Set (TriadicCube d)}
    {n : ℕ} {Q : TriadicCube d} (hQ : Q ∈ J) (hQn : Q ∈ whitneyLayer m hn n) :
    leastWhitneyLayer m hn J ≤ n :=
  Nat.sInf_le ⟨Q, hQ, hQn⟩

theorem exists_mem_leastWhitneyLayer {m : ℤ} {hn : ℕ → ℕ} {J : Set (TriadicCube d)}
    (hne : J.Nonempty) (hJ : J ⊆ whitneyPartition m hn) :
    ∃ Q ∈ J, Q ∈ whitneyLayer m hn (leastWhitneyLayer m hn J) := by
  obtain ⟨Q, hQ⟩ := hne
  obtain ⟨n, hQn⟩ := hJ hQ
  have hne' : (whitneyLayerIndices m hn J).Nonempty := ⟨n, Q, hQ, hQn⟩
  exact Nat.sInf_mem hne'

/-! ## The lift to the base lattice -/

/-- **The lift `□`**: `A` is a depth-`h` triadic descendant of `□_m` having the
Whitney cube `V` among its descendants within the nine generations of
`e.Bext.def`. -/
def IsWhitneyLift (m : ℤ) (h : ℕ) (V A : TriadicCube d) : Prop :=
  A ∈ descendantsAtDepth (originCube d m) h ∧ ∃ g : ℕ, g < 10 ∧ V ∈ descendantsAtDepth A g

theorem closedBall_subset_closedBall_of_mem_descendantsAtDepth {A V : TriadicCube d}
    {g : ℕ} (h : V ∈ descendantsAtDepth A g) :
    Metric.closedBall (cubeCenter V) (HCPolySupport.cubeRadius V) ⊆
      Metric.closedBall (cubeCenter A) (HCPolySupport.cubeRadius A) := by
  rw [← closure_cubeSet_eq_closedBall, ← closure_cubeSet_eq_closedBall]
  exact closure_mono (cubeSet_subset_of_mem_descendantsAtDepth h)

/-- Every Whitney cube of a layer at least as deep as `h` has a lift at depth
`h`, provided the generation gap stays inside the nine generations of
`e.Bext.def`. -/
theorem exists_isWhitneyLift {m : ℤ} {hn : ℕ → ℕ} {n h : ℕ} {V : TriadicCube d}
    (hV : V ∈ whitneyLayer m hn n) (hh : h ≤ n + hn n) (hgap : n + hn n - h < 10) :
    ∃ A, IsWhitneyLift m h V A := by
  have hVd := mem_descendantsAtDepth_of_mem_whitneyLayer hV
  have hsplit : n + hn n = h + (n + hn n - h) := by omega
  rw [hsplit] at hVd
  obtain ⟨A, hA, hVA⟩ := exists_descendant_ancestor_at_depth h (n + hn n - h) hVd
  refine ⟨A, ?_⟩
  show A ∈ descendantsAtDepth (originCube d m) h ∧
    ∃ g : ℕ, g < 10 ∧ V ∈ descendantsAtDepth A g
  exact ⟨hA, n + hn n - h, hgap, hVA⟩

/-- The bad event at a Whitney cube forces the extended bad event at its lift: the
manuscript's "`□` is a descendant of `□` within `< 9` generations and `𝓑(□)`
occurs, so `𝓑^*(□)` occurs". -/
theorem badExtended_of_isWhitneyLift {M : ABKModel d} {m : ℤ} {h : ℕ}
    {omega : CutoffSample d} {V A : TriadicCube d} (hlift : IsWhitneyLift m h V A)
    (hbad : omega ∈ BadEvents.bad M V) : omega ∈ BadEvents.badExtended M A := by
  obtain ⟨-, g, hg, hVA⟩ := hlift
  refine Set.mem_biUnion (Finset.mem_range.2 hg) ?_
  refine Set.mem_biUnion ?_ hbad
  have hk : A.scale - (g : ℤ) ≤ A.scale := by omega
  rw [descendantsAtScale_eq_descendantsAtDepth A hk,
    show (A.scale - (A.scale - (g : ℤ))).toNat = g from by omega]
  exact hVA

/-- The lift of a bad Whitney cube is a **bad site** of the base lattice at depth
`h`: this is the entry point into the proved 2-cluster machinery. -/
theorem index_mem_badSiteFinset_of_isWhitneyLift {M : ABKModel d} {m : ℤ} {h : ℕ}
    {omega : CutoffSample d} {V A : TriadicCube d} (hlift : IsWhitneyLift m h V A)
    (hbad : omega ∈ BadEvents.bad M V) :
    A.index ∈ Percolation.badSiteFinset M m h omega := by
  refine Percolation.mem_badSiteFinset_iff.mpr
    ⟨index_mem_cubeFinset_of_mem_descendantsAtDepth hlift.1, ?_⟩
  rw [siteCube_index_of_mem_descendantsAtDepth hlift.1]
  exact badExtended_of_isWhitneyLift hlift hbad

/-- **"Adjacent cubes lift to identical or adjacent cubes"**: the lifts of two
touching Whitney cubes are at lattice sup distance at most one, so in
particular they are 2-adjacent in the sense. -/
theorem latDist_index_le_one_of_cubeTouch {m : ℤ} {h : ℕ} {U W AU AW : TriadicCube d}
    (hU : IsWhitneyLift m h U AU) (hW : IsWhitneyLift m h W AW)
    (htouch : CubeTouch U W) : Percolation.latDist AU.index AW.index ≤ 1 := by
  obtain ⟨hAU, gU, -, hUA⟩ := hU
  obtain ⟨hAW, gW, -, hWA⟩ := hW
  have hAUs : AU.scale = m - (h : ℤ) := by
    have := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hAU
    simpa only [originCube] using this
  have hAWs : AW.scale = m - (h : ℤ) := by
    have := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hAW
    simpa only [originCube] using this
  obtain ⟨z, hzU, hzW⟩ := htouch
  have hlift : CubeTouch AU AW :=
    ⟨z, closedBall_subset_closedBall_of_mem_descendantsAtDepth hUA hzU,
      closedBall_subset_closedBall_of_mem_descendantsAtDepth hWA hzW⟩
  have hcoord := cubeTouch_iff.mp hlift
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - (h : ℤ)) := zpow_pos (by norm_num) _
  refine Percolation.latDist_le_iff.mpr fun j => ?_
  have hj := hcoord j
  rw [cubeRadius_eq_zpow_div_two, cubeRadius_eq_zpow_div_two, hAUs, hAWs] at hj
  simp only [cubeCenter, cubeScaleFactor, hAUs, hAWs] at hj
  have hsub : |((AU.index j : ℤ) : ℝ) - ((AW.index j : ℤ) : ℝ)| ≤ 1 := by
    rw [show ((AU.index j : ℤ) : ℝ) * (3 : ℝ) ^ (m - (h : ℤ)) -
      ((AW.index j : ℤ) : ℝ) * (3 : ℝ) ^ (m - (h : ℤ)) =
      (((AU.index j : ℤ) : ℝ) - ((AW.index j : ℤ) : ℝ)) * (3 : ℝ) ^ (m - (h : ℤ)) from by ring,
      abs_mul, abs_of_pos hpos] at hj
    nlinarith [hj, hpos, abs_nonneg (((AU.index j : ℤ) : ℝ) - ((AW.index j : ℤ) : ℝ))]
  have hint : ((AU.index j - AW.index j).natAbs : ℤ) ≤ (1 : ℤ) := by
    rw [← Int.abs_eq_natAbs]
    have : ((|AU.index j - AW.index j| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      exact hsub
    exact_mod_cast this
  exact_mod_cast hint

/-- The physical distance between two Whitney cubes, in terms of the lattice
distance of their lifts: passing from cube centres to lattice sites costs one
side length in total (the "+1" of the corrected display). -/
theorem norm_cubeCenter_sub_le_of_isWhitneyLift {m : ℤ} {h : ℕ}
    {U W AU AW : TriadicCube d} (hU : IsWhitneyLift m h U AU)
    (hW : IsWhitneyLift m h W AW) :
    ‖cubeCenter U - cubeCenter W‖ ≤
      ((Percolation.latDist AU.index AW.index : ℝ) + 1) * (3 : ℝ) ^ (m - (h : ℤ)) := by
  obtain ⟨hAU, gU, -, hUA⟩ := hU
  obtain ⟨hAW, gW, -, hWA⟩ := hW
  have hAUs : AU.scale = m - (h : ℤ) := by
    have := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hAU
    simpa only [originCube] using this
  have hAWs : AW.scale = m - (h : ℤ) := by
    have := HCPolySupport.scale_eq_sub_of_mem_descendantsAtDepth hAW
    simpa only [originCube] using this
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - (h : ℤ)) := zpow_pos (by norm_num) _
  have hU' : ‖cubeCenter U - cubeCenter AU‖ ≤ (3 : ℝ) ^ (m - (h : ℤ)) / 2 := by
    have hmem := closedBall_subset_closedBall_of_mem_descendantsAtDepth hUA
      ((cubeSet_subset_closedBall U) (cubeCenter_mem_cubeSet U))
    rw [Metric.mem_closedBall, dist_eq_norm, cubeRadius_eq_zpow_div_two, hAUs] at hmem
    exact hmem
  have hW' : ‖cubeCenter AW - cubeCenter W‖ ≤ (3 : ℝ) ^ (m - (h : ℤ)) / 2 := by
    have hmem := closedBall_subset_closedBall_of_mem_descendantsAtDepth hWA
      ((cubeSet_subset_closedBall W) (cubeCenter_mem_cubeSet W))
    rw [Metric.mem_closedBall, dist_eq_norm, cubeRadius_eq_zpow_div_two, hAWs] at hmem
    rw [← norm_neg, neg_sub]
    exact hmem
  have hmid : ‖cubeCenter AU - cubeCenter AW‖ ≤
      (Percolation.latDist AU.index AW.index : ℝ) * (3 : ℝ) ^ (m - (h : ℤ)) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    have hnat := Percolation.coord_le_latDist AU.index AW.index j
    have hint : ((AU.index j - AW.index j).natAbs : ℤ) ≤
        (Percolation.latDist AU.index AW.index : ℤ) := by exact_mod_cast hnat
    have hreal : |((AU.index j : ℤ) : ℝ) - ((AW.index j : ℤ) : ℝ)| ≤
        (Percolation.latDist AU.index AW.index : ℝ) := by
      rw [← Int.abs_eq_natAbs] at hint
      have := (Int.cast_le (R := ℝ)).2 hint
      rw [Int.cast_abs] at this
      push_cast at this ⊢
      exact this
    simp only [Pi.sub_apply, Real.norm_eq_abs, cubeCenter, cubeScaleFactor, hAUs, hAWs]
    rw [show ((AU.index j : ℤ) : ℝ) * (3 : ℝ) ^ (m - (h : ℤ)) -
      ((AW.index j : ℤ) : ℝ) * (3 : ℝ) ^ (m - (h : ℤ)) =
      (((AU.index j : ℤ) : ℝ) - ((AW.index j : ℤ) : ℝ)) * (3 : ℝ) ^ (m - (h : ℤ)) from by ring,
      abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right hreal hpos.le
  have htri : ‖cubeCenter U - cubeCenter W‖ ≤
      ‖cubeCenter U - cubeCenter AU‖ + ‖cubeCenter AU - cubeCenter AW‖ +
        ‖cubeCenter AW - cubeCenter W‖ := by
    calc ‖cubeCenter U - cubeCenter W‖
        ≤ ‖cubeCenter U - cubeCenter AW‖ + ‖cubeCenter AW - cubeCenter W‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (‖cubeCenter U - cubeCenter AU‖ + ‖cubeCenter AU - cubeCenter AW‖) +
            ‖cubeCenter AW - cubeCenter W‖ := by
          gcongr
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  nlinarith [htri, hU', hW', hmid, hpos]

/-! ## The diameter estimate at a common lift scale -/

/-- **The physical diameter estimate at the lift scale.**  Two Whitney cubes whose
lifts are 2-connected inside the bad site set of a common base site `z` have
centres less than `3^{bh}·3^{m-h}` apart: the manuscript's first inequality,
read between cube centres. -/
theorem norm_cubeCenter_sub_lt_of_connected₂ {M : ABKModel d} {m : ℤ} {b : ℝ}
    {h : ℕ} {omega : CutoffSample d} {U W AU AW : TriadicCube d} {z : Fin d → ℤ}
    (hU : IsWhitneyLift m h U AU) (hW : IsWhitneyLift m h W AW)
    (hz : z ∈ Percolation.badSiteFinset M m h omega)
    (hconnU : Percolation.Connected₂ (Percolation.badSiteFinset M m h omega) z AU.index)
    (hconnW : Percolation.Connected₂ (Percolation.badSiteFinset M m h omega) z AW.index)
    (hdiam : (Percolation.badClusterDiam M m h omega z : ℝ) <
      (3 : ℝ) ^ (b * (h : ℝ))) :
    ‖cubeCenter U - cubeCenter W‖ <
      (3 : ℝ) ^ (b * (h : ℝ)) * (3 : ℝ) ^ (m - (h : ℤ)) := by
  have hz' : z ∈ Percolation.cluster₂ (Percolation.badSiteFinset M m h omega) z :=
    Percolation.self_mem_cluster₂ hz
  have hmemU : AU.index ∈ Percolation.cluster₂ (Percolation.badSiteFinset M m h omega) z :=
    Percolation.mem_cluster₂_iff.mpr ⟨hz, hconnU⟩
  have hmemW : AW.index ∈ Percolation.cluster₂ (Percolation.badSiteFinset M m h omega) z :=
    Percolation.mem_cluster₂_iff.mpr ⟨hz, hconnW⟩
  have hlat := Percolation.latDist_le_latDiam hmemU hmemW
  have hcd : Percolation.closedLatDiam
      (Percolation.cluster₂ (Percolation.badSiteFinset M m h omega) z) =
      Percolation.latDiam
        (Percolation.cluster₂ (Percolation.badSiteFinset M m h omega) z) + 1 :=
    Percolation.closedLatDiam_eq_of_nonempty ⟨z, hz'⟩
  have hstep : ((Percolation.latDist AU.index AW.index : ℝ) + 1) ≤
      (Percolation.badClusterDiam M m h omega z : ℝ) := by
    have hnat : Percolation.latDist AU.index AW.index + 1 ≤
        Percolation.badClusterDiam M m h omega z := by
      unfold Percolation.badClusterDiam Percolation.badCluster₂
      omega
    exact_mod_cast hnat
  have hnorm := norm_cubeCenter_sub_le_of_isWhitneyLift hU hW
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - (h : ℤ)) := zpow_pos (by norm_num) _
  nlinarith [hnorm, hstep, hdiam, hpos]

/-! ## The core: the component occupies at most two layers -/

section Core

variable {M : ABKModel d} {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : CutoffSample d}

/-- The core induction: every cube of the component sits in the least occupied
layer or its successor, and its lift is 2-connected to the lift of a minimal
cube. -/
private theorem core_layer_le_and_connected (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d}
    {Qmin : TriadicCube d} (hQmin : Qmin ∈ badComponent S Q₀)
    (hQminlay : Qmin ∈ whitneyLayer m (whitneyScaleSeq b hs k₀)
      (leastWhitneyLayer m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))) :
    ∀ V : TriadicCube d,
      Relation.ReflTransGen (fun X Y => X ∈ S ∧ Y ∈ S ∧ CubeTouch X Y) Qmin V →
      (∃ A, IsWhitneyLift m
          (leastWhitneyLayer m (whitneyScaleSeq b hs k₀) (badComponent S Q₀) +
            whitneyScaleSeq b hs k₀
              (leastWhitneyLayer m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))) V A ∧
        Percolation.Connected₂ (Percolation.badSiteFinset M m
            (leastWhitneyLayer m (whitneyScaleSeq b hs k₀) (badComponent S Q₀) +
              whitneyScaleSeq b hs k₀
                (leastWhitneyLayer m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)))
            omega)
          Qmin.index A.index) ∧
      ∀ nV : ℕ, V ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) nV →
        nV ≤ leastWhitneyLayer m (whitneyScaleSeq b hs k₀) (badComponent S Q₀) + 1 := by
  classical
  set hn := whitneyScaleSeq b hs k₀ with hhn
  set C := badComponent S Q₀ with hC
  set r := leastWhitneyLayer m hn C with hr
  set L : ℕ := r + hn r with hL
  -- the profile facts, once and for all
  have hmono : Monotone hn := by
    rw [hhn]; exact whitneyScaleSeq_mono (by linarith) (by linarith) hs k₀
  have hone : ∀ j, 1 ≤ hn j := by
    rw [hhn]
    intro j
    have := add_le_whitneyScaleSeq b hs k₀ j
    omega
  have hsepbd : ∀ j, hs ≤ hn j := by
    rw [hhn]
    intro j
    exact hsep_le_whitneyScaleSeq b hs k₀ j
  have hdepth10 : ∀ r' n' : ℕ, r' ≤ n' → n' ≤ r' + 3 →
      (n' + hn n') - (r' + hn r') < 10 := by
    rw [hhn]
    intro r' n' h1 h2
    exact whitneyDepth_sub_lt_ten hb0 hb hs k₀ h1 h2
  have hgate : ∀ n' : ℕ, 4 * (3 : ℝ) ^ (b * ((n' + hn n' : ℕ) : ℝ)) *
      (3 : ℝ) ^ (m - ((n' + hn n' : ℕ) : ℤ)) < (2 / 3 : ℝ) * (3 : ℝ) ^ (m - (n' : ℤ)) := by
    rw [hhn]
    intro n'
    exact four_mul_three_rpow_whitneyDepth_lt_two_thirds (hs := hs) hb0 hb hk₀ m n'
  have hsL : hs ≤ L := by
    have := hsepbd r
    omega
  -- the base lift of a minimal cube is the cube itself
  have hQmind : Qmin ∈ descendantsAtDepth (originCube d m) L :=
    mem_descendantsAtDepth_of_mem_whitneyLayer hQminlay
  have hQminlift : IsWhitneyLift m L Qmin Qmin :=
    ⟨hQmind, 0, by omega, by simp [HCPolySupport.descendantsAtDepth_zero]⟩
  have hQminS : Qmin ∈ S := hQmin.1
  have hQminsite : Qmin.index ∈ Percolation.badSiteFinset M m L omega :=
    index_mem_badSiteFinset_of_isWhitneyLift hQminlift (hSbad Qmin hQminS)
  have hdiam := havoid L hsL Qmin.index
    (index_mem_cubeFinset_of_mem_descendantsAtDepth hQmind)
  intro V hV
  induction hV with
  | refl =>
      refine ⟨⟨Qmin, hQminlift, Percolation.Connected₂.refl hQminsite⟩, ?_⟩
      intro nV hnV
      have := whitneyLayer_index_unique hmono hQminlay hnV
      omega
  | @tail V' V hchain hstep ih =>
      obtain ⟨⟨A', hA'lift, hA'conn⟩, hlay'⟩ := ih
      obtain ⟨hV'S, hVS, htouch⟩ := hstep
      have hVC : V ∈ C :=
        ⟨hVS, Relation.ReflTransGen.trans hQmin.2
          (Relation.ReflTransGen.tail hchain ⟨hV'S, hVS, htouch⟩)⟩
      have hV'C : V' ∈ C := ⟨hV'S, Relation.ReflTransGen.trans hQmin.2 hchain⟩
      obtain ⟨nV', hnV'⟩ := hSsub hV'S
      obtain ⟨nV, hnV⟩ := hSsub hVS
      have hrV' : r ≤ nV' := leastWhitneyLayer_le_of_mem hV'C hnV'
      have hrV : r ≤ nV := leastWhitneyLayer_le_of_mem hVC hnV
      have hupV' : nV' ≤ r + 1 := hlay' nV' hnV'
      have hclose := whitneyLayer_index_close_of_cubeTouch hone hnV' hnV htouch
      have hVbound : nV ≤ r + 2 := by omega
      -- the lift of `V` exists and is 2-adjacent to the lift of `V'`
      have hdepthle : L ≤ nV + hn nV := by
        have := hmono hrV
        omega
      have hgap : nV + hn nV - L < 10 := by
        have := hdepth10 r nV hrV (by omega)
        omega
      obtain ⟨A, hAlift⟩ := exists_isWhitneyLift hnV hdepthle hgap
      have hAsite : A.index ∈ Percolation.badSiteFinset M m L omega :=
        index_mem_badSiteFinset_of_isWhitneyLift hAlift (hSbad V hVS)
      have hadj : Percolation.latDist A'.index A.index ≤ 1 :=
        latDist_index_le_one_of_cubeTouch hA'lift hAlift htouch
      have hconn : Percolation.Connected₂ (Percolation.badSiteFinset M m L omega)
          Qmin.index A.index := by
        refine hA'conn.trans ⟨1, fun i => if i = 0 then A'.index else A.index, by simp,
          by simp, ?_, ?_⟩
        · intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          simpa using le_trans hadj (by omega : (1 : ℕ) ≤ 2)
        · intro i _
          by_cases hi : i = 0
          · simpa [hi] using hA'conn.mem_right
          · simpa [hi] using hAsite
      refine ⟨⟨A, hAlift, hconn⟩, ?_⟩
      intro nV₁ hnV₁
      have hnVeq : nV₁ = nV := whitneyLayer_index_unique hmono hnV₁ hnV
      subst hnVeq
      by_contra hcon
      -- the only remaining case is `nV = r + 2`, ruled out by the diameter bound
      have hfar : r + 2 ≤ nV₁ := by omega
      have hsep := two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers hfar hQminlay hnV₁
      have hnorm := norm_cubeCenter_sub_lt_of_connected₂ hQminlift hAlift hQminsite
        (Percolation.Connected₂.refl hQminsite) hconn hdiam
      have hg := hgate r
      rw [← hL] at hg
      have hposX : (0 : ℝ) < (3 : ℝ) ^ (b * (L : ℝ)) * (3 : ℝ) ^ (m - (L : ℤ)) :=
        mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (zpow_pos (by norm_num) _)
      linarith [hsep, hnorm, hg, hposX]

end Core

/-! ## The headline statements -/

/-- **`l.bad.clusters.geometry`(1), the pairwise form.**  On avoidance of the
bad-cluster diameter failure, any two Whitney cubes in the closure-touching
neighborhood of one connected component of an abstract bad family occupy equal
or neighbouring Whitney layers.

The family `S` is any subfamily of `𝒲(□_m)` all of whose cubes are bad; the
manuscript's `ℐ` is the instance
`badFamily_whitneyNeighborhood_finite_and_mem_leastLayer_or_succ` below. -/
theorem whitneyNeighborhood_layer_index_close {M : ABKModel d} {m : ℤ} {b : ℝ}
    {hs k₀ : ℕ} {omega : CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d} (hQ₀ : Q₀ ∈ S)
    {A D : TriadicCube d} {nA nD : ℕ}
    (hA : A ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))
    (hD : D ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))
    (hAn : A ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) nA)
    (hDn : D ∈ whitneyLayer m (whitneyScaleSeq b hs k₀) nD) :
    nA ≤ nD + 1 ∧ nD ≤ nA + 1 := by
  classical
  set hn := whitneyScaleSeq b hs k₀ with hhn
  set C := badComponent S Q₀ with hC
  set r := leastWhitneyLayer m hn C with hr
  set L : ℕ := r + hn r with hL
  have hmono : Monotone hn := by
    rw [hhn]; exact whitneyScaleSeq_mono (by linarith) (by linarith) hs k₀
  have hone : ∀ j, 1 ≤ hn j := by
    rw [hhn]
    intro j
    have := add_le_whitneyScaleSeq b hs k₀ j
    omega
  have hthree : ∀ j, 3 ≤ hn j := by
    rw [hhn]
    intro j
    have := add_le_whitneyScaleSeq b hs k₀ j
    omega
  have hsepbd : ∀ j, hs ≤ hn j := by
    rw [hhn]
    intro j
    exact hsep_le_whitneyScaleSeq b hs k₀ j
  have hstepseq : ∀ j, hn (j + 1) ≤ hn j + 1 := by
    rw [hhn]
    intro j
    exact whitneyScaleSeq_succ_le hb0 hb hs k₀ j
  have hgate : ∀ n' : ℕ, 4 * (3 : ℝ) ^ (b * ((n' + hn n' : ℕ) : ℝ)) *
      (3 : ℝ) ^ (m - ((n' + hn n' : ℕ) : ℤ)) < (2 / 3 : ℝ) * (3 : ℝ) ^ (m - (n' : ℤ)) := by
    rw [hhn]
    intro n'
    exact four_mul_three_rpow_whitneyDepth_lt_two_thirds (hs := hs) hb0 hb hk₀ m n'
  have hCsub : C ⊆ whitneyPartition m hn := fun Q hQ => hSsub hQ.1
  have hQ₀C : Q₀ ∈ C := self_mem_badComponent hQ₀
  obtain ⟨Qmin, hQmin, hQminlay⟩ := exists_mem_leastWhitneyLayer ⟨Q₀, hQ₀C⟩ hCsub
  have hcore := core_layer_le_and_connected hb0 hb hk₀ havoid hSsub hSbad hQmin hQminlay
  have hsL : hs ≤ L := by
    have := hsepbd r
    omega
  have hQmind : Qmin ∈ descendantsAtDepth (originCube d m) L :=
    mem_descendantsAtDepth_of_mem_whitneyLayer hQminlay
  have hQminlift : IsWhitneyLift m L Qmin Qmin :=
    ⟨hQmind, 0, by omega, by simp [HCPolySupport.descendantsAtDepth_zero]⟩
  have hQminsite : Qmin.index ∈ Percolation.badSiteFinset M m L omega :=
    index_mem_badSiteFinset_of_isWhitneyLift hQminlift (hSbad Qmin hQmin.1)
  have hdiam := havoid L hsL Qmin.index
    (index_mem_cubeFinset_of_mem_descendantsAtDepth hQmind)
  -- every cube of the component is chain-reachable from `Qmin`
  have hreach : ∀ V ∈ C,
      Relation.ReflTransGen (fun X Y => X ∈ S ∧ Y ∈ S ∧ CubeTouch X Y) Qmin V :=
    fun V hV => Relation.ReflTransGen.trans (badChain_symm hQmin.2) hV.2
  have hCwin : ∀ V ∈ C, ∀ nV : ℕ, V ∈ whitneyLayer m hn nV → r ≤ nV ∧ nV ≤ r + 1 :=
    fun V hV nV hVn =>
      ⟨leastWhitneyLayer_le_of_mem hV hVn, (hcore V (hreach V hV)).2 nV hVn⟩
  -- the diameter estimate inside the component
  have hCdist : ∀ U ∈ C, ∀ W ∈ C, ‖cubeCenter U - cubeCenter W‖ <
      (3 : ℝ) ^ (b * (L : ℝ)) * (3 : ℝ) ^ (m - (L : ℤ)) := by
    intro U hU W hW
    obtain ⟨⟨AU, hAUlift, hAUconn⟩, -⟩ := hcore U (hreach U hU)
    obtain ⟨⟨AW, hAWlift, hAWconn⟩, -⟩ := hcore W (hreach W hW)
    exact norm_cubeCenter_sub_lt_of_connected₂ hAUlift hAWlift hQminsite hAUconn
      hAWconn hdiam
  -- the radius of a cube of the neighborhood, in units of the lift side
  have hrad : ∀ {V : TriadicCube d} {nV : ℕ}, V ∈ whitneyLayer m hn nV → r ≤ nV + 1 →
      HCPolySupport.cubeRadius V ≤ 9 * (3 : ℝ) ^ (m - (L : ℤ)) / 2 := by
    intro V nV hVn hge
    have hdepthle : L ≤ nV + hn nV + 2 := by
      rcases le_or_gt r nV with hle | hlt
      · have := hmono hle
        omega
      · have hreq : r = nV + 1 := by omega
        have hst := hstepseq nV
        rw [hreq] at hL
        omega
    have hVs := scale_eq_of_mem_whitneyLayer hVn
    have hle : (3 : ℝ) ^ V.scale ≤ (3 : ℝ) ^ (m - (L : ℤ) + 2) := by
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      rw [hVs]
      omega
    have h9 : (3 : ℝ) ^ (m - (L : ℤ) + 2) = 9 * (3 : ℝ) ^ (m - (L : ℤ)) := by
      have h2 : (3 : ℝ) ^ ((2 : ℤ)) = 9 := by norm_num
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), h2]
      ring
    rw [cubeRadius_eq_zpow_div_two]
    rw [h9] at hle
    linarith
  have hradsmall : ∀ {V : TriadicCube d} {nV : ℕ}, V ∈ whitneyLayer m hn nV → r ≤ nV →
      HCPolySupport.cubeRadius V ≤ (3 : ℝ) ^ (m - (L : ℤ)) / 2 := by
    intro V nV hVn hge
    have hmm := hmono hge
    have hVs := scale_eq_of_mem_whitneyLayer hVn
    have hle : (3 : ℝ) ^ V.scale ≤ (3 : ℝ) ^ (m - (L : ℤ)) := by
      refine zpow_le_zpow_right₀ (by norm_num) ?_
      rw [hVs]
      omega
    rw [cubeRadius_eq_zpow_div_two]
    linarith
  -- the key exclusion for a pair of neighborhood cubes
  have key : ∀ {U W : TriadicCube d} {nU nW : ℕ},
      U ∈ whitneyNeighborhood m hn C → W ∈ whitneyNeighborhood m hn C →
      U ∈ whitneyLayer m hn nU → W ∈ whitneyLayer m hn nW → nU + 2 ≤ nW → False := by
    intro U W nU nW hUN hWN hUn hWn hlt
    obtain ⟨-, QU, hQU, hQUt⟩ := hUN
    obtain ⟨-, QW, hQW, hQWt⟩ := hWN
    obtain ⟨qU, hqU⟩ := hCsub hQU
    obtain ⟨qW, hqW⟩ := hCsub hQW
    obtain ⟨hqUlo, hqUhi⟩ := hCwin QU hQU qU hqU
    obtain ⟨hqWlo, hqWhi⟩ := hCwin QW hQW qW hqW
    have hcU := whitneyLayer_index_close_of_cubeTouch hone hUn hqU hQUt
    have hcW := whitneyLayer_index_close_of_cubeTouch hone hWn hqW hQWt
    have hUlo : r ≤ nU + 1 := by omega
    have hUhi : nU ≤ r := by omega
    have hWlo : r ≤ nW := by omega
    have hsep := two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers hlt hUn hWn
    have hmid := hCdist QU hQU QW hQW
    have hradU := hrad hUn hUlo
    have hradW := hradsmall hWn hWlo
    have hradQU := hradsmall hqU hqUlo
    have hradQW := hradsmall hqW hqWlo
    have htU := norm_cubeCenter_sub_le_of_cubeTouch hQUt
    have htW := norm_cubeCenter_sub_le_of_cubeTouch hQWt.symm
    have htri : ‖cubeCenter U - cubeCenter W‖ ≤
        ‖cubeCenter U - cubeCenter QU‖ + ‖cubeCenter QU - cubeCenter QW‖ +
          ‖cubeCenter QW - cubeCenter W‖ := by
      calc ‖cubeCenter U - cubeCenter W‖
          ≤ ‖cubeCenter U - cubeCenter QW‖ + ‖cubeCenter QW - cubeCenter W‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (‖cubeCenter U - cubeCenter QU‖ + ‖cubeCenter QU - cubeCenter QW‖) +
              ‖cubeCenter QW - cubeCenter W‖ := by
            gcongr
            exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hg := hgate r
    rw [← hL] at hg
    have hYsmall : 27 * (3 : ℝ) ^ (m - (L : ℤ)) ≤ (3 : ℝ) ^ (m - (r : ℤ)) := by
      have h3r := hthree r
      have hle : (3 : ℝ) ^ (m - (L : ℤ) + 3) ≤ (3 : ℝ) ^ (m - (r : ℤ)) := by
        refine zpow_le_zpow_right₀ (by norm_num) ?_
        omega
      have h27 : (3 : ℝ) ^ ((3 : ℤ)) = 27 := by norm_num
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), h27] at hle
      linarith
    have hshrink : (3 : ℝ) ^ (m - (r : ℤ)) ≤ (3 : ℝ) ^ (m - (nU : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hposY : (0 : ℝ) < (3 : ℝ) ^ (m - (L : ℤ)) := zpow_pos (by norm_num) _
    linarith [hsep, hmid, hradU, hradW, hradQU, hradQW, htU, htW, htri, hg,
      hYsmall, hshrink, hposY]
  refine ⟨?_, ?_⟩
  · by_contra hcon
    exact key hD hA hDn hAn (by omega)
  · by_contra hcon
    exact key hA hD hAn hDn (by omega)

/-- **`l.bad.clusters.geometry`(1), the layer form.**  The neighborhood of a
connected component of an abstract bad family is finite and contained in its
least occupied Whitney layer together with that layer's successor: the
manuscript's "every 2-connected component intersects at most two consecutive
layers". -/
theorem whitneyNeighborhood_finite_and_mem_leastLayer_or_succ {M : ABKModel d}
    {m : ℤ} {b : ℝ} {hs k₀ : ℕ} {omega : CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀)
    (havoid : ∀ h : ℕ, hs ≤ h → ∀ u ∈ Percolation.cubeFinset (d := d) h,
      (Percolation.badClusterDiam M m h omega u : ℝ) < (3 : ℝ) ^ (b * (h : ℝ)))
    {S : Set (TriadicCube d)} (hSsub : S ⊆ whitneyPartition m (whitneyScaleSeq b hs k₀))
    (hSbad : ∀ Q ∈ S, omega ∈ BadEvents.bad M Q)
    {Q₀ : TriadicCube d} (hQ₀ : Q₀ ∈ S) :
    (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)).Finite ∧
      ∀ R ∈ whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀),
        R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀)
            (leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
              (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀))) ∨
          R ∈ whitneyLayer m (whitneyScaleSeq b hs k₀)
            (leastWhitneyLayer m (whitneyScaleSeq b hs k₀)
              (whitneyNeighborhood m (whitneyScaleSeq b hs k₀) (badComponent S Q₀)) + 1) := by
  classical
  set hn := whitneyScaleSeq b hs k₀ with hhn
  set C := badComponent S Q₀ with hC
  set N := whitneyNeighborhood m hn C with hN
  have hCsub : C ⊆ whitneyPartition m hn := fun Q hQ => hSsub hQ.1
  have hQ₀N : Q₀ ∈ N := subset_whitneyNeighborhood hCsub (self_mem_badComponent hQ₀)
  have hNsub : N ⊆ whitneyPartition m hn := whitneyNeighborhood_subset m hn C
  obtain ⟨R₀, hR₀N, hR₀lay⟩ := exists_mem_leastWhitneyLayer ⟨Q₀, hQ₀N⟩ hNsub
  set l := leastWhitneyLayer m hn N with hl
  have hmem : ∀ R ∈ N, R ∈ whitneyLayer m hn l ∨ R ∈ whitneyLayer m hn (l + 1) := by
    intro R hR
    obtain ⟨nR, hRn⟩ := hNsub hR
    have hlo : l ≤ nR := leastWhitneyLayer_le_of_mem hR hRn
    have hcl := whitneyNeighborhood_layer_index_close hb0 hb hk₀ havoid hSsub hSbad hQ₀
      hR hR₀N hRn hR₀lay
    have hcase : nR = l ∨ nR = l + 1 := by omega
    rcases hcase with h | h
    · exact Or.inl (h ▸ hRn)
    · exact Or.inr (h ▸ hRn)
  refine ⟨?_, hmem⟩
  refine Set.Finite.subset
    (((whitneyLayer (d := d) m hn l).finite_toSet).union
      ((whitneyLayer (d := d) m hn (l + 1)).finite_toSet)) ?_
  intro R hR
  rcases hmem R hR with h | h
  · exact Set.mem_union_left _ (Finset.mem_coe.mpr h)
  · exact Set.mem_union_right _ (Finset.mem_coe.mpr h)

/-! ## The concrete bad family -/

/-- The concrete instance at the manuscript's own bad family `ℐ = badFamily M m h_n
omega`, with the avoidance binder discharged by the proved
`e.diameter.deterministic` (`Percolation.badClusterDiam_lt_of_hsep_le`). -/
theorem badFamily_whitneyNeighborhood_finite_and_mem_leastLayer_or_succ
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ} {omega : CutoffSample d}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 3 ≤ k₀)
    (hne : (Percolation.hsepSet M m E b omega).Nonempty)
    {Q₀ : TriadicCube d}
    (hQ₀ : Q₀ ∈ badFamily M m (whitneyScale M m E b k₀ omega) omega) :
    (whitneyNeighborhood m (whitneyScale M m E b k₀ omega)
        (badComponent (badFamily M m (whitneyScale M m E b k₀ omega) omega) Q₀)).Finite ∧
      ∀ R ∈ whitneyNeighborhood m (whitneyScale M m E b k₀ omega)
          (badComponent (badFamily M m (whitneyScale M m E b k₀ omega) omega) Q₀),
        R ∈ whitneyLayer m (whitneyScale M m E b k₀ omega)
            (leastWhitneyLayer m (whitneyScale M m E b k₀ omega)
              (whitneyNeighborhood m (whitneyScale M m E b k₀ omega)
                (badComponent (badFamily M m (whitneyScale M m E b k₀ omega) omega) Q₀))) ∨
          R ∈ whitneyLayer m (whitneyScale M m E b k₀ omega)
            (leastWhitneyLayer m (whitneyScale M m E b k₀ omega)
              (whitneyNeighborhood m (whitneyScale M m E b k₀ omega)
                (badComponent (badFamily M m (whitneyScale M m E b k₀ omega) omega) Q₀)) + 1) :=
  whitneyNeighborhood_finite_and_mem_leastLayer_or_succ hb0 hb hk₀
    (fun _ hh _ hu => Percolation.badClusterDiam_lt_of_hsep_le hne hh hu)
    (fun _ hQ => hQ.1) (fun _ hQ => hQ.2) hQ₀

end

end Algsuperdiff.Section3.Provider.Whitney
