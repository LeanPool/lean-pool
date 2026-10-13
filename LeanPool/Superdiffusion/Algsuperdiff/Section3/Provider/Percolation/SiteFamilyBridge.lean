/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.SiteFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.ClusterEvent
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaLocal

/-!
# SiteFamilyBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The site family of `l.percolation.bad.clusters` and its independence

This module proves a local finite-range result used by
`l.percolation.bad.clusters` (ABK26): it turns the abstract percolation layer's
independence hypothesis

```
∀ l S S', (∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) →
  Indep (siteSigma B S l) (siteSigma B S' l) mu
```

into a *theorem* for an explicit implementation `B` of the manuscript's
scale-`L` bad events, with no independence assumed anywhere: everything is
routed through the proved cutoff range lemma, which is itself routed through
the frozen (J1) unit-range-dependence assumption.

## The three disclosed constants

1. **Region radius (sharp).**  `cubeTreeRegion Q` — the union of the closed
   cubes of the nine-generation descendant tree of `Q` — is exactly the closed
   sup-ball `Metric.closedBall (cubeBasePoint Q) ((1/2) * 3 ^ Q.scale)`, i.e.
   the closed cube itself (`cubeTreeRegion_subset_closedBall_half`).  The
   concentric *double* of `SiteFamily.cubeTreeRegion_subset_closedBall` is not
   optimal: a descendant `R ⊆ Q` has its closed cube inside the closed cube of
   `Q`, so the constant `1` is replaced by the sharp `1/2` here.

2. **Lattice-to-Euclidean conversion.**  Two sites `u, v` of the base lattice
   `3^base Z^d` at sup-lattice distance `latDist u v` carry tree regions whose
   Euclidean distance is at least `(latDist u v - 1) * 3 ^ base`
   (`vecNorm_sub_ge_of_mem_cubeTreeRegion`).  The `- 1` is the sharp radius of
   item 1 counted twice (`1/2 + 1/2`).

3. **The reindexing shift (the manuscript's "after reindexing").**  The
   level-`L` bad event of a base-scale cube reads shells of index at most `base
   + L`; the proved cutoff range lemma
   `indep_cutoffShellLocalSigma_of_separation` therefore needs the *Euclidean*
   separation `sqrt(d) * 3 ^ (base + L)`, i.e. lattice separation `1 + sqrt(d)
   * 3 ^ L`, whereas the abstract layer supplies only `3 ^ L < latDist`.  The
   `sqrt(d)` is intrinsic: it is the literal hypothesis of the frozen (J1)
   assumption (a unit cube has Euclidean diameter `sqrt(d)`), and it cannot be
   removed downstream.  The manuscript's own sentence "satisfy (after
   reindexing) the independence requirements of
   Lemma~\ref{l.percolation.bound.general}" is implemented locally by the
   explicit shift `sepShift d = d`, which satisfies `sqrt(d) <= 3 ^ (sepShift
   d)`:

   ```
   siteBadEvent M base l u = if l < sepShift d then ∅
                             else badScaleEvent M (siteCube base u) (l - sepShift d)
   ```

   The shift costs exactly a factor `3 ^ (-a * sepShift d)` in the tail
   parameter `T ^ 2` (a `d`-dependent constant, which is what the manuscript's
   `C(d)` absorbs) and nothing else: the union `⋃ l, siteBadEvent M base l u`
   is unchanged, because `l ↦ l - sepShift d` is onto `N` on `l ≥ sepShift d`.

## Main results

* `cubeTreeRegion_subset_closedBall_half`: the sharp region radius.
* `measurableSet_badScaleEvent_zero_cutoffSampleLocal`: locality of level `0`
  of the D-9 family (the `badLoc` level), completing
  `measurableSet_badScaleEvent_succ_cutoffShellLocal`.
* `measurableSet_badScaleEvent_cutoffSampleLocal`: locality of every level.
* `siteSigma_le_cutoffSampleLocalSigma`: the `siteSigma` bridge.
* `indep_siteSigma_siteBadEvent`: the abstract layer's `hindep`, discharged.

## References

* ABK26, `l.percolation.bad.clusters`.
* ABK26, `l.percolation.bound.general`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents

noncomputable section

variable {d : ℕ}

/-! ## The sharp radius of the descendant-tree region -/

/-- A subcube's closed cube lies in the ambient closed cube.  This is the sharp
form of the concentric bound: the closed sup-ball of radius
`(1/2) 3 ^ R.scale` around `cubeBasePoint R` is the closed cube `R`, and the
closed cubes of the descendants of `Q` are contained in the closed cube `Q`. -/
theorem closedBall_subset_closedBall_of_cubeSet_subset {Q R : TriadicCube d}
    (h : cubeSet R ⊆ cubeSet Q) :
    Metric.closedBall (cubeBasePoint R) ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale) ⊆
      Metric.closedBall (cubeBasePoint Q) ((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale) := by
  have hfR : (0 : ℝ) < (3 : ℝ) ^ R.scale := zpow_pos (by norm_num) _
  have hfQ : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hkey : ∀ i : Fin d,
      ((Q.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ Q.scale ≤
          ((R.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale ∧
        ((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale ≤
          ((Q.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ Q.scale := by
    intro i
    constructor
    · have hmem : (fun j : Fin d => ((R.index j : ℝ) - 1 / 2) * (3 : ℝ) ^ R.scale) ∈
          cubeSet R := by
        intro j
        simp only [cubeScaleFactor]
        exact ⟨le_rfl, by nlinarith [hfR]⟩
      have hQ := (h hmem) i
      simp only [cubeScaleFactor] at hQ
      exact hQ.1
    · by_contra hcon
      push Not at hcon
      set t : ℝ := min ((1 / 2 : ℝ) * (3 : ℝ) ^ R.scale)
        (((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale -
          ((Q.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ Q.scale) with htdef
      have ht0 : 0 < t := lt_min (by nlinarith [hfR]) (by linarith)
      have htle : t ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ R.scale := min_le_left _ _
      have htle2 : t ≤ ((R.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale -
          ((Q.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ Q.scale := min_le_right _ _
      have hmem : (fun j : Fin d =>
          ((R.index j : ℝ) + 1 / 2) * (3 : ℝ) ^ R.scale - t) ∈ cubeSet R := by
        intro j
        simp only [cubeScaleFactor]
        exact ⟨by nlinarith [hfR], by linarith⟩
      have hQ := (h hmem) i
      simp only [cubeScaleFactor] at hQ
      linarith [hQ.2]
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)] at hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)]
  intro i
  have hxi := hx i
  rw [Real.dist_eq, abs_le] at hxi
  rw [Real.dist_eq, abs_le]
  have hcR : cubeBasePoint R i = (R.index i : ℝ) * (3 : ℝ) ^ R.scale := rfl
  have hcQ : cubeBasePoint Q i = (Q.index i : ℝ) * (3 : ℝ) ^ Q.scale := rfl
  rw [hcR] at hxi
  rw [hcQ]
  obtain ⟨h1, h2⟩ := hkey i
  exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

/-- **The sharp disclosed range constant.**  The nine-generation descendant
tree of `Q` lives in the closed sup-ball of radius `(1/2) 3 ^ Q.scale` around
the base point, i.e. in the closed cube `Q` itself. -/
theorem cubeTreeRegion_subset_closedBall_half (Q : TriadicCube d) :
    cubeTreeRegion Q ⊆
      Metric.closedBall (cubeBasePoint Q) ((1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale) := by
  refine Set.iUnion₂_subset fun i hi => Set.iUnion₂_subset fun R hR => ?_
  have hle : Q.scale - (i : ℤ) ≤ Q.scale := by
    have : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i
    omega
  exact closedBall_subset_closedBall_of_cubeSet_subset
    (cubeSet_subset_of_mem_descendantsAtScale hle hR)

/-- The closed cube of a descendant of `Q` is inside the tree region of `Q`. -/
theorem cubeSet_subset_cubeTreeRegion_of_mem_descendantsAtScale {Q R : TriadicCube d}
    {i : ℕ} (hi : i ∈ Finset.range 10)
    (hR : R ∈ descendantsAtScale Q (Q.scale - (i : ℤ))) :
    cubeSet R ⊆ cubeTreeRegion Q :=
  (cubeSet_subset_closedBall R).trans
    (closedBall_cubeBasePoint_subset_cubeTreeRegion hi hR)

theorem measurableSet_cubeTreeRegion (Q : TriadicCube d) :
    MeasurableSet (cubeTreeRegion Q) :=
  MeasurableSet.biUnion (Set.to_countable _) fun _ _ =>
    MeasurableSet.biUnion (Set.to_countable _) fun _ _ => Metric.isClosed_closedBall.measurableSet

/-! ## Locality of every level of the site family -/

/-- **Level `0` of the D-9 family is integral-local.**  Together with the proved
`measurableSet_badScaleEvent_succ_cutoffShellLocal` this proves the local
Provider result for the locality part of `l.percolation.bound.general` for the
manuscript's scale-resolved bad events. -/
theorem measurableSet_badScaleEvent_zero_cutoffSampleLocal (M : ABKModel d)
    (Q : TriadicCube d) {U : Set (Vec d)} (hU : cubeTreeRegion Q ⊆ U) :
    MeasurableSet[cutoffSampleLocalSigma M Q.scale U] (badScaleEvent M Q 0) := by
  let : MeasurableSpace (CutoffSample d) := cutoffSampleLocalSigma M Q.scale U
  refine Finset.measurableSet_biUnion _ fun i hi => ?_
  refine Finset.measurableSet_biUnion _ fun R hR => ?_
  have hscale : R.scale = Q.scale - (i : ℤ) :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i
  have hRU : cubeSet R ⊆ U :=
    (cubeSet_subset_cubeTreeRegion_of_mem_descendantsAtScale hi hR).trans hU
  exact cutoffSampleLocalSigma_mono M (by omega : R.scale ≤ Q.scale)
    (le_refl U) _ (measurableSet_badLoc_cutoffSampleLocal M R hRU)

/-- **Locality of every level of the D-9 family**, in the completed
cutoff-sample local sigma-field at the exact shell index `Q.scale + l`. -/
theorem measurableSet_badScaleEvent_cutoffSampleLocal (M : ABKModel d)
    (Q : TriadicCube d) (l : ℕ) {U : Set (Vec d)} (hU : cubeTreeRegion Q ⊆ U) :
    MeasurableSet[cutoffSampleLocalSigma M (Q.scale + (l : ℤ)) U]
      (badScaleEvent M Q l) := by
  cases l with
  | zero =>
      have h := measurableSet_badScaleEvent_zero_cutoffSampleLocal M Q hU
      have hle : cutoffSampleLocalSigma M Q.scale U ≤
          cutoffSampleLocalSigma M (Q.scale + ((0 : ℕ) : ℤ)) U :=
        cutoffSampleLocalSigma_mono M (by omega) (le_refl U)
      exact hle _ h
  | succ l =>
      have h := measurableSet_badScaleEvent_succ_cutoffShellLocal M Q l hU
      have hle : cutoffShellLocalSigma (Q.scale + (l : ℤ) + 1) U ≤
          cutoffSampleLocalSigma M (Q.scale + ((l + 1 : ℕ) : ℤ)) U := by
        have hidx : Q.scale + (l : ℤ) + 1 = Q.scale + ((l + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [hidx]
        exact MeasurableSpace.comap_mono
          (lowerShellLocalSigma_le_completion M (Q.scale + ((l + 1 : ℕ) : ℤ)) U)
      exact hle _ h

/-! ## The site family of `e.bad.cluster.def` -/

/-- The base-scale triadic cube `z + square_base` at the lattice site `u`,
i.e. `z = 3^base u`. -/
def siteCube (base : ℤ) (u : Fin d → ℤ) : TriadicCube d :=
  { scale := base, index := u }

@[simp] theorem siteCube_scale (base : ℤ) (u : Fin d → ℤ) :
    (siteCube base u).scale = base := rfl


/-- **The disclosed reindexing shift.**  Any `q` with `sqrt(d) ≤ 3 ^ q` works;
`q = d` is the explicit choice made here. -/
def sepShift (d : ℕ) : ℕ := d

theorem sqrt_le_three_pow_sepShift (d : ℕ) :
    Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (sepShift d) := by
  have hlt : (d : ℝ) ≤ (3 : ℝ) ^ d := by
    have : d < 3 ^ d := Nat.lt_pow_self (by norm_num)
    calc (d : ℝ) ≤ ((3 ^ d : ℕ) : ℝ) := by exact_mod_cast this.le
      _ = (3 : ℝ) ^ d := by push_cast; ring
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hsq : (d : ℝ) ≤ ((3 : ℝ) ^ d) ^ 2 := by nlinarith
  calc Real.sqrt (d : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ d) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (3 : ℝ) ^ d := Real.sqrt_sq (by positivity)

/-- **The reindexed scale-`l` bad event of `l.percolation.bad.clusters`.**  The
levels below the disclosed shift are empty; from the shift on, this is exactly
the manuscript's `B_L(z + cu_base)` with `L = l - sepShift d`. -/
def siteBadEvent (M : ABKModel d) (base : ℤ) (l : ℕ) (u : Fin d → ℤ) :
    Set (CutoffSample d) :=
  if l < sepShift d then ∅ else badScaleEvent M (siteCube base u) (l - sepShift d)

theorem measurableSet_siteBadEvent (M : ABKModel d) (base : ℤ) (l : ℕ)
    (u : Fin d → ℤ) : MeasurableSet (siteBadEvent M base l u) := by
  rw [siteBadEvent]
  split
  · exact MeasurableSet.empty
  · exact measurableSet_badScaleEvent M (siteCube base u) (l - sepShift d)

/-- The reindexing loses nothing: the union over the reindexed levels is the
union over the manuscript's own levels, so the manuscript's inclusion
`B^*(z + cu_base) ⊆ ⋃_L B_L(z + cu_base)` survives verbatim. -/
theorem badExtended_subset_iUnion_siteBadEvent (M : ABKModel d) (base : ℤ)
    (u : Fin d → ℤ) :
    badExtended M (siteCube base u) ⊆ ⋃ l : ℕ, siteBadEvent M base l u := by
  intro omega homega
  obtain ⟨L, hL⟩ := Set.mem_iUnion.1
    (badExtended_subset_iUnion_badScaleEvent M (siteCube base u) homega)
  refine Set.mem_iUnion.2 ⟨L + sepShift d, ?_⟩
  rw [siteBadEvent, ite_eq_right (by omega)]
  have : L + sepShift d - sepShift d = L := by omega
  rw [this]
  exact hL

/-! ## The observation region of a set of sites -/

/-- The spatial region read by the whole site family at the sites of `S`. -/
def siteRegion (base : ℤ) (S : Set (Fin d → ℤ)) : Set (Vec d) :=
  ⋃ u ∈ S, cubeTreeRegion (siteCube base u)

theorem measurableSet_siteRegion (base : ℤ) (S : Set (Fin d → ℤ)) :
    MeasurableSet (siteRegion base S) :=
  MeasurableSet.biUnion (Set.to_countable S) fun u _ =>
    measurableSet_cubeTreeRegion (siteCube base u)

theorem cubeTreeRegion_subset_siteRegion {base : ℤ} {S : Set (Fin d → ℤ)}
    {u : Fin d → ℤ} (hu : u ∈ S) :
    cubeTreeRegion (siteCube base u) ⊆ siteRegion base S :=
  Set.subset_biUnion_of_mem (u := fun v : Fin d → ℤ => cubeTreeRegion (siteCube base v)) hu

/-! ## The lattice-to-Euclidean separation conversion -/

private theorem abs_le_vecNorm (v : Vec d) (i : Fin d) :
    |v i| ≤ HCPolySupport.Book.Ch02.vecNorm v := by
  have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin d => ℝ)
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) i
  simpa [HCPolySupport.Book.Ch02.vecNorm, Real.norm_eq_abs] using h

/-- **The disclosed separation conversion.**  Two base-scale sites at sup
lattice distance `latDist u v` have descendant-tree regions at Euclidean
distance at least `(latDist u v - 1) * 3 ^ base`.  The `- 1` is the sharp
region radius `1/2` counted at both sites. -/
theorem vecNorm_sub_ge_of_mem_cubeTreeRegion (hd : 0 < d) (base : ℤ)
    {u v : Fin d → ℤ} {x y : Vec d}
    (hx : x ∈ cubeTreeRegion (siteCube base u))
    (hy : y ∈ cubeTreeRegion (siteCube base v)) :
    (((latDist u v : ℕ) : ℝ) - 1) * (3 : ℝ) ^ base ≤
      HCPolySupport.Book.Ch02.vecNorm (x - y) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ base := zpow_pos (by norm_num) _
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    Finset.univ_nonempty (fun j => (u j - v j).natAbs)
  have hxball := cubeTreeRegion_subset_closedBall_half (siteCube base u) hx
  have hyball := cubeTreeRegion_subset_closedBall_half (siteCube base v) hy
  rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)] at hxball hyball
  have hxi := hxball i
  have hyi := hyball i
  rw [Real.dist_eq, abs_le] at hxi hyi
  simp only [siteCube_scale] at hxi hyi
  have hcu : cubeBasePoint (siteCube base u) i = (u i : ℝ) * (3 : ℝ) ^ base := rfl
  have hcv : cubeBasePoint (siteCube base v) i = (v i : ℝ) * (3 : ℝ) ^ base := rfl
  rw [hcu] at hxi
  rw [hcv] at hyi
  have hlat : ((latDist u v : ℕ) : ℝ) = |(u i : ℝ) - (v i : ℝ)| := by
    rw [latDist, hi]
    have : (((u i - v i).natAbs : ℕ) : ℝ) = |((u i - v i : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs]
      push_cast
      ring
    rw [this]
    push_cast
    ring_nf
  have hdiff : |(x i - y i)| ≥
      |(u i : ℝ) * (3 : ℝ) ^ base - (v i : ℝ) * (3 : ℝ) ^ base| -
        (1 / 2 : ℝ) * (3 : ℝ) ^ base - (1 / 2 : ℝ) * (3 : ℝ) ^ base := by
    have h1 : |(u i : ℝ) * (3 : ℝ) ^ base - (v i : ℝ) * (3 : ℝ) ^ base| ≤
        |(u i : ℝ) * (3 : ℝ) ^ base - x i| + |x i - y i| +
          |y i - (v i : ℝ) * (3 : ℝ) ^ base| := by
      have := abs_sub_abs_le_abs_sub
        ((u i : ℝ) * (3 : ℝ) ^ base - x i) ((v i : ℝ) * (3 : ℝ) ^ base - y i)
      calc |(u i : ℝ) * (3 : ℝ) ^ base - (v i : ℝ) * (3 : ℝ) ^ base|
          = |((u i : ℝ) * (3 : ℝ) ^ base - x i) + (x i - y i) +
              (y i - (v i : ℝ) * (3 : ℝ) ^ base)| := by ring_nf
        _ ≤ |((u i : ℝ) * (3 : ℝ) ^ base - x i) + (x i - y i)| +
              |y i - (v i : ℝ) * (3 : ℝ) ^ base| := abs_add_le _ _
        _ ≤ |(u i : ℝ) * (3 : ℝ) ^ base - x i| + |x i - y i| +
              |y i - (v i : ℝ) * (3 : ℝ) ^ base| := by
            have := abs_add_le ((u i : ℝ) * (3 : ℝ) ^ base - x i) (x i - y i)
            linarith
    have h2 : |(u i : ℝ) * (3 : ℝ) ^ base - x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ base := by
      rw [abs_sub_comm, abs_le]
      exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
    have h3 : |y i - (v i : ℝ) * (3 : ℝ) ^ base| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ base := by
      rw [abs_le]
      exact ⟨by linarith [hyi.1], by linarith [hyi.2]⟩
    linarith
  have habs : |(u i : ℝ) * (3 : ℝ) ^ base - (v i : ℝ) * (3 : ℝ) ^ base| =
      ((latDist u v : ℕ) : ℝ) * (3 : ℝ) ^ base := by
    calc |(u i : ℝ) * (3 : ℝ) ^ base - (v i : ℝ) * (3 : ℝ) ^ base|
        = |((u i : ℝ) - (v i : ℝ)) * (3 : ℝ) ^ base| := by ring_nf
      _ = |(u i : ℝ) - (v i : ℝ)| * |(3 : ℝ) ^ base| := abs_mul _ _
      _ = ((latDist u v : ℕ) : ℝ) * (3 : ℝ) ^ base := by
          rw [← hlat, abs_of_pos hpos]
  have hfinal : |x i - y i| ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
    have := abs_le_vecNorm (x - y) i
    simpa using this
  rw [habs] at hdiff
  linarith

/-! ## The `siteSigma` bridge and the independence discharge -/

/-- **The `siteSigma` bridge.**  All the information the site family at the
sites of `S` carries up to level `l` is integral-local information of the
shells of index at most `base + (l - sepShift d)` in the region `siteRegion`. -/
theorem siteSigma_le_cutoffSampleLocalSigma (M : ABKModel d) (base : ℤ) (l : ℕ)
    (S : Set (Fin d → ℤ)) :
    siteSigma (siteBadEvent M base) S l ≤
      cutoffSampleLocalSigma M (base + ((l - sepShift d : ℕ) : ℤ)) (siteRegion base S) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro A ⟨L, hL, y, hy, rfl⟩
  rw [siteBadEvent]
  split
  · exact @MeasurableSet.empty (CutoffSample d)
      (cutoffSampleLocalSigma M (base + ((l - sepShift d : ℕ) : ℤ)) (siteRegion base S))
  · rename_i hLq
    push Not at hLq
    have hbase := measurableSet_badScaleEvent_cutoffSampleLocal M (siteCube base y)
      (L - sepShift d) (U := cubeTreeRegion (siteCube base y)) (le_refl _)
    refine cutoffSampleLocalSigma_mono M ?_ (cubeTreeRegion_subset_siteRegion hy) _ hbase
    have : L - sepShift d ≤ l - sepShift d := Nat.sub_le_sub_right hL _
    simp only [siteCube_scale]
    omega

/-- **The independence hypothesis of `l.percolation.bound.general`, discharged.**
Nothing is assumed: the two site families at sup-lattice separation more than
`3 ^ l` generate integral-local information on two regions whose Euclidean
separation exceeds the literal cutoff range `sqrt(d) * 3 ^ (base + l - sepShift
d)`, and the proved cutoff range lemma — routed through the frozen (J1)
unit-range assumption — supplies the independence. -/
theorem indep_siteSigma_siteBadEvent (M : ABKModel d) (base : ℤ) (l : ℕ)
    (S S' : Set (Fin d → ℤ))
    (hsep : ∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v) :
    Indep (siteSigma (siteBadEvent M base) S l)
      (siteSigma (siteBadEvent M base) S' l) (cutoffSampleLaw M).toMeasure := by
  have hd : 0 < d := lt_of_lt_of_le (by omega) M.shellPrefix.dimension
  by_cases hlq : l < sepShift d
  · have htrivial : ∀ T : Set (Fin d → ℤ),
        siteSigma (siteBadEvent M base) T l ≤ ⊥ := by
      intro T
      refine MeasurableSpace.generateFrom_le ?_
      rintro A ⟨L, hL, y, -, rfl⟩
      rw [siteBadEvent, ite_eq_left (by omega)]
      exact @MeasurableSet.empty (CutoffSample d) ⊥
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left
        (ProbabilityTheory.indep_bot_left _) (htrivial S)) (htrivial S')
  · push Not at hlq
    set n : ℕ := l - sepShift d with hndef
    have hln : l = n + sepShift d := by omega
    have hEuclid : ∀ ⦃x y : Vec d⦄, x ∈ siteRegion base S → y ∈ siteRegion base S' →
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ (base + (n : ℤ)) ≤
          HCPolySupport.Book.Ch02.vecNorm (x - y) := by
      intro x y hx hy
      obtain ⟨u, hu, hx⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨v, hv, hy⟩ := Set.mem_iUnion₂.1 hy
      have hlat : (3 : ℝ) ^ l + 1 ≤ ((latDist u v : ℕ) : ℝ) := by
        have h := hsep u hu v hv
        have : (3 : ℕ) ^ l + 1 ≤ latDist u v := by omega
        calc (3 : ℝ) ^ l + 1 = (((3 : ℕ) ^ l + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((latDist u v : ℕ) : ℝ) := by exact_mod_cast this
      have hbase : (0 : ℝ) < (3 : ℝ) ^ base := zpow_pos (by norm_num) _
      have hgeom : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n : ℕ) ≤ (3 : ℝ) ^ l := by
        have hq := sqrt_le_three_pow_sepShift d
        have hn : (0 : ℝ) < (3 : ℝ) ^ (n : ℕ) := by positivity
        calc Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n : ℕ)
            ≤ (3 : ℝ) ^ (sepShift d) * (3 : ℝ) ^ (n : ℕ) := by nlinarith
          _ = (3 : ℝ) ^ l := by rw [← pow_add, hln]; ring_nf
      have hsplit : (3 : ℝ) ^ (base + (n : ℤ)) = (3 : ℝ) ^ base * (3 : ℝ) ^ (n : ℕ) := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
      have hregion := vecNorm_sub_ge_of_mem_cubeTreeRegion hd base hx hy
      have hchain : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (base + (n : ℤ)) ≤
          (((latDist u v : ℕ) : ℝ) - 1) * (3 : ℝ) ^ base := by
        rw [hsplit]
        have : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n : ℕ) ≤ ((latDist u v : ℕ) : ℝ) - 1 := by
          linarith
        nlinarith
      linarith
    have hsource := indep_cutoffSampleLocalSigma_of_indep_completion M (base + (n : ℤ))
      (siteRegion base S) (siteRegion base S')
      (indep_lowerShellLocalCompletion_of_cutoff_separation M (base + (n : ℤ))
        (measurableSet_siteRegion base S) (measurableSet_siteRegion base S') hEuclid)
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hsource
        (siteSigma_le_cutoffSampleLocalSigma M base l S))
      (siteSigma_le_cutoffSampleLocalSigma M base l S')

end

end Algsuperdiff.Section3.Provider.Percolation
