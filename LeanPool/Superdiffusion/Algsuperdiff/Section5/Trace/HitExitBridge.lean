/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.CrossingTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Process.Trajectory.HitExitTail

/-!
# HitExitBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# From visited partition cubes to hit-exit chaining

This file supplies the geometric and counting interface required by the
hit-then-exit argument.  A finite injective enumeration lists the relevant
scale-`n` lattice sites.  Its closed cells are padded by the empty set to a
family indexed by `ℕ`; its open enlargements have the same centers and three
times the side length.  At most `3^d` closed cells meet any one enlargement.
-/

open HCPolySupport MeasureTheory Set
open scoped ENNReal NNReal

namespace Algsuperdiff.Section5.Trace

noncomputable section

/-- The closed scale-`n` cell centered at the embedded lattice site `z`. -/
def closedPartitionCube {d : ℕ} (n : ℤ) (z : Section5.Percolation.Site d) :
    Set (Vec d) :=
  Metric.closedBall (rescaleSite n z) ((1 / 2 : ℝ) * (3 : ℝ) ^ n)

/-- The open enlargement of a scale-`n` cell, with the same center and side
length `3^(n+1)`. -/
def openEnlargedPartitionCube {d : ℕ} (n : ℤ)
    (z : Section5.Percolation.Site d) : Set (Vec d) :=
  Metric.ball (rescaleSite n z) ((3 / 2 : ℝ) * (3 : ℝ) ^ n)

/-- The half-open partition representative lies in its closed cell. -/
theorem cubeSet_partitionCube_subset_closedPartitionCube {d : ℕ} (n : ℤ)
    (z : Section5.Percolation.Site d) :
    cubeSet (partitionCube n z) ⊆ closedPartitionCube n z := by
  intro x hx
  have hclosed := cubeSet_subset_closedBall (Q := partitionCube n z) hx
  simpa only [closedPartitionCube, partitionCube, rescaleSite, cubeCenter,
    cubeRadius, cubeScaleFactor] using! hclosed

def neighboringSites {d : ℕ} (v : Section5.Percolation.Site d) :
    Finset (Section5.Percolation.Site d) :=
  (Section5.Percolation.cubeSites d 1).image fun delta => v + delta

private theorem card_neighboringSites {d : ℕ} (v : Section5.Percolation.Site d) :
    (neighboringSites v).card = 3 ^ d := by
  rw [neighboringSites, Finset.card_image_of_injective]
  · simp only [Section5.Percolation.card_cubeSites, mul_one]
  · intro delta eta h
    exact add_left_cancel h

private theorem mem_neighboringSites_of_siteDist_le_one {d : ℕ}
    {v z : Section5.Percolation.Site d}
    (hvz : Section5.Percolation.siteDist z v ≤ 1) :
    z ∈ neighboringSites v := by
  apply Finset.mem_image.mpr
  refine ⟨z - v, Section5.Percolation.mem_cubeSites_of_inCube ?_, ?_⟩
  · intro i
    have hi := Section5.Percolation.natAbs_sub_le_siteDist z v i
    change 2 * (z i - v i).natAbs < 3
    omega
  · funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

/-- If a closed scale-`n` cell meets the open threefold enlargement of
another cell, their lattice sites differ by at most one in every coordinate. -/
theorem siteDist_le_one_of_closedPartitionCube_inter_openEnlarged_nonempty
    {d : ℕ} (n : ℤ) {z v : Section5.Percolation.Site d}
    (hinter : (closedPartitionCube n z ∩ openEnlargedPartitionCube n v).Nonempty) :
    Section5.Percolation.siteDist z v ≤ 1 := by
  obtain ⟨x, hxz, hxv⟩ := hinter
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hxz' : dist x (rescaleSite n z) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    simpa only [closedPartitionCube, Metric.mem_closedBall] using hxz
  have hxv' : dist x (rescaleSite n v) < (3 / 2 : ℝ) * (3 : ℝ) ^ n := by
    simpa only [openEnlargedPartitionCube, Metric.mem_ball] using hxv
  have hcenters : dist (rescaleSite n z) (rescaleSite n v) <
      2 * (3 : ℝ) ^ n := by
    calc
      dist (rescaleSite n z) (rescaleSite n v) ≤
          dist (rescaleSite n z) x + dist x (rescaleSite n v) := dist_triangle _ _ _
      _ < (1 / 2 : ℝ) * (3 : ℝ) ^ n +
          (3 / 2 : ℝ) * (3 : ℝ) ^ n :=
        add_lt_add_of_le_of_lt (by simpa only [dist_comm] using hxz') hxv'
      _ = 2 * (3 : ℝ) ^ n := by ring
  apply Finset.sup_le
  intro i _hi
  have hi := (dist_pi_lt_iff (by positivity : 0 < 2 * (3 : ℝ) ^ n)).mp hcenters i
  rw [Real.dist_eq] at hi
  change |(z i : ℝ) * (3 : ℝ) ^ n - (v i : ℝ) * (3 : ℝ) ^ n| <
    2 * (3 : ℝ) ^ n at hi
  rw [← sub_mul, abs_mul, abs_of_pos hs] at hi
  have habs : |(z i : ℝ) - (v i : ℝ)| < 2 := by
    exact lt_of_mul_lt_mul_right hi hs.le
  have habsZ : |z i - v i| < (2 : ℤ) := by
    exact_mod_cast habs
  rw [← Int.natCast_natAbs] at habsZ
  have hnat : (z i - v i).natAbs < 2 := by
    exact_mod_cast habsZ
  omega

/-- A finite injective site enumeration, padded by empty sets, as closed hit
sets for the chaining theorem. -/
def enumeratedClosedCubeFamily {d r : ℕ} (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) : Set (Vec d) :=
  if hi : i < r then closedPartitionCube n (sites ⟨i, hi⟩) else ∅

/-- The corresponding padded family of open threefold enlargements. -/
def enumeratedOpenEnlargementFamily {d r : ℕ} (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) : Set (Vec d) :=
  if hi : i < r then openEnlargedPartitionCube n (sites ⟨i, hi⟩) else ∅

/-- Every padded enlargement is open. -/
theorem isOpen_enumeratedOpenEnlargementFamily {d r : ℕ} (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) :
    IsOpen (enumeratedOpenEnlargementFamily n sites i) := by
  unfold enumeratedOpenEnlargementFamily
  split
  · exact Metric.isOpen_ball
  · exact isOpen_empty

/-- For an injective enumeration, each open enlargement meets at most `3^d`
members of the padded closed-cell family. -/
theorem enumeratedCubeFamily_overlap {d r : ℕ} (n : ℤ)
    (sites : Fin r ↪ Section5.Percolation.Site d) (i : ℕ) :
    ∃ s : Finset ℕ, s.card ≤ 3 ^ d ∧ ∀ j,
      (enumeratedClosedCubeFamily n sites j ∩
        enumeratedOpenEnlargementFamily n sites i).Nonempty → j ∈ s := by
  by_cases hi : i < r
  swap
  · refine ⟨∅, by simp only [Finset.card_empty, Nat.zero_le], fun j hinter => ?_⟩
    rw [enumeratedOpenEnlargementFamily, dite_eq_right hi] at hinter
    obtain ⟨x, _hx, hx⟩ := hinter
    exact (Set.notMem_empty x hx).elim
  let ii : Fin r := ⟨i, hi⟩
  let q : Finset (Fin r) := Finset.univ.filter fun j =>
    sites j ∈ neighboringSites (sites ii)
  let s : Finset ℕ := q.image Fin.val
  refine ⟨s, ?_, ?_⟩
  · have hqImage : q.image sites ⊆ neighboringSites (sites ii) := by
      intro z hz
      obtain ⟨j, hjq, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hjq).2
    calc
      s.card = q.card := Finset.card_image_of_injective q Fin.val_injective
      _ = (q.image sites).card :=
        (Finset.card_image_of_injective q sites.injective).symm
      _ ≤ (neighboringSites (sites ii)).card := Finset.card_le_card hqImage
      _ = 3 ^ d := card_neighboringSites _
  · intro j hinter
    have hj : j < r := by
      by_contra hj
      rw [enumeratedClosedCubeFamily, dite_eq_right hj] at hinter
      obtain ⟨x, hx, _hx⟩ := hinter
      exact Set.notMem_empty x hx
    let jj : Fin r := ⟨j, hj⟩
    have hinter' :
        (closedPartitionCube n (sites jj) ∩
          openEnlargedPartitionCube n (sites ii)).Nonempty := by
      simpa only [enumeratedClosedCubeFamily, enumeratedOpenEnlargementFamily,
        dite_eq_left hj, dite_eq_left hi, jj, ii] using hinter
    have hneighbor : sites jj ∈ neighboringSites (sites ii) :=
      mem_neighboringSites_of_siteDist_le_one
        (siteDist_le_one_of_closedPartitionCube_inter_openEnlarged_nonempty n hinter')
    apply Finset.mem_image.mpr
    refine ⟨jj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneighbor⟩, rfl⟩

end

end Algsuperdiff.Section5.Trace
