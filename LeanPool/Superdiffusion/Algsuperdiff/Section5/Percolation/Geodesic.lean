/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.FixedPath
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Geodesic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Synchronous lattice geodesics

This file defines the graph of sup-adjacent lattice sites and the synchronous
geodesic between two sites: an adjacency path whose length is the sup distance
and which stays inside every centered triadic cube containing both endpoints.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory

/-- The simple graph whose edges are sup-adjacent lattice sites. -/
def latticeGraph (d : ℕ) : SimpleGraph (Site d) where
  Adj := Adj
  symm := by
    constructor
    intro x y hxy
    unfold Adj at hxy ⊢
    rwa [siteDist_comm]
  loopless := by
    constructor
    intro x hx
    unfold Adj at hx
    rw [siteDist_self] at hx
    exact Nat.zero_ne_one hx

/-- The point reached after `n` synchronous sup-geodesic steps from `x`
toward `y`. -/
def geodesicPoint {d : ℕ} (x y : Site d) (n : ℕ) : Site d :=
  fun i => x i + (y i - x i).sign *
    (Nat.min n (y i - x i).natAbs : ℤ)

/-- The synchronous sup-geodesic from `x` to `y`, including both endpoints. -/
def geodesic {d : ℕ} (x y : Site d) : List (Site d) :=
  (List.range (siteDist x y + 1)).map (geodesicPoint x y)

private theorem odd_three_pow_minimizer (L : ℕ) : Odd (3 ^ L) := by
  exact (show Odd 3 by norm_num).pow

private theorem mem_latticeCubeSites_iff_coord {d L : ℕ} {v z : Site d} :
    z ∈ latticeCubeSites L v ↔
      ∀ i, (z i - (cubeCenter L v) i).natAbs ≤ 3 ^ L / 2 := by
  constructor
  · intro hz i
    have hcoord := natAbs_sub_le_siteDist z (cubeCenter L v) i
    rw [siteDist_comm] at hcoord
    exact hcoord.trans (siteDist_cubeCenter_le_half hz)
  · intro hz
    let r : Site d := fun i => z i - (cubeCenter L v) i
    have hrCube : inCube L r := by
      intro i
      have hodd : 2 * (3 ^ L / 2) + 1 = 3 ^ L :=
        Nat.two_mul_div_two_add_one_of_odd (odd_three_pow_minimizer L)
      have hri := hz i
      change 2 * (z i - (cubeCenter L v) i).natAbs < 3 ^ L
      omega
    apply Finset.mem_image.mpr
    refine ⟨r, mem_cubeSites_of_inCube hrCube, ?_⟩
    funext i
    change (cubeCenter L v) i + (z i - (cubeCenter L v) i) = z i
    ring

private theorem mem_latticeCubeSites_of_between {d L : ℕ} {v x y z : Site d}
    (hx : x ∈ latticeCubeSites L v) (hy : y ∈ latticeCubeSites L v)
    (hz : ∀ i, (x i ≤ z i ∧ z i ≤ y i) ∨ (y i ≤ z i ∧ z i ≤ x i)) :
    z ∈ latticeCubeSites L v := by
  rw [mem_latticeCubeSites_iff_coord] at hx hy ⊢
  intro i
  have hx' := hx i
  have hy' := hy i
  have hxCast : |x i - (cubeCenter L v) i| ≤ ((3 ^ L / 2 : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hx'
  have hyCast : |y i - (cubeCenter L v) i| ≤ ((3 ^ L / 2 : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hy'
  have hzCast : |z i - (cubeCenter L v) i| ≤ ((3 ^ L / 2 : ℕ) : ℤ) := by
    apply abs_le.mpr
    obtain hxy | hyx := hz i
    · have hxl := (abs_le.mp hxCast).1
      have hyu := (abs_le.mp hyCast).2
      constructor <;> omega
    · have hyl := (abs_le.mp hyCast).1
      have hxu := (abs_le.mp hxCast).2
      constructor <;> omega
  rw [← Int.natCast_natAbs] at hzCast
  exact_mod_cast hzCast

private theorem geodesicPoint_between {d : ℕ} (x y : Site d) (n : ℕ) (i : Fin d) :
    (x i ≤ geodesicPoint x y n i ∧ geodesicPoint x y n i ≤ y i) ∨
      (y i ≤ geodesicPoint x y n i ∧ geodesicPoint x y n i ≤ x i) := by
  let delta := y i - x i
  have hmin : Nat.min n delta.natAbs ≤ delta.natAbs := Nat.min_le_right _ _
  rcases lt_trichotomy delta 0 with hneg | hzero | hpos
  · right
    have hsign : delta.sign = -1 := Int.sign_eq_neg_one_of_neg hneg
    have habs : (delta.natAbs : ℤ) = -delta := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
    have hminCast : (Nat.min n delta.natAbs : ℤ) ≤ delta.natAbs := by
      exact_mod_cast hmin
    change y i ≤ x i + delta.sign * (Nat.min n delta.natAbs : ℤ) ∧
      x i + delta.sign * (Nat.min n delta.natAbs : ℤ) ≤ x i
    rw [hsign]
    constructor <;> omega
  · subst delta
    left
    simp only [geodesicPoint, sub_eq_zero.mp hzero, sub_self, Int.sign_zero,
      Int.natAbs_zero, Nat.min_zero, Nat.cast_zero, mul_zero, add_zero, le_refl,
      and_self]
  · left
    have hsign : delta.sign = 1 := Int.sign_eq_one_of_pos hpos
    have habs : (delta.natAbs : ℤ) = delta := by
      rw [Int.natCast_natAbs, abs_of_pos hpos]
    have hminCast : (Nat.min n delta.natAbs : ℤ) ≤ delta.natAbs := by
      exact_mod_cast hmin
    change x i ≤ x i + delta.sign * (Nat.min n delta.natAbs : ℤ) ∧
      x i + delta.sign * (Nat.min n delta.natAbs : ℤ) ≤ y i
    rw [hsign]
    constructor <;> omega

/-- Every point of the synchronous geodesic between two cube sites remains in
the same cube. -/
theorem geodesicPoint_mem_latticeCubeSites {d L : ℕ} {v x y : Site d}
    (hx : x ∈ latticeCubeSites L v) (hy : y ∈ latticeCubeSites L v) (n : ℕ) :
    geodesicPoint x y n ∈ latticeCubeSites L v := by
  exact mem_latticeCubeSites_of_between hx hy (geodesicPoint_between x y n)

/-- The synchronous geodesic begins at its first endpoint. -/
@[simp] theorem geodesicPoint_zero {d : ℕ} (x y : Site d) :
    geodesicPoint x y 0 = x := by
  funext i
  simp only [geodesicPoint, Nat.zero_min, Nat.cast_zero, mul_zero, add_zero]

/-- After the sup distance many steps, the synchronous geodesic has reached
its second endpoint. -/
theorem geodesicPoint_siteDist {d : ℕ} (x y : Site d) :
    geodesicPoint x y (siteDist x y) = y := by
  funext i
  have hi : (y i - x i).natAbs ≤ siteDist x y := by
    have h := natAbs_sub_le_siteDist y x i
    rwa [siteDist_comm] at h
  simp only [geodesicPoint, Nat.min_eq_right hi]
  change x i + (y i - x i).sign * ((y i - x i).natAbs : ℤ) = y i
  rw [Int.sign_mul_natAbs]
  ring

/-- The synchronous geodesic has one more vertex than the sup distance. -/
@[simp] theorem length_geodesic {d : ℕ} (x y : Site d) :
    (geodesic x y).length = siteDist x y + 1 := by
  simp only [geodesic, List.length_map, List.length_range]

/-- The synchronous geodesic starts at `x`. -/
@[simp] theorem head?_geodesic {d : ℕ} (x y : Site d) :
    (geodesic x y).head? = some x := by
  have hpos : siteDist x y + 1 ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_succ _)
  simp only [geodesic, List.head?_map, List.head?_range, ite_eq_right hpos,
    Option.map_some, geodesicPoint_zero]

/-- The synchronous geodesic ends at `y`. -/
@[simp] theorem getLast?_geodesic {d : ℕ} (x y : Site d) :
    (geodesic x y).getLast? = some y := by
  rw [geodesic, List.getLast?_map]
  have hpos : 0 < siteDist x y + 1 := Nat.zero_lt_succ _
  rw [List.getLast?_range, ite_eq_right (Nat.ne_of_gt hpos)]
  simp only [Option.map_some, Nat.add_sub_cancel, geodesicPoint_siteDist]

private theorem natAbs_geodesicPoint_succ_sub_eq_one {d : ℕ}
    (x y : Site d) (n : ℕ) (i : Fin d)
    (hn : n < (y i - x i).natAbs) :
    (geodesicPoint x y (n + 1) i - geodesicPoint x y n i).natAbs = 1 := by
  let delta := y i - x i
  have hdelta : delta ≠ 0 := by
    intro hzero
    change n < delta.natAbs at hn
    rw [hzero, Int.natAbs_zero] at hn
    omega
  have hnle : n ≤ delta.natAbs := Nat.le_of_lt hn
  have hsuccle : n + 1 ≤ delta.natAbs := hn
  have heq : geodesicPoint x y (n + 1) i - geodesicPoint x y n i = delta.sign := by
    change x i + delta.sign * (Nat.min (n + 1) delta.natAbs : ℤ) -
      (x i + delta.sign * (Nat.min n delta.natAbs : ℤ)) = delta.sign
    simp only [Nat.min_eq_left hsuccle, Nat.min_eq_left hnle]
    push_cast
    ring
  rw [heq, Int.natAbs_sign_of_ne_zero hdelta]

private theorem natAbs_geodesicPoint_succ_sub_le_one {d : ℕ}
    (x y : Site d) (n : ℕ) (i : Fin d) :
    (geodesicPoint x y (n + 1) i - geodesicPoint x y n i).natAbs ≤ 1 := by
  by_cases hn : n < (y i - x i).natAbs
  · exact (natAbs_geodesicPoint_succ_sub_eq_one x y n i hn).le
  · have habsle : (y i - x i).natAbs ≤ n := Nat.le_of_not_gt hn
    have habssucc : (y i - x i).natAbs ≤ n + 1 := habsle.trans (Nat.le_succ n)
    have heq : geodesicPoint x y (n + 1) i = geodesicPoint x y n i := by
      simp only [geodesicPoint, Nat.min_eq_right habssucc, Nat.min_eq_right habsle]
    rw [heq, sub_self, Int.natAbs_zero]
    norm_num

/-- Consecutive synchronous geodesic points are sup-adjacent until the second
endpoint is reached. -/
theorem adj_geodesicPoint_succ {d : ℕ} (x y : Site d) {n : ℕ}
    (hn : n < siteDist x y) : Adj (geodesicPoint x y n) (geodesicPoint x y (n + 1)) := by
  unfold Adj
  apply le_antisymm
  · apply Finset.sup_le
    intro i _hi
    have hcoord := natAbs_geodesicPoint_succ_sub_le_one x y n i
    have hneg : geodesicPoint x y n i - geodesicPoint x y (n + 1) i =
        -(geodesicPoint x y (n + 1) i - geodesicPoint x y n i) := by
      ring
    rw [hneg, Int.natAbs_neg]
    exact hcoord
  · have hdistPos : 0 < siteDist x y := (Nat.zero_le n).trans_lt hn
    have hdPos : 0 < d := by
      by_contra hd
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
      subst d
      have hzero : siteDist x y = 0 := by
        unfold siteDist
        apply Nat.eq_zero_of_le_zero
        apply Finset.sup_le
        intro i _hi
        exact Fin.elim0 i
      rw [hzero] at hdistPos
      omega
    have huniv : (Finset.univ : Finset (Fin d)).Nonempty :=
      ⟨⟨0, hdPos⟩, Finset.mem_univ _⟩
    obtain ⟨i, _hi, hmax⟩ :=
      Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) huniv
        (fun j => (x j - y j).natAbs)
    change siteDist x y = (x i - y i).natAbs at hmax
    have habsEq : (y i - x i).natAbs = siteDist x y := by
      have hneg : y i - x i = -(x i - y i) := by ring
      rw [hneg, Int.natAbs_neg, ← hmax]
    have hni : n < (y i - x i).natAbs := by rwa [habsEq]
    have hcoordEq := natAbs_geodesicPoint_succ_sub_eq_one x y n i hni
    have hneg : geodesicPoint x y n i - geodesicPoint x y (n + 1) i =
        -(geodesicPoint x y (n + 1) i - geodesicPoint x y n i) := by
      ring
    have hcoord : (geodesicPoint x y n i -
        geodesicPoint x y (n + 1) i).natAbs = 1 := by
      rw [hneg, Int.natAbs_neg, hcoordEq]
    have hle := natAbs_sub_le_siteDist
      (geodesicPoint x y n) (geodesicPoint x y (n + 1)) i
    rw [hcoord] at hle
    exact hle

/-- The synchronous geodesic is a lattice path. -/
theorem isPath_geodesic {d : ℕ} (x y : Site d) : IsPath (geodesic x y) := by
  rw [IsPath, geodesic, List.isChain_map, List.isChain_range_succ]
  intro n hn
  exact adj_geodesicPoint_succ x y hn

/-- Every vertex of a geodesic between two sites of one triadic cube belongs
to that cube. -/
theorem mem_latticeCubeSites_of_mem_geodesic {d L : ℕ} {v x y z : Site d}
    (hx : x ∈ latticeCubeSites L v) (hy : y ∈ latticeCubeSites L v)
    (hz : z ∈ geodesic x y) : z ∈ latticeCubeSites L v := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hz
  exact geodesicPoint_mem_latticeCubeSites hx hy n

/-- The sup distance between two sites of one scale-`L` cube is at most
`3^L`. -/
theorem siteDist_le_three_pow_of_mem_latticeCubeSites {d L : ℕ}
    {v x y : Site d} (hx : x ∈ latticeCubeSites L v)
    (hy : y ∈ latticeCubeSites L v) : siteDist x y ≤ 3 ^ L := by
  have hxRadius := siteDist_cubeCenter_le_half hx
  have hyRadius := siteDist_cubeCenter_le_half hy
  have htriangle := siteDist_triangle x (cubeCenter L v) y
  rw [siteDist_comm x (cubeCenter L v)] at htriangle
  have hodd : 2 * (3 ^ L / 2) + 1 = 3 ^ L :=
    Nat.two_mul_div_two_add_one_of_odd (odd_three_pow_minimizer L)
  omega

end Algsuperdiff.Section5.Percolation
