/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Lattice
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCube
public import LeanPool.MarkovProcess.MarkovProcess.Path.Sampling
public import Mathlib.Data.List.ChainOfFn

/-!
# CubeTrace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Triadic cube traces of uniformly sampled paths

This file turns a sufficiently fine uniform sampling of a continuous path in
`Vec d` into the weak lattice paths used by the Section 5 percolation bound.

We use `Homogenization.cubeSet`, the half-open realization
`[(z_i - 1/2) 3^n, (z_i + 1/2) 3^n)`, so every point belongs to the cube whose
site is obtained by coordinatewise integer rounding after division by `3^n`.
Thus the cube site is exactly `Algsuperdiff.Section5.Percolation.Site d` after
rescaling by `3⁻ⁿ`.  The predicate `Percolation.inCube k` is the centered open
cube condition on these rescaled integer sites.
-/

open HCPolySupport
open scoped ENNReal NNReal

namespace Algsuperdiff.Section5.Trace

/-- The site of the scale-`n` half-open triadic partition containing `x`.
At boundary points, integer rounding selects the cube on the positive side. -/
noncomputable def nearestTriadicSite {d : ℕ} (n : ℤ) (x : Vec d) :
    Section5.Percolation.Site d :=
  fun i => round (x i / (3 : ℝ) ^ n)

/-- The scale-`n` triadic partition cube indexed by the lattice site `z`. -/
def partitionCube {d : ℕ} (n : ℤ) (z : Section5.Percolation.Site d) : TriadicCube d where
  scale := n
  index := z

/-- The embedding of a lattice site as the center of its scale-`n` cube. -/
noncomputable def rescaleSite {d : ℕ} (n : ℤ) (z : Section5.Percolation.Site d) : Vec d :=
  fun i => (z i : ℝ) * (3 : ℝ) ^ n

/-- Coordinatewise rounding assigns every point to its half-open partition
cube, including points on cube boundaries. -/
theorem mem_partitionCube_nearestTriadicSite {d : ℕ} (n : ℤ) (x : Vec d) :
    x ∈ cubeSet (partitionCube n (nearestTriadicSite n x)) := by
  intro i
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  let a : ℝ := x i / (3 : ℝ) ^ n
  have hloRound : ((round a : ℤ) : ℝ) ≤ a + 1 / 2 := round_le_add_half a
  have hhiRound : a - 1 / 2 < ((round a : ℤ) : ℝ) := sub_half_lt_round a
  have hlo : ((round a : ℤ) : ℝ) - 1 / 2 ≤ a := by
    linarith only [hloRound]
  have hhi : a < ((round a : ℤ) : ℝ) + 1 / 2 := by
    linarith only [hhiRound]
  change ((((round a : ℤ) : ℝ) - 1 / 2) * (3 : ℝ) ^ n ≤ x i) ∧
    x i < (((round a : ℤ) : ℝ) + 1 / 2) * (3 : ℝ) ^ n
  constructor
  · exact (le_div_iff₀ hs).mp hlo
  · exact (div_lt_iff₀ hs).mp hhi

/-- Points less than one scale-`n` side length apart in the `Vec d` sup metric
are assigned sites at lattice sup distance at most one. -/
theorem siteDist_nearestTriadicSite_le_one_of_dist_lt {d : ℕ} (n : ℤ)
    {x y : Vec d} (hxy : dist x y < (3 : ℝ) ^ n) :
    Section5.Percolation.siteDist (nearestTriadicSite n x) (nearestTriadicSite n y) ≤ 1 := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  apply Finset.sup_le
  intro i _hi
  have hcoord : dist (x i) (y i) < (3 : ℝ) ^ n :=
    (dist_pi_lt_iff hs).mp hxy i
  rw [Real.dist_eq] at hcoord
  let a : ℝ := x i / (3 : ℝ) ^ n
  let b : ℝ := y i / (3 : ℝ) ^ n
  have hab : |a - b| < 1 := by
    change |x i / (3 : ℝ) ^ n - y i / (3 : ℝ) ^ n| < 1
    rw [div_sub_div_same, abs_div, abs_of_pos hs, div_lt_one hs]
    exact hcoord
  have ha := abs_le.mp (abs_sub_round a)
  have hb := abs_le.mp (abs_sub_round b)
  have hab' := abs_lt.mp hab
  have hloR : (-2 : ℝ) <
      ((round a : ℤ) : ℝ) - ((round b : ℤ) : ℝ) := by
    linarith only [ha.1, ha.2, hb.1, hb.2, hab'.1, hab'.2]
  have hhiR : ((round a : ℤ) : ℝ) - ((round b : ℤ) : ℝ) < 2 := by
    linarith only [ha.1, ha.2, hb.1, hb.2, hab'.1, hab'.2]
  have hloZ : (-2 : ℤ) < round a - round b := by
    exact_mod_cast hloR
  have hhiZ : round a - round b < (2 : ℤ) := by
    exact_mod_cast hhiR
  change (round a - round b).natAbs ≤ 1
  omega

/-- The sequence of scale-`n` cube sites containing a tuple of sample points. -/
noncomputable def cubeTrace {d M : ℕ} (n : ℤ) (point : Fin (M + 1) → Vec d) :
    List (Section5.Percolation.Site d) :=
  List.ofFn fun k => nearestTriadicSite n (point k)

/-- A point tuple with consecutive sup distances less than `3^n` has a weak
lattice cube trace. -/
theorem cubeTrace_isWeakPath {d M : ℕ} (n : ℤ) (point : Fin (M + 1) → Vec d)
    (hstep : ∀ k (hk : k + 1 < M + 1),
      dist (point ⟨k, Nat.lt_of_succ_lt hk⟩) (point ⟨k + 1, hk⟩) < (3 : ℝ) ^ n) :
    Section5.Percolation.IsWeakPath (cubeTrace n point) := by
  rw [cubeTrace, Section5.Percolation.IsWeakPath, List.isChain_ofFn]
  intro k hk
  exact siteDist_nearestTriadicSite_le_one_of_dist_lt n (hstep k hk)

/-- The time of the `k`th point in the uniform subdivision of `[0,T]` into
`M` pieces. -/
noncomputable def uniformSampleTime (T : NNReal) (M : ℕ) (k : Fin (M + 1)) : NNReal :=
  (k.1 : NNReal) * T / (M : NNReal)

/-- The cube trace of the uniform subdivision of a continuous path. -/
noncomputable def uniformCubeTrace {d : ℕ} (n : ℤ) (M : ℕ)
    (omega : MarkovProcess.ContinuousPath (Vec d)) (T : NNReal) :
    List (Section5.Percolation.Site d) :=
  cubeTrace n fun k => omega (uniformSampleTime T M k)

/-- Uniform continuity supplies a strictly pre-exit uniform sampling whose
scale-`n` cube trace is weakly adjacent.  Every sampled point lies in its
recorded half-open partition cube. -/
theorem exists_uniformCubeTrace_lt_exitTime {d : ℕ} (U : Set (Vec d))
    (omega : MarkovProcess.ContinuousPath (Vec d)) (T : NNReal)
    (hT : (T : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime U omega) (n : ℤ) :
    ∃ M : ℕ, 0 < M ∧
      (∀ k : Fin (M + 1),
        ((uniformSampleTime T M k : NNReal) : ℝ≥0∞) <
          MarkovProcess.ContinuousPath.exitTime U omega) ∧
      Section5.Percolation.IsWeakPath (uniformCubeTrace n M omega T) ∧
      (∀ k : Fin (M + 1), omega (uniformSampleTime T M k) ∈
        cubeSet (partitionCube n (nearestTriadicSite n
          (omega (uniformSampleTime T M k))))) := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  obtain ⟨M, hM, hbefore, hstep⟩ :=
    omega.exists_uniform_sampling_lt_exitTime U T hT ((3 : ℝ) ^ n) hs
  refine ⟨M, hM, ?_, ?_, fun k => mem_partitionCube_nearestTriadicSite n _⟩
  · intro k
    exact hbefore k.1 (Nat.lt_succ_iff.mp k.2)
  · apply cubeTrace_isWeakPath
    intro k hk
    simpa only [uniformSampleTime, Nat.cast_add, Nat.cast_one] using hstep k (by omega)

end Algsuperdiff.Section5.Trace
