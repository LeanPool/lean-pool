/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Hypotheses
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Inflate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Inflated bad events on triadic lattice cubes

This file partitions the integer lattice into centered triadic cubes, defines
the corresponding inflated bad events, and records the residue colouring used
to separate cubes in one colour class.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The center indexed by `v` in the sublattice `3^L ℤ^d`. -/
def cubeCenter {d : ℕ} (L : ℕ) (v : Site d) : Site d :=
  fun i => (3 ^ L : ℕ) * v i

/-- The canonical index of the centered triadic cube containing `z`. -/
def centerIndex {d : ℕ} (L : ℕ) (z : Site d) : Site d :=
  fun i => Int.bdiv (z i) (3 ^ L)

/-- The centered remainder of `z` modulo `3^L`, coordinatewise. -/
def centeredRemainder {d : ℕ} (L : ℕ) (z : Site d) : Site d :=
  fun i => Int.bmod (z i) (3 ^ L)

/-- A site is its canonical triadic center plus its centered remainder. -/
theorem cubeCenter_add_centeredRemainder {d L : ℕ} (z : Site d) :
    cubeCenter L (centerIndex L z) + centeredRemainder L z = z := by
  funext i
  exact Int.bdiv_add_bmod (z i) (3 ^ L)

private theorem odd_three_pow (L : ℕ) : Odd (3 ^ L) := by
  exact (show Odd 3 by norm_num).pow

/-- The canonical centered remainder lies in the open scale-`L` cube. -/
theorem centeredRemainder_inCube {d L : ℕ} (z : Site d) :
    inCube L (centeredRemainder L z) := by
  intro i
  let q := 3 ^ L
  have hq : 0 < q := pow_pos (by norm_num) L
  have hodd : 2 * (q / 2) + 1 = q :=
    Nat.two_mul_div_two_add_one_of_odd (odd_three_pow L)
  have hlo : -((q / 2 : ℕ) : ℤ) ≤ Int.bmod (z i) q := Int.le_bmod hq
  have hhi : Int.bmod (z i) q < (((q + 1) / 2 : ℕ) : ℤ) := Int.bmod_lt hq
  have hhalf : (q + 1) / 2 = q / 2 + 1 := by omega
  rw [hhalf] at hhi
  change 2 * (Int.bmod (z i) q).natAbs < q
  by_cases hr : 0 ≤ Int.bmod (z i) q
  · have hcast : (2 * (Int.bmod (z i) q).natAbs : ℤ) < q := by
      push_cast
      rw [abs_of_nonneg hr]
      omega
    exact_mod_cast hcast
  · have hr' : Int.bmod (z i) q < 0 := lt_of_not_ge hr
    have hcast : (2 * (Int.bmod (z i) q).natAbs : ℤ) < q := by
      push_cast
      rw [abs_of_neg hr']
      omega
    exact_mod_cast hcast

/-- The finite set of sites in the centered scale-`L` cube indexed by `v`. -/
def latticeCubeSites {d : ℕ} (L : ℕ) (v : Site d) : Finset (Site d) :=
  (cubeSites d L).image fun r => cubeCenter L v + r

/-- Every site lies in its canonical centered triadic cube. -/
theorem mem_latticeCubeSites_centerIndex {d L : ℕ} (z : Site d) :
    z ∈ latticeCubeSites L (centerIndex L z) := by
  apply Finset.mem_image.mpr
  refine ⟨centeredRemainder L z,
    mem_cubeSites_of_inCube (centeredRemainder_inCube z), ?_⟩
  exact cubeCenter_add_centeredRemainder z

private theorem cubeCenter_add_injective {d L : ℕ} (v : Site d) :
    Function.Injective (fun r : Site d => cubeCenter L v + r) := by
  intro r r' h
  exact add_left_cancel h

/-- Every translated scale-`L` cube has exactly `3^(dL)` lattice sites. -/
theorem card_latticeCubeSites (d L : ℕ) (v : Site d) :
    (latticeCubeSites L v).card = 3 ^ (d * L) := by
  rw [latticeCubeSites, Finset.card_image_of_injective _
    (cubeCenter_add_injective v), card_cubeSites]

/-- The residue colour of a triadic cube index. -/
def centerColor {d : ℕ} (v : Site d) : Fin d → ZMod 3 :=
  fun i => v i

private theorem inCube_natAbs_le_half {d L : ℕ} {r : Site d}
    (hr : inCube L r) (i : Fin d) :
    (r i).natAbs ≤ 3 ^ L / 2 := by
  have hodd : 2 * (3 ^ L / 2) + 1 = 3 ^ L :=
    Nat.two_mul_div_two_add_one_of_odd (odd_three_pow L)
  have hri := hr i
  omega

private theorem mem_cubeSites_inCube {d L : ℕ} {r : Site d}
    (hr : r ∈ cubeSites d L) : inCube L r := by
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hr
  exact cubeSiteOfIndex_inCube j

/-- A site belongs to only its canonical centered triadic cube. -/
theorem centerIndex_eq_of_mem_latticeCubeSites {d L : ℕ} {v z : Site d}
    (hz : z ∈ latticeCubeSites L v) : centerIndex L z = v := by
  obtain ⟨r, hr, hzr⟩ := Finset.mem_image.mp hz
  have hrCube : inCube L r := mem_cubeSites_inCube hr
  funext i
  let q := 3 ^ L
  have hq : 0 < q := pow_pos (by norm_num) L
  have hodd : 2 * (q / 2) + 1 = q :=
    Nat.two_mul_div_two_add_one_of_odd (odd_three_pow L)
  have hrle : (r i).natAbs ≤ q / 2 := inCube_natAbs_le_half hrCube i
  have hrlo : -((q / 2 : ℕ) : ℤ) ≤ r i := by
    have habs : |r i| ≤ ((q / 2 : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hrle
    exact (abs_le.mp habs).1
  have hrhi : r i < (((q + 1) / 2 : ℕ) : ℤ) := by
    have hhalf : (q + 1) / 2 = q / 2 + 1 := by omega
    rw [hhalf]
    have habs : r i ≤ (r i).natAbs := Int.le_natAbs
    exact lt_of_le_of_lt habs (by exact_mod_cast (Nat.lt_succ_of_le hrle))
  have hdvd : (q : ℤ) ∣ r i - z i := by
    refine ⟨-(v i), ?_⟩
    have hi := congr_fun hzr i
    change (cubeCenter L v) i + r i = z i at hi
    change r i - z i = (q : ℤ) * (-(v i))
    rw [← hi]
    change r i - ((q : ℤ) * v i + r i) = (q : ℤ) * (-(v i))
    ring
  have hrmod : Int.bmod (z i) q = r i :=
    (Int.bmod_eq_iff hq).2 ⟨hrlo, hrhi, hdvd⟩
  have hdecomp := Int.bdiv_add_bmod (z i) q
  rw [hrmod] at hdecomp
  have hi := congr_fun hzr i
  change (q : ℤ) * v i + r i = z i at hi
  have hdecomp' : (q : ℤ) * Int.bdiv (z i) q + r i =
      (q : ℤ) * v i + r i := hdecomp.trans hi.symm
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  exact Int.eq_of_mul_eq_mul_left hq0 (add_right_cancel hdecomp')

/-- Cube membership is characterized by the canonical cube index. -/
theorem mem_latticeCubeSites_iff_centerIndex_eq {d L : ℕ} {v z : Site d} :
    z ∈ latticeCubeSites L v ↔ centerIndex L z = v := by
  constructor
  · exact centerIndex_eq_of_mem_latticeCubeSites
  · intro h
    rw [← h]
    exact mem_latticeCubeSites_centerIndex z

/-- Sites at sup distance strictly less than `3^L` have canonical scale-`L`
cube indices differing by at most one in every coordinate. -/
theorem natAbs_centerIndex_sub_le_one_of_siteDist_lt {d L : ℕ}
    {z y : Site d} (hzy : siteDist z y < 3 ^ L) (i : Fin d) :
    ((centerIndex L z) i - (centerIndex L y) i).natAbs ≤ 1 := by
  let q := 3 ^ L
  have hqPos : 0 < q := pow_pos (by norm_num) L
  have hcoordLe := natAbs_sub_le_siteDist z y i
  have hcoord : (z i - y i).natAbs < q := hcoordLe.trans_lt hzy
  have hzRem := inCube_natAbs_le_half (L := L) (r := centeredRemainder L z)
    (centeredRemainder_inCube (L := L) z) i
  have hyRem := inCube_natAbs_le_half (L := L) (r := centeredRemainder L y)
    (centeredRemainder_inCube (L := L) y) i
  have hodd : 2 * (q / 2) + 1 = q :=
    Nat.two_mul_div_two_add_one_of_odd (odd_three_pow L)
  have hrem : ((centeredRemainder L z) i -
      (centeredRemainder L y) i).natAbs ≤ q - 1 := by
    have htri := Int.natAbs_sub_le
      ((centeredRemainder L z) i) ((centeredRemainder L y) i)
    omega
  have hdecompZ := congr_fun (cubeCenter_add_centeredRemainder (L := L) z) i
  have hdecompY := congr_fun (cubeCenter_add_centeredRemainder (L := L) y) i
  have heq : (q : ℤ) * ((centerIndex L z) i - (centerIndex L y) i) =
      (z i - y i) -
        ((centeredRemainder L z) i - (centeredRemainder L y) i) := by
    change (q : ℤ) * (centerIndex L z) i + (centeredRemainder L z) i = z i at hdecompZ
    change (q : ℤ) * (centerIndex L y) i + (centeredRemainder L y) i = y i at hdecompY
    rw [← hdecompZ, ← hdecompY]
    ring
  have hmul : q * ((centerIndex L z) i - (centerIndex L y) i).natAbs <
      2 * q := by
    have htri := Int.natAbs_sub_le (z i - y i)
      ((centeredRemainder L z) i - (centeredRemainder L y) i)
    rw [← heq, Int.natAbs_mul, Int.natAbs_natCast] at htri
    omega
  by_contra hnot
  have htwo : 2 ≤ ((centerIndex L z) i - (centerIndex L y) i).natAbs := by
    omega
  have hmulLower := Nat.mul_le_mul_left q htwo
  omega

/-- Every site of a translated scale-`L` cube is within sup distance
`3^L / 2` of its center. -/
theorem siteDist_cubeCenter_le_half {d L : ℕ} {v z : Site d}
    (hz : z ∈ latticeCubeSites L v) :
    siteDist (cubeCenter L v) z ≤ 3 ^ L / 2 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  apply Finset.sup_le
  intro i _hi
  change ((cubeCenter L v) i - ((cubeCenter L v) i + r i)).natAbs ≤ 3 ^ L / 2
  have hneg : (cubeCenter L v) i - ((cubeCenter L v) i + r i) = -(r i) := by
    ring
  rw [hneg, Int.natAbs_neg]
  exact inCube_natAbs_le_half (mem_cubeSites_inCube hr) i

private theorem natAbs_coord_sub_ge_three_of_sameColor {d : ℕ}
    {v w : Site d} (hvw : v ≠ w) (hcolor : centerColor v = centerColor w) :
    ∃ i : Fin d, 3 ≤ (v i - w i).natAbs := by
  have hex : ∃ i : Fin d, v i ≠ w i := by
    by_contra h
    push Not at h
    exact hvw (funext h)
  obtain ⟨i, hi⟩ := hex
  have hcast : (v i : ZMod 3) = (w i : ZMod 3) := congr_fun hcolor i
  have hdvdInt : (3 : ℤ) ∣ w i - v i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (v i) (w i) 3).mp hcast
  have hdvd : 3 ∣ (v i - w i).natAbs := by
    have hneg : w i - v i = -(v i - w i) := by ring
    rw [hneg] at hdvdInt
    have : (3 : ℤ).natAbs ∣ (-(v i - w i)).natAbs :=
      Int.natAbs_dvd_natAbs.mpr hdvdInt
    simpa only [Int.natAbs_natCast, Int.natAbs_neg] using! this
  have hpos : 0 < (v i - w i).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hi)
  exact ⟨i, Nat.le_of_dvd hpos hdvd⟩

private theorem siteDist_cubeCenter_ge_three_mul {d L : ℕ} {v w : Site d}
    (hvw : v ≠ w) (hcolor : centerColor v = centerColor w) :
    3 * 3 ^ L ≤ siteDist (cubeCenter L v) (cubeCenter L w) := by
  obtain ⟨i, hi⟩ := natAbs_coord_sub_ge_three_of_sameColor hvw hcolor
  have hcoord := natAbs_sub_le_siteDist (cubeCenter L v) (cubeCenter L w) i
  change (((3 ^ L : ℕ) : ℤ) * v i - ((3 ^ L : ℕ) : ℤ) * w i).natAbs ≤
    siteDist (cubeCenter L v) (cubeCenter L w) at hcoord
  have heq : ((3 ^ L : ℕ) : ℤ) * v i - ((3 ^ L : ℕ) : ℤ) * w i =
      ((3 ^ L : ℕ) : ℤ) * (v i - w i) := by ring
  rw [heq, Int.natAbs_mul, Int.natAbs_natCast] at hcoord
  have hmul := Nat.mul_le_mul_left (3 ^ L) hi
  simpa only [Nat.mul_comm] using hmul.trans hcoord

/-- Distinct triadic cubes of one residue colour are separated by more than
their scale.  This is the geometric input for within-colour independence. -/
theorem latticeCubeSites_separated_of_sameColor {d L : ℕ} {v w : Site d}
    (hvw : v ≠ w) (hcolor : centerColor v = centerColor w)
    {z y : Site d} (hz : z ∈ latticeCubeSites L v)
    (hy : y ∈ latticeCubeSites L w) :
    3 ^ L < siteDist z y := by
  have hcenters := siteDist_cubeCenter_ge_three_mul (L := L) hvw hcolor
  have hzrad := siteDist_cubeCenter_le_half hz
  have hyrad := siteDist_cubeCenter_le_half hy
  have htri₁ := siteDist_triangle (cubeCenter L v) z (cubeCenter L w)
  have htri₂ := siteDist_triangle z y (cubeCenter L w)
  have hzsym : siteDist z (cubeCenter L v) = siteDist (cubeCenter L v) z :=
    siteDist_comm _ _
  have hfull : siteDist (cubeCenter L v) (cubeCenter L w) ≤
      siteDist (cubeCenter L v) z + siteDist z y +
        siteDist y (cubeCenter L w) := by
    exact htri₁.trans (by
      simpa only [Nat.add_assoc] using
        (Nat.add_le_add_left htri₂ (siteDist (cubeCenter L v) z)))
  rw [siteDist_comm y (cubeCenter L w)] at hfull
  have hodd : 2 * (3 ^ L / 2) + 1 = 3 ^ L :=
    Nat.two_mul_div_two_add_one_of_odd (odd_three_pow L)
  omega

/-- The scale-`L` bad event inflated over one triadic cube. -/
def inflatedBadEvent {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (L : ℕ) (v : Site d) : Set Ω :=
  ⋃ z ∈ latticeCubeSites L v, B L z

/-- The union, over all scales, of the inflated cube event containing `z`. -/
def inflatedBadSet {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (z : Site d) : Set Ω :=
  ⋃ L, inflatedBadEvent B L (centerIndex L z)

/-- The original bad event at a site is contained in its inflated version. -/
theorem badSet_subset_inflatedBadSet {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (z : Site d) :
    badSet B z ⊆ inflatedBadSet B z := by
  intro ω hω
  simp only [badSet, Set.mem_iUnion] at hω
  obtain ⟨L, hωL⟩ := hω
  simp only [inflatedBadSet, inflatedBadEvent, Set.mem_iUnion]
  exact ⟨L, z, mem_latticeCubeSites_centerIndex z, hωL⟩

/-- Inflated bad events are measurable when every original bad event is. -/
theorem measurableSet_inflatedBadEvent {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {B : ℕ → Site d → Set Ω} (hB : ∀ L z, MeasurableSet (B L z))
    (L : ℕ) (v : Site d) :
    MeasurableSet (inflatedBadEvent B L v) := by
  apply Finset.measurableSet_biUnion
  intro z _hz
  exact hB L z

/-- A union bound for one inflated cube, retaining the exact cube-cardinality
factor. -/
theorem measureReal_inflatedBadEvent_le {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (P : Measure Ω) (B : ℕ → Site d → Set Ω) (a T : ℝ)
    (hB : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (L : ℕ) (v : Site d) :
    P.real (inflatedBadEvent B L v) ≤
      (3 ^ (d * L) : ℝ) * Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))) := by
  calc
    P.real (inflatedBadEvent B L v) ≤
        ∑ z ∈ latticeCubeSites L v, P.real (B L z) := by
      exact measureReal_biUnion_finset_le (latticeCubeSites L v) (B L)
    _ ≤ ∑ _z ∈ latticeCubeSites L v,
        Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))) := by
      apply Finset.sum_le_sum
      intro z _hz
      exact hB L z
    _ = (3 ^ (d * L) : ℝ) *
        Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))) := by
      rw [Finset.sum_const, card_latticeCubeSites]
      norm_num

private theorem nat_le_three_pow_inflate (L : ℕ) : L ≤ 3 ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
      rw [pow_succ]
      have hpos : 0 < 3 ^ L := pow_pos (by norm_num) L
      omega

/-- Once `T` exceeds a dimension-only threshold, the polynomial cube-volume
factor is absorbed into half of the stretched-exponential exponent. -/
theorem measureReal_inflatedBadEvent_le_exp_half
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (B : ℕ → Site d → Set Ω) (a T : ℝ)
    (hB : ∀ L z,
      P.real (B L z) ≤ Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L))))
    (ha : 1 ≤ a) (hT : 2 * (d + 1) ≤ T) (L : ℕ) (v : Site d) :
    P.real (inflatedBadEvent B L v) ≤
      Real.exp (-(T ^ 2 * (3 : ℝ) ^ (a * L) / 2)) := by
  have hbase := measureReal_inflatedBadEvent_le P B a T hB L v
  apply hbase.trans
  let N : ℝ := (3 : ℝ) ^ (d * L)
  let X : ℝ := T ^ 2 * (3 : ℝ) ^ (a * L)
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have hlogThree : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [h]
  have hlogN : Real.log N ≤ 2 * (d : ℝ) * L := by
    dsimp only [N]
    rw [Real.log_pow]
    have h := mul_le_mul_of_nonneg_left hlogThree
      (show (0 : ℝ) ≤ (d * L : ℕ) by positivity)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm,
      mul_left_comm] using h
  have hLpow : (L : ℝ) ≤ (3 : ℝ) ^ (a * L) := by
    have hnat := nat_le_three_pow_inflate L
    have hcast : (L : ℝ) ≤ (3 : ℝ) ^ L := by exact_mod_cast hnat
    have hexp : (L : ℝ) ≤ a * L := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg L)
    exact hcast.trans (by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  have hdimNonneg : 0 ≤ (2 : ℝ) * (d + 1) := by positivity
  have hTsq : ((2 : ℝ) * (d + 1)) ^ 2 ≤ T ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hdimNonneg hT
  have hdLeSq : (d : ℝ) ≤ (d + 1) ^ 2 := by
    have hdOne : (d : ℝ) ≤ d + 1 := by norm_num
    have hone : (1 : ℝ) ≤ d + 1 := by norm_num
    calc
      (d : ℝ) ≤ d + 1 := hdOne
      _ = (d + 1) * 1 := by ring
      _ ≤ (d + 1) * (d + 1) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
      _ = (d + 1) ^ 2 := by ring
  have hcoef : 2 * (d : ℝ) ≤ T ^ 2 / 2 := by
    linarith only [hTsq, hdLeSq]
  have hlogAbsorb : Real.log N ≤ X / 2 := by
    apply hlogN.trans
    calc
      2 * (d : ℝ) * L ≤ 2 * (d : ℝ) * (3 : ℝ) ^ (a * L) :=
        mul_le_mul_of_nonneg_left hLpow (by positivity)
      _ ≤ (T ^ 2 / 2) * (3 : ℝ) ^ (a * L) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = X / 2 := by simp only [X]; ring
  change N * Real.exp (-X) ≤ Real.exp (-(X / 2))
  calc
    N * Real.exp (-X) = Real.exp (Real.log N) * Real.exp (-X) := by
      rw [Real.exp_log hNpos]
    _ = Real.exp (Real.log N - X) := by rw [← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp (-(X / 2)) := by
      rw [Real.exp_le_exp]
      linarith only [hlogAbsorb]

private theorem measurableSet_inflatedBadEvent_generated {Ω : Type*}
    {d L : ℕ} {B : ℕ → Site d → Set Ω} (v : Site d) :
    MeasurableSet[MeasurableSpace.generateFrom
      {S | ∃ z ∈ (latticeCubeSites L v : Set (Site d)),
        ∃ L' ≤ L, S = B L' z}] (inflatedBadEvent B L v) := by
  apply Finset.measurableSet_biUnion
  intro z hz
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨z, hz, L, le_rfl, rfl⟩

/-- Inflated-event indicators over finitely many cubes of one residue colour
are mutually independent. -/
theorem iIndepFun_inflatedIndicator_of_sameColor
    {Ω : Type*} [MeasurableSpace Ω] {d L : ℕ} (P : Measure Ω)
    (B : ℕ → Site d → Set Ω) (hsep : SepIndep P B)
    (hB : ∀ L z, MeasurableSet (B L z)) (s : Finset (Site d))
    (b : Fin d → ZMod 3) (hcolor : ∀ v ∈ s, centerColor v = b) :
    ProbabilityTheory.iIndepFun
      (fun v : {v // v ∈ s} =>
        (inflatedBadEvent B L v.1).indicator fun _ω => (1 : ℝ)) P := by
  let blocks : {v // v ∈ s} → Set (Site d) :=
    fun v => latticeCubeSites L v.1
  have hblocks : ∀ i j, i ≠ j → ∀ z ∈ blocks i, ∀ y ∈ blocks j,
      3 ^ L < siteDist z y := by
    intro i j hij z hz y hy
    have hijv : i.1 ≠ j.1 := by
      intro h
      exact hij (Subtype.ext h)
    have hc : centerColor i.1 = centerColor j.1 := by
      rw [hcolor i.1 i.2, hcolor j.1 j.2]
    exact latticeCubeSites_separated_of_sameColor hijv hc hz hy
  have hindSpaces := hsep {v // v ∈ s} L blocks hblocks
  have hindSet : ProbabilityTheory.iIndepSet
      (fun v : {v // v ∈ s} => inflatedBadEvent B L v.1) P := by
    rw [ProbabilityTheory.iIndepSet_iff_meas_biInter]
    · intro t
      exact hindSpaces.meas_biInter fun v _hv =>
        measurableSet_inflatedBadEvent_generated v.1
    · intro v
      exact measurableSet_inflatedBadEvent hB L v.1
  exact hindSet.iIndepFun_indicator

/-- The finite set of canonical scale-`L` cube indices touched by a path. -/
def touchingCenters {d : ℕ} (L : ℕ) (Γ : List (Site d)) : Finset (Site d) :=
  Γ.toFinset.image (centerIndex L)

/-- A path vertex contributes its canonical cube to `touchingCenters`. -/
theorem centerIndex_mem_touchingCenters {d L : ℕ} {Γ : List (Site d)} {z : Site d}
    (hz : z ∈ Γ) : centerIndex L z ∈ touchingCenters L Γ := by
  exact Finset.mem_image.mpr ⟨z, List.mem_toFinset.mpr hz, rfl⟩

open Classical in
/-- The number of touched scale-`L` cubes whose inflated event occurs. -/
noncomputable def inflatedCubeCount {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (L : ℕ) (Γ : List (Site d)) (ω : Ω) : ℕ :=
  ((touchingCenters L Γ).filter fun v => ω ∈ inflatedBadEvent B L v).card

end Algsuperdiff.Section5.Percolation
