/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.CrossingTrace
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Trace.RescaledPathBound

/-!
# GoodCubeCrossing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Good cubes met by a crossing of the annulus

The chains-of-good-cubes estimate counts the sites of a crossing of the annulus
between `□_{m-1}` and the complement of `□_m` at which the event
`Q(z + □_n, ε)` occurs.  It reads a crossing as a function `x : ℕ → ℤ^d` on
`{0, …, N}` and counts with `qSiteCount`, while the pre-exit cube trace of a
continuous path is a *list* of strictly adjacent sites whose good vertices are
counted with `Finset.filter`.  This file converts the first count into the
second at the crossing index `(m - n).toNat` of the lattice `3^{n-1} ℤ^d`, and
carries the resulting bound to the trace of a continuous path stopped on
leaving `□_m`.

## Main definitions

* `goodSites`, `goodSiteEnum` — the good sites of a centered lattice cube and
  their injective enumeration.

## Main results

* `rescaledLatticePoint_eq_paperLatticePoint` — the two embeddings of the site
  lattice `3^{n-1} ℤ^d` into `ℝ^d` agree.
* `le_card_filter_of_isPathFrom` — the good-site count along a list crossing
  in the discrete reading of the annulus.
* `natThreshold_le_card_filter_of_isPathFrom` — the same bound with the
  threshold `(3/4) 3^{m-n}` read as a natural number.
* `exists_preExit_goodCubeTrace` — a pre-exit cube trace of a continuous path
  crossing `□_{n+k+1}` whose good-vertex count is within `2 d` of the count
  available along every crossing of the discrete annulus at index `k`.
* `inCube_of_mem_cubeSet_partitionCube` — a scale-`n` cell meeting `□_{n+k+1}`
  is indexed by a site of the centered cube of index `k + 1`, so the trace
  vertices are enumerated by `goodSiteEnum`.
-/

open HCPolySupport MeasureTheory
open scoped ENNReal NNReal

namespace Algsuperdiff.Section5.Trace

open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## 1. The two embeddings of the site lattice -/

/-- The embedding `z ↦ 3^{n-1} z` used by the good cube events is the embedding
used by the path estimate. -/
theorem rescaledLatticePoint_eq_paperLatticePoint (n : ℤ)
    (z : Section5.Percolation.Site d) :
    Support.rescaledLatticePoint n z = paperLatticePoint n z := by
  have hcast : Real.rpow 3 ((n : ℝ) - 1) = (3 : ℝ) ^ (n - 1) := by
    rw [show ((n : ℝ) - 1) = ((n - 1 : ℤ) : ℝ) by push_cast; ring]
    exact Real.rpow_intCast 3 (n - 1)
  funext i
  simp only [Support.rescaledLatticePoint, paperLatticePoint, rescaleSite,
    Pi.smul_apply, smul_eq_mul, hcast]
  ring

/-! ## 2. From the crossing count to the good-vertex count -/

/-- **The good-vertex count along a list crossing.**  The crossing bound
supplied for the functional reading of a crossing of the annulus at index
`(m - n).toNat` bounds the number of good vertices of every list crossing at
the same index. -/
theorem le_card_filter_of_isPathFrom (M : ABKModel d) (Creg Cinj : ℝ) (m n : ℤ)
    (ep : ℝ) (omega : Cutoff.CutoffSample d)
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (hGood : ∀ z, Good z ↔
      omega ∈ Support.qEvent M Creg Cinj n (Support.rescaledLatticePoint n z) ep)
    (hcrossing : ∀ (N : ℕ) (x : ℕ → Fin d → ℤ),
      Provider.Percolation.IsLatticePath x N →
      x 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
      x N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
      (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
        ((Support.qSiteCount M Creg Cinj n ep
          (Section5.Percolation.pathSites N x) omega : ℕ) : ℝ))
    (Xi : List (Section5.Percolation.Site d))
    (hXi : Section5.Percolation.IsPathFrom (m - n).toNat Xi) :
    (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤ ((Xi.toFinset.filter Good).card : ℝ) := by
  let hqdec : DecidablePred fun z : Section5.Percolation.Site d =>
      omega ∈ Support.qEvent M Creg Cinj n (Support.rescaledLatticePoint n z) ep :=
    fun z => decidable_of_iff (Good z) (hGood z)
  by_contra hlt
  push Not at hlt
  have hfilter : Xi.toFinset.filter (fun z => omega ∈ Support.qEvent M Creg Cinj n
      (Support.rescaledLatticePoint n z) ep) = Xi.toFinset.filter Good :=
    Finset.filter_congr fun z _ => (hGood z).symm
  have hcount : ((Support.qSiteCount M Creg Cinj n ep Xi.toFinset omega : ℕ) : ℝ) <
      (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat := by
    rw [Support.qSiteCount_eq_card_filter M Creg Cinj n ep Xi.toFinset omega, hfilter]
    exact hlt
  obtain ⟨N, x, hpath, h0, hN, hlight⟩ :=
    (Section5.Percolation.exists_crossing_iff (m - n).toNat
      (fun S => ((Support.qSiteCount M Creg Cinj n ep S omega : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat)).mpr ⟨Xi, hXi, hcount⟩
  exact absurd (hcrossing N x hpath h0 hN) (not_le.mpr hlight)

/-- The threshold `(3/4) 3^k`, rounded down to a natural number. -/
private theorem natCast_natThreshold_le (k : ℕ) :
    ((3 * 3 ^ k / 4 : ℕ) : ℝ) ≤ (3 / 4 : ℝ) * (3 : ℝ) ^ k := by
  have hdiv : (3 * 3 ^ k / 4 : ℕ) * 4 ≤ 3 * 3 ^ k := Nat.div_mul_le_self _ 4
  have hdivR : ((3 * 3 ^ k / 4 : ℕ) : ℝ) * 4 ≤ 3 * (3 : ℝ) ^ k := by
    exact_mod_cast hdiv
  linarith only [hdivR]

/-- **The good-vertex count with a natural-number threshold.**  This is the
form the trace of a continuous path consumes. -/
theorem natThreshold_le_card_filter_of_isPathFrom (M : ABKModel d) (Creg Cinj : ℝ)
    (m n : ℤ) (ep : ℝ) (omega : Cutoff.CutoffSample d)
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (hGood : ∀ z, Good z ↔
      omega ∈ Support.qEvent M Creg Cinj n (Support.rescaledLatticePoint n z) ep)
    (hcrossing : ∀ (N : ℕ) (x : ℕ → Fin d → ℤ),
      Provider.Percolation.IsLatticePath x N →
      x 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
      x N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
      (3 / 4 : ℝ) * (3 : ℝ) ^ (m - n).toNat ≤
        ((Support.qSiteCount M Creg Cinj n ep
          (Section5.Percolation.pathSites N x) omega : ℕ) : ℝ))
    (Xi : List (Section5.Percolation.Site d))
    (hXi : Section5.Percolation.IsPathFrom (m - n).toNat Xi) :
    3 * 3 ^ (m - n).toNat / 4 ≤ (Xi.toFinset.filter Good).card := by
  have hreal := le_card_filter_of_isPathFrom M Creg Cinj m n ep omega Good hGood
    hcrossing Xi hXi
  have hle : ((3 * 3 ^ (m - n).toNat / 4 : ℕ) : ℝ) ≤ ((Xi.toFinset.filter Good).card : ℝ) :=
    (natCast_natThreshold_le (m - n).toNat).trans hreal
  exact_mod_cast hle

/-! ## 3. The pre-exit cube trace at a general threshold -/

private theorem head?_uniformCubeTrace {M : ℕ} (n : ℤ)
    (omega : MarkovProcess.ContinuousPath (Vec d)) (T : NNReal) :
    (uniformCubeTrace n M omega T).head? =
      some (nearestTriadicSite n (omega 0)) := by
  rw [uniformCubeTrace, cubeTrace, List.ofFn_succ]
  simp only [List.head?_cons, uniformSampleTime, Fin.val_zero,
    Nat.cast_zero, zero_mul, zero_div]

private theorem uniformSampleTime_last' {M : ℕ} (hM : 0 < M) (T : NNReal) :
    uniformSampleTime T M (Fin.last M) = T := by
  unfold uniformSampleTime
  simp only [Fin.val_last]
  have hMne : (M : NNReal) ≠ 0 := by exact_mod_cast hM.ne'
  rw [mul_div_cancel_left₀ T hMne]

private theorem getLast?_uniformCubeTrace {M : ℕ} (hM : 0 < M) (n : ℤ)
    (omega : MarkovProcess.ContinuousPath (Vec d)) (T : NNReal) :
    (uniformCubeTrace n M omega T).getLast? =
      some (nearestTriadicSite n (omega T)) := by
  rw [uniformCubeTrace, cubeTrace, List.ofFn_succ_last]
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    uniformSampleTime_last' hM]

/-- **A pre-exit cube trace with the crossing count of its scale.**  A path
starting in the closed cube `□_{n+k}` and leaving `□_{n+k+1}` in finite
positive time has a uniformly sampled scale-`n` cube trace, all of whose
vertices are visited strictly before the exit, with at least `L - 2 d` good
vertices whenever every crossing of the discrete annulus at index `k` has at
least `L` of them.  The two vertices lost are the endpoint corrections that
turn the trace into a crossing; neither of them is claimed to be visited. -/
theorem exists_preExit_goodCubeTrace (hd : 0 < d) (n : ℤ) (k L : ℕ)
    (omega : MarkovProcess.ContinuousPath (Vec d))
    (hstart : omega 0 ∈ Metric.closedBall (0 : Vec d)
      ((1 / 2 : ℝ) * (3 : ℝ) ^ (n + (k : ℤ))))
    (hpos : 0 < MarkovProcess.ContinuousPath.exitTime
      (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) omega)
    (hfin : MarkovProcess.ContinuousPath.exitTime
      (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) omega ≠ ⊤)
    (Good : Section5.Percolation.Site d → Prop) [DecidablePred Good]
    (hcross : ∀ Xi : List (Section5.Percolation.Site d),
      Section5.Percolation.IsPathFrom k Xi → L ≤ (Xi.toFinset.filter Good).card) :
    ∃ Gamma : List (Section5.Percolation.Site d),
      L - 2 * d ≤ (Gamma.toFinset.filter Good).card ∧
      ∀ z ∈ Gamma.toFinset, ∃ t : NNReal,
        ((t : NNReal) : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime
          (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) omega ∧
        omega t ∈ cubeSet (partitionCube n z) := by
  have hU : IsOpen (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) :=
    isOpen_openCubeSet _
  obtain ⟨T, hT, hexit, hnear⟩ :=
    MarkovProcess.ContinuousPath.exists_lt_exitTime_mem_frontier_dist_lt
      (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) hU omega hpos hfin
      ((3 : ℝ) ^ n) (zpow_pos (by norm_num) n)
  obtain ⟨M, hM, hbefore, hweak, hmem⟩ :=
    exists_uniformCubeTrace_lt_exitTime
      (openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) omega T hT n
  obtain ⟨a, hain, ha⟩ :=
    exists_inCube_siteDist_nearestTriadicSite_le_one n k (omega 0) hstart
  have hTin : omega T ∈ openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ))) :=
    MarkovProcess.ContinuousPath.mem_of_lt_exitTime _ omega T hT
  obtain ⟨b, hbout, hb⟩ :=
    exists_not_inCube_siteDist_nearestTriadicSite_le_one_of_frontier
      n (k + 1) hTin hexit hnear
  obtain ⟨Delta, hDelta, hvertices⟩ :=
    exists_isPathFrom_extension hweak
      (head?_uniformCubeTrace n omega T) (getLast?_uniformCubeTrace hM n omega T)
      ha hb hain hbout
  refine ⟨uniformCubeTrace n M omega T, ?_, ?_⟩
  · exact good_toFinset_card_lower_bound_of_isPathFrom_extension
      hd Good hDelta hvertices hcross
  · intro z hz
    have hzList : z ∈ uniformCubeTrace n M omega T := List.mem_toFinset.mp hz
    rw [uniformCubeTrace, cubeTrace, List.mem_ofFn] at hzList
    obtain ⟨j, hj⟩ := hzList
    exact ⟨uniformSampleTime T M j, hbefore j, by simpa only [hj] using hmem j⟩

/-! ## 4. The trace vertices, and their enumeration -/

/-- A scale-`n` cell that meets `□_{n+k+1}` is indexed by a site of the
centered cube of index `k + 1`.  The cell of a site with
`2 |z i| = 3^{k+1} + 1` already lies outside, and both sides being integers with
`3^{k+1}` odd, the strict inequality `2 |z i| < 3^{k+1}` follows by parity. -/
theorem inCube_of_mem_cubeSet_partitionCube (n : ℤ) (k : ℕ)
    {z : Section5.Percolation.Site d} {x : Vec d}
    (hz : x ∈ cubeSet (partitionCube n z))
    (hx : x ∈ openCubeSet (originCube d (n + ((k + 1 : ℕ) : ℤ)))) :
    Section5.Percolation.inCube (k + 1) z := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hpow : (3 : ℝ) ^ (n + ((k + 1 : ℕ) : ℤ)) = (3 : ℝ) ^ n * (3 : ℝ) ^ (k + 1) := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  intro i
  have hzi : ((z i : ℝ) - 1 / 2) * (3 : ℝ) ^ n ≤ x i ∧
      x i < ((z i : ℝ) + 1 / 2) * (3 : ℝ) ^ n := hz i
  have hxi := mem_openCubeSet_originCube_iff.mp hx i
  rw [hpow] at hxi
  have hupper : (z i : ℝ) < (1 / 2) * ((3 : ℝ) ^ (k + 1) + 1) := by
    have h := hzi.1.trans_lt hxi.2
    nlinarith only [h, hs]
  have hlower : -((1 / 2) * ((3 : ℝ) ^ (k + 1) + 1)) < (z i : ℝ) := by
    have h := hxi.1.trans hzi.2
    nlinarith only [h, hs]
  have habs : (2 : ℝ) * |(z i : ℝ)| < (3 : ℝ) ^ (k + 1) + 1 := by
    rcases abs_cases ((z i : ℝ)) with hcase | hcase <;> rw [hcase.1] <;>
      linarith only [hupper, hlower]
  have hcastAbs : (((z i).natAbs : ℕ) : ℝ) = |(z i : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have habsN : ((2 * (z i).natAbs : ℕ) : ℝ) < ((3 ^ (k + 1) + 1 : ℕ) : ℝ) := by
    push_cast
    rw [hcastAbs]
    exact habs
  have hlt : 2 * (z i).natAbs < 3 ^ (k + 1) + 1 := by exact_mod_cast habsN
  have hodd : 3 ^ (k + 1) % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

/-- The good sites of the centered lattice cube of index `k`. -/
def goodSites (k : ℕ) (Good : Section5.Percolation.Site d → Prop)
    [DecidablePred Good] : Finset (Section5.Percolation.Site d) :=
  (Section5.Percolation.cubeSites d k).filter Good

/-- An injective enumeration of the good sites of the centered lattice cube of
index `k`. -/
def goodSiteEnum (k : ℕ) (Good : Section5.Percolation.Site d → Prop)
    [DecidablePred Good] :
    Fin (goodSites k Good).card ↪ Section5.Percolation.Site d where
  toFun j := ((goodSites k Good).equivFin.symm j : Section5.Percolation.Site d)
  inj' := by
    intro j j' hjj
    exact (goodSites k Good).equivFin.symm.injective (Subtype.ext hjj)

/-- Every good site of the centered lattice cube of index `k` is enumerated. -/
theorem exists_goodSiteEnum_eq {k : ℕ} (Good : Section5.Percolation.Site d → Prop)
    [DecidablePred Good] {z : Section5.Percolation.Site d}
    (hz : Section5.Percolation.inCube k z) (hgood : Good z) :
    ∃ j, goodSiteEnum k Good j = z := by
  have hmem : z ∈ goodSites k Good :=
    Finset.mem_filter.mpr ⟨Section5.Percolation.mem_cubeSites_of_inCube hz, hgood⟩
  refine ⟨(goodSites k Good).equivFin ⟨z, hmem⟩, ?_⟩
  show ((goodSites k Good).equivFin.symm
    ((goodSites k Good).equivFin ⟨z, hmem⟩) : Section5.Percolation.Site d) = z
  rw [Equiv.symm_apply_apply]

end

end Algsuperdiff.Section5.Trace
