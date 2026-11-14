/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4984T1ContactDiameter
public import LeanPool.ApollonianSuperharmonic.P4828T1HistoryRealization

-- [TABLET NODE: P4984T1BranchDecay]

/-!
# P4984T1BranchDecay

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4984T1BranchDecay (a : GaussianInt) (side : Bool)
    (branch : Nat → Fin 3) :
    let q (n : Nat) := P4828T1Evaluate a side ((List.range n).map branch)
    let c (n : Nat) : Int := (q n 0).1
    StrictMono c ∧
    (∀ n : Nat, c 0 + (n : Int) ≤ c n) ∧
    Filter.Tendsto
      (fun n ↦ Metric.diam (P4984T1ClosedGap (2 * (a.re : Real)) (q n)))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n ↦ 1 / (c n : Real)) Filter.atTop (nhds 0) := by
-- BODY
  let q (n : Nat) := P4828T1Evaluate a side ((List.range n).map branch)
  let c (n : Nat) : Int := (q n 0).1
  have hq (n : Nat) := P4828T1HistoryRealization a side ((List.range n).map branch)
  have hp (n : Nat) : ProperBandQuadruple (q n) := (hq n).1.1
  have hnext (n : Nat) : q (n + 1) =
      P4828T1Step (P4828T1Rotate (q n) (branch n)) := by
    simp [q, List.range_succ, P4828T1Evaluate, List.foldl_append]
  have hstep (n : Nat) : c n < c (n + 1) := by
    have hh := (hp (n + 1)).2 (0 : Fin 3)
    have hfirst : q (n + 1) (Fin.succ 0) = q n 0 := by
      rw [hnext]; rfl
    rw [hfirst] at hh
    exact hh
  have hgrow (n : Nat) : c 0 + (n : Int) ≤ c n := by
    induction n with
    | zero => simp
    | succ n ih => have := hstep n; push_cast; omega
  have hpos (n : Nat) : 0 < c n := (ProperBandCurvatureStructure _ (hp n)).1
  have hc : Filter.Tendsto (fun n ↦ (c n : Real)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop (R := Real))
    have hh := hgrow n
    have h0 := hpos 0
    have hh' : (n : Int) ≤ c n := by omega
    exact_mod_cast hh'
  have hr : Filter.Tendsto (fun n ↦ 1 / (c n : Real))
      Filter.atTop (nhds 0) := hc.const_div_atTop 1
  have hbound (n : Nat) :
      Metric.diam (P4984T1ClosedGap (2 * (a.re : Real)) (q n)) ≤
        6 * Real.sqrt (1 / (c n : Real)) :=
    P4984T1ContactDiameter _ _ (hp n) (hq n).1.2.1 (hq n).1.2.2
  have hlim : Filter.Tendsto (fun n ↦ 6 * Real.sqrt (1 / (c n : Real)))
      Filter.atTop (nhds 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hr).const_mul 6
  exact ⟨strictMono_nat_of_lt_succ hstep, hgrow,
    squeeze_zero (fun _ => Metric.diam_nonneg) hbound hlim, hr⟩

end ApollonianSuperharmonic

end
