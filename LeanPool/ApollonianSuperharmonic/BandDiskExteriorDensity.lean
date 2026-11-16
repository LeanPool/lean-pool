/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingExterior
public import LeanPool.ApollonianSuperharmonic.BandOrientedGapRefinementExists
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: BandDiskExteriorDensity]

/-!
# BandDiskExteriorDensity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandDiskExteriorDensity (z : Complex) (hz : BandPackingExterior z)
    (eps : Real) (heps : 0 < eps) :
    ∃ C : BandCircle,
      (BandCircleEuclideanData C).radius < eps ∧
      dist z (BandCircleEuclideanData C).center < eps := by
-- BODY
  obtain ⟨R⟩ := BandOrientedGapRefinementExists
  obtain ⟨a, side, hzroot⟩ := R.root_cover z hz
  let chooseChild : ∀ (l : List (Fin 3)), z ∈ R.gap (a, side, l) →
      {b : Fin 3 // z ∈ R.gap (a, side, l ++ [b])} :=
    fun l hl => by
      have existence : ∃ b : Fin 3, z ∈ R.gap (a, side, l ++ [b]) := by
        have hsplit : z ∈ Metric.closedBall
              (BandCircleEuclideanData (R.circle (a, side, l))).center
              (BandCircleEuclideanData (R.circle (a, side, l))).radius ∨
            z ∈ ⋃ b : Fin 3, R.gap (a, side, l ++ [b]) := by
          have decomposition := congrArg (fun s : Set Complex => z ∈ s)
            (R.exact_three_residual (a, side, l))
          have normalized : (z ∈ R.gap (a, side, l)) =
              (z ∈ Metric.closedBall
                (BandCircleEuclideanData (R.circle (a, side, l))).center
                (BandCircleEuclideanData (R.circle (a, side, l))).radius ∨
                z ∈ ⋃ b : Fin 3, R.gap (a, side, l ++ [b])) := by
            simpa only [Set.mem_union] using decomposition
          exact normalized ▸ hl
        rcases hsplit with hball | hres
        · have hle : dist z (BandCircleEuclideanData (R.circle (a, side, l))).center ≤
              (BandCircleEuclideanData (R.circle (a, side, l))).radius := by
            simpa [Metric.mem_closedBall] using hball
          have hge := hz (R.circle (a, side, l))
          have heq : dist z (BandCircleEuclideanData (R.circle (a, side, l))).center =
              (BandCircleEuclideanData (R.circle (a, side, l))).radius := le_antisymm hle hge
          have hs : z ∈ Metric.sphere
              (BandCircleEuclideanData (R.circle (a, side, l))).center
              (BandCircleEuclideanData (R.circle (a, side, l))).radius := by
            change dist z (BandCircleEuclideanData (R.circle (a, side, l))).center =
              (BandCircleEuclideanData (R.circle (a, side, l))).radius
            exact heq
          have hu := R.inserted_boundary_covered (a, side, l) hs
          rcases Set.mem_iUnion.1 hu with ⟨b, hb⟩
          exact ⟨b, hb⟩
        · rcases Set.mem_iUnion.1 hres with ⟨b, hb⟩
          exact ⟨b, hb⟩
      exact ⟨Classical.choose existence, Classical.choose_spec existence⟩
  let step : {l : List (Fin 3) // z ∈ R.gap (a, side, l)} →
      {l : List (Fin 3) // z ∈ R.gap (a, side, l)} := fun previous =>
    let child := chooseChild previous.1 previous.2
    ⟨previous.1 ++ [child.1], child.2⟩
  let path : Nat → {l : List (Fin 3) // z ∈ R.gap (a, side, l)} :=
    Nat.rec ⟨[], hzroot⟩ (fun _ previous => step previous)
  let branch : Nat → Fin 3 := fun n =>
    (chooseChild (path n).1 (path n).2).1
  have hpath : ∀ n, (path n).1 = (List.range n).map branch := by
    intro n
    induction n with
    | zero => simp [path]
    | succ n ih =>
      change (path n).1 ++ [branch n] = (List.range (n + 1)).map branch
      rw [ih]
      rw [List.range_succ, List.map_append]
      rfl
  have hshrink := R.branch_shrinks a side branch
  have hdiam : ∀ᶠ n in Filter.atTop,
      Metric.diam (R.gap (a, side, (List.range n).map branch)) < eps := by
    filter_upwards [Metric.tendsto_nhds.1 hshrink.1 eps heps] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg] using hn
  have hradius : ∀ᶠ n in Filter.atTop,
      (BandCircleEuclideanData (R.circle (a, side, (List.range n).map branch))).radius < eps := by
    filter_upwards [Metric.tendsto_nhds.1 hshrink.2 eps heps] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_pos
      (BandCircleEuclideanData (R.circle (a, side, (List.range n).map branch))).radius_pos] using hn
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (hdiam.and hradius)
  let l := (List.range n).map branch
  let C := R.circle (a, side, l)
  have hzmem : z ∈ R.gap (a, side, l) := by
    dsimp [l]
    rw [← hpath n]
    exact (path n).2
  have rootBound : Bornology.IsBounded (R.gap (a, side, [])) := by
    apply Metric.isBounded_iff.2
    refine ⟨3, ?_⟩
    intro x hx y hy
    rcases side with _ | _
    · rw [R.root_left a] at hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      rw [Complex.dist_eq_re_im]
      apply Real.sqrt_le_iff.2
      constructor
      · positivity
      · nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]
    · rw [R.root_right a] at hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      rw [Complex.dist_eq_re_im]
      apply Real.sqrt_le_iff.2
      constructor
      · positivity
      · nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]
  have hcontained : ∀ (u v : List (Fin 3)),
      R.gap (a, side, u ++ v) ⊆ R.gap (a, side, u) := by
    intro u v
    induction v generalizing u with
    | nil => intro x hx; simpa using hx
    | cons b v ih =>
      intro x hx
      have hx' : x ∈ R.gap (a, side, u ++ [b] ++ v) := by
        simpa [List.append_assoc] using hx
      exact R.child_contained (a, side, u) b (ih (u ++ [b]) hx')
  have hbounded : Bornology.IsBounded (R.gap (a, side, l)) := by
    rcases rootBound with ⟨bound, root_bound⟩
    refine ⟨bound, ?_⟩
    intro x hx y hy
    have hx0 : x ∈ R.gap (a, side, l) := by simpa using hx
    have hy0 : y ∈ R.gap (a, side, l) := by simpa using hy
    have hx1 : x ∈ (R.gap (a, side, []))ᶜᶜ := by simpa using hcontained [] l hx0
    have hy1 : y ∈ (R.gap (a, side, []))ᶜᶜ := by simpa using hcontained [] l hy0
    exact root_bound hx1 hy1
  have hcenter : (BandCircleEuclideanData C).center ∈ R.gap (a, side, l) := by
    have hball : (BandCircleEuclideanData C).center ∈
        Metric.closedBall (BandCircleEuclideanData C).center
          (BandCircleEuclideanData C).radius :=
      Metric.mem_closedBall_self (BandCircleEuclideanData C).radius_pos.le
    have normalized : R.gap (a, side, l) =
        Metric.closedBall (BandCircleEuclideanData C).center
          (BandCircleEuclideanData C).radius ∪
        ⋃ b : Fin 3, R.gap (a, side, l ++ [b]) := by
      simpa [C] using R.exact_three_residual (a, side, l)
    rw [normalized]
    exact Or.inl hball
  have hdist : dist z (BandCircleEuclideanData C).center ≤
      Metric.diam (R.gap (a, side, l)) := by
    exact Metric.dist_le_diam_of_mem hbounded hzmem hcenter
  refine ⟨C, ?_, ?_⟩
  · exact hn.2
  · exact lt_of_le_of_lt hdist hn.1

end ApollonianSuperharmonic

end
