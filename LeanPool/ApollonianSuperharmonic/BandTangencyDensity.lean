/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandDescartesGapSubdivision
public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandCircleClassification
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity
public import LeanPool.ApollonianSuperharmonic.BandOrientedGapRefinementExists
public import LeanPool.ApollonianSuperharmonic.BandOrientedGapRefinement

-- [TABLET NODE: BandTangencyDensity]

/-!
# BandTangencyDensity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandTangencyDensity (C : BandCircle) (p : Complex)
    (hp : dist p (BandCircleEuclideanData C).center =
      (BandCircleEuclideanData C).radius) (eps : Real) (heps : 0 < eps) :
    ∃ D : BandCircle, D ≠ C ∧
      (BandCircleEuclideanData D).radius < eps ∧
      ∃ t : Complex,
        dist t p < eps ∧
        dist t (BandCircleEuclideanData C).center =
          (BandCircleEuclideanData C).radius ∧
        dist t (BandCircleEuclideanData D).center =
          (BandCircleEuclideanData D).radius ∧
        dist (BandCircleEuclideanData C).center
            (BandCircleEuclideanData D).center =
          (BandCircleEuclideanData C).radius +
            (BandCircleEuclideanData D).radius := by
-- BODY
  obtain ⟨R⟩ := BandOrientedGapRefinementExists
  obtain ⟨seeds, hcover, hseeds⟩ := R.initial_incident_arcs C
  have hpSphere : p ∈ Metric.sphere (BandCircleEuclideanData C).center
      (BandCircleEuclideanData C).radius := by
    exact hp
  have hpCover : p ∈ ⋃ ι ∈ seeds, R.gap ι ∩
      Metric.sphere (BandCircleEuclideanData C).center
        (BandCircleEuclideanData C).radius := by
    rw [← hcover]
    exact hpSphere
  obtain ⟨ι₀, hp₀⟩ := Set.mem_iUnion.1 hpCover
  obtain ⟨hι₀, hp₀⟩ := Set.mem_iUnion.1 hp₀
  obtain ⟨hι₀s, hp₀s, hn₀, hparent₀⟩ := hseeds ι₀ hι₀
  let State := {ι : GaussianInt × Bool × List (Fin 3) //
    p ∈ R.gap ι ∩ Metric.sphere (BandCircleEuclideanData C).center
      (BandCircleEuclideanData C).radius ∧
    ∃ j : Fin 3, R.presentation ι j.succ = C.1.1}
  let digit : State → Fin 3 := fun s =>
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec (R.incident_arc_step C s.1 p s.2.2 s.2.1)))
  let next : State → State := fun s => by
    have hs := R.incident_arc_step C s.1 p s.2.2 s.2.1
    have h₁ := Classical.choose_spec hs
    have h₂ := Classical.choose_spec h₁
    have h₃ := Classical.choose_spec h₂
    have hb : (Classical.choose h₂) ∈ Classical.choose h₁ := h₃.2.1
    have hiff := h₃.2.2.1
    have hpnext := h₃.2.2.2.2.2.1
    refine ⟨(s.1.1, s.1.2.1, s.1.2.2 ++ [digit s]), hpnext, ?_⟩
    exact (hiff (digit s)).mp (by simpa [digit] using hb)
  have digit_spec : ∀ s : State,
      ∃ t : Complex, ∃ keep : Finset (Fin 3),
        ∃ b : Fin 3, b = digit s ∧ keep.card = 2 ∧ b ∈ keep ∧
          (∀ c : Fin 3, c ∈ keep ↔
            ∃ j : Fin 3,
              R.presentation (s.1.1, s.1.2.1, s.1.2.2 ++ [c]) j.succ = C.1.1) ∧
          (s.1.1, s.1.2.1, s.1.2.2 ++ [b]) = (next s).1 ∧
          t ∈ R.gap (next s).1 ∩
            Metric.sphere (BandCircleEuclideanData C).center
              (BandCircleEuclideanData C).radius ∧
          p ∈ R.gap (next s).1 ∩
            Metric.sphere (BandCircleEuclideanData C).center
              (BandCircleEuclideanData C).radius ∧
          R.circle s.1 ≠ C ∧
          (BandCircleEuclideanData (R.circle s.1)).radius <
            (BandCircleEuclideanData C).radius ∧
          dist t (BandCircleEuclideanData C).center =
            (BandCircleEuclideanData C).radius ∧
          dist t (BandCircleEuclideanData (R.circle s.1)).center =
            (BandCircleEuclideanData (R.circle s.1)).radius ∧
          dist (BandCircleEuclideanData C).center
              (BandCircleEuclideanData (R.circle s.1)).center =
            (BandCircleEuclideanData C).radius +
              (BandCircleEuclideanData (R.circle s.1)).radius := by
    intro s
    have hs := R.incident_arc_step C s.1 p s.2.2 s.2.1
    have h₁ := Classical.choose_spec hs
    have h₂ := Classical.choose_spec h₁
    have h₃ := Classical.choose_spec h₂
    rcases h₃ with ⟨hcard, hb, hiff, hsplit, hforall, hpnext, hneq,
      hrsmall, htc, htd, hcent⟩
    have htchild := hforall (digit s) (by simpa [digit] using hb) |>.2.2
    refine ⟨Classical.choose hs, Classical.choose h₁, digit s, rfl, hcard,
      by simpa [digit] using hb, hiff, rfl, htchild, hpnext, hneq, hrsmall,
      htc, htd, hcent⟩
  let s₀ : State := ⟨ι₀, hp₀, hparent₀⟩
  let path : Nat → State := Nat.rec s₀ (fun _ s => next s)
  have path_shape : ∀ n, (path n).1 =
      (ι₀.1, ι₀.2.1, ι₀.2.2 ++ (List.range n).map (fun k => digit (path k))) := by
    intro n
    induction n with
    | zero => simp [path, s₀]
    | succ n ih =>
      change (next (path n)).1 =
        (ι₀.1, ι₀.2.1, ι₀.2.2 ++
          (List.range (n + 1)).map (fun k => digit (path k)))
      change ((path n).1.1, (path n).1.2.1,
        (path n).1.2.2 ++ [digit (path n)]) = _
      rw [ih, List.range_succ, List.map_append]
      simp
  let branch : Nat → Fin 3 := fun n =>
    if h : n < ι₀.2.2.length then ι₀.2.2.get ⟨n, h⟩
    else digit (path (n - ι₀.2.2.length))
  have prefix_map : (List.range ι₀.2.2.length).map branch = ι₀.2.2 := by
    have range_fin : (List.finRange ι₀.2.2.length).map Fin.val =
        List.range ι₀.2.2.length := by
      induction ι₀.2.2.length with
      | zero => simp
      | succ k ih =>
          rw [List.finRange_succ, List.range_succ_eq_map]
          simp only [List.map_cons, List.map_map]
          rw [← ih]
          simp only [List.map_map]
          congr 1
    rw [← range_fin, List.map_map]
    change List.map (fun i => branch i.val) (List.finRange ι₀.2.2.length) = _
    rw [show (fun (i : Fin ι₀.2.2.length) => branch i.val) =
        ι₀.2.2.get by
      funext i
      simp [branch, i.isLt]]
    exact List.map_get_finRange ι₀.2.2
  have tail_map (n : Nat) :
      (List.range (ι₀.2.2.length + n)).map branch =
        ι₀.2.2 ++ (List.range n).map (fun k => digit (path k)) := by
    rw [List.range_add, List.map_append, prefix_map]
    congr 1
    simp [branch]
  have hshrink := R.branch_shrinks ι₀.1 ι₀.2.1 branch
  have hdiam : ∀ᶠ n in Filter.atTop,
      Metric.diam (R.gap (ι₀.1, ι₀.2.1,
        (List.range n).map branch)) < eps := by
    filter_upwards [Metric.tendsto_nhds.1 hshrink.1 eps heps] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg] using hn
  have hradius : ∀ᶠ n in Filter.atTop,
      (BandCircleEuclideanData (R.circle (ι₀.1, ι₀.2.1,
        (List.range n).map branch))).radius < eps := by
    filter_upwards [Metric.tendsto_nhds.1 hshrink.2 eps heps] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_pos
      (BandCircleEuclideanData (R.circle (ι₀.1, ι₀.2.1,
        (List.range n).map branch))).radius_pos] using hn
  have hlarge : ∀ᶠ m in Filter.atTop, ι₀.2.2.length ≤ m :=
    Filter.eventually_ge_atTop _
  obtain ⟨m, hm⟩ := Filter.Eventually.exists ((hdiam.and hradius).and hlarge)
  let n := m - ι₀.2.2.length
  have hmn : ι₀.2.2.length + n = m := by
    dsimp [n]
    exact Nat.add_sub_of_le hm.2
  have hn : Metric.diam (R.gap (ι₀.1, ι₀.2.1,
      ι₀.2.2 ++ (List.range n).map (fun k => digit (path k)))) < eps ∧
      (BandCircleEuclideanData (R.circle (ι₀.1, ι₀.2.1,
        ι₀.2.2 ++ (List.range n).map (fun k => digit (path k))))).radius < eps := by
    have hmn' := hmn
    rw [← hmn', tail_map] at hm
    exact ⟨hm.1.1, hm.1.2⟩
  have hshape := path_shape n
  let D := R.circle (path n).1
  obtain ⟨t, keep, b, hbigit, hcard, hb, hiff, hnext, htarc, hpnext,
    hneq, hrsmall, htc, htd, hcent⟩ := digit_spec (path n)
  have hpathmem : p ∈ R.gap (path n).1 := (path n).2.1.1
  have hcontained : ∀ (u v : List (Fin 3)),
      R.gap (ι₀.1, ι₀.2.1, u ++ v) ⊆ R.gap (ι₀.1, ι₀.2.1, u) := by
    intro u v
    induction v generalizing u with
    | nil => intro x hx; simpa using hx
    | cons b v ih =>
      intro x hx
      have hx' : x ∈ R.gap (ι₀.1, ι₀.2.1, u ++ [b] ++ v) := by
        simpa [List.append_assoc] using hx
      exact R.child_contained (ι₀.1, ι₀.2.1, u) b (ih (u ++ [b]) hx')
  have rootBound : Bornology.IsBounded
      (R.gap (ι₀.1, ι₀.2.1, [])) := by
    apply Metric.isBounded_iff.2
    refine ⟨3, ?_⟩
    intro x hx y hy
    by_cases hside : ι₀.2.1 = false
    · rw [hside, R.root_left ι₀.1] at hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      rw [Complex.dist_eq_re_im]
      apply Real.sqrt_le_iff.2
      constructor
      · positivity
      · nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]
    · have hside' : ι₀.2.1 = true := Bool.eq_true_of_not_eq_false hside
      rw [hside', R.root_right ι₀.1] at hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      rw [Complex.dist_eq_re_im]
      apply Real.sqrt_le_iff.2
      constructor
      · positivity
      · nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]
  have hdiamdist : dist p t ≤ Metric.diam (R.gap (path n).1) := by
    have hbounded : Bornology.IsBounded (R.gap (path n).1) := by
      rw [hshape]
      exact rootBound.subset (hcontained [] _)
    have htchild : t ∈ R.gap
        ((path n).1.1, (path n).1.2.1, (path n).1.2.2 ++ [digit (path n)]) := by
      have heq : ((path n).1.1, (path n).1.2.1,
          (path n).1.2.2 ++ [digit (path n)]) = (next (path n)).1 := by
        simpa [hbigit] using hnext
      rw [heq]
      simpa [hbigit] using htarc.1
    have htparent : t ∈ R.gap (path n).1 := by
      exact R.child_contained (path n).1 (digit (path n)) htchild
    apply Metric.dist_le_diam_of_mem hbounded hpathmem
    exact htparent
  refine ⟨D, ?_, ?_, ?_⟩
  · simpa [D] using hneq
  · simpa [D, hshape] using hn.2
  · refine ⟨t, ?_, htc, htd, hcent⟩
    have hn' : Metric.diam (R.gap (path n).1) < eps := by
      rw [hshape]
      exact hn.1
    simpa [dist_comm] using lt_of_le_of_lt hdiamdist hn'

end ApollonianSuperharmonic

end
