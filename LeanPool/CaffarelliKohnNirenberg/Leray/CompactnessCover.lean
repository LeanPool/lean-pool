/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compactness Cover

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open Set Metric
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Balls of one Euclidean radius about a compact set remain in an open
neighborhood of that set. -/
theorem exists_uniform_euclidean_ball_subset_open
    {K W : Set Vec3} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, CKN.euclideanBall x δ ⊆ W := by
  let K' : Set L2Vec3 := vec3Homeomorph '' K
  let W' : Set L2Vec3 := vec3Homeomorph '' W
  have hK' : IsCompact K' := hK.image vec3Homeomorph.continuous
  have hW' : IsOpen W' := vec3Homeomorph.isOpenMap W hW
  have hKW' : K' ⊆ W' := image_mono hKW
  obtain ⟨δ, hδ, hδsub⟩ := hK'.exists_cthickening_subset_open hW' hKW'
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy
  have hx' : vec3Homeomorph x ∈ K' := ⟨x, hx, rfl⟩
  have hyball : vec3Homeomorph y ∈ Metric.ball (vec3Homeomorph x) δ := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hδ] at hy
    simpa only [CKN.Foundation.Parabolic.mem_vec3Ball,
      Metric.mem_ball, vec3Homeomorph_apply, dist_eq_norm,
      ← WithLp.toLp_sub, vec3EuclideanNorm_eq_l2] using hy
  have hy' : vec3Homeomorph y ∈ W' :=
    hδsub (Metric.closedBall_subset_cthickening hx' δ
      (Metric.ball_subset_closedBall hyball))
  rcases hy' with ⟨z, hz, hzy⟩
  exact (vec3Homeomorph.injective hzy).symm ▸ hz

/-- One overlap-color count works for every radius in covers of a fixed
compact set. -/
theorem exists_uniform_finite_euclidean_ball_cover_with_bounded_overlap
    {K : Set Vec3} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ r : ℝ, 0 < r →
      ∃ s : Fin N → Set {x : Vec3 // x ∈ K},
        (∀ i, (s i).PairwiseDisjoint
          (fun x => Metric.closedBall (vec3Homeomorph x.1) r)) ∧
        ∃ t : Finset (Σ i : Fin N, {x : {x : Vec3 // x ∈ K} // x ∈ s i}),
          K ⊆ ⋃ p ∈ t, vec3Ball p.2.1.1 r := by
  classical
  obtain ⟨N, τ, hτ, hN⟩ :=
    HasBesicovitchCovering.no_satelliteConfig (α := L2Vec3)
  refine ⟨N, fun r hr => ?_⟩
  let β : Type := {x : Vec3 // x ∈ K}
  let q : Besicovitch.BallPackage β L2Vec3 := {
    c := fun x => vec3Homeomorph x.1
    r := fun _ => r
    rpos := fun _ => hr
    r_bound := r
    r_le := fun _ => le_rfl }
  obtain ⟨s, hsDisjoint, hsCover⟩ :=
    Besicovitch.exist_disjoint_covering_families hτ hN q
  let I : Type := Σ i : Fin N, {x : β // x ∈ s i}
  have hcover : K ⊆ ⋃ p : I, vec3Ball p.2.1.1 r := by
    intro x hx
    have hxrange : vec3Homeomorph x ∈ Set.range q.c := ⟨⟨x, hx⟩, rfl⟩
    rcases Set.mem_iUnion.mp (hsCover hxrange) with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyS, hxy⟩
    let p : I := ⟨i, ⟨y, hyS⟩⟩
    have hballEq : vec3Ball y.1 r =
        vec3Homeomorph ⁻¹' Metric.ball (vec3Homeomorph y.1) r := by
      ext z
      simp only [mem_preimage, mem_vec3Ball, Metric.mem_ball,
        vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
        vec3EuclideanNorm_eq_l2]
    apply Set.mem_iUnion.mpr
    refine ⟨p, ?_⟩
    rw [hballEq]
    exact hxy
  have hopen : ∀ p : I, IsOpen (vec3Ball p.2.1.1 r) := by
    intro p
    exact CKN.Foundation.Parabolic.isOpen_vec3Ball p.2.1.1 r
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun p : I => vec3Ball p.2.1.1 r) hopen hcover
  exact ⟨s, hsDisjoint, t, ht⟩


/-- A compact region has a finite equal-radius ball cover with a measurable
partition of unity and finitely many disjoint colors. -/
theorem exists_weighted_colored_finite_vec3_ball_cover
    {K : Set Vec3} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ r : ℝ, 0 < r →
    ∃ s : Fin N → Set {x : Vec3 // x ∈ K},
    ∃ t : Finset (Σ i : Fin N, {x : {x : Vec3 // x ∈ K} // x ∈ s i}),
    ∃ φ : {p : Σ i : Fin N, {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t} →
        Vec3 → ℝ,
      (∀ i, (s i).PairwiseDisjoint
        (fun x => Metric.closedBall
          (CKN.Foundation.Parabolic.vec3Homeomorph x.1) r)) ∧
      K ⊆ ⋃ p ∈ t, CKN.Foundation.Parabolic.vec3Ball p.2.1.1 r ∧
      (∀ p, Measurable (φ p)) ∧
      (∀ p y, 0 ≤ φ p y ∧ φ p y ≤ 1) ∧
      (∀ y ∈ K, ∑ p, φ p y = 1) ∧
      (∀ p y, y ∈ K → φ p y ≠ 0 → y ∈ CKN.Foundation.Parabolic.vec3Ball
        p.1.2.1.1 r) ∧
      (∀ p y, y ∉ K → φ p y = 0) ∧
      (∀ (p q : {p : Σ i : Fin N,
          {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t}),
        p ≠ q → p.1.1 = q.1.1 →
        Disjoint (CKN.Foundation.Parabolic.vec3Ball p.1.2.1.1 r) (CKN.Foundation.Parabolic.vec3Ball q.1.2.1.1 r)) := by
  classical
  obtain ⟨N, hcoverAll⟩ :=
    exists_uniform_finite_euclidean_ball_cover_with_bounded_overlap hK
  refine ⟨N, fun r hr => ?_⟩
  obtain ⟨s, hsDisjoint, t, hsCover⟩ := hcoverAll r hr
  let ι := {p : Σ i : Fin N, {x : {x : Vec3 // x ∈ K} // x ∈ s i} // p ∈ t}
  let c : ι → Vec3 := fun p => p.1.2.1.1
  have hcover : K ⊆ ⋃ p : ι, CKN.Foundation.Parabolic.vec3Ball (c p) r := by
    intro y hy
    rcases Set.mem_iUnion.mp (hsCover hy) with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hpt, hball⟩
    exact Set.mem_iUnion.mpr ⟨⟨p, hpt⟩, hball⟩
  obtain ⟨φ, hφ, hweight, hsum, hzero, hsupport⟩ :=
    CKN.Foundation.exists_measurable_weights_for_finite_vec3_ball_cover hK c hr hcover
  have hsupport' (p : ι) (y : Vec3) (hyK : y ∈ K) (hne : φ p y ≠ 0) :
      y ∈ CKN.Foundation.Parabolic.vec3Ball (c p) r := hsupport p y hyK hne
  have hballEq (a : Vec3) :
      CKN.Foundation.Parabolic.vec3Ball a r =
        CKN.Foundation.Parabolic.vec3Homeomorph ⁻¹' Metric.ball
        (CKN.Foundation.Parabolic.vec3Homeomorph a) r := by
    ext z
    simp only [Set.mem_preimage, CKN.Foundation.Parabolic.mem_vec3Ball,
      Metric.mem_ball, dist_eq_norm, CKN.Foundation.Parabolic.vec3Homeomorph_apply,
      ← WithLp.toLp_sub, CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  have hcenterEq {i j : Fin N} (hij : i = j)
      (a : {x : {x : Vec3 // x ∈ K} // x ∈ s i})
      (b : {x : {x : Vec3 // x ∈ K} // x ∈ s j}) (hab : a.1 = b.1) :
      (⟨i, a⟩ : Σ k : Fin N,
        {x : {x : Vec3 // x ∈ K} // x ∈ s k}) = ⟨j, b⟩ := by
    apply Sigma.ext hij
    apply heq_of_cast_eq
      (congrArg (fun k : Fin N => {x : {x : Vec3 // x ∈ K} // x ∈ s k}) hij)
    cases hij
    apply Subtype.ext
    exact hab
  have hmemColor {i j : Fin N} (hij : i = j)
      (b : {x : {x : Vec3 // x ∈ K} // x ∈ s j}) :
      b.1 ∈ s i := by
    cases hij
    exact b.2
  refine ⟨s, t, φ, hsDisjoint, hsCover, hφ, hweight, hsum,
    hsupport', hzero, ?_⟩
  intro p q hpq hcolor
  have hpcenter : p.1.2.1 ≠ q.1.2.1 := by
    intro heq
    apply hpq
    apply Subtype.ext
    exact hcenterEq hcolor p.1.2 q.1.2 heq
  have hqmem : q.1.2.1 ∈ s p.1.1 := by
    exact hmemColor hcolor q.1.2
  have hclosed := (hsDisjoint p.1.1).disjoint_of_ne
    p.1.2.2 hqmem hpcenter
  apply Set.disjoint_left.mpr
  intro y hy₁ hy₂
  have hy₁' : CKN.Foundation.Parabolic.vec3Homeomorph y ∈ Metric.ball
      (CKN.Foundation.Parabolic.vec3Homeomorph p.1.2.1.1) r := by
    have h := hy₁
    rw [hballEq] at h
    simpa only [Set.mem_preimage] using h
  have hy₂' : CKN.Foundation.Parabolic.vec3Homeomorph y ∈ Metric.ball
      (CKN.Foundation.Parabolic.vec3Homeomorph q.1.2.1.1) r := by
    have h := hy₂
    rw [hballEq] at h
    simpa only [Set.mem_preimage] using h
  exact hclosed.le_bot ⟨Metric.ball_subset_closedBall hy₁',
    Metric.ball_subset_closedBall hy₂'⟩



end CKN.Leray
