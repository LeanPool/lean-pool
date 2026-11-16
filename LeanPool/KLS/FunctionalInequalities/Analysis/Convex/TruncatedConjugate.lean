/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Coercivity
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Extension
public import Mathlib.Analysis.Convex.Extrema

/-! # TruncatedConjugate in convex Monge--Ampere analysis

Caffarelli contact geometry supporting Letwin arXiv:2607.24164v1
Lemma 2.2 through BB arXiv:1207.6128v1 Theorem 2.24(ii).
The declarations retain their given-source hypotheses; domain contact
rigidity and moment-source regularity have separate consumers.
-/

@[expose] public section

noncomputable section

section TruncatedConjugate

open Set Metric
open scoped RealInnerProductSpace

/-! The truncated conjugate used to localize the contact-set argument. -/

namespace FunctionalInequalities.Analysis

/-- The **ball-truncated conjugate** `p ↦ sup_{‖x‖ ≤ M} (⟪p, x⟫ − u x)`: a globally finite convex
function that agrees with the Legendre
transform of `u` wherever the supremum is attained inside the ball. -/
def truncatedConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (M : ℝ) (p : E) : ℝ :=
  sSup ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M)

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The supremum is attained and dominates every value on the ball. -/
theorem exists_truncatedConjugate_eq {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (p : E) :
    (∃ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x) ∧
      ∀ x ∈ closedBall (0 : E) M, ⟪p, x⟫ - u x ≤ truncatedConjugate u M p := by
  have hc :
      IsCompact ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M) :=
    (isCompact_closedBall (0 : E) M).image
      ((continuous_const.inner continuous_id).sub hu)
  have hn :
      ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M).Nonempty :=
    ⟨⟪p, 0⟫ - u 0, ⟨0, mem_closedBall_self hM, rfl⟩⟩
  constructor
  · obtain ⟨x, hx, heq⟩ := hc.sSup_mem hn
    exact ⟨x, hx, heq.symm⟩
  · intro x hx
    exact le_csSup hc.bddAbove ⟨x, hx, rfl⟩

/-- The truncated conjugate is convex. -/
theorem convexOn_truncatedConjugate {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
    ConvexOn ℝ univ (truncatedConjugate u M) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  obtain ⟨x, hx, heq⟩ :=
    (exists_truncatedConjugate_eq hu hM (a • p + b • q)).1
  have hpx := (exists_truncatedConjugate_eq hu hM p).2 x hx
  have hqx := (exists_truncatedConjugate_eq hu hM q).2 x hx
  change truncatedConjugate u M (a • p + b • q) ≤
    a * truncatedConjugate u M p + b * truncatedConjugate u M q
  rw [heq]
  calc
    ⟪a • p + b • q, x⟫ - u x =
        a * (⟪p, x⟫ - u x) + b * (⟪q, x⟫ - u x) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith [congrArg (fun t : ℝ => t * u x) hab]
    _ ≤ a * truncatedConjugate u M p + b * truncatedConjugate u M q :=
      add_le_add (mul_le_mul_of_nonneg_left hpx ha)
        (mul_le_mul_of_nonneg_left hqx hb)

/-- **Zeros of the centred truncated conjugate are the subgradients**: for convex `u` and
`‖xc‖ < M`, `f p := truncatedConjugate u M p − ⟪p, xc⟫ + u xc` is nonnegative, vanishes exactly at
the
subgradients of `u` at `xc`, and has compact sublevel sets. -/
theorem truncatedConjugate_centered_spec {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {M : ℝ}
    {xc : E} (hxc : ‖xc‖ < M) :
    (∀ p, 0 ≤ truncatedConjugate u M p - ⟪p, xc⟫ + u xc) ∧
      (∀ p, truncatedConjugate u M p - ⟪p, xc⟫ + u xc = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y) ∧
        ∀ R : ℝ, IsCompact {p | truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R} := by
  have hu : Continuous u := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  have hM : 0 ≤ M := (norm_nonneg xc).trans hxc.le
  have hxc_mem : xc ∈ closedBall (0 : E) M := mem_closedBall_zero_iff.mpr hxc.le
  have hnonneg (p : E) : 0 ≤ truncatedConjugate u M p - ⟪p, xc⟫ + u xc := by
    have h := (exists_truncatedConjugate_eq hu hM p).2 xc hxc_mem
    linarith
  refine ⟨hnonneg, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      have htilt : ConvexOn ℝ univ (fun x => u x - ⟪p, x⟫) := by
        refine ⟨convex_univ, ?_⟩
        intro x hx y hy a b ha hb hab
        have hc := hconv.2 hx hy ha hb hab
        change u (a • x + b • y) - ⟪p, a • x + b • y⟫ ≤ a * (u x - ⟪p, x⟫) + b * (u y - ⟪p, y⟫)
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        change u (a • x + b • y) ≤ a * u x + b * u y at hc
        linarith
      have hmin : IsMinOn (fun x => u x - ⟪p, x⟫) (closedBall (0 : E) M) xc := by
        intro x hx
        have h := (exists_truncatedConjugate_eq hu hM p).2 x hx
        change u xc - ⟪p, xc⟫ ≤ u x - ⟪p, x⟫
        linarith
      have hnbhd : closedBall (0 : E) M ∈ nhds xc :=
        Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxc))
          ball_subset_closedBall
      have hglobal := IsMinOn.of_isLocalMin_of_convex_univ (hmin.isLocalMin hnbhd) htilt
      intro y
      have hy := hglobal y
      rw [inner_sub_right]
      linarith
    · intro hp
      obtain ⟨x, hx, heq⟩ := (exists_truncatedConjugate_eq hu hM p).1
      have hs := hp x
      rw [inner_sub_right] at hs
      have hn := hnonneg p
      rw [heq] at hn ⊢
      linarith
  · intro R
    have htc : Continuous (truncatedConjugate u M) :=
      continuousOn_univ.mp
        (ConvexOn.continuousOn isOpen_univ (convexOn_truncatedConjugate hu hM))
    have hf : Continuous (fun p => truncatedConjugate u M p - ⟪p, xc⟫ + u xc) :=
      (htc.sub (continuous_id.inner continuous_const)).add continuous_const
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hu.continuousOn
    have hd : 0 < M - ‖xc‖ := sub_pos.mpr hxc
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hf continuous_const)
    apply (Metric.isBounded_iff_subset_closedBall (0 : E)).2
    refine ⟨max 0 ((R + C - u xc) / (M - ‖xc‖)), ?_⟩
    intro p hp
    change truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R at hp
    apply mem_closedBall_zero_iff.mpr
    by_cases hp0 : p = 0
    · subst p
      rw [norm_zero]
      exact le_max_left _ _
    · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
      let x : E := xc + ((M - ‖xc‖) / ‖p‖) • p
      have hnorm : ‖((M - ‖xc‖) / ‖p‖) • p‖ = M - ‖xc‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hd.le (norm_nonneg p)),
          div_mul_cancel₀ _ hn]
      have hx : x ∈ closedBall (0 : E) M := by
        apply mem_closedBall_zero_iff.mpr
        calc
          ‖x‖ ≤ ‖xc‖ + ‖((M - ‖xc‖) / ‖p‖) • p‖ := norm_add_le _ _
          _ = M := by rw [hnorm]; ring
      have hinner : ⟪p, x⟫ = ⟪p, xc⟫ + (M - ‖xc‖) * ‖p‖ := by
        dsimp only [x]
        rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        congr 1
        field_simp
      have hux : u x ≤ C := by
        have hc := hC x hx
        rw [Real.norm_eq_abs] at hc
        exact (le_abs_self (u x)).trans hc
      have hdom := (exists_truncatedConjugate_eq hu hM p).2 x hx
      rw [hinner] at hdom
      calc
        ‖p‖ ≤ (R + C - u xc) / (M - ‖xc‖) := by
          apply (le_div_iff₀ hd).2
          nlinarith
        _ ≤ max 0 ((R + C - u xc) / (M - ‖xc‖)) := le_max_right _ _

end FiniteDimensional

end FunctionalInequalities.Analysis

end TruncatedConjugate

section TruncatedConjugateSubgradients

open Set Metric
open scoped RealInnerProductSpace Topology

/-! Subgradients and subgradient images of the truncated conjugate. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma isClosed_truncatedConjugate_contact_slopes [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) {C : Set E} (hC : IsClosed C) :
    IsClosed {p : E | ∃ x ∈ closedBall (0 : E) M,
      x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
  let B := closedBall (0 : E) M
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 M)
  have hT : Continuous (truncatedConjugate u M) :=
    continuousOn_univ.mp ((convexOn_truncatedConjugate hu hM).continuousOn isOpen_univ)
  let D : Set (B × E) :=
    {q | (q.1 : E) ∈ C ∧ truncatedConjugate u M q.2 = ⟪q.2, (q.1 : E)⟫ - u q.1}
  have hD : IsClosed D :=
    (hC.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isClosed_eq (hT.comp continuous_snd)
        ((continuous_snd.inner (continuous_subtype_val.comp continuous_fst)).sub
          (hu.comp (continuous_subtype_val.comp continuous_fst))))
  have he : Prod.snd '' D =
      {p : E | ∃ x ∈ closedBall (0 : E) M,
        x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hx, rfl⟩
      exact ⟨x, x.property, hx⟩
    · rintro ⟨x, hx, hc, he⟩
      exact ⟨(⟨x, hx⟩, p), ⟨hc, he⟩, rfl⟩
  rw [← he]
  exact isClosedMap_snd_of_compactSpace D hD

private lemma isMinOn_sub_inner_of_support {u : E → ℝ} {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    IsMinOn (fun y => u y - ⟪p, y⟫) univ x := by
  intro y _
  have h := hp y
  rw [inner_sub_right] at h
  dsimp
  linarith

/-- A strictly convex function has at most one point supported by a given slope `p`. -/
theorem eq_of_strictConvexOn_of_support {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {x z p : E}
    (hx : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (hz : ∀ y, u z + ⟪p, y - z⟫ ≤ u y) : x = z := by
  exact (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
    (isMinOn_sub_inner_of_support hx) (isMinOn_sub_inner_of_support hz) (mem_univ x) (mem_univ z)

private lemma truncatedConjugate_eq_of_support {u : E → ℝ} {M : ℝ} {x p : E}
    (hx : x ∈ closedBall (0 : E) M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    truncatedConjugate u M p = ⟪p, x⟫ - u x := by
  have hb : ∀ y, ⟪p, y⟫ - u y ≤ ⟪p, x⟫ - u x := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h
    linarith
  apply le_antisymm
  · exact csSup_le ⟨_, ⟨x, hx, rfl⟩⟩ (by
      rintro _ ⟨y, _, rfl⟩
      exact hb y)
  · exact le_csSup ⟨_, by
      rintro _ ⟨y, _, rfl⟩
      exact hb y⟩ ⟨x, hx, rfl⟩

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private lemma support_of_truncatedConjugate_contact {u : E → ℝ}
    (hu : Continuous u) (hconv : ConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M)
    {x p : E} (hx : ‖x‖ < M)
    (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x) :
    ∀ y, u x + ⟪p, y - x⟫ ≤ u y := by
  let f : E → ℝ := fun z => u z - ⟪p, z⟫
  have hf : ConvexOn ℝ univ f :=
    hconv.sub ((innerₗ E p).concaveOn convex_univ)
  have hmin : ∀ z ∈ ball (0 : E) M, f x ≤ f z := by
    intro z hz
    have h := (exists_truncatedConjugate_eq hu hM p).2 z
      (closedBall_subset_closedBall (le_refl M)
        (ball_subset_closedBall hz))
    rw [heq] at h
    dsimp [f]
    linarith
  intro y
  have hpre : (AffineMap.lineMap x y) ⁻¹' ball (0 : E) M ∈ 𝓝 (0 : ℝ) :=
    (AffineMap.lineMap_continuous (p := x) (q := y)).continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (by
        rw [AffineMap.lineMap_apply_zero]
        exact mem_ball_zero_iff.mpr hx))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hz : AffineMap.lineMap x y t ∈ ball (0 : E) M := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htε
  have hxz := hmin _ hz
  have hzy := hf.le_right_of_left_le (mem_univ x) (mem_univ y)
    (lineMap_mem_openSegment ℝ x y ⟨ht, ht1⟩) hxz
  have hxy : f x ≤ f y := hxz.trans hzy
  dsimp [f] at hxy
  rw [inner_sub_right]
  linarith

/-- The set of slopes whose ball maximisers all lie in the open ball is open. -/
theorem isOpen_setOf_truncatedConjugate_maximizer_lt {u : E → ℝ} (hu : Continuous u) {M : ℝ}
    (hM : 0 ≤ M) :
    IsOpen {p : E | ∀ x ∈ closedBall (0 : E) M,
      truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} := by
  classical
  have hc : IsClosed {x : E | M ≤ ‖x‖} :=
    isClosed_le continuous_const continuous_norm
  have he :
      {p : E | ∀ x ∈ closedBall (0 : E) M,
        truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} =
      {p : E | ∃ x ∈ closedBall (0 : E) M,
        x ∈ {x : E | M ≤ ‖x‖} ∧
          truncatedConjugate u M p = ⟪p, x⟫ - u x}ᶜ := by
    ext p
    constructor
    · intro hp
      rintro ⟨x, hx, hn, heq⟩
      exact (not_lt_of_ge hn) (hp x hx heq)
    · intro hp x hx heq
      by_contra hn
      exact hp ⟨x, hx, le_of_not_gt hn, heq⟩
  rw [he]
  exact (isClosed_truncatedConjugate_contact_slopes hu hM hc).isOpen_compl

end FiniteDimensional

/--
For strictly convex `u`, a subgradient `p` at a point `x` of the open ball has `x` as its only ball
maximiser. -/
theorem eq_of_truncatedConjugate_eq_of_subgradient [FiniteDimensional ℝ E] {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} {x p : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {x' : E} (hx' : x' ∈ closedBall (0 : E) M)
    (heq : truncatedConjugate u M p = ⟪p, x'⟫ - u x') : x' = x := by
  have hxeq := truncatedConjugate_eq_of_support (mem_closedBall_zero_iff.mpr hx.le) hp
  have hp' : ∀ y, u x' + ⟪p, y - x'⟫ ≤ u y := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h ⊢
    linarith [heq, hxeq]
  exact
    (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
      (isMinOn_sub_inner_of_support hp') (isMinOn_sub_inner_of_support hp)
      ((subset_univ (closedBall (0 : E) M)) hx') (mem_univ x)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

private lemma subgradient_truncatedConjugate_eq_maximizer {u : E → ℝ}
    (hu : Continuous u) (hstrict : StrictConvexOn ℝ univ u)
    {M : ℝ} (hM : 0 ≤ M) {p x g : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x)
    (hg : ∀ q, truncatedConjugate u M p + ⟪g, q - p⟫ ≤ truncatedConjugate u M q) :
    g = x := by
  classical
  by_contra hne
  let v := g - x
  have hv : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  have hgap : ⟪v, x⟫ < ⟪v, g⟫ := by
    have hh : ⟪v, v⟫ = ⟪v, g⟫ - ⟪v, x⟫ := by
      dsimp [v]
      rw [inner_sub_right]
    linarith
  let c : ℝ := (⟪v, x⟫ + ⟪v, g⟫) / 2
  have hxc : ⟪v, x⟫ < c := by dsimp [c]; linarith
  have hcg : c < ⟪v, g⟫ := by dsimp [c]; linarith
  let C : Set E := {z | c ≤ ⟪v, z⟫}
  let A : Set E := {q | ∃ z ∈ closedBall (0 : E) M,
    z ∈ C ∧ truncatedConjugate u M q = ⟪q, z⟫ - u z}
  have hA : IsClosed A :=
    isClosed_truncatedConjugate_contact_slopes hu hM
      (isClosed_le continuous_const (continuous_const.inner continuous_id))
  have hpA : p ∈ Aᶜ := by
    rintro ⟨z, hz, hc, hzmax⟩
    have hzx := eq_of_truncatedConjugate_eq_of_subgradient hstrict hx hp hz hzmax
    subst z
    exact (not_le_of_gt hxc) hc
  have hpath : Continuous (fun t : ℝ => p + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun t : ℝ => p + t • v) ⁻¹' Aᶜ ∈ 𝓝 (0 : ℝ) :=
    hpath.continuousAt.preimage_mem_nhds
      (hA.isOpen_compl.mem_nhds (by simpa only [zero_smul, add_zero] using hpA))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htε : t < ε := by dsimp [t]; linarith
  have hqA : p + t • v ∈ Aᶜ := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htε
  obtain ⟨z, hz, hzmax⟩ := (exists_truncatedConjugate_eq hu hM (p + t • v)).1
  have hzc : ⟪v, z⟫ < c := by
    by_contra hn
    exact hqA ⟨z, hz, le_of_not_gt hn, hzmax⟩
  have hbase := (exists_truncatedConjugate_eq hu hM p).2 z hz
  have hsub := hg (p + t • v)
  rw [hzmax, add_sub_cancel_left, inner_smul_right] at hsub
  rw [inner_add_left, real_inner_smul_left] at hsub
  have hgv : ⟪g, v⟫ = ⟪v, g⟫ := real_inner_comm v g
  have hle : t * ⟪v, g⟫ ≤ t * ⟪v, z⟫ := by
    rw [heq] at hbase hsub
    rw [hgv] at hsub
    linarith
  have hgz : ⟪v, g⟫ ≤ ⟪v, z⟫ := (mul_le_mul_iff_right₀ ht).mp hle
  linarith

/--
**Danskin identification of subgradient images**: for strictly convex continuous `u`, on a set
`S` of slopes whose ball maximisers lie in the open ball, the subgradient image of the truncated
conjugate is the
inverse subgradient image `{x | ∃ p ∈ S, p ∈ ∂u(x)}`. -/
theorem subgradientImage_truncatedConjugate_eq {u : E → ℝ} (hu : Continuous u)
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M) {S : Set E}
    (hS :
      ∀ p ∈ S, ∀ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M) :
    subgradientImage (truncatedConjugate u M) S = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
  ext g
  constructor
  · rintro ⟨p, hpS, hg⟩
    obtain ⟨x, hxB, heq⟩ := (exists_truncatedConjugate_eq hu hM p).1
    have hx := hS p hpS x hxB heq
    have hp := support_of_truncatedConjugate_contact hu hstrict.convexOn hM hx heq
    have hgx := subgradient_truncatedConjugate_eq_maximizer hu hstrict hM hx hp heq hg
    subst g
    exact ⟨p, hpS, hp⟩
  · rintro ⟨p, hpS, hp⟩
    obtain ⟨x, hxB, heq⟩ := (exists_truncatedConjugate_eq hu hM p).1
    have hx := hS p hpS x hxB heq
    have hpx := support_of_truncatedConjugate_contact hu hstrict.convexOn hM hx heq
    have hxg : x = g := eq_of_strictConvexOn_of_support hstrict hpx hp
    subst g
    refine ⟨p, hpS, ?_⟩
    intro q
    have hq := (exists_truncatedConjugate_eq hu hM q).2 x hxB
    rw [heq, inner_sub_right]
    have hcomm : ⟪x, q⟫ = ⟪q, x⟫ := real_inner_comm q x
    have hcomm' : ⟪x, p⟫ = ⟪p, x⟫ := real_inner_comm p x
    rw [hcomm, hcomm']
    linarith

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end TruncatedConjugateSubgradients
