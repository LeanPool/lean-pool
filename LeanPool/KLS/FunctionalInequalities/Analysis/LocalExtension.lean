/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Local finite-order and smooth extensions

A function of class `C^m`, for `m ≤ ∞`, on an open set agrees locally with a
function of the same class on the whole finite-dimensional real normed space.
The bump construction gives agreement on a ball; it does not extend the
function on its entire domain or assert real analyticity. A finite partition
of bumps covering the compact closure of a bounded set `K` gives a global `C^∞`
function agreeing with a given `C^∞` function on `closure K`
(`exists_contDiff_eqOn_closure`).
-/

@[expose] public section

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-- Local extension with an explicit agreement ball, for finite order or `C^∞`. -/
theorem exists_contDiff_eqOn_ball {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ∞} {f : E → F}
    {O : Set E} {z : E} (hO : IsOpen O) (hf : ContDiffOn ℝ m f O) (hz : z ∈ O) :
    ∃ (ρ : ℝ) (w : E → F),
      0 < ρ ∧ Metric.ball z ρ ⊆ O ∧ ContDiff ℝ m w ∧ Set.EqOn w f (Metric.ball z ρ) := by
  classical
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO z hz
  set χ : ContDiffBump z := ⟨r / 3, r / 2, by positivity, by linarith⟩ with hχ
  have hχsmall : Metric.ball z (r / 3) ⊆ O := fun y hy =>
    hrO (Metric.ball_subset_ball (by linarith) hy)
  have htsupp : tsupport (χ : E → ℝ) ⊆ O := by
    rw [χ.tsupport_eq]
    exact fun y hy =>
      hrO
        (by
          simp only [Metric.mem_closedBall] at hy
          simpa [Metric.mem_ball] using hy.trans_lt (by simp [hχ]; linarith))
  refine ⟨r / 3, fun y => if y ∈ O then (χ y) • f y else 0, by positivity, hχsmall, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ O
    · refine
        ContDiffAt.congr_of_eventuallyEq
          ((χ.contDiff (n := m)).contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hy))) ?_
      filter_upwards [hO.mem_nhds hy] with y' hy'
      simp [hy']
    · have hyt : y ∈ (tsupport (χ : E → ℝ))ᶜ := fun hc => hy (htsupp hc)
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : F))) ?_
      filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hyt] with y' hy'
      have hzero : χ y' = 0 := image_eq_zero_of_notMem_tsupport hy'
      by_cases hy'O : y' ∈ O <;> simp [hy'O, hzero]
  · intro y hy
    have hyO : y ∈ O := hχsmall hy
    have hone : χ y = 1 :=
      χ.one_of_mem_closedBall
        (by simpa [Metric.mem_closedBall, hχ] using (Metric.mem_ball.mp hy).le)
    simp [hyO, hone]

/-- Local extension expressed as equality in a neighbourhood of the chosen point. -/
theorem exists_contDiff_eventuallyEq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ∞} {f : E → F} {O : Set E} {z : E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ m f O) (hz : z ∈ O) :
    ∃ g : E → F, ContDiff ℝ m g ∧ g =ᶠ[𝓝 z] f := by
  obtain ⟨r, g, hr, _, hg, heq⟩ := exists_contDiff_eqOn_ball hO hf hz
  exact ⟨g, hg, Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Metric.ball z r, Metric.ball_mem_nhds z hr, heq⟩⟩

/-- Extension from a neighbourhood of a compact closure: a function `C^∞` on an open set `U`
containing the closure of a bounded set `K` agrees on `closure K` with a function `C^∞` on the whole
finite-dimensional real normed space. -/
theorem exists_contDiff_eqOn_closure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E}
    (hKb : Bornology.IsBounded K) (hU : IsOpen U) (hKU : closure K ⊆ U)
    {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) :
    ∃ W : E → ℝ, ContDiff ℝ ∞ W ∧ EqOn W V (closure K) := by
  classical
  choose ε hε hball using
    (fun x : closure K => Metric.isOpen_iff.mp hU x.1 (hKU x.2))
  let b : (i : closure K) → ContDiffBump i.1 :=
    fun i =>
      { rIn := ε i / 4
        rOut := ε i / 2
        rIn_pos := div_pos (hε i) (by norm_num)
        rIn_lt_rOut := by
          have := hε i
          linarith }
  have hb : ∀ i : closure K, ContDiff ℝ ∞ (b i) := fun i => (b i).contDiff
  have hcover : closure K ⊆
      ⋃ i : closure K, Metric.ball i.1 (ε i / 4) := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (div_pos (hε ⟨x, hx⟩) (by norm_num))
  obtain ⟨t, ht⟩ := hKb.isCompact_closure.elim_finite_subcover
    (fun i : closure K => Metric.ball i.1 (ε i / 4))
    (fun _ => Metric.isOpen_ball) hcover
  let χ : E → ℝ :=
    fun x => 1 - ∏ i ∈ t, (1 - b i x)
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_const.sub (contDiff_prod fun i _ => contDiff_const.sub (hb i))
  have hzero : ∀ x ∉ U, ∀ᶠ y in 𝓝 x, χ y = 0 := by
    intro x hx
    have hz : ∀ i : closure K, ∀ᶠ y in 𝓝 x, b i y = 0 := by
      intro i
      have hxball : x ∉ Metric.closedBall i.1 (ε i / 2) := by
        intro hm
        apply hx
        apply hball i
        exact lt_of_le_of_lt hm (half_lt_self (hε i))
      have hsupp : Function.support (b i) ⊆
          Metric.closedBall i.1 (ε i / 2) := by
        rw [(b i).support_eq]
        exact Metric.ball_subset_closedBall
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hxball] with y hy
      by_contra hyzero
      exact hy (hsupp hyzero)
    filter_upwards [(Filter.eventually_all_finset t).2 fun i _ => hz i] with y hy
    have hp : ∏ i ∈ t, (1 - b i y) = 1 :=
      Finset.prod_eq_one fun i hi => by rw [hy i hi, sub_zero]
    simp only [χ, hp, sub_self]
  have hone : EqOn χ (fun _ => 1) (closure K) := by
    intro x hx
    rcases mem_iUnion.mp (ht hx) with ⟨i, hi⟩
    rcases mem_iUnion.mp hi with ⟨hit, hxi⟩
    have hbi : b i x = 1 := (b i).one_of_mem_closedBall (Metric.ball_subset_closedBall hxi)
    have hp : (∏ j ∈ t, (1 - b j x)) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨i, hit, by rw [hbi, sub_self]⟩
    dsimp only [χ]
    rw [hp, sub_zero]
  refine ⟨fun x => χ x * V x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.mul ((hV x hx).contDiffAt (hU.mem_nhds hx))
    · have he :
          (fun y => χ y * V y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hzero x hx] with y hy
        rw [hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro x hx
    change χ x * V x = V x
    rw [hone hx, one_mul]

end FunctionalInequalities.Analysis
