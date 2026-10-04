/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.DiffQuotientBound


/-!
# Weak limits of difference quotients

The `H^k` bootstrap of Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2
runs the interior `H²` estimate on a directional derivative `∂_ℓ u`. In the graph encoding of
`EllipticPdes.Sobolev.Basic` that derivative has to be produced as a limit of the discrete
family `Dₖ^h u`, and the limit is taken weakly, so this file supplies the two weak-limit
facts the bootstrap needs.

The first is weak sequential compactness of a bounded sequence in a separable real Hilbert
space, which is the abstract form of `EllipticPdes.Regularity.exists_weak_limit_of_bounded`:
the difference-quotient engine needs it on the ambient graph space `H1amb Ω`, not only on the
whole-space `EucL2 d` where that theorem states it.

The second is weak `L²` convergence of the difference quotients themselves. The bound
`norm_diffQuot_le_of_hasWeakDeriv` makes the family uniformly bounded, and against a smooth
compactly supported test the discrete integration-by-parts identity together with the strong
convergence `Dₖ^{-h} φ → ∂ₖφ` identifies the limit as the weak derivative; density of the
smooth compactly supported classes then upgrades the test class to an arbitrary one.

## Main declarations

* `exists_weak_limit_of_bounded_hilbert`: weak sequential compactness in a separable real
  Hilbert space.
* `tendsto_inner_of_dense_of_bounded`: a uniformly bounded sequence converging weakly against a
  dense set converges weakly against every vector.
* `tendsto_inner_diffQuot_of_hasWeakDeriv`: `Dₖ^{hₘ} g ⇀ g'` whenever `g'` is the weak
  `k`-derivative of `g` and `hₘ → 0` through nonzero steps.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Weak sequential compactness in a separable real Hilbert space -/

/-- **Weak sequential compactness of bounded sequences.** A sequence bounded by `M` in a
separable real Hilbert space has a subsequence converging weakly to a limit `g'` with
`‖g'‖ ≤ M`. This is `EllipticPdes.Regularity.exists_weak_limit_of_bounded` with the whole-space
`L²` substrate replaced by an abstract space, so that it also applies to the ambient graph
space `H1amb Ω`. Assembled from the sequential Banach-Alaoglu theorem on the weak dual
(`WeakDual.isSeqCompact_closedBall`), the Riesz self-duality of the Hilbert space
(`InnerProductSpace.toDual`), and the closed-ball membership of the weak-\* limit. -/
theorem exists_weak_limit_of_bounded_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {x : ℕ → E} {M : ℝ} (hx : ∀ m, ‖x m‖ ≤ M) :
    ∃ (g' : E) (σ : ℕ → ℕ), StrictMono σ ∧ ‖g'‖ ≤ M ∧
      ∀ y : E, Filter.Tendsto (fun m => ⟪x (σ m), y⟫) Filter.atTop (nhds ⟪g', y⟫) := by
  set F : ℕ → WeakDual ℝ E :=
    fun m => WeakDual.toStrongDual.symm (InnerProductSpace.toDual ℝ E (x m)) with hFdef
  have hFtoS : ∀ m, WeakDual.toStrongDual (F m) = InnerProductSpace.toDual ℝ E (x m) :=
    fun m => WeakDual.toStrongDual.apply_symm_apply _
  have hFmem : ∀ m, F m ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall
      (0 : StrongDual ℝ E) M := by
    intro m
    simp only [Set.mem_preimage, hFtoS m, Metric.mem_closedBall, dist_zero_right]
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hx m
  obtain ⟨L, hLmem, σ, hσmono, hLtend⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ E 0 M hFmem
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L), σ, hσmono, ?_, ?_⟩
  · rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hLmem
  · intro y
    have heval := (tendsto_iff_forall_eval_tendsto_topDualPairing.mp hLtend) y
    have hL1 : ∀ m, topDualPairing ℝ E (F (σ m)) y = ⟪x (σ m), y⟫ := by
      intro m
      change (F (σ m)) y = ⟪x (σ m), y⟫
      rw [show (F (σ m)) y = (InnerProductSpace.toDual ℝ E (x (σ m))) y from rfl,
        InnerProductSpace.toDual_apply_apply]
    have hL2 : topDualPairing ℝ E L y
        = ⟪(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L), y⟫ := by
      change L y = ⟪(InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L), y⟫
      rw [InnerProductSpace.toDual_symm_apply]
      exact (WeakDual.toStrongDual_apply L y).symm
    rw [hL2] at heval
    exact heval.congr (fun m => hL1 m)

/-! ### Upgrading weak convergence from a dense set -/

/-- **Density upgrade for weak convergence.** A sequence bounded by `M`, whose weak limit
candidate is also bounded by `M`, and which converges weakly against every vector of a dense
set, converges weakly against every vector: split the pairing across a nearby dense vector and
spend a third of the tolerance on each of the three pieces. -/
theorem tendsto_inner_of_dense_of_bounded {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X : ℕ → E} {L : E} {M : ℝ} (hX : ∀ m, ‖X m‖ ≤ M) (hL : ‖L‖ ≤ M)
    {S : Set E} (hS : Dense S)
    (hconv : ∀ z ∈ S, Filter.Tendsto (fun m => ⟪X m, z⟫) Filter.atTop (nhds ⟪L, z⟫))
    (y : E) :
    Filter.Tendsto (fun m => ⟪X m, y⟫) Filter.atTop (nhds ⟪L, y⟫) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hX 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpos : (0 : ℝ) < ε / (3 * (M + 1)) := by positivity
  obtain ⟨z, hzS, hzy⟩ := Metric.mem_closure_iff.mp (hS.closure_eq ▸ Set.mem_univ y) _ hpos
  have hyz : ‖y - z‖ < ε / (3 * (M + 1)) := by
    rw [← dist_eq_norm]; exact hzy
  have hMyz : M * ‖y - z‖ < ε / 3 := by
    rcases eq_or_lt_of_le hM0 with h0 | h0
    · rw [← h0, zero_mul]; linarith
    · calc M * ‖y - z‖ < M * (ε / (3 * (M + 1))) := by
            exact mul_lt_mul_of_pos_left hyz h0
        _ < ε / 3 := by
            rw [mul_div_assoc']
            rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 3)]
            nlinarith [hε.le, h0]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hconv z hzS) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hsplit : ⟪X n, y⟫ - ⟪L, y⟫
      = ⟪X n, y - z⟫ + (⟪X n, z⟫ - ⟪L, z⟫) + ⟪L, z - y⟫ := by
    rw [inner_sub_right, inner_sub_right]; ring
  have hb1 : |⟪X n, y - z⟫| ≤ M * ‖y - z‖ :=
    le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_right (hX n) (norm_nonneg _))
  have hb3 : |⟪L, z - y⟫| ≤ M * ‖y - z‖ := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    rw [show ‖z - y‖ = ‖y - z‖ from norm_sub_rev z y]
    exact mul_le_mul_of_nonneg_right hL (norm_nonneg _)
  have hb2 : |⟪X n, z⟫ - ⟪L, z⟫| < ε / 3 := by
    have := hN n hn
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq, hsplit]
  calc |⟪X n, y - z⟫ + (⟪X n, z⟫ - ⟪L, z⟫) + ⟪L, z - y⟫|
      ≤ |⟪X n, y - z⟫ + (⟪X n, z⟫ - ⟪L, z⟫)| + |⟪L, z - y⟫| := abs_add_le _ _
    _ ≤ |⟪X n, y - z⟫| + |⟪X n, z⟫ - ⟪L, z⟫| + |⟪L, z - y⟫| := by
        have hsub := abs_add_le ⟪X n, y - z⟫ (⟪X n, z⟫ - ⟪L, z⟫)
        linarith
    _ < ε := by linarith

/-! ### Weak convergence of the difference quotients -/

/-- **Weak `L²` convergence of difference quotients (Evans §5.8.2).** If `g'` is the weak
`k`-derivative of `g` in `L²(ℝᵈ)` and the steps `ηₘ → 0` are nonzero, then
`Dₖ^{ηₘ} g ⇀ g'` weakly in `L²`. Against a smooth compactly supported test the discrete
integration-by-parts identity `⟪Dₖ^h g, φ⟫ = -⟪g, Dₖ^{-h} φ⟫` together with the strong
convergence `Dₖ^{-ηₘ} φ → ∂ₖφ` gives the limit `-⟪g, ∂ₖφ⟫ = ⟪g', φ⟫`, and the uniform bound
`‖Dₖ^h g‖ ≤ ‖g'‖` extends it to every test class by density. -/
theorem tendsto_inner_diffQuot_of_hasWeakDeriv (k : Fin d) {g g' : EucL2 d}
    (hg : HasWeakDeriv k g g') {η : ℕ → ℝ} (hη0 : ∀ m, η m ≠ 0)
    (hηlim : Filter.Tendsto η Filter.atTop (nhds 0)) (y : EucL2 d) :
    Filter.Tendsto (fun m => ⟪diffQuot k (η m) g, y⟫) Filter.atTop (nhds ⟪g', y⟫) := by
  classical
  set S : Set (EucL2 d) := {w : EucL2 d | ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ,
    w =ᵐ[volume] ρ ∧ HasCompactSupport ρ ∧ ContDiff ℝ (⊤ : ℕ∞) ρ} with hS
  have hdense : Dense S :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (by norm_num)
  refine tendsto_inner_of_dense_of_bounded
    (fun m => norm_diffQuot_le_of_hasWeakDeriv k g g' hg (η m)) (le_refl _) hdense ?_ y
  rintro w ⟨ρ, hwρ, hρcs, hρcd⟩
  have hρL2 : MemLp ρ 2 volume := hρcd.continuous.memLp_of_hasCompactSupport hρcs
  have hρpc : Continuous (partialD k ρ) :=
    (hρcd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hρpcs : HasCompactSupport (partialD k ρ) :=
    hρcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hρpL2 : MemLp (partialD k ρ) 2 volume := hρpc.memLp_of_hasCompactSupport hρpcs
  have hweq : w = hρL2.toLp ρ := Lp.ext (hwρ.trans hρL2.coeFn_toLp.symm)
  subst hweq
  -- The negated steps tend to `0` through nonzero values.
  have hnη0 : ∀ m, -(η m) ≠ 0 := fun m => neg_ne_zero.mpr (hη0 m)
  have hnηlim : Filter.Tendsto (fun m => -(η m)) Filter.atTop (nhds 0) := by
    simpa using hηlim.neg
  have hstrong : Filter.Tendsto (fun m => diffQuot k (-(η m)) (hρL2.toLp ρ)) Filter.atTop
      (nhds (hρpL2.toLp (partialD k ρ))) :=
    tendsto_diffQuot_partialD k hρcd hρcs hρL2 hρpL2 _ hnη0 hnηlim
  have hinner : Filter.Tendsto (fun m => ⟪g, diffQuot k (-(η m)) (hρL2.toLp ρ)⟫)
      Filter.atTop (nhds ⟪g, hρpL2.toLp (partialD k ρ)⟫) := tendsto_const_nhds.inner hstrong
  have hlim : Filter.Tendsto (fun m => ⟪diffQuot k (η m) g, hρL2.toLp ρ⟫) Filter.atTop
      (nhds (-⟪g, hρpL2.toLp (partialD k ρ)⟫)) := by
    refine hinner.neg.congr (fun m => ?_)
    exact (diffQuot_inner_adjoint k (η m) g (hρL2.toLp ρ)).symm
  -- The weak-derivative identity turns the limit into the pairing against `g'`.
  have hIg : ⟪g, hρpL2.toLp (partialD k ρ)⟫ = ∫ x, (g x : ℝ) * partialD k ρ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hρpL2.coeFn_toLp] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  have hIg' : ⟪g', hρL2.toLp ρ⟫ = ∫ x, (g' x : ℝ) * ρ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hρL2.coeFn_toLp] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  have hweak := hg ρ hρcd hρcs
  rw [show -⟪g, hρpL2.toLp (partialD k ρ)⟫ = ⟪g', hρL2.toLp ρ⟫ by
    rw [hIg, hIg', hweak, neg_neg]] at hlim
  exact hlim

end EllipticPdes.Regularity
