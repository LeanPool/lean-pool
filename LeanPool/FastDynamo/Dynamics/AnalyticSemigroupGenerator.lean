/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.AnalyticSemigroup
public import LeanPool.FastDynamo.Dynamics.SemigroupGenerator
public import LeanPool.FastDynamo.Operator.UnboundedResolvent

/-!
# The generator of an analytic semigroup

For an analytic semigroup `S` the operators `S(t)`, `t > 0`, map into the domain of the
generator `G`, and `G S(t)` is bounded (Engel–Nagel, Theorem II.4.6).  This is the regularising
effect of analyticity used in the paper's Lemma A.1 (`lem:semigroup-spectral-growth`).

* `IsAnalyticSemigroup.exists_generator_comp`: for `t > 0` the semigroup maps into `D(G)` and
  `x ↦ G S(t) x` is a bounded operator, namely the complex derivative of the holomorphic
  extension at `t`.
* `IsAnalyticSemigroup.isCompactOperator`: if the generator has a compact resolvent, then
  `S(t)` is compact for every `t > 0`, because `S(t) = R (r - G) S(t)`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

universe u

/-- For an analytic semigroup and `t > 0`, `S(t)` maps into the domain of the generator and the
composition `G S(t)` is a bounded operator (the derivative at `t` of the holomorphic extension;
Engel–Nagel, Theorem II.4.6). -/
theorem IsAnalyticSemigroup.exists_generator_comp {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {S : StronglyContinuousSemigroup X} {δ : ℝ} (hS : IsAnalyticSemigroup S δ)
    {t : NNReal} (ht : 0 < t) :
    ∃ G : X →L[ℂ] X, ∀ x : X, ∃ h : S t x ∈ S.generator.domain,
      S.generator ⟨S t x, h⟩ = G x := by
  obtain ⟨hδ0, hδ, ⟨T⟩⟩ := hS
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hmem : ((t : ℝ) : ℂ) ∈ openSector δ :=
    ⟨by exact_mod_cast htR.ne', by
      rw [Complex.arg_ofReal_of_nonneg htR.le]; simpa using hδ0⟩
  have hopen : IsOpen (openSector δ) :=
    isOpen_openSector (hδ.trans (by linarith [Real.pi_pos]))
  have hd : HasDerivAt T.toFun (deriv T.toFun ((t : ℝ) : ℂ)) ((t : ℝ) : ℂ) :=
    ((T.differentiableOn _ hmem).differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
  refine ⟨deriv T.toFun ((t : ℝ) : ℂ), fun x ↦ ?_⟩
  have hlim : Tendsto (S.diffQuotient (S t x)) (𝓝[>] (0 : ℝ))
      (𝓝 (deriv T.toFun ((t : ℝ) : ℂ) x)) := by
    have h1 := hd.tendsto_slope_zero
    have h2 : Tendsto (fun h : ℝ ↦ (h : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        have hh0 : (0 : ℝ) < h := hh
        exact Set.mem_compl_singleton_iff.mpr (by exact_mod_cast hh0.ne')
    have h3 := ((ContinuousLinearMap.apply ℂ X x).continuous.tendsto _).comp (h1.comp h2)
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : (0 : ℝ) < h := hh
    have hsum : T.toFun (((t : ℝ) : ℂ) + (h : ℂ)) =
        (S (Real.toNNReal h)).comp (S t) := by
      have := T.toFun_ofReal (Real.toNNReal h + t)
      rw [S.operator_add] at this
      rw [← this]
      push_cast
      rw [Real.coe_toNNReal h hh0.le, add_comm]
    have hT0 := T.toFun_ofReal t
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply,
      smul_apply, sub_apply, hsum, hT0,
      StronglyContinuousSemigroup.diffQuotient, ContinuousLinearMap.comp_apply]
  exact ⟨⟨_, hlim⟩, (S.generator_eq_iff ⟨_, ⟨_, hlim⟩⟩ _).mpr hlim⟩

/-- If the generator of an analytic semigroup has a compact resolvent, then `S(t)` is compact for
every `t > 0` (Engel–Nagel, Theorem II.4.6): `S(t) = R (r - G S(t))`
where `x ↦ G S(t) x` is bounded. -/
theorem IsAnalyticSemigroup.isCompactOperator {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {S : StronglyContinuousSemigroup X} {δ : ℝ} (hS : IsAnalyticSemigroup S δ)
    {r : ℂ} {R : X →L[ℂ] X} (hR : LinearPMap.IsResolvent S.generator r R)
    (hc : IsCompactOperator R) {t : NNReal} (ht : 0 < t) :
    IsCompactOperator (S t) := by
  obtain ⟨G, hG⟩ := hS.exists_generator_comp ht
  have heq : (S t : X → X) = R ∘ ⇑(r • S t - G) := by
    funext x
    obtain ⟨h, hGx⟩ := hG x
    have := hR.2 ⟨S t x, h⟩
    simp only [hGx] at this
    simpa using this.symm
  rw [heq]
  exact hc.comp_clm _

end

end FastDynamo
