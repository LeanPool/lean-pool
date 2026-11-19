/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.LocalSets
public import LeanPool.StableManifold.Linear.SplittingConstruction
public import LeanPool.StableManifold.Perron.Smooth
public import LeanPool.StableManifold.Local.Cutoff

/-!
# The local stable manifold

Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood of a fixed point `p` of a finite-dimensional real
normed space, and suppose that the stable and unstable subspaces `Eₛ`, `Eᵤ` of `A = Df(p)` are
complementary (for instance, `A` hyperbolic). Then there are `δ > 0` and a `Cⁿ` map
`hₛ : Eₛ → Eᵤ` with `hₛ 0 = 0`, `Dhₛ(0) = 0`, such that for **every** neighborhood `U` of `p`
inside the ball of radius `δ`, the local stable set of `f|_U` is the graph
`{p + x + hₛ x | x ∈ Vₛ}` over some neighborhood `Vₛ` of `0` in `Eₛ`
(`Function.exists_localStableSet_eq_graph_of_isCompl`). The map `hₛ` does not depend on `U`.
Inside a small ball, a forward orbit that stays in `U` tends to `p`, so the local stable set of
`f|_U` is the set of points whose forward orbit stays in `U`
(`Function.exists_localStableSet_eq_setOf_forall_iterate_mem`).

Ingredients:

* `StableManifold.localStableSet_eq_image_add`: translating the fixed point to `0`;
* `StableManifold.Perturbation.localStableSet_map_eq`: for a globally small Lipschitz perturbation
  `F = A + φ` and a bounded `U`, the local stable set of `F|_U` at `0` is the part of the global
  stable manifold whose forward orbit stays in `U` (a bounded orbit lies on the graph, and orbits
  on the graph tend to `0`);
* `StableManifold.Perturbation.stableGraph`: the graph map as a map `Eₛ → Eᵤ` between the
  subspaces, with its regularity and tangency (`contDiff_stableGraph`, `fderiv_stableGraph_zero`);
* `StableManifold.Perturbation.exists_localStableSet_map_eq_image`: for a bounded neighborhood `U`
  of `0`, the local stable set of `F|_U` is a graph over a neighborhood `Vₛ` of `0` in `Eₛ`
  (it contains the ball of radius `r / (2 C)` when `U` contains the ball of radius `r`, by the
  decay estimate `Perturbation.norm_iterate_le`).

## Proofs

* `localStableSet_eq_image_add`: `Function.localStableSet_conj` for the translation
  `Homeomorph.addLeft p`, with `(p + ·) '' ((p + ·) ⁻¹' U) = U` (`Set.image_preimage_eq`).
* `localStableSet_map_eq`: a forward orbit in the bounded `U` is bounded, so `(1 - P) x = graph x`
  (`Perturbation.bddOrbit_iff`); conversely, the orbits starting on the graph tend to `0`
  (`Perturbation.tendsto_iterate`).
* `stableGraph`: `graph ξ ∈ Eᵤ` since `P (graph ξ) = 0` (`proj_graph`, `proj_apply_eq_zero_iff`).
  `contDiff_stableGraph`, `fderiv_stableGraph_zero`: `stableGraph = πᵤ ∘ graph ∘ ιₛ`, with
  `ιₛ = Eₛ.subtypeL` and `πᵤ` the map `1 - P` co-restricted to `Eᵤ` (`codRestrict`); then
  `contDiff_graph`, resp. `hasFDerivAt_graph_zero` and the chain rule.
* `exists_localStableSet_map_eq_image`: `Vₛ = {ξ | ∀ n, F^[n] (ξ + stableGraph ξ) ∈ U}`. A point
  `x` of the set in `localStableSet_map_eq` is `P x + graph (P x)` with `P x ∈ Eₛ` (`graph_proj`,
  `proj_apply_eq_self_iff`), and conversely every `ξ + graph ξ` lies on the graph. If `U`
  contains the ball of radius `r`, then `Vₛ` contains the ball of radius `r / (2 C)`, since
  `‖Fⁿ (ξ + graph ξ)‖ ≤ 2 C θⁿ ‖ξ‖ < r` there (`norm_iterate_le`).
* `Function.exists_localStableSet_eq_graph_of_isCompl`: take a splitting `S` of `A = Df(p)`
  (`nonempty_hyperbolicSplitting`). The translate `g x = f (p + x) - p` is `Cⁿ` near `0` with
  derivative `A` at `0`; the cut-off (`exists_contDiff_lipschitzWith_eqOn_ball`, with
  `η = 1 / (2 S.bound)`) gives a `Perturbation S` equal to `g` on `ball 0 δ`, and
  `hₛ = stableGraph`. For `U ⊆ ball p δ`: `localStableSet_eq_image_add`,
  `Function.localStableSet_congr` on `(p + ·) ⁻¹' U ⊆ ball 0 δ`,
  `exists_localStableSet_map_eq_image`, and `Set.image_image`.
* `Function.exists_localStableSet_eq_setOf_forall_iterate_mem`: the same cut-off `F`. If the
  `f`-orbit of `x` stays in `U ⊆ ball p δ`, then `F^[k] (x - p) = f^[k] x - p` by induction, as
  `F = g` on `ball 0 δ`; this orbit is bounded, so it lies on the graph
  (`Perturbation.bddOrbit_iff`) and tends to `0` (`Perturbation.tendsto_iterate`).
-/

@[expose] public section

open Filter Topology Metric Set
open scoped NNReal

namespace StableManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **Translation**: the local stable set of `f` at `p` is the translate by `p` of the local stable
set of `x ↦ f (p + x) - p` at `0`.

Proof: `Function.localStableSet_conj` with `Homeomorph.addLeft p`. -/
theorem localStableSet_eq_image_add (f : E → E) (p : E) (U : Set E) :
    Function.localStableSet f p U =
      (p + ·) '' Function.localStableSet (fun x ↦ f (p + x) - p) 0 ((p + ·) ⁻¹' U) := by
  have h := Function.localStableSet_conj (Homeomorph.addLeft p) (fun x ↦ f (p + x) - p) 0
    ((p + ·) ⁻¹' U)
  have hf : (Homeomorph.addLeft p) ∘ (fun x ↦ f (p + x) - p) ∘ (Homeomorph.addLeft p).symm = f := by
    funext y
    simp [Homeomorph.addLeft_symm]
  have hU : (Homeomorph.addLeft p) '' ((p + ·) ⁻¹' U) = U :=
    image_preimage_eq U (Homeomorph.addLeft p).surjective
  rw [hf, hU] at h
  simpa using h

namespace Perturbation

variable {A : E →L[ℝ] E} {S : A.HyperbolicSplitting} (F : Perturbation S)

section Complete

variable [CompleteSpace E]

/-- For a bounded `U`, the local stable set of `F|_U` at `0` is the part of the global stable
manifold whose forward orbit stays in `U`.

Proof: `bddOrbit_iff` and `tendsto_iterate`. -/
theorem localStableSet_map_eq {U : Set E} (hU : Bornology.IsBounded U) :
    Function.localStableSet F.map 0 U =
      {x | (1 - S.proj) x = F.graph x ∧ ∀ n, F.map^[n] x ∈ U} := by
  obtain ⟨M, hM⟩ := hU.exists_norm_le
  ext x
  constructor
  · rintro ⟨hxU, -⟩
    exact ⟨(F.bddOrbit_iff x).1 ⟨M, fun n ↦ hM _ (hxU n)⟩, hxU⟩
  · rintro ⟨hx, hxU⟩
    exact ⟨hxU, F.tendsto_iterate hx⟩

/-- The graph map as a map from the stable to the unstable subspace. -/
noncomputable def stableGraph (ξ : A.stableSubspace) : A.unstableSubspace :=
  ⟨F.graph ξ, S.proj_apply_eq_zero_iff.1 (F.proj_graph ξ)⟩

@[simp]
theorem coe_stableGraph (ξ : A.stableSubspace) : (F.stableGraph ξ : E) = F.graph ξ :=
  rfl

theorem stableGraph_zero : F.stableGraph 0 = 0 := by
  ext
  simp [F.graph_zero]

/-- The projection `1 - P` onto the unstable subspace, as a map into the subspace. -/
private noncomputable def unstableProj : E →L[ℝ] A.unstableSubspace :=
  (1 - S.proj).codRestrict A.unstableSubspace fun x ↦ S.proj_apply_eq_zero_iff.1 <| by
    rw [← mul_apply_eq_comp, S.proj_mul_one_sub_proj, zero_apply]

/-- `stableGraph = πᵤ ∘ graph ∘ ιₛ`. -/
private lemma stableGraph_eq_comp :
    F.stableGraph = unstableProj (S := S) ∘ F.graph ∘ A.stableSubspace.subtypeL := by
  funext ξ
  ext
  simp [unstableProj, F.proj_graph]

/-- The typed graph map has derivative `0` at `0` when `φ` has.

Proof: the same composition and `hasFDerivAt_graph_zero`. -/
theorem fderiv_stableGraph_zero (hφ : HasFDerivAt F.φ (0 : E →L[ℝ] E) 0) :
    fderiv ℝ F.stableGraph 0 = 0 := by
  have hg : HasFDerivAt F.graph (0 : E →L[ℝ] E) (A.stableSubspace.subtypeL 0) := by
    simpa using F.hasFDerivAt_graph_zero hφ
  have h := (unstableProj (S := S)).hasFDerivAt.comp (0 : A.stableSubspace)
    (hg.comp (0 : A.stableSubspace) A.stableSubspace.subtypeL.hasFDerivAt)
  rw [F.stableGraph_eq_comp, h.fderiv]
  simp

/-- **The local stable set of the globalized map**: for a bounded neighborhood `U` of `0`, the
local stable set of `F|_U` at `0` is the graph of `stableGraph` over a neighborhood `Vₛ` of `0` in
the stable subspace.

Proof: `Vₛ = {ξ | ∀ n, F^[n] (ξ + stableGraph ξ) ∈ U}` (`localStableSet_map_eq`); it contains a
ball by the decay estimate `norm_iterate_le`. -/
theorem exists_localStableSet_map_eq_image {U : Set E} (hU : U ∈ 𝓝 0)
    (hUb : Bornology.IsBounded U) :
    ∃ Vs ∈ 𝓝 (0 : A.stableSubspace),
      Function.localStableSet F.map 0 U =
        (fun x : A.stableSubspace ↦ (x : E) + (F.stableGraph x : E)) '' Vs := by
  have hon (ξ : A.stableSubspace) : S.proj ((ξ : E) + F.graph ξ) = ξ ∧
      (1 - S.proj) ((ξ : E) + F.graph ξ) = F.graph ((ξ : E) + F.graph ξ) := by
    have hP : S.proj ((ξ : E) + F.graph ξ) = ξ := by
      rw [map_add, S.proj_apply_eq_self_iff.2 ξ.2, F.proj_graph, add_zero]
    refine ⟨hP, ?_⟩
    rw [← F.graph_proj ((ξ : E) + F.graph ξ), hP, sub_apply, one_apply_eq_self, hP]
    abel
  refine ⟨{ξ | ∀ n, F.map^[n] ((ξ : E) + F.graph ξ) ∈ U}, ?_, ?_⟩
  · obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
    have hC := S.const_pos
    refine mem_of_superset (ball_mem_nhds 0 (div_pos hr (mul_pos two_pos hC))) fun ξ hξ n ↦ ?_
    apply hrU
    rw [mem_ball_zero_iff] at hξ ⊢
    have hξ' := (lt_div_iff₀ (mul_pos two_pos hC)).1 hξ
    have hθ : S.decayRate ^ n ≤ 1 := pow_le_one₀ S.decayRate_pos.le S.decayRate_lt_one.le
    calc ‖F.map^[n] ((ξ : E) + F.graph ξ)‖
        ≤ 2 * S.const * S.decayRate ^ n * ‖S.proj ((ξ : E) + F.graph ξ)‖ :=
          F.norm_iterate_le (hon ξ).2 n
      _ = 2 * S.const * S.decayRate ^ n * ‖ξ‖ := by rw [(hon ξ).1]; rfl
      _ ≤ 2 * S.const * 1 * ‖ξ‖ := by gcongr
      _ < r := by linarith
  · rw [F.localStableSet_map_eq hUb]
    ext x
    constructor
    · rintro ⟨hx, hxU⟩
      have hPx : S.proj x ∈ A.stableSubspace :=
        S.proj_apply_eq_self_iff.1 (by rw [← mul_apply_eq_comp, S.proj_mul_proj])
      have hxe : S.proj x + F.graph (S.proj x) = x := by
        rw [F.graph_proj, ← hx, sub_apply, one_apply_eq_self]
        abel
      exact ⟨⟨S.proj x, hPx⟩, fun n ↦ by simpa [hxe] using hxU n, hxe⟩
    · rintro ⟨ξ, hξ, rfl⟩
      exact ⟨(hon ξ).2, hξ⟩

end Complete

variable [FiniteDimensional ℝ E]

/-- The typed graph map is `Cⁿ` when `φ` is.

Proof: `stableGraph = πᵤ ∘ graph ∘ ιₛ` with continuous linear `πᵤ`, `ιₛ`; `contDiff_graph`. -/
theorem contDiff_stableGraph {n : ℕ∞} (hφ : ContDiff ℝ n F.φ) : ContDiff ℝ n F.stableGraph := by
  rw [F.stableGraph_eq_comp]
  exact (unstableProj (S := S)).contDiff.comp
    ((F.contDiff_graph hφ).comp A.stableSubspace.subtypeL.contDiff)

end Perturbation

end StableManifold

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The cut-off at a fixed point**: if the stable and unstable subspaces of `Df(p)` are
complementary, the translate `x ↦ f (p + x) - p` agrees on a ball around `0` with a perturbation
`F = Df(p) + φ` of a hyperbolic splitting of `Df(p)`, with `φ` of class `Cⁿ` and `Dφ(0) = 0`. -/
private lemma exists_perturbation_eqOn_ball {f : E → E} {p : E} {W : Set E} {n : ℕ∞}
    (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hsplit : IsCompl (fderiv ℝ f p).stableSubspace (fderiv ℝ f p).unstableSubspace) :
    ∃ S : (fderiv ℝ f p).HyperbolicSplitting, ∃ F : StableManifold.Perturbation S, ∃ δ > 0,
      ContDiff ℝ n F.φ ∧ HasFDerivAt F.φ (0 : E →L[ℝ] E) 0 ∧
      EqOn (fun x ↦ f (p + x) - p) F.map (ball 0 δ) := by
  obtain ⟨S⟩ := ContinuousLinearMap.nonempty_hyperbolicSplitting hsplit
  -- the translated map `g x = f (p + x) - p`, `Cⁿ` near `0`, with derivative `Df(p)` at `0`
  have hcont : Continuous (fun x : E ↦ p + x) := continuous_const.add continuous_id
  have hpre : (p + ·) ⁻¹' W ∈ 𝓝 (0 : E) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  have hg : ContDiffOn ℝ n (fun x ↦ f (p + x) - p) ((p + ·) ⁻¹' W) :=
    (hf.comp (contDiff_const.add contDiff_id).contDiffOn fun _ hx ↦ hx).sub contDiffOn_const
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    have : (0 : ℕ∞) < n := zero_lt_one.trans_le hn
    exact_mod_cast this.ne'
  have hgA : HasFDerivAt (fun x ↦ f (p + x) - p) (fderiv ℝ f p) 0 := by
    have h1 : HasFDerivAt (fun x : E ↦ p + x) (ContinuousLinearMap.id ℝ E) 0 :=
      (hasFDerivAt_id 0).const_add p
    have h2 : HasFDerivAt f (fderiv ℝ f p) (p + 0) := by
      rw [add_zero]
      exact ((hf.contDiffAt hW).differentiableAt hn0).hasFDerivAt
    simpa using (h2.comp 0 h1).sub_const p
  -- the cut-off, with Lipschitz constant `1 / (2 S.bound)`
  have hb := S.bound_pos
  have hη : 0 < (1 / (2 * S.bound)).toNNReal := by simpa using hb
  obtain ⟨δ, hδ, φ, hφ, hlip, hφ0, hdφ, hEq⟩ :=
    StableManifold.exists_contDiff_lipschitzWith_eqOn_ball hn hpre hg (by simp [hfix]) hgA hη
  let F : StableManifold.Perturbation S :=
    { φ := φ
      lip := (1 / (2 * S.bound)).toNNReal
      lipschitzWith := hlip
      map_zero := hφ0
      lip_mul_bound_le := by
        rw [Real.coe_toNNReal _ (by positivity)]
        field_simp
        rfl }
  exact ⟨S, F, δ, hδ, hφ, hdφ, hEq⟩

/-- **The local stable manifold theorem**, for every small neighborhood. Let `f` be `Cⁿ`
(`1 ≤ n ≤ ∞`) on a neighborhood `W` of a fixed point `p`, and suppose that the stable and unstable
subspaces of `A = Df(p)` are complementary. Then there are `δ > 0` and a `Cⁿ` map
`hₛ : Eₛ → Eᵤ` with `hₛ 0 = 0` and `Dhₛ(0) = 0` such that, for every neighborhood `U` of `p`
inside the ball of radius `δ`, the local stable set of `f|_U` is the graph `{p + x + hₛ x}` over a
neighborhood `Vₛ` of `0` in `Eₛ`.

Proof: translate `p` to `0`, cut off (`StableManifold.exists_contDiff_lipschitzWith_eqOn_ball`),
and apply `StableManifold.Perturbation.exists_localStableSet_map_eq_image` to the globalized map,
which agrees with `f` on `U`. -/
theorem exists_localStableSet_eq_graph_of_isCompl {f : E → E} {p : E} {W : Set E} {n : ℕ∞}
    (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hsplit : IsCompl (fderiv ℝ f p).stableSubspace (fderiv ℝ f p).unstableSubspace) :
    ∃ δ > 0, ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
      ContDiff ℝ n hs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
      ∀ U ∈ 𝓝 p, U ⊆ ball p δ →
        ∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs := by
  obtain ⟨S, F, δ, hδ, hφ, hdφ, hEq⟩ := exists_perturbation_eqOn_ball hn hW hf hfix hsplit
  refine ⟨δ, hδ, F.stableGraph, F.contDiff_stableGraph hφ, F.stableGraph_zero,
    F.fderiv_stableGraph_zero hdφ, fun U hU hUδ ↦ ?_⟩
  have hUδ' : (p + ·) ⁻¹' U ⊆ ball 0 δ := fun x hx ↦ by
    simpa [dist_eq_norm] using hUδ hx
  have hpre : (p + ·) ⁻¹' U ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨Vs, hVs, hVeq⟩ :=
    F.exists_localStableSet_map_eq_image hpre (isBounded_ball.subset hUδ')
  refine ⟨Vs, hVs, ?_⟩
  have hcongr : localStableSet (fun x ↦ f (p + x) - p) 0 ((p + ·) ⁻¹' U) =
      localStableSet F.map 0 ((p + ·) ⁻¹' U) :=
    localStableSet_congr (hEq.mono hUδ')
  rw [StableManifold.localStableSet_eq_image_add, hcongr, hVeq, image_image]
  simp only [add_assoc]

/-- **Convergence is automatic near a hyperbolic fixed point**. Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a
neighborhood `W` of a fixed point `p`, and suppose that the stable and unstable subspaces of
`A = Df(p)` are complementary. Then there is `δ > 0` such that, for every set `U` inside the ball
of radius `δ` around `p`, a forward orbit that stays in `U` tends to `p`: the local stable set of
`f|_U` is the set of points whose forward orbit stays in `U`.

Proof: on the ball, `f` is conjugate by the translation to the cut-off map `F`, whose bounded
orbits lie on the graph (`StableManifold.Perturbation.bddOrbit_iff`) and tend to `0`
(`StableManifold.Perturbation.tendsto_iterate`). -/
theorem exists_localStableSet_eq_setOf_forall_iterate_mem {f : E → E} {p : E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hsplit : IsCompl (fderiv ℝ f p).stableSubspace (fderiv ℝ f p).unstableSubspace) :
    ∃ δ > 0, ∀ U ⊆ ball p δ, localStableSet f p U = {x | ∀ k, f^[k] x ∈ U} := by
  obtain ⟨S, F, δ, hδ, -, -, hEq⟩ := exists_perturbation_eqOn_ball hn hW hf hfix hsplit
  refine ⟨δ, hδ, fun U hUδ ↦ ?_⟩
  ext x
  refine ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, ?_⟩⟩
  have hball (k : ℕ) : f^[k] x - p ∈ ball (0 : E) δ := by
    rw [mem_ball_zero_iff, ← mem_ball_iff_norm]
    exact hUδ (hx k)
  -- the `F`-orbit of `x - p` is the translate of the `f`-orbit of `x`
  let translated : E → E := fun y ↦ f (p + y) - p
  have htranslate : Semiconj (fun y : E ↦ y - p) f translated := by
    intro y
    change f y - p = f (p + (y - p)) - p
    rw [add_comm, sub_add_cancel]
  have htranslated (k : ℕ) : translated^[k] (x - p) = f^[k] x - p :=
    (htranslate.iterate_right k x).symm
  have hit (k : ℕ) : F.map^[k] (x - p) = f^[k] x - p := by
    rw [← htranslated k]
    exact (iterate_eq_of_eqOn hEq (fun m ↦ (htranslated m).symm ▸ hball m) k).symm
  have hgraph : (1 - S.proj) (x - p) = F.graph (x - p) :=
    (F.bddOrbit_iff _).1 ⟨δ, fun k ↦ by
      rw [hit]
      exact (mem_ball_zero_iff.1 (hball k)).le⟩
  have ht := (F.tendsto_iterate hgraph).const_add p
  simp only [hit, add_sub_cancel, add_zero] at ht
  exact ht

end Function
