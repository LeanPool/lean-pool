/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.LocalSetDefinitions
public import LeanPool.StableManifold.Perron.Graph

/-!
# Local stable graphs of small Lipschitz perturbations

In a complete normed space with an exponential splitting, the local stable set of the perturbed
operator is the portion of its Lyapunov–Perron graph whose forward orbit stays in the neighborhood.
For a bounded neighborhood this graph is defined over a neighborhood in the stable subspace.
-/

@[expose] public section

open Filter Topology Metric Set
open scoped NNReal

namespace StableManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

end Perturbation

end StableManifold
