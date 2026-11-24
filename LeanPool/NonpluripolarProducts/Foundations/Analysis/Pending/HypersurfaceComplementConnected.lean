/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicZeroSetThin
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complements of hypersurfaces in a ball are path-connected

Blueprint `lag:hypersurface-complement-connected` (Demailly, *Complex analytic and
differential geometry*, II.4.19).

If `g` is holomorphic on a ball `B` of a finite-dimensional complex normed space and not
identically zero near the centre, then `B \ g⁻¹(0)` is path-connected.  Two points
`a, b` of the complement are joined inside the complex line through them: `t ↦ g(a + t(b-a))`
is holomorphic on a convex open set of `ℂ` and nonzero at `0`, so its zeros are countable,
and among the uncountably many internally disjoint polygonal paths `0 → 1/2 + is → 1` one
avoids them.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology Convex

namespace SGPT.Foundations.Analysis.Pending.HypersurfaceComplementConnected

section Real

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousAdd F]
  [ContinuousSMul ℝ F]

/-- In a real vector space of dimension `> 1`, two points of a convex open set `U` lying
outside a countable set `s` can be joined by a path in `U \ s`. -/
theorem joinedIn_diff_of_convex_of_countable (h : 1 < Module.rank ℝ F) {U s : Set F}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hs : s.Countable) {a b : F} (ha : a ∈ U \ s)
    (hb : b ∈ U \ s) : JoinedIn (U \ s) a b := by
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [c, x]
    module
  have Ib : c + x = b := by
    simp only [c, x]
    module
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb.2
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha.2
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  have hT : IsOpen {t : ℝ | c + t • y ∈ U} :=
    hUo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hcU : c ∈ U := by
    have hc : c = (2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • b := by
      simp only [c]
      module
    rw [hc]
    exact hUc ha.1 hb.1 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨t, htU, ht⟩ : ({t : ℝ | c + t • y ∈ U} ∩
      ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty}
        ∪ {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty})ᶜ).Nonempty :=
    ((A.union B).dense_compl ℝ).inter_open_nonempty _ hT ⟨0, by simpa using hcU⟩
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq,
    not_nonempty_iff_eq_empty] at ht htU
  have JA : JoinedIn (U \ s) a (c + t • y) := by
    apply JoinedIn.of_segment_subset
    refine subset_sdiff.2 ⟨hUc.segment_subset ha.1 htU, ?_⟩
    rw [disjoint_iff_inter_eq_empty, ← Ia]
    exact ht.2
  have JB : JoinedIn (U \ s) b (c + t • y) := by
    apply JoinedIn.of_segment_subset
    refine subset_sdiff.2 ⟨hUc.segment_subset hb.1 htU, ?_⟩
    rw [disjoint_iff_inter_eq_empty, ← Ib]
    exact ht.1
  exact JA.trans JB.symm

end Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- **The complement of a hypersurface in a ball is path-connected.** -/
theorem isPathConnected_ball_diff_zeroSet {c : E} {r : ℝ} (hr : 0 < r) {g : E → ℂ}
    (hg : DifferentiableOn ℂ g (ball c r)) (hne : ¬ ∀ᶠ z in 𝓝 c, g z = 0) :
    IsPathConnected (ball c r \ g ⁻¹' {0}) := by
  rw [isPathConnected_iff]
  refine ⟨closure_nonempty_iff.1 ⟨c, RiemannExtension.dense_compl_zeroSet isOpen_ball
    (convex_ball c r).isPreconnected hg (mem_ball_self hr) hne (mem_ball_self hr)⟩, ?_⟩
  rintro a ⟨haB, ha0⟩ b ⟨hbB, hb0⟩
  set ℓ : ℂ → E := fun t => a + t • (b - a) with hℓ
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  set D : Set ℂ := ℓ ⁻¹' ball c r with hD
  have hDo : IsOpen D := isOpen_ball.preimage hℓc
  have hDc : Convex ℝ D := by
    intro p hp q hq s t hs ht hst
    have key : a + (s • p + t • q) • (b - a) =
        s • (a + p • (b - a)) + t • (a + q • (b - a)) := by
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hst, one_smul, add_smul, smul_assoc,
        smul_assoc]
    simp only [hD, hℓ, Set.mem_preimage] at hp hq ⊢
    rw [key]
    exact convex_ball c r hp hq hs ht hst
  have h0D : (0 : ℂ) ∈ D := by simpa [hD, hℓ] using haB
  have h1D : (1 : ℂ) ∈ D := by simpa [hD, hℓ] using hbB
  have hℓd : Differentiable ℂ ℓ := (differentiable_const a).add (differentiable_id.smul_const _)
  have hφ : AnalyticOnNhd ℂ (g ∘ ℓ) D :=
    (hg.comp hℓd.differentiableOn fun t ht => ht).analyticOnNhd hDo
  have hiso : ∀ t ∈ D, ∀ᶠ u in 𝓝[≠] t, (g ∘ ℓ) u ≠ 0 := by
    intro t ht
    refine ((hφ t ht).eventually_eq_zero_or_eventually_ne_zero).resolve_left fun h0 => ha0 ?_
    have := hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc.isPreconnected ht h0 h0D
    simpa [hℓ] using this
  have hN : (D ∩ (g ∘ ℓ) ⁻¹' {0}).Countable := by
    refine (HereditarilyLindelofSpace.isLindelof _).countable ?_
    rw [discreteTopology_subtype_iff]
    rintro t ⟨ht, -⟩
    rw [inf_principal_eq_bot]
    filter_upwards [hiso t ht] with u hu hmem
    exact hu hmem.2
  have e0 : ℓ 0 = a := by simp [hℓ]
  have e1 : ℓ 1 = b := by simp [hℓ]
  have hJ : JoinedIn (D \ (D ∩ (g ∘ ℓ) ⁻¹' {0})) 0 1 :=
    joinedIn_diff_of_convex_of_countable
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) hDc hDo hN
      ⟨h0D, fun h => ha0 (by rw [← e0]; exact h.2)⟩
      ⟨h1D, fun h => hb0 (by rw [← e1]; exact h.2)⟩
  rw [← e0, ← e1]
  refine (hJ.map hℓc.continuousOn).mono ?_
  rintro _ ⟨t, ⟨htD, htN⟩, rfl⟩
  exact ⟨htD, fun h => htN ⟨htD, h⟩⟩

end SGPT.Foundations.Analysis.Pending.HypersurfaceComplementConnected
