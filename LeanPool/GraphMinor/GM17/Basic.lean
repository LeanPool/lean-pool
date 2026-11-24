/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Defs2
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.RankNullity

import LeanPool.GraphMinor.Surface.Classification

import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Foundational Lemmas and Section 1 of Graph Minors XVII

This file proves (1.1) of N. Robertson and P. D. Seymour, *Graph Minors. XVII. Taming a vortex*,
J. Combin. Theory Ser. B 77 (1999) 162–210, together with the foundational topological and
combinatorial lemmas on `arcComponentsIn`, closed discs with finitely many points removed, lines,
and paintings (`GM17.Painting`) that are used throughout Sections 2–14.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open scoped Convex
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-! ## 1. Classification of Surfaces: (1.1) (Page 163) -/

/-- **Graph Minors XVII, (1.1)(i)** (page 163):
Every connected surface $\Sigma$ is homeomorphic to $\Sigma(a, b, c)$ for some integers
$a, b, c \ge 0$. -/
theorem theorem_1_1_i
    (S : Type u) [TopologicalSpace S] (hS : IsSurface S) (hConn : ConnectedSpace S) :
    ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c) :=
  GraphMinor.Surface.classification.{u} S hS hConn

/-- **Graph Minors XVII, (1.1)(ii)** (page 163):
For integers $a, b, c, a', b', c' \ge 0$, the surfaces $\Sigma(a, b, c)$ and $\Sigma(a', b', c')$
are homeomorphic if and only if $c = c'$, $2a + b = 2a' + b'$, and either $b, b'$ are both zero
or neither is zero. -/
theorem theorem_1_1_ii
    (a b c a' b' c' : ℕ) :
    Nonempty (SurfaceModel a b c ≃ₜ SurfaceModel a' b' c') ↔
      c = c' ∧ 2 * a + b = 2 * a' + b' ∧ (b = 0 ↔ b' = 0) :=
  GraphMinor.Surface.modelCriterion.2 a b c a' b' c'

/-- **Graph Minors XVII, (1.1)** (page 163):
Combined statement of (1.1)(i) and (1.1)(ii). -/
theorem theorem_1_1_proof :
    (∀ (S : Type u) [TopologicalSpace S], IsSurface S → ConnectedSpace S →
      ∃ a b c : ℕ, Nonempty (S ≃ₜ SurfaceModel a b c)) ∧
    (∀ a b c a' b' c' : ℕ,
      Nonempty (SurfaceModel a b c ≃ₜ SurfaceModel a' b' c') ↔
        c = c' ∧ 2 * a + b = 2 * a' + b' ∧ (b = 0 ↔ b' = 0)) :=
  ⟨GraphMinor.Surface.classification.{u}, GraphMinor.Surface.modelCriterion.2⟩

/-! ## 2. General Lemmas on `arcComponentsIn` -/

section ArcComponents

variable {S : Type*} [TopologicalSpace S] {F : Set S}

theorem arcComponentsIn_nonempty {c : Set S} (hc : c ∈ arcComponentsIn F) : c.Nonempty :=
  hc.1

theorem arcComponentsIn_subset {c : Set S} (hc : c ∈ arcComponentsIn F) : c ⊆ F :=
  hc.2.1

theorem arcComponentsIn_isPathConnected {c : Set S} (hc : c ∈ arcComponentsIn F) :
    IsPathConnected c :=
  hc.2.2.1

theorem arcComponentsIn_maximal {c D : Set S} (hc : c ∈ arcComponentsIn F)
    (hDF : D ⊆ F) (hD : IsPathConnected D) (hcD : c ⊆ D) : D = c :=
  hc.2.2.2 D hDF hD hcD

/-- If $D \subseteq F$ is path-connected and meets an arc-component $c \in \text{arcComponentsIn }
F$,
then $D \subseteq c$. -/
theorem subset_arcComponent_of_isPathConnected {c D : Set S} (hc : c ∈ arcComponentsIn F)
    (hDF : D ⊆ F) (hD : IsPathConnected D) (hinter : (D ∩ c).Nonempty) : D ⊆ c := by
  rcases hinter with ⟨x, hxD, hxc⟩
  have hunion : IsPathConnected (c ∪ D) := hc.2.2.1.union hD ⟨x, hxc, hxD⟩
  have heq : c ∪ D = c := hc.2.2.2 (c ∪ D) (union_subset hc.2.1 hDF) hunion subset_union_left
  exact subset_union_right.trans heq.subset

/-- Two arc-components of $F$ that share a point are equal. -/
theorem arcComponentsIn_eq_of_mem {c₁ c₂ : Set S}
    (hc₁ : c₁ ∈ arcComponentsIn F) (hc₂ : c₂ ∈ arcComponentsIn F)
    {x : S} (hx₁ : x ∈ c₁) (hx₂ : x ∈ c₂) : c₁ = c₂ := by
  have h12 : c₁ ⊆ c₂ :=
    subset_arcComponent_of_isPathConnected hc₂ hc₁.2.1 hc₁.2.2.1 ⟨x, hx₁, hx₂⟩
  have h21 : c₂ ⊆ c₁ :=
    subset_arcComponent_of_isPathConnected hc₁ hc₂.2.1 hc₂.2.2.1 ⟨x, hx₂, hx₁⟩
  exact Subset.antisymm h12 h21

/-- Distinct arc-components of $F$ are disjoint. -/
theorem arcComponentsIn_disjoint {c₁ c₂ : Set S}
    (hc₁ : c₁ ∈ arcComponentsIn F) (hc₂ : c₂ ∈ arcComponentsIn F) (hne : c₁ ≠ c₂) :
    Disjoint c₁ c₂ := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact hne (arcComponentsIn_eq_of_mem hc₁ hc₂ hx₁ hx₂)

theorem pathComponentIn_mem_arcComponentsIn {x : S} (hx : x ∈ F) :
    pathComponentIn F x ∈ arcComponentsIn F := by
  refine ⟨⟨x, mem_pathComponentIn_self hx⟩, pathComponentIn_subset,
    isPathConnected_pathComponentIn hx, ?_⟩
  intro D hDF hD hxD
  exact Subset.antisymm (hD.subset_pathComponentIn (hxD (mem_pathComponentIn_self hx)) hDF) hxD

/-- Every point of $F$ belongs to an arc-component of $F$. -/
theorem exists_mem_arcComponentsIn {x : S} (hx : x ∈ F) :
    ∃ c ∈ arcComponentsIn F, x ∈ c :=
  ⟨pathComponentIn F x, pathComponentIn_mem_arcComponentsIn hx, mem_pathComponentIn_self hx⟩

/-- The union of all arc-components of $F$ is $F$. -/
theorem sUnion_arcComponentsIn (F : Set S) : ⋃₀ arcComponentsIn F = F := by
  ext x
  constructor
  · rintro ⟨c, hc, hxc⟩
    exact hc.2.1 hxc
  · intro hx
    exact exists_mem_arcComponentsIn hx

/-- If a finite family $\mathcal{J}$ of nonempty, path-connected, pairwise disjoint subsets covers
$F$ and each $J \in \mathcal{J}$ satisfies $\bar{J} \cap F = J$, then
$\text{arcComponentsIn } F = \mathcal{J}$. -/
theorem arcComponentsIn_eq_of_finite_cover {𝒥 : Set (Set S)}
    (hfin : 𝒥.Finite)
    (hcov : ⋃₀ 𝒥 = F)
    (hne : ∀ J ∈ 𝒥, J.Nonempty)
    (hpc : ∀ J ∈ 𝒥, IsPathConnected J)
    (hdisj : ∀ J₁ ∈ 𝒥, ∀ J₂ ∈ 𝒥, J₁ ≠ J₂ → Disjoint J₁ J₂)
    (hclosed : ∀ J ∈ 𝒥, closure J ∩ F = J) :
    arcComponentsIn F = 𝒥 := by
  have hsubF : ∀ J ∈ 𝒥, J ⊆ F := fun J hJ => hcov ▸ subset_sUnion_of_mem hJ
  have hpre : ∀ {D : Set S} {J : Set S} {x : S},
      IsPreconnected D → D ⊆ F → J ∈ 𝒥 → x ∈ D → x ∈ J → D ⊆ J := by
    intro D J x hD hDF hJ hxD hxJ
    set B : Set S := ⋃ K ∈ 𝒥 \ {J}, closure K
    have hBcl : IsClosed B :=
      (hfin.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
    have hAcl : IsClosed (closure J) := isClosed_closure
    have hcover : D ⊆ closure J ∪ B := by
      intro y hyD
      have hyF : y ∈ ⋃₀ 𝒥 := hcov.symm ▸ hDF hyD
      rcases hyF with ⟨K, hK, hyK⟩
      by_cases hKJ : K = J
      · exact Or.inl (subset_closure (hKJ ▸ hyK))
      · exact Or.inr (mem_iUnion₂.mpr ⟨K, ⟨hK, hKJ⟩, subset_closure hyK⟩)
    have hnone : ¬ (D ∩ B).Nonempty := by
      intro ⟨z, hzD, hzB⟩
      obtain ⟨y, hyD, hyJ, hyB⟩ := isPreconnected_closed_iff.mp hD (closure J) B hAcl hBcl hcover
        ⟨x, hxD, subset_closure hxJ⟩ ⟨z, hzD, hzB⟩
      obtain ⟨K, ⟨hK, hKJ⟩, hyK⟩ := mem_iUnion₂.mp hyB
      have hyF : y ∈ F := hDF hyD
      have hyJ' : y ∈ J := by rw [← hclosed J hJ]; exact ⟨hyJ, hyF⟩
      have hyK' : y ∈ K := by rw [← hclosed K hK]; exact ⟨hyK, hyF⟩
      exact Set.disjoint_left.mp (hdisj K hK J hJ hKJ) hyK' hyJ'
    intro y hyD
    have hyJ : y ∈ closure J := (hcover hyD).resolve_right fun hyB => hnone ⟨y, hyD, hyB⟩
    rw [← hclosed J hJ]
    exact ⟨hyJ, hDF hyD⟩
  ext C
  constructor
  · rintro ⟨⟨x, hxC⟩, hCF, hCpc, hCmax⟩
    have hxF : x ∈ ⋃₀ 𝒥 := hcov.symm ▸ hCF hxC
    rcases hxF with ⟨J, hJ, hxJ⟩
    have hCJ : C ⊆ J := hpre hCpc.isConnected.isPreconnected hCF hJ hxC hxJ
    have heq : J = C := hCmax J (hsubF J hJ) (hpc J hJ) hCJ
    exact heq ▸ hJ
  · intro hJ
    refine ⟨hne C hJ, hsubF C hJ, hpc C hJ, fun D hDF hDpc hCD => ?_⟩
    rcases hne C hJ with ⟨x, hxC⟩
    exact Subset.antisymm (hpre hDpc.isConnected.isPreconnected hDF hJ (hCD hxC) hxC) hCD

end ArcComponents

/-! ## 3. Closed Discs with Finitely Many Points Removed and Lines -/

section DiscsAndLines

private theorem one_lt_finrank_euclideanPlane : 1 < Module.finrank ℝ EuclideanPlane := by
  simp [EuclideanPlane]

/-- Removing a countable subset from `ClosedUnitDisc` leaves a dense subset of `ClosedUnitDisc`. -/
theorem closure_closedUnitDisc_diff_of_countable {K : Set EuclideanPlane} (hK : K.Countable) :
    closure (ClosedUnitDisc \ K) = ClosedUnitDisc := by
  refine Subset.antisymm (closure_minimal sdiff_subset isClosed_closedBall) ?_
  have hsub : OpenUnitDisc ⊆ closure (OpenUnitDisc ∩ Kᶜ) :=
    (hK.dense_compl ℝ).open_subset_closure_inter isOpen_ball
  have hsub2 : closure (OpenUnitDisc ∩ Kᶜ) ⊆ closure (ClosedUnitDisc \ K) := by
    refine closure_mono fun x ⟨hxO, hxK⟩ => ⟨ball_subset_closedBall hxO, hxK⟩
  have hcl : closure OpenUnitDisc = ClosedUnitDisc :=
    closure_ball (0 : EuclideanPlane) one_ne_zero
  calc ClosedUnitDisc
    _ = closure OpenUnitDisc := hcl.symm
    _ ⊆ closure (closure (OpenUnitDisc ∩ Kᶜ)) := closure_mono hsub
    _ = closure (OpenUnitDisc ∩ Kᶜ) := closure_closure
    _ ⊆ closure (ClosedUnitDisc \ K) := hsub2

/-- Removing a countable subset from `ClosedUnitDisc` leaves a path-connected set. -/
theorem isPathConnected_closedUnitDisc_diff_of_countable {K : Set EuclideanPlane}
    (hK : K.Countable) : IsPathConnected (ClosedUnitDisc \ K) := by
  obtain ⟨a, haO, haK⟩ : (OpenUnitDisc ∩ Kᶜ).Nonempty :=
    (hK.dense_compl ℝ).inter_open_nonempty OpenUnitDisc isOpen_ball ⟨0, zero_mem_openUnitDisc⟩
  have ha : a ∈ ClosedUnitDisc \ K := ⟨ball_subset_closedBall haO, haK⟩
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  let c : EuclideanPlane := (2 : ℝ)⁻¹ • (a + b)
  let x : EuclideanPlane := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by simp only [c, x]; module
  have Ib : c + x = b := by simp only [c, x]; module
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y : EuclideanPlane, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_finrank one_lt_finrank_euclideanPlane x_ne_zero
  have hy_ne : y ≠ 0 := hy.ne_zero 1
  have hnorm_a : ‖a‖ < 1 := mem_ball_zero_iff.mp haO
  have hnorm_b : ‖b‖ ≤ 1 := mem_closedBall_zero_iff.mp hb.1
  have hnorm_c : ‖c‖ < 1 := by
    calc ‖c‖ = ‖(2 : ℝ)⁻¹ • (a + b)‖ := rfl
      _ = 2⁻¹ * ‖a + b‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ 2⁻¹ * (‖a‖ + ‖b‖) := mul_le_mul_of_nonneg_left (norm_add_le a b) (by positivity)
      _ < 2⁻¹ * (1 + 1) := by linarith
      _ = 1 := by norm_num
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ K).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun _ => inter_subset_right) hK
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ K = ∅ := by
      simpa only [singleton_inter_eq_empty, Ib] using hb.2
    rw [inter_assoc, inter_comm K, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ K).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun _ => inter_subset_right) hK
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ K = ∅ := by
      simpa only [singleton_inter_eq_empty, Ia] using ha.2
    rw [inter_assoc, inter_comm K, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  let r : ℝ := (1 - ‖c‖) / ‖y‖
  have hr : 0 < r := div_pos (sub_pos.mpr hnorm_c) (norm_pos_iff.mpr hy_ne)
  obtain ⟨t, htIoo, htAB⟩ :
      (Ioo (-r) r ∩ ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ K).Nonempty} ∪
        {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ K).Nonempty})ᶜ).Nonempty :=
    ((A.union B).dense_compl ℝ).inter_open_nonempty (Ioo (-r) r) isOpen_Ioo ⟨0, neg_lt_zero.mpr hr,
      hr⟩
  let z : EuclideanPlane := c + t • y
  have hz_mem : z ∈ ClosedUnitDisc := by
    rw [ClosedUnitDisc, mem_closedBall_zero_iff]
    have htabs : |t| < r := abs_lt.mpr htIoo
    have hty : ‖t • y‖ ≤ 1 - ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_lt_mul_of_pos_right htabs (norm_pos_iff.mpr hy_ne)).le.trans_eq
        (div_mul_cancel₀ (1 - ‖c‖) (norm_ne_zero_iff.mpr hy_ne))
    exact (norm_add_le c (t • y)).trans (by linarith)
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty]
    at htAB
  have JA : JoinedIn (ClosedUnitDisc \ K) a z := by
    apply JoinedIn.of_segment_subset
    intro p hp
    refine ⟨convex_closedUnitDisc.segment_subset ha.1 hz_mem hp, fun hpK => ?_⟩
    have hmem : p ∈ [c - x -[ℝ] z] ∩ K := ⟨by simpa [Ia] using hp, hpK⟩
    rw [htAB.2] at hmem
    exact hmem
  have JB : JoinedIn (ClosedUnitDisc \ K) b z := by
    apply JoinedIn.of_segment_subset
    intro p hp
    refine ⟨convex_closedUnitDisc.segment_subset hb.1 hz_mem hp, fun hpK => ?_⟩
    have hmem : p ∈ [c + x -[ℝ] z] ∩ K := ⟨by simpa [Ib] using hp, hpK⟩
    rw [htAB.1] at hmem
    exact hmem
  exact JA.trans JB.symm

variable {S : Type*} [TopologicalSpace S]

/-- Every closed disc in a topological space is compact. -/
theorem isCompact_of_isClosedDisc {Δ : Set S} (hΔ : IsClosedDisc Δ) : IsCompact Δ := by
  rcases hΔ with ⟨φ⟩
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have : CompactSpace Δ := φ.compactSpace
  exact isCompact_iff_compactSpace.mpr ‹CompactSpace Δ›

/-- Every closed disc in a T2 space is closed. -/
theorem isClosed_of_isClosedDisc [T2Space S] {Δ : Set S} (hΔ : IsClosedDisc Δ) : IsClosed Δ :=
  (isCompact_of_isClosedDisc hΔ).isClosed

/-- If $\Delta$ is a closed disc and $A \subseteq \Delta$ has $(\Delta \setminus A)$ finite,
then $A$ is path-connected. -/
theorem isPathConnected_of_isClosedDisc_finite_diff {Δ A : Set S}
    (hΔ : IsClosedDisc Δ) (hA : A ⊆ Δ) (hfin : (Δ \ A).Finite) :
    IsPathConnected A := by
  classical
  rcases hΔ with ⟨φ⟩
  set K : Set EuclideanPlane := Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (Δ \ A)))
  have hKfin : K.Finite := by
    have hsub : (Subtype.val ⁻¹' (Δ \ A) : Set Δ).Finite :=
      hfin.preimage Subtype.val_injective.injOn
    exact (hsub.preimage φ.injective.injOn).image Subtype.val
  have hpc := isPathConnected_closedUnitDisc_diff_of_countable hKfin.countable
  let f : EuclideanPlane → S := fun x =>
    if hx : x ∈ ClosedUnitDisc then (φ ⟨x, hx⟩).1 else (φ ⟨0, zero_mem_closedUnitDisc⟩).1
  have hf_cont : ContinuousOn f (ClosedUnitDisc \ K) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (ClosedUnitDisc \ K).domRestrict f =
        fun z : ↑(ClosedUnitDisc \ K) => (φ ⟨z.1, z.2.1⟩).1 := by
      ext z
      simp [f, z.2.1]
    rw [heq]
    exact continuous_subtype_val.comp (φ.continuous.comp (Continuous.subtype_mk
      continuous_subtype_val _))
  have himg : f '' (ClosedUnitDisc \ K) = A := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxD, hxK⟩, rfl⟩
      simp only [f, hxD, dite_true]
      by_contra hyA
      apply hxK
      exact ⟨⟨x, hxD⟩, ⟨(φ ⟨x, hxD⟩).2, hyA⟩, rfl⟩
    · intro hyA
      obtain ⟨z, hz⟩ := φ.surjective ⟨y, hA hyA⟩
      have hyz : (φ z).1 = y := congrArg Subtype.val hz
      refine ⟨z.1, ⟨z.2, ?_⟩, ?_⟩
      · rintro ⟨w, ⟨_, hwA⟩, hwz⟩
        have hw_eq : w = z := Subtype.ext hwz
        rw [hw_eq, hyz] at hwA
        exact hwA hyA
      · simp only [f, z.2, dite_true, hyz]
  rw [← himg]
  exact hpc.image' hf_cont

/-- If $\Delta$ is a closed disc in a T2 space and $A \subseteq \Delta$ has $(\Delta \setminus A)$
finite, then $\bar{A} = \Delta$. -/
theorem closure_eq_of_isClosedDisc_finite_diff [T2Space S] {Δ A : Set S}
    (hΔ : IsClosedDisc Δ) (hA : A ⊆ Δ) (hfin : (Δ \ A).Finite) :
    closure A = Δ := by
  refine Subset.antisymm (closure_minimal hA (isClosed_of_isClosedDisc hΔ)) ?_
  rcases hΔ with ⟨φ⟩
  set K : Set EuclideanPlane := Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' (Δ \ A)))
  have hKfin : K.Finite := by
    have hsub : (Subtype.val ⁻¹' (Δ \ A) : Set Δ).Finite :=
      hfin.preimage Subtype.val_injective.injOn
    exact (hsub.preimage φ.injective.injOn).image Subtype.val
  have hcl := closure_closedUnitDisc_diff_of_countable hKfin.countable
  intro y hyΔ
  obtain ⟨z, hz⟩ := φ.surjective ⟨y, hyΔ⟩
  have hyz : (φ z).1 = y := congrArg Subtype.val hz
  rw [_root_.mem_closure_iff]
  intro V hV hyV
  have hz_mem : z.1 ∈ closure (ClosedUnitDisc \ K) := by rw [hcl]; exact z.2
  let U : Set EuclideanPlane :=
    {x : EuclideanPlane | ∃ hx : x ∈ ClosedUnitDisc, (φ ⟨x, hx⟩).1 ∈ V}
  have hU_open_sub : IsOpen (Subtype.val ⁻¹' U : Set ClosedUnitDisc) := by
    have heq : (Subtype.val ⁻¹' U : Set ClosedUnitDisc) =
        (fun w : ClosedUnitDisc => (φ w).1) ⁻¹' V := by
      ext w
      simp [U]
    rw [heq]
    exact hV.preimage (continuous_subtype_val.comp φ.continuous)
  obtain ⟨W, hW_open, hW_eq⟩ := isOpen_induced_iff.mp hU_open_sub
  have hzW : z.1 ∈ W := by
    have hzU : z ∈ Subtype.val ⁻¹' U := ⟨z.2, by rw [hyz]; exact hyV⟩
    rw [← hW_eq] at hzU
    exact hzU
  obtain ⟨x, hxW, hxD, hxK⟩ := _root_.mem_closure_iff.mp hz_mem W hW_open hzW
  have hxU : (⟨x, hxD⟩ : ClosedUnitDisc) ∈ Subtype.val ⁻¹' U := by
    rw [← hW_eq]; exact hxW
  rcases hxU with ⟨_, hxV⟩
  refine ⟨(φ ⟨x, hxD⟩).1, hxV, ?_⟩
  by_contra hxA
  apply hxK
  exact ⟨⟨x, hxD⟩, ⟨(φ ⟨x, hxD⟩).2, hxA⟩, rfl⟩

/-- If $\Delta$ is a closed disc in a T2 space and $K$ is a finite set, then
$\widetilde{\Delta \setminus K} = \Delta \cap K$. -/
theorem tilde_diff_eq_of_isClosedDisc_finite [T2Space S] {Δ K : Set S}
    (hΔ : IsClosedDisc Δ) (hK : K.Finite) :
    tilde (Δ \ K) = Δ ∩ K := by
  have hfin : (Δ \ (Δ \ K)).Finite := hK.subset fun x hx => by
    simp only [mem_sdiff, not_and, not_not] at hx
    exact hx.2 hx.1
  have hcl : closure (Δ \ K) = Δ := closure_eq_of_isClosedDisc_finite_diff hΔ sdiff_subset hfin
  ext x
  simp only [tilde, hcl, mem_sdiff, mem_inter_iff, not_and, not_not]
  exact ⟨fun ⟨hxΔ, h⟩ => ⟨hxΔ, h hxΔ⟩, fun ⟨hxΔ, hxK⟩ => ⟨hxΔ, fun _ => hxK⟩⟩

/-- Symmetry of `IsLineWithEnds`: a line with ends $u$ and $v$ is also a line with ends $v$ and $u$.
-/
theorem isLineWithEnds_symm {L : Set S} {u v : S} (h : IsLineWithEnds L u v) :
    IsLineWithEnds L v u := by
  rcases h with ⟨f, hf0, hf1⟩
  let rev : unitInterval ≃ₜ unitInterval :=
    { toFun := unitInterval.symm
      invFun := unitInterval.symm
      left_inv := unitInterval.symm_symm
      right_inv := unitInterval.symm_symm
      continuous_toFun := unitInterval.continuous_symm
      continuous_invFun := unitInterval.continuous_symm }
  refine ⟨rev.trans f, ?_, ?_⟩
  · change (f (unitInterval.symm 0)).1 = v
    rw [unitInterval.symm_zero]
    exact hf1
  · change (f (unitInterval.symm 1)).1 = u
    rw [unitInterval.symm_one]
    exact hf0

/-- The two ends of a line are distinct. -/
theorem ne_of_isLineWithEnds {L : Set S} {u v : S} (h : IsLineWithEnds L u v) : u ≠ v := by
  rcases h with ⟨f, hf0, hf1⟩
  intro huv
  have h01 : f 0 = f 1 := Subtype.ext (hf0.trans (huv.trans hf1.symm))
  have : (0 : unitInterval) = 1 := f.injective h01
  exact zero_ne_one this

/-- Both ends of a line $L$ belong to $L$ and to `lineEnds L`. -/
theorem ends_subset_of_isLineWithEnds {L : Set S} {u v : S} (h : IsLineWithEnds L u v) :
    {u, v} ⊆ L ∧ {u, v} ⊆ lineEnds L := by
  rcases h with ⟨f, hf0, hf1⟩
  refine ⟨?_, ?_⟩
  · rintro x (rfl | rfl)
    · rw [← hf0]; exact (f 0).2
    · rw [← hf1]; exact (f 1).2
  · rintro x (rfl | rfl)
    · exact ⟨v, f, hf0, hf1⟩
    · exact ⟨u, isLineWithEnds_symm ⟨f, hf0, hf1⟩⟩

/-- The interior $L \setminus \{u, v\}$ of a line $L$ with ends $u, v$ is path-connected and
nonempty. -/
theorem isPathConnected_diff_ends_of_isLineWithEnds {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) :
    (L \ {u, v}).Nonempty ∧ IsPathConnected (L \ {u, v}) := by
  obtain ⟨f, hf0, hf1⟩ := hL
  have hIoo_ne : (Ioo (0 : ℝ) 1).Nonempty := ⟨1 / 2, by norm_num, by norm_num⟩
  have hIoo : IsPathConnected (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).isPathConnected hIoo_ne
  let g : ℝ → S := fun t => (f (projIcc 0 1 zero_le_one t)).1
  have hg : Continuous g :=
    continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
  have hEq : L \ {u, v} = g '' Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨hxL, hx⟩
      obtain ⟨t, ht⟩ := f.surjective ⟨x, hxL⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        apply hx
        have := congrArg Subtype.val ht
        simp only [hf0] at this
        simp [← this]
      have ht1 : t ≠ 1 := by
        rintro rfl
        apply hx
        have := congrArg Subtype.val ht
        simp only [hf1] at this
        simp [← this]
      have h0 : (0 : ℝ) < t.1 := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
      have h1 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
      refine ⟨t.1, ⟨h0, h1⟩, ?_⟩
      have : projIcc (0 : ℝ) 1 zero_le_one t.1 = t := projIcc_val zero_le_one t
      simp only [g, this, ht]
    · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
      have hmem : (f (projIcc 0 1 zero_le_one t)).1 ∈ L := (f _).2
      refine ⟨hmem, ?_⟩
      have hp : projIcc (0 : ℝ) 1 zero_le_one t = ⟨t, h0.le, h1.le⟩ :=
        projIcc_of_mem zero_le_one ⟨h0.le, h1.le⟩
      intro hx
      rcases hx with hx | hx
      · have : f (projIcc 0 1 zero_le_one t) = f 0 := Subtype.ext (hx.trans hf0.symm)
        have := f.injective this
        rw [hp] at this
        have := congrArg Subtype.val this
        simp only [Icc.coe_zero] at this
        linarith
      · have : f (projIcc 0 1 zero_le_one t) = f 1 :=
          Subtype.ext ((mem_singleton_iff.mp hx).trans hf1.symm)
        have := f.injective this
        rw [hp] at this
        have := congrArg Subtype.val this
        simp only [Icc.coe_one] at this
        linarith
  rw [hEq]
  exact ⟨hIoo_ne.image g, hIoo.image hg⟩

end DiscsAndLines

/-! ## 4. Foundational Lemmas for Paintings (`GM17.Painting`) -/

namespace Painting

variable {S : Type} [TopologicalSpace S] (Γ : Painting S)

theorem cell_nonempty {c : Set S} (hc : c ∈ Γ.C) : c.Nonempty :=
  hc.1

theorem cell_subset_diff {c : Set S} (hc : c ∈ Γ.C) : c ⊆ Γ.U \ Γ.N :=
  hc.2.1

theorem cell_subset_U {c : Set S} (hc : c ∈ Γ.C) : c ⊆ Γ.U :=
  (Γ.cell_subset_diff hc).trans sdiff_subset

theorem cell_disjoint_N {c : Set S} (hc : c ∈ Γ.C) : Disjoint c Γ.N :=
  Set.disjoint_left.mpr fun _ hx => (Γ.cell_subset_diff hc hx).2

theorem cell_isPathConnected {c : Set S} (hc : c ∈ Γ.C) : IsPathConnected c :=
  hc.2.2.1

theorem cell_eq_of_mem {c₁ c₂ : Set S} (hc₁ : c₁ ∈ Γ.C) (hc₂ : c₂ ∈ Γ.C)
    {x : S} (hx₁ : x ∈ c₁) (hx₂ : x ∈ c₂) : c₁ = c₂ :=
  arcComponentsIn_eq_of_mem hc₁ hc₂ hx₁ hx₂

theorem cell_disjoint {c₁ c₂ : Set S} (hc₁ : c₁ ∈ Γ.C) (hc₂ : c₂ ∈ Γ.C) (hne : c₁ ≠ c₂) :
    Disjoint c₁ c₂ :=
  arcComponentsIn_disjoint hc₁ hc₂ hne

theorem closure_cell_subset_U {c : Set S} (hc : c ∈ Γ.C) : closure c ⊆ Γ.U :=
  closure_minimal (Γ.cell_subset_U hc) Γ.isClosed_U

theorem isClosedDisc_closure_cell {c : Set S} (hc : c ∈ Γ.C) : IsClosedDisc (closure c) :=
  (Γ.cell_disc c hc).1

theorem tilde_subset_discBd {c : Set S} (hc : c ∈ Γ.C) : tilde c ⊆ discBd (closure c) :=
  (Γ.cell_disc c hc).2.1

theorem finite_tilde_cell {c : Set S} (hc : c ∈ Γ.C) : (tilde c).Finite :=
  (Γ.cell_disc c hc).2.2.1

theorem ncard_tilde_cell_le {c : Set S} (hc : c ∈ Γ.C) : (tilde c).ncard ≤ 3 :=
  (Γ.cell_disc c hc).2.2.2

/-- For any cell $c \in C(\Gamma)$ and any $x \in \bar{c}$, the set $c \cup \{x\}$ is
path-connected. -/
theorem isPathConnected_cell_insert {c : Set S} (hc : c ∈ Γ.C) {x : S} (hx : x ∈ closure c) :
    IsPathConnected (c ∪ {x}) := by
  have hsub : c ∪ {x} ⊆ closure c := union_subset subset_closure (singleton_subset_iff.mpr hx)
  have hfin : (closure c \ (c ∪ {x})).Finite :=
    (Γ.finite_tilde_cell hc).subset fun y hy => ⟨hy.1, fun hyc => hy.2 (Or.inl hyc)⟩
  exact isPathConnected_of_isClosedDisc_finite_diff (Γ.isClosedDisc_closure_cell hc) hsub hfin

/-- For every cell $c \in C(\Gamma)$, $\tilde{c} = \bar{c} \setminus c \subseteq N(\Gamma)$. -/
theorem tilde_subset_N {c : Set S} (hc : c ∈ Γ.C) : tilde c ⊆ Γ.N := by
  intro x ⟨hxcl, hxc⟩
  by_contra hxN
  have hxU : x ∈ Γ.U := Γ.closure_cell_subset_U hc hxcl
  have hsub : c ∪ {x} ⊆ Γ.U \ Γ.N :=
    union_subset (Γ.cell_subset_diff hc) (singleton_subset_iff.mpr ⟨hxU, hxN⟩)
  have hpc : IsPathConnected (c ∪ {x}) := Γ.isPathConnected_cell_insert hc hxcl
  have heq : c ∪ {x} = c := hc.2.2.2 (c ∪ {x}) hsub hpc subset_union_left
  have hx_in_c : x ∈ c := heq ▸ Or.inr rfl
  exact hxc hx_in_c

/-- For every cell $c \in C(\Gamma)$, $\bar{c} \setminus N(\Gamma) = c$. -/
theorem closure_cell_diff_N {c : Set S} (hc : c ∈ Γ.C) : closure c \ Γ.N = c := by
  ext x
  constructor
  · rintro ⟨hxcl, hxN⟩
    by_contra hxc
    exact hxN (Γ.tilde_subset_N hc ⟨hxcl, hxc⟩)
  · intro hxc
    exact ⟨subset_closure hxc, (Γ.cell_subset_diff hc hxc).2⟩

/-- For every cell $c \in C(\Gamma)$, $\bar{c} \cap N(\Gamma) = \tilde{c}$. -/
theorem closure_cell_inter_N {c : Set S} (hc : c ∈ Γ.C) : closure c ∩ Γ.N = tilde c := by
  ext x
  constructor
  · rintro ⟨hxcl, hxN⟩
    exact ⟨hxcl, fun hxc => (Γ.cell_subset_diff hc hxc).2 hxN⟩
  · intro hx
    exact ⟨hx.1, Γ.tilde_subset_N hc hx⟩

/-- For distinct cells $c_1, c_2 \in C(\Gamma)$, $\bar{c}_1 \cap \bar{c}_2 = \tilde{c}_1 \cap
\tilde{c}_2 \subseteq N(\Gamma)$. -/
theorem closure_cell_inter_closure_cell {c₁ c₂ : Set S}
    (hc₁ : c₁ ∈ Γ.C) (hc₂ : c₂ ∈ Γ.C) (hne : c₁ ≠ c₂) :
    closure c₁ ∩ closure c₂ = tilde c₁ ∩ tilde c₂ := by
  ext x
  constructor
  · rintro ⟨hx₁, hx₂⟩
    by_cases hxN : x ∈ Γ.N
    · rw [← Γ.closure_cell_inter_N hc₁, ← Γ.closure_cell_inter_N hc₂]
      exact ⟨⟨hx₁, hxN⟩, ⟨hx₂, hxN⟩⟩
    · have h1 : x ∈ c₁ := by rw [← Γ.closure_cell_diff_N hc₁]; exact ⟨hx₁, hxN⟩
      have h2 : x ∈ c₂ := by rw [← Γ.closure_cell_diff_N hc₂]; exact ⟨hx₂, hxN⟩
      exact False.elim (hne (Γ.cell_eq_of_mem hc₁ hc₂ h1 h2))
  · rintro ⟨hx₁, hx₂⟩
    exact ⟨hx₁.1, hx₂.1⟩

theorem sUnion_cells : ⋃₀ Γ.C = Γ.U \ Γ.N :=
  sUnion_arcComponentsIn (Γ.U \ Γ.N)

theorem U_eq_N_union_cells : Γ.U = Γ.N ∪ ⋃₀ Γ.C := by
  rw [Γ.sUnion_cells]
  ext x
  simp only [mem_union, mem_sdiff]
  constructor
  · intro hx
    by_cases h : x ∈ Γ.N
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  · rintro (h | ⟨h, _⟩)
    · exact Γ.N_subset h
    · exact h

theorem U_eq_N_union_biUnion_closure : Γ.U = Γ.N ∪ ⋃ c ∈ Γ.C, closure c := by
  refine Subset.antisymm ?_ ?_
  · rw [Γ.U_eq_N_union_cells]
    refine union_subset_union_right Γ.N ?_
    rintro x ⟨c, hc, hxc⟩
    exact mem_iUnion₂.mpr ⟨c, hc, subset_closure hxc⟩
  · exact union_subset Γ.N_subset (iUnion₂_subset fun c hc => Γ.closure_cell_subset_U hc)

/-- For every border cell $c \in C(\Gamma)$, there exist distinct nodes $u, v \in N(\Gamma) \cap
\operatorname{bd}(\Sigma)$
such that $\tilde{c} = \{u, v\}$, $\bar{c} \cap \operatorname{bd}(\Sigma)$ is a line with ends
$u, v$, and $c \cap \operatorname{bd}(\Sigma) = (\bar{c} \cap \operatorname{bd}(\Sigma)) \setminus
\{u, v\}$. -/
theorem border_cell_exists_ends {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    ∃ u v : S, u ≠ v ∧ tilde c = {u, v} ∧
      IsLineWithEnds (closure c ∩ bd S) u v ∧
      c ∩ bd S = (closure c ∩ bd S) \ {u, v} ∧
      u ∈ Γ.N ∩ bd S ∧ v ∈ Γ.N ∩ bd S := by
  obtain ⟨hncard, hfin, ⟨f⟩, hends⟩ := Γ.border_cell c hc hbd
  set L := closure c ∩ bd S
  let u : S := (f 0).1
  let v : S := (f 1).1
  have hL : IsLineWithEnds L u v := ⟨f, rfl, rfl⟩
  have huv : u ≠ v := ne_of_isLineWithEnds hL
  have hsub_L : {u, v} ⊆ L := (ends_subset_of_isLineWithEnds hL).1
  have hsub_tilde : {u, v} ⊆ tilde c := hends ▸ (ends_subset_of_isLineWithEnds hL).2
  have hpair_ncard : ({u, v} : Set S).ncard = 2 := ncard_pair huv
  have heq_tilde : {u, v} = tilde c :=
    eq_of_subset_of_ncard_le hsub_tilde (by omega) hfin
  have hdiff : c ∩ bd S = L \ {u, v} := by
    rw [heq_tilde]
    ext x
    simp only [L, tilde, mem_inter_iff, mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨hxc, hxbd⟩ => ⟨⟨subset_closure hxc, hxbd⟩, fun _ => hxc⟩,
      fun ⟨⟨hxcl, hxbd⟩, h⟩ => ⟨h hxcl, hxbd⟩⟩
  have huN : u ∈ Γ.N := Γ.tilde_subset_N hc (heq_tilde ▸ mem_insert u {v})
  have hvN : v ∈ Γ.N := Γ.tilde_subset_N hc (heq_tilde ▸ mem_insert_of_mem u rfl)
  have hubd : u ∈ bd S := (hsub_L (mem_insert u {v})).2
  have hvbd : v ∈ bd S := (hsub_L (mem_insert_of_mem u rfl)).2
  exact ⟨u, v, huv, heq_tilde.symm, hL, hdiff, ⟨huN, hubd⟩, ⟨hvN, hvbd⟩⟩

/-- If a cell $c \in C(\Gamma)$ meets a cuff $\Theta \in \text{cuffs } S$, then
$\bar{c} \cap \operatorname{bd}(\Sigma) \subseteq \Theta$, so $c$ borders no other cuff and
$\tilde{c} \subseteq N(\Gamma) \cap \Theta$. -/
theorem border_cell_subset_cuff {c Θ : Set S} (hc : c ∈ Γ.C) (hΘ : Θ ∈ cuffs S)
    (hinter : (c ∩ Θ).Nonempty) :
    closure c ∩ bd S ⊆ Θ ∧
    c ∩ bd S = c ∩ Θ ∧
    closure c ∩ bd S = closure c ∩ Θ ∧
    tilde c ⊆ Γ.N ∩ Θ ∧
    ∀ Θ' ∈ cuffs S, (c ∩ Θ').Nonempty → Θ' = Θ := by
  rcases hΘ with ⟨x₀, hx₀, rfl⟩
  have hΘ_sub : connectedComponentIn (bd S) x₀ ⊆ bd S := connectedComponentIn_subset (bd S) x₀
  have hbd : (c ∩ bd S).Nonempty := hinter.mono (inter_subset_inter_right c hΘ_sub)
  obtain ⟨u, v, _, htilde, ⟨f, _, _⟩, _, hu, hv⟩ := Γ.border_cell_exists_ends hc hbd
  have hconn_L : IsPreconnected (closure c ∩ bd S) := by
    have hrange : Set.range (fun t : unitInterval => (f t).1) = closure c ∩ bd S := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩; exact (f t).2
      · intro hz; exact ⟨f.symm ⟨z, hz⟩, congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)⟩
    rw [← hrange]
    exact isPreconnected_range (continuous_subtype_val.comp f.continuous)
  rcases hinter with ⟨y, hyc, hyΘ⟩
  have hyL : y ∈ closure c ∩ bd S := ⟨subset_closure hyc, hΘ_sub hyΘ⟩
  have hsubΘ : closure c ∩ bd S ⊆ connectedComponentIn (bd S) x₀ := by
    rw [connectedComponentIn_eq hyΘ]
    exact hconn_L.subset_connectedComponentIn hyL inter_subset_right
  have hc_eq : c ∩ bd S = c ∩ connectedComponentIn (bd S) x₀ := by
    refine Subset.antisymm (fun z ⟨hzc, hzbd⟩ => ⟨hzc, hsubΘ ⟨subset_closure hzc, hzbd⟩⟩) ?_
    exact inter_subset_inter_right c hΘ_sub
  have hcl_eq : closure c ∩ bd S = closure c ∩ connectedComponentIn (bd S) x₀ := by
    refine Subset.antisymm (fun z hz => ⟨hz.1, hsubΘ hz⟩) ?_
    exact inter_subset_inter_right (closure c) hΘ_sub
  have htilde_sub : tilde c ⊆ Γ.N ∩ connectedComponentIn (bd S) x₀ := by
    intro z hz
    have hz_bd : z ∈ bd S := by
      rw [htilde] at hz
      rcases hz with rfl | rfl
      · exact hu.2
      · exact hv.2
    exact ⟨Γ.tilde_subset_N hc hz, hsubΘ ⟨hz.1, hz_bd⟩⟩
  refine ⟨hsubΘ, hc_eq, hcl_eq, htilde_sub, ?_⟩
  rintro Θ' ⟨x₁, _, rfl⟩ ⟨w, hwc, hwΘ'⟩
  have hwbd : w ∈ bd S := connectedComponentIn_subset (bd S) x₁ hwΘ'
  have hwΘ : w ∈ connectedComponentIn (bd S) x₀ := hsubΘ ⟨subset_closure hwc, hwbd⟩
  exact (connectedComponentIn_eq hwΘ').trans (connectedComponentIn_eq hwΘ).symm

/-- Every point of $\operatorname{bd}(\Sigma) \setminus N(\Gamma)$ belongs to a unique border cell
$c \in C(\Gamma)$. -/
theorem exists_border_cell_of_mem_bd {x : S} (hx : x ∈ bd S \ Γ.N) :
    ∃! c, c ∈ Γ.C ∧ x ∈ c := by
  have hxU : x ∈ Γ.U \ Γ.N := ⟨Γ.bd_subset hx.1, hx.2⟩
  obtain ⟨c, hc, hxc⟩ := exists_mem_arcComponentsIn hxU
  refine ⟨c, ⟨hc, hxc⟩, ?_⟩
  rintro c' ⟨hc', hxc'⟩
  exact Γ.cell_eq_of_mem hc' hc hxc' hxc

end Painting

end GraphMinor.GM17
