/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Open
public import LeanPool.GraphMinor.GM07.Section9MoveOff
import LeanPool.GraphMinor.GM07.Section5a
import LeanPool.GraphMinor.GM07.DiscChain
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM12.Section3OneDiscComplement
import LeanPool.GraphMinor.GM12.Section3PuncturedModel
import LeanPool.GraphMinor.GM12.Section3CapOneDisc
import LeanPool.GraphMinor.GM12.Section3CapComparison
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.Surface.CutIArc

/-!
# Reductions from Sphere to Disc and Disc to Cylinder (Graph Minors VII, (9.4)–(9.5))

This file proves `sphereToDiscReduction` ((9.5) from (9.4), page 246) and
`discToCylinderReduction` ((9.4) from (9.3), page 246), formalizing each claim of the
paper's proofs as a lemma.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12

universe u

/-- Membership in `discComplement Δ` is equivalent to avoiding `discInt (Δ i)` for every `i`. -/
theorem mem_discComplement_iff {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) (x : S) :
    x ∈ discComplement Δ ↔ ∀ i, x ∉ discInt (Δ i) := by
  constructor
  · intro hx i hxi
    exact hxi.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨hx, hxi.1⟩)
  · intro h
    by_cases hxU : x ∈ ⋃ i, Δ i
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxU
      have hxb : x ∈ discBd (Δ i) := by
        by_contra hnb
        exact h i ⟨hxi, hnb⟩
      exact disc_boundary_subset_discComplement hS Δ hΔ hdisj i hxb
    · exact subset_closure hxU

/-- A sphere `S` is a closed connected surface. -/
theorem closedSurface_and_connected_of_isSphere {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (hSph : IsSphere S) :
    bd S = ∅ ∧ IsClosedSurface S ∧ ConnectedSpace S ∧ Nonempty (S ≃ₜ SurfaceModel 0 0 0) := by
  have hbd : bd S = ∅ := by
    by_contra hbd_ne
    exact not_isSphere_of_bd_ne_empty hbd_ne hSph
  have hCS : IsClosedSurface S :=
    ⟨hS.1, hS.2.1, fun x => by
      by_contra hn
      have : x ∈ bd S := hn
      rw [hbd] at this
      exact this⟩
  obtain ⟨φ⟩ := hSph
  obtain ⟨s₀⟩ := isSphere_model_zero
  have : ConnectedSpace (SurfaceModel 0 0 0) := (isSurface_model 0 0 0).2
  let e : SurfaceModel 0 0 0 ≃ₜ S := s₀.trans φ.symm
  have hconn : ConnectedSpace S := e.surjective.connectedSpace e.continuous
  exact ⟨hbd, hCS, hconn, ⟨e.symm⟩⟩

/-- **Graph Minors VII, (9.5), Claim 1** (page 246):
In the proof of (9.5) ("Choose a closed disc $\Delta \subseteq \Sigma$ with $\Delta \cap F_2 =
\emptyset$
and $\Delta \cap U(G) = \emptyset$, such that $\Delta$ and $F_1$ lie in different components of
$\Sigma - F_2$"), there exist closed discs $\Delta_1, \Delta_2 \subseteq \Sigma$ with
$\Delta_1 \cup \Delta_2 = \Sigma$ and $\Delta_1 \cap \Delta_2 = \mathrm{bd}(\Delta_1) =
\mathrm{bd}(\Delta_2) = F_2$
such that $F_1 \subseteq \mathrm{int}(\Delta_1)$. -/
theorem lemma_9_5_claim_1 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (hSph : IsSphere S)
    {F₁ F₂ : Set S} (hO₁ : IsOArc F₁) (hO₂ : IsOArc F₂) (hDisj : Disjoint F₁ F₂) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      Δ₁ ∪ Δ₂ = univ ∧ Δ₁ ∩ Δ₂ = F₂ ∧
      discBd Δ₁ = F₂ ∧ discBd Δ₂ = F₂ ∧
      F₁ ⊆ discInt Δ₁ ∧ Disjoint F₁ Δ₂ := by
  have : T2Space S := hS.2.1
  obtain ⟨A, B, -, hA, hB, hbA, hbB, hcup, hcap, -, -⟩ := sphere_disc S hSph F₂ hO₂
  have hconn₁ : IsPreconnected F₁ := hO₁.isPreconnected
  rcases hA.side hS.2.2 hconn₁ (hbA.symm ▸ hDisj) with hin | hout
  · refine ⟨A, B, hA, hB, hcup, hcap, hbA, hbB, hin, disjoint_left.mpr fun x hx₁ hxB => ?_⟩
    have hxA := hin hx₁
    have hxF₂ : x ∈ F₂ := hcap ▸ ⟨hxA.1, hxB⟩
    exact hxA.2 (hbA.symm ▸ hxF₂)
  · refine ⟨B, A, hB, hA, union_comm A B ▸ hcup, inter_comm A B ▸ hcap, hbB, hbA,
      fun x hx₁ => ⟨?_, ?_⟩, hout⟩
    · have hxU : x ∈ A ∪ B := hcup ▸ mem_univ x
      exact hxU.resolve_left (disjoint_left.mp hout hx₁)
    · rw [hbB]
      exact disjoint_left.mp hDisj hx₁

/-- **Graph Minors VII, (9.5), Claim 2** (page 246):
In the closed disc $\Sigma' = \Sigma - \mathrm{int}(\Delta)$ obtained by removing the interior of a
closed disc $\Delta \subseteq \Delta_2 - F_2$, the lifted $O$-arc $F_1'$ is inside $F_2'$, witnessed
by the preimage of $\Delta_1$. -/
theorem lemma_9_5_claim_2 {S : Type u} [TopologicalSpace S]
    {F₁ F₂ Δ₁ Δ : Set S} (hO₂ : IsOArc F₂) (hΔ₁ : IsClosedDisc Δ₁)
    (hb₁ : discBd Δ₁ = F₂) (hF₁_in : F₁ ⊆ discInt Δ₁)
    (hΔ₁_sub : Δ₁ ⊆ discComplement ![Δ]) :
    let C_sub := discComplement ![Δ]
    IsInsideOArc (liftEdge id C_sub F₁) (liftEdge id C_sub F₂) := by
  intro C_sub x hx
  have hF₂_sub : F₂ ⊆ C_sub := hb₁ ▸ (Surface.discBd_subset Δ₁).trans hΔ₁_sub
  have hF₂'_eq : liftEdge id C_sub F₂ = (Subtype.val : C_sub → S) ⁻¹' F₂ := by
    simp [liftEdge]
  obtain ⟨hΔ₁'_disc, hΔ₁'_bd⟩ := isClosedDisc_subtype_preimage hΔ₁_sub hΔ₁
  rw [hb₁, ← hF₂'_eq] at hΔ₁'_bd
  have hO₂' : IsOArc (liftEdge id C_sub F₂) :=
    isOArc_liftEdge IsEmbedding.id (by simpa using hF₂_sub) hO₂
  have hnull : IsNullHomotopicOArc (liftEdge id C_sub F₂) :=
    isNullHomotopicOArcIn_of_subset_disc hO₂' (subset_univ _) hΔ₁'_disc
      (hΔ₁'_bd ▸ Surface.discBd_subset _)
  left
  refine ⟨hnull, (Subtype.val : C_sub → S) ⁻¹' Δ₁, hΔ₁'_disc, hΔ₁'_bd, ?_⟩
  have hxF₁ : x.val ∈ F₁ := by simpa [liftEdge] using hx
  have hx_in := hF₁_in hxF₁
  refine ⟨hx_in.1, ?_⟩
  rw [hF₂'_eq]
  exact hb₁ ▸ hx_in.2

/-- **Graph Minors VII, proof of (9.5) from (9.4)** (page 246):
"Choose a closed disc $\Delta \subseteq \Sigma$ with $\Delta \cap F_2 = \emptyset$ and
$\Delta \cap U(G) = \emptyset$, such that $\Delta$ and $F_1$ lie in different components of
$\Sigma - F_2$. The result follows by applying (9.4) to the surface obtained from $\Sigma$ by
removing the interior of $\Delta$, and to an isomorphic copy of $(H, H^+, H^-)$ in this surface." -/
theorem sphereToDiscReduction :
    ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
      IsSurface S → IsSphere S →
      ∀ H G : SurfaceDigraph S, H.IsProper → G.IsProper →
        ∀ F₁ F₂ : Set S,
          G.G.IsNormal F₁ → G.G.IsNormal F₂ →
          IsOArc F₁ → IsOArc F₂ → Disjoint F₁ F₂ →
          (∀ F : Set S, G.G.IsNormal F → IsLine F →
            (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
            2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard) →
          rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂ →
          ∃ (S' : Type u) (_ : TopologicalSpace S') (_ : T1Space S')
            (C : Set S') (H' G' : SurfaceDigraph S') (F₁' F₂' : Set S'),
            IsSurface S' ∧ IsClosedDisc (univ : Set S') ∧
            cuffs S' = {C} ∧
            H'.IsProper ∧ G'.IsProper ∧ G'.G.V ∩ bd S' = H'.G.V ∩ bd S' ∧
            G'.G.IsNormal F₁' ∧ G'.G.IsNormal F₂' ∧
            IsOArc F₁' ∧ IsOArc F₂' ∧ Disjoint F₁' F₂' ∧
            IsInsideOArc F₁' F₂' ∧ Disjoint F₂' (bd S') ∧
            (∀ F : Set S', G'.G.IsNormal F → IsLine F →
              (F ∩ F₁').Nonempty → (F ∩ F₂').Nonempty →
              2 * (rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard)) ≤ (G'.G.V ∩ F).ncard) ∧
            rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard) ≤ maxDisjointPaths G'.G F₁' F₂'
              ∧
            (G'.G.V ∩ C).ncard ≤ maxDisjointPaths G'.G F₁' C ∧
            (IsBoundaryRootedMinor H' G' → IsBoundaryRootedMinor H G) := by
  intro S _ _ hS hSph H G hH hG F₁ F₂ hF₁ hF₂ hO₁ hO₂ hDisj hLine hk12
  classical
  have : T2Space S := hS.2.1
  obtain ⟨hbdS, hCS, hconnS, _⟩ := closedSurface_and_connected_of_isSphere hS hSph
  have : ConnectedSpace S := hconnS
  have : Nonempty S := hO₂.elim fun f => ⟨(f 1).val⟩
  obtain ⟨Δ₁, Δ₂, hΔ₁, hΔ₂, hcup, hcap, hb₁, hb₂, hF₁_in, hF₁_disj_Δ₂⟩ :=
    lemma_9_5_claim_1 hS hSph hO₁ hO₂ hDisj
  have hΔ₂_bd : Δ₂ ∩ bd S = ∅ := by simp [hbdS]
  obtain ⟨Δ, hΔ, hΔ_in_Δ₂, hΔ_disj_G⟩ :=
    exists_subdisc_disjoint_drawing hS G.G hΔ₂ hΔ₂_bd
  have hΔ_bd : Δ ∩ bd S = ∅ := by simp [hbdS]
  obtain ⟨β, hβ_fix, hΔ_disj_H⟩ := exists_move_drawing_off_disc hS H.G hΔ hΔ_bd
  let P : Fin 1 → Set S := ![Δ]
  have hP : ∀ i, IsClosedDisc (P i) := fun i => by fin_cases i; exact hΔ
  have hP_disj : Pairwise (fun i j => Disjoint (P i) (P j)) := fun i j hij => by
    fin_cases i; fin_cases j; exact (hij rfl).elim
  let C_sub : Set S := discComplement P
  let S' : Type u := ↥C_sub
  have hS' : IsSurface S' := discComplement_isSurface hCS P hP hP_disj
  have : T2Space S' := hS'.2.1
  have hDiscS' : IsClosedDisc (univ : Set S') := by
    obtain ⟨φ⟩ := isClosedDiscSpace_discComplement_one hCS hSph P hP
    exact ⟨φ.trans (Homeomorph.Set.univ S').symm⟩
  let C : Set S' := (Subtype.val : S' → S) ⁻¹' discBd Δ
  have hcuffs' : cuffs S' = {C} := by
    rw [discComplement_cuffs_eq hCS P hP hP_disj]
    ext X
    simp only [mem_range, Fin.exists_fin_one, mem_singleton_iff]
    exact eq_comm
  have hbdS' : bd S' = C := by
    rw [discComplement_boundary_eq hCS P hP]
    ext x
    simp [P, C]
  have : Nonempty S' := (Subtype.connectedSpace (discComplement_isConnected hCS P hP
    hP_disj)).toNonempty
  have hUC_H : (embedDrawing β.isClosedEmbedding H.G).U ⊆ C_sub := by
    rintro y ⟨x, hxU, rfl⟩
    rw [mem_discComplement_iff hCS P hP hP_disj]
    intro i
    fin_cases i
    intro hxΔ
    exact disjoint_left.mp hΔ_disj_H ⟨x, hxU, rfl⟩ hxΔ.1
  have hUC_G : (embedDrawing IsClosedEmbedding.id G.G).U ⊆ C_sub := by
    rintro y ⟨x, hxU, rfl⟩
    rw [mem_discComplement_iff hCS P hP hP_disj]
    intro i
    fin_cases i
    intro hxΔ
    exact disjoint_left.mp hΔ_disj_G hxΔ.1 hxU
  let H' : SurfaceDigraph S' := liftSurfaceDigraph β.isClosedEmbedding H C_sub hUC_H
  let G' : SurfaceDigraph S' := liftSurfaceDigraph IsClosedEmbedding.id G C_sub hUC_G
  have hH'_bd_U : bd S' ∩ H'.G.U = ∅ := by
    rw [hbdS', eq_empty_iff_forall_notMem]
    rintro x ⟨hxC, hxU⟩
    rw [show H'.G = drawingInSubspace (embedDrawing β.isClosedEmbedding H.G) C_sub hUC_H from rfl,
      drawingInSubspace_embedDrawing_U] at hxU
    obtain ⟨z, hzU, hβz⟩ := hxU
    exact disjoint_left.mp hΔ_disj_H ⟨z, hzU, hβz⟩ (Surface.discBd_subset Δ hxC)
  have hG'_bd_U : bd S' ∩ G'.G.U = ∅ := by
    rw [hbdS', eq_empty_iff_forall_notMem]
    rintro x ⟨hxC, hxU⟩
    rw [show G'.G = drawingInSubspace (embedDrawing IsClosedEmbedding.id G.G) C_sub hUC_G from rfl,
      drawingInSubspace_embedDrawing_U] at hxU
    obtain ⟨z, hzU, hfz⟩ := hxU
    have hxz : x.val = z := hfz.symm
    exact disjoint_left.mp hΔ_disj_G (Surface.discBd_subset Δ hxC) (hxz ▸ hzU)
  have hH'_prop : H'.IsProper := by
    change bd S' ∩ H'.G.U ⊆ H'.G.V
    rw [hH'_bd_U]
    exact empty_subset _
  have hG'_prop : G'.IsProper := by
    change bd S' ∩ G'.G.U ⊆ G'.G.V
    rw [hG'_bd_U]
    exact empty_subset _
  have hH'_bd_V : H'.G.V ∩ bd S' = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxV, hxBd⟩
    have : x ∈ bd S' ∩ H'.G.U := ⟨hxBd, H'.G.V_subset_U hxV⟩
    rw [hH'_bd_U] at this
    exact this
  have hG'_bd_V : G'.G.V ∩ bd S' = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxV, hxBd⟩
    have : x ∈ bd S' ∩ G'.G.U := ⟨hxBd, G'.G.V_subset_U hxV⟩
    rw [hG'_bd_U] at this
    exact this
  have hbd_eq' : G'.G.V ∩ bd S' = H'.G.V ∩ bd S' := by rw [hG'_bd_V, hH'_bd_V]
  have hΔ₁_disj_Δ : Disjoint Δ₁ Δ := by
    rw [disjoint_left]
    intro x hx₁ hxΔ
    have hx₂ := hΔ_in_Δ₂ hxΔ
    have hxF₂ : x ∈ F₂ := hcap ▸ ⟨hx₁, hx₂.1⟩
    exact hx₂.2 (hb₂.symm ▸ hxF₂)
  have hΔ₁_sub : Δ₁ ⊆ C_sub := by
    intro x hx₁
    rw [mem_discComplement_iff hCS P hP hP_disj]
    intro i
    fin_cases i
    intro hxΔ
    exact disjoint_left.mp hΔ₁_disj_Δ hx₁ hxΔ.1
  have hF₁_sub : F₁ ⊆ C_sub := (hF₁_in.trans (discInt_subset Δ₁)).trans hΔ₁_sub
  have hF₂_sub : F₂ ⊆ C_sub := hb₁ ▸ (Surface.discBd_subset Δ₁).trans hΔ₁_sub
  let F₁' : Set S' := liftEdge id C_sub F₁
  let F₂' : Set S' := liftEdge id C_sub F₂
  have hF₁'_norm : G'.G.IsNormal F₁' :=
    drawingInSubspace_embedDrawing_isNormal_liftEdge IsClosedEmbedding.id G.G C_sub hUC_G hF₁
  have hF₂'_norm : G'.G.IsNormal F₂' :=
    drawingInSubspace_embedDrawing_isNormal_liftEdge IsClosedEmbedding.id G.G C_sub hUC_G hF₂
  have hO₁' : IsOArc F₁' := isOArc_liftEdge IsEmbedding.id (by simpa using hF₁_sub) hO₁
  have hO₂' : IsOArc F₂' := isOArc_liftEdge IsEmbedding.id (by simpa using hF₂_sub) hO₂
  have hDisj' : Disjoint F₁' F₂' := disjoint_liftEdge injective_id C_sub hDisj
  have hInside' : IsInsideOArc F₁' F₂' := lemma_9_5_claim_2 hO₂ hΔ₁ hb₁ hF₁_in hΔ₁_sub
  have hbd₂' : Disjoint F₂' (bd S') := by
    rw [hbdS', disjoint_left]
    rintro x ⟨z, hzF₂, hzx⟩ hxC
    have hxz : x.val = z := hzx.symm
    have hzΔ₁ : z ∈ Δ₁ := Surface.discBd_subset Δ₁ (hb₁.symm ▸ hzF₂)
    have hzΔ : z ∈ Δ := hxz ▸ Surface.discBd_subset Δ hxC
    exact disjoint_left.mp hΔ₁_disj_Δ hzΔ₁ hzΔ
  have hH'_V_ncard : H'.G.V.ncard = H.G.V.ncard :=
    drawingInSubspace_embedDrawing_V_ncard β.isClosedEmbedding H.G C_sub hUC_H
  have hH'_E_ncard : H'.G.E.ncard = H.G.E.ncard :=
    drawingInSubspace_embedDrawing_E_ncard β.isClosedEmbedding H.G C_sub hUC_H
  have hr_eq : rCylinderBound H'.G = rCylinderBound H.G := by
    simp only [rCylinderBound, hH'_V_ncard, hH'_E_ncard]
  refine ⟨S', inferInstance, inferInstance, C, H', G', F₁', F₂',
    hS', hDiscS', hcuffs', hH'_prop, hG'_prop, hbd_eq',
    hF₁'_norm, hF₂'_norm, hO₁', hO₂', hDisj', hInside', hbd₂',
    ?_, ?_, ?_, ?_⟩
  · intro F' hF'_norm hF'_line hF'₁ hF'₂
    rw [hr_eq, hH'_V_ncard, hH'_E_ncard,
      show G'.G = drawingInSubspace (embedDrawing IsClosedEmbedding.id G.G) C_sub hUC_G from rfl,
      drawingInSubspace_embedDrawing_V_inter_unliftEdge_ncard]
    apply hLine (unliftEdge id C_sub F')
    · exact drawingInSubspace_embedDrawing_isNormal_unliftEdge IsClosedEmbedding.id G.G C_sub
        hUC_G hF'_norm
    · exact isLine_unliftEdge IsEmbedding.id (by simp) hF'_line
    · obtain ⟨x, hxF', z, hzF₁, hzx⟩ := hF'₁
      exact ⟨z, ⟨x, hxF', hzx.symm⟩, hzF₁⟩
    · obtain ⟨x, hxF', z, hzF₂, hzx⟩ := hF'₂
      exact ⟨z, ⟨x, hxF', hzx.symm⟩, hzF₂⟩
  · rw [hr_eq, hH'_V_ncard, hH'_E_ncard]
    exact hk12.trans (maxDisjointPaths_le_liftEdge IsClosedEmbedding.id G.G C_sub hUC_G F₁ F₂)
  · have hC_empty : G'.G.V ∩ C = ∅ := hbdS' ▸ hG'_bd_V
    rw [hC_empty, Set.ncard_empty]
    exact Nat.zero_le _
  · intro hminor'
    exact isBoundaryRootedMinor_of_lift β.isClosedEmbedding IsClosedEmbedding.id H G C_sub
      hUC_H hUC_G (by simp [hbdS]) (fun x hx => by rw [hbdS] at hx; exact hx.elim)
      (fun v hv => by rw [hbdS] at hv; exact hv.2.elim) hminor'

/-! ### Reduction from Closed Disc to Cylinder ((9.4) from (9.3), page 246) -/

/-- **Graph Minors VII, (9.4), Claim 1** (page 246):
In a closed disc `Σ` with disjoint `O`-arcs `F₁, F₂` such that `F₁` is inside `F₂` and
`Disjoint F₂ (bd Σ)`, `F₁` and `F₂` bound closed discs `Δ₁ ⊆ discInt Δ₂` with
`Disjoint Δ₂ (bd Σ)`. -/
theorem lemma_9_4_claim_1 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (hD : IsClosedDisc (univ : Set S))
    {F₁ F₂ : Set S} (hO₁ : IsOArc F₁) (hO₂ : IsOArc F₂) (hDisj : Disjoint F₁ F₂)
    (hInside : IsInsideOArc F₁ F₂) (hbd₂ : Disjoint F₂ (bd S)) :
    ∃ Δ₁ Δ₂ : Set S, IsClosedDisc Δ₁ ∧ discBd Δ₁ = F₁ ∧
      IsClosedDisc Δ₂ ∧ discBd Δ₂ = F₂ ∧
      Δ₁ ⊆ discInt Δ₂ ∧ Disjoint Δ₂ (bd S) := by
  have : T2Space S := hS.2.1
  obtain ⟨x₀, hx₀⟩ : F₁.Nonempty := hO₁.elim fun φ => ⟨(φ 1).1, (φ 1).2⟩
  have hx₀_null : IsPointInsideNullOArc F₂ x₀ := by
    rcases hInside x₀ hx₀ with hnull | ⟨C', _, hsurr⟩
    · exact hnull
    · exact (hsurr.2.1.2.2 ⟨univ, hD, subset_univ F₂⟩).elim
  obtain ⟨_, Δ₂, hΔ₂, hb₂, hx₀_in⟩ := hx₀_null
  have hF₁_in : F₁ ⊆ discInt Δ₂ := by
    rcases hΔ₂.side hS.2.2 hO₁.isPreconnected (hb₂.symm ▸ hDisj) with hin | hout
    · exact hin
    · exact (disjoint_left.mp hout hx₀ hx₀_in.1).elim
  obtain ⟨Δ₁, ⟨hΔ₁_sub, hΔ₁, hb₁, -, hΔ₁_disj_bd, -⟩, -⟩ :=
    disc_oArc Δ₂ F₁ hΔ₂ (hF₁_in.trans (discInt_subset Δ₂)) hO₁
  have hΔ₁_in_Δ₂ : Δ₁ ⊆ discInt Δ₂ := by
    intro x hx
    by_cases hxF₁ : x ∈ F₁
    · exact hF₁_in hxF₁
    · exact ⟨hΔ₁_sub hx, disjoint_left.mp hΔ₁_disj_bd ⟨hx, hxF₁⟩⟩
  obtain ⟨Δ₂', ⟨-, hΔ₂', hb₂', -, hΔ₂'_disj_bd, -⟩, huniq⟩ :=
    disc_oArc univ F₂ hD (subset_univ F₂) hO₂
  have hΔ₂_eq : Δ₂ = Δ₂' := huniq Δ₂ (subset_univ Δ₂) hΔ₂ hb₂
  have hdiscBd_univ : discBd (univ : Set S) = bd S := by
    simpa [discBd, Homeomorph.Set.univ] using image_bd_homeomorph (Homeomorph.Set.univ S)
  have hΔ₂_disj_bd : Disjoint Δ₂ (bd S) := by
    rw [← hdiscBd_univ, disjoint_left]
    intro x hxΔ₂ hxbd
    by_cases hxF₂ : x ∈ F₂
    · exact disjoint_left.mp hbd₂ hxF₂ (hdiscBd_univ ▸ hxbd)
    · exact disjoint_left.mp hΔ₂'_disj_bd ⟨hΔ₂_eq ▸ hxΔ₂, hxF₂⟩ hxbd
  exact ⟨Δ₁, Δ₂, hΔ₁, hb₁, hΔ₂, hb₂, hΔ₁_in_Δ₂, hΔ₂_disj_bd⟩

/-- In a closed sphere `Z`, every closed disc `A` has a complementary closed disc `E = (discInt A)ᶜ`
with `discBd E = discBd A` and `discInt E = Aᶜ`. -/
theorem exists_compl_disc_in_sphere {Z : Type u} [TopologicalSpace Z]
    (hSph : IsSphere Z) {A : Set Z} (hA : IsClosedDisc A) :
    ∃ E : Set Z, IsClosedDisc E ∧ discBd E = discBd A ∧
      E = (discInt A)ᶜ ∧ discInt E = Aᶜ := by
  obtain ⟨D₁, D₂, -, hD₁, hD₂, hb₁, hb₂, hcup, hcap, -, huniq⟩ :=
    sphere_disc Z hSph (discBd A) hA.isOArc_discBd
  have hex : ∃ E : Set Z, IsClosedDisc E ∧ discBd E = discBd A ∧
      A ∪ E = univ ∧ A ∩ E = discBd A := by
    rcases huniq A hA rfl with rfl | rfl
    · exact ⟨D₂, hD₂, hb₂, hcup, hcap⟩
    · exact ⟨D₁, hD₁, hb₁, union_comm D₁ A ▸ hcup, inter_comm D₁ A ▸ hcap⟩
  obtain ⟨E, hE, hbE, hU, hI⟩ := hex
  refine ⟨E, hE, hbE, ?_, ?_⟩
  · ext z
    simp only [mem_compl_iff, discInt, mem_sdiff, not_and, not_not]
    constructor
    · intro hzE hzA
      exact hI ▸ ⟨hzA, hzE⟩
    · intro h
      rcases (hU ▸ mem_univ z : z ∈ A ∪ E) with hzA | hzE
      · exact Surface.discBd_subset E (hbE.symm ▸ h hzA)
      · exact hzE
  · ext z
    simp only [discInt, hbE, mem_sdiff, mem_compl_iff]
    constructor
    · rintro ⟨hzE, hnb⟩ hzA
      exact hnb (hI ▸ ⟨hzA, hzE⟩)
    · intro hnzA
      refine ⟨(hU ▸ mem_univ z : z ∈ A ∪ E).resolve_left hnzA, fun hzb => ?_⟩
      exact hnzA (Surface.discBd_subset A hzb)

/-- Homeomorphism invariance of `IsPointInsideNullOArc`. -/
theorem isPointInsideNullOArc_image_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {F : Set X} {x : X} (h : IsPointInsideNullOArc F x) :
    IsPointInsideNullOArc (e '' F) (e x) := by
  obtain ⟨_, Δ, hΔ, hbd, hxΔ, hxF⟩ := h
  obtain ⟨hΔ', hbd'⟩ := hΔ.image e.continuous.continuousOn e.symm.continuous.continuousOn
    (fun z _ => e.symm_apply_apply z)
  rw [hbd] at hbd'
  have hO' : IsOArc (e '' F) := hbd' ▸ hΔ'.isOArc_discBd
  have hnull' : IsNullHomotopicOArc (e '' F) :=
    isNullHomotopicOArcIn_of_subset_disc hO' (subset_univ _) hΔ'
      (hbd' ▸ Surface.discBd_subset _)
  refine ⟨hnull', e '' Δ, hΔ', hbd', ⟨x, hxΔ, rfl⟩, ?_⟩
  rintro ⟨z, hzF, hze⟩
  exact hxF (e.injective hze ▸ hzF)

/-- If `IsPointInsideNullOArc (j₁ '' F) (j₁ x)` holds in one cap `(S₁, j₁, D₁)` of a cuff `C`, then
`IsPointInsideSurroundingOArc C F x` holds. -/
theorem isPointInsideSurroundingOArc_of_one_cap {S S₁ : Type u}
    [TopologicalSpace S] [TopologicalSpace S₁]
    (hS : IsSurface S) {C F : Set S} {x : S} (hO : IsOArc F) (hSurr : SurroundsCuff F C)
    {j₁ : S → S₁} {D₁ : Set S₁} (h₁ : IsCappedCuff C S₁ j₁ D₁)
    (hin₁ : IsPointInsideNullOArc (j₁ '' F) (j₁ x)) :
    IsPointInsideSurroundingOArc C F x := by
  refine ⟨hO, hSurr, ⟨S₁, inferInstance, j₁, D₁, h₁, hin₁⟩, fun S₂ _ j₂ D₂ h₂ => ?_⟩
  obtain ⟨H, hH⟩ := cappedCuff_homeomorph hS h₁ h₂
  have himg : H '' (j₁ '' F) = j₂ '' F := by
    rw [image_image]
    exact image_congr fun y _ => hH y
  rw [← himg, ← hH x]
  exact isPointInsideNullOArc_image_homeo H hin₁

/-- Universe-polymorphic version of `not_null_of_separating`: an `O`-arc in a surface `S` embedded
in a sphere `Z` whose image bounds a closed disc `B ⊆ Z` separating two points outside `range j` is
not null-homotopic in `S`. -/
theorem not_null_of_separating_u {S Z : Type u} [TopologicalSpace S]
    [TopologicalSpace Z] [T2Space Z] (hS : IsSurface S) (hsph : IsSphere Z)
    {j : S → Z} (hj : IsClosedEmbedding j) {F : Set S} (hF : IsOArc F) {B : Set Z}
    (hB : IsClosedDisc B) (hb : discBd B = j '' F) {p a : Z}
    (hpB : p ∈ B) (haB : a ∉ B) (hp : p ∉ range j) (ha : a ∉ range j) :
    ¬ IsNullHomotopicOArc F := by
  intro hnull
  obtain ⟨Δ, hΔ, hbΔ⟩ := nullHomotopicOArc_bounds_disc hS hF hnull
  obtain ⟨hd, hbd⟩ := isClosedDisc_image hΔ hj.continuous.continuousOn hj.injective.injOn
  have hO : IsOArc (j '' F) := hb ▸ hB.isOArc_discBd
  obtain ⟨Δ₁, Δ₂, -, h1, h2, b1, b2, hcup, -, -, huniq⟩ := sphere_disc Z hsph _ hO
  have hset : discBd (j '' Δ) = j '' F := by rw [hbd, hbΔ]
  have hBeq := huniq B hB hb
  have hΔeq := huniq _ hd hset
  have hra : ∀ {x}, x ∈ j '' Δ → x ∈ range j := fun {x} hx => image_subset_range _ _ hx
  rcases hBeq with rfl | rfl <;> rcases hΔeq with h | h
  · exact hp (hra (h ▸ hpB))
  · have : a ∈ B ∪ Δ₂ := hcup ▸ mem_univ a
    exact ha (hra (h ▸ this.resolve_left haB))
  · have : a ∈ Δ₁ ∪ B := hcup ▸ mem_univ a
    exact ha (hra (h ▸ this.resolve_right haB))
  · exact hp (hra (h ▸ hpB))

private theorem lift_preserves_proper_first_drawing
    (S : Type u)
    [TopologicalSpace S]
    [Nonempty S]
    (C : Set S)
    (H : SurfaceDigraph S)
    (hH : H.IsProper)
    (hbdS : bd S = C)
    (β : S ≃ₜ S)
    (hβ_fix : ∀ x ∈ bd S, β x = x)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (hcap : IsCappedCuff C Z j D₁)
    (hj : IsClosedEmbedding j)
    (C_sub : Set Z) [Nonempty ↥C_sub] :
    let S' : Type u := ↥C_sub
    let C₁ : Set S' := Subtype.val ⁻¹' discBd D₁
    ∀ (C₂ : Set S'),
    (bd S' = C₁ ∪ C₂) →
    let f_H : S → Z := j ∘ ⇑β
    ∀ (hf_H : IsClosedEmbedding f_H),
    ∀ (hUC_H : (embedDrawing hf_H H.G).U ⊆ C_sub),
    let H' : SurfaceDigraph S' := liftSurfaceDigraph hf_H H C_sub hUC_H
    (C₂ ∩ H'.G.U = ∅) →
    H'.IsProper := by
  intro S' C₁ C₂ hbdS' f_H hf_H hUC_H H' hH'_C₂_U
  rintro x ⟨hxBd, hxU⟩
  rw [hbdS'] at hxBd
  rcases hxBd with hxC₁ | hxC₂
  · have : x ∈ C₁ := hxC₁
    change x.val ∈ discBd D₁ at this
    rw [hcap.discBd_eq] at this
    obtain ⟨c, hc, hcx⟩ := this
    rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C_sub hUC_H from rfl,
      drawingInSubspace_embedDrawing_U] at hxU
    obtain ⟨z, hzU, hfz⟩ := hxU
    have hcz : c = β z := hj.injective (hcx.trans hfz.symm)
    have hc_bd : c ∈ bd S := hbdS.symm ▸ hc
    have hβc : β c = c := hβ_fix c hc_bd
    have hzc : z = c := β.injective (hcz.symm.trans hβc.symm)
    subst hzc
    have hzV : z ∈ H.G.V := hH ⟨hc_bd, hzU⟩
    rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C_sub hUC_H from rfl,
      drawingInSubspace_embedDrawing_V]
    exact ⟨z, hzV, hfz⟩
  · exfalso
    have : x ∈ C₂ ∩ H'.G.U := ⟨hxC₂, hxU⟩
    rw [hH'_C₂_U] at this
    exact this

private theorem lift_preserves_proper_second_drawing
    (S : Type u)
    [TopologicalSpace S]
    [Nonempty S]
    (C : Set S)
    (G : SurfaceDigraph S)
    (hG : G.IsProper)
    (hbdS : bd S = C)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (hcap : IsCappedCuff C Z j D₁)
    (hj : IsClosedEmbedding j)
    (C_sub : Set Z) [Nonempty ↥C_sub] :
    let S' : Type u := ↥C_sub
    let C₁ : Set S' := Subtype.val ⁻¹' discBd D₁
    ∀ (C₂ : Set S'),
    (bd S' = C₁ ∪ C₂) →
    ∀ (hUC_G : (embedDrawing hj G.G).U ⊆ C_sub),
    let G' : SurfaceDigraph S' := liftSurfaceDigraph hj G C_sub hUC_G
    (C₂ ∩ G'.G.U = ∅) →
    G'.IsProper := by
  intro S' C₁ C₂ hbdS' hUC_G G' hG'_C₂_U
  rintro x ⟨hxBd, hxU⟩
  rw [hbdS'] at hxBd
  rcases hxBd with hxC₁ | hxC₂
  · have : x ∈ C₁ := hxC₁
    change x.val ∈ discBd D₁ at this
    rw [hcap.discBd_eq] at this
    obtain ⟨c, hc, hcx⟩ := this
    rw [show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
      drawingInSubspace_embedDrawing_U] at hxU
    obtain ⟨z, hzU, hfz⟩ := hxU
    have hcz : c = z := hj.injective (hcx.trans hfz.symm)
    subst hcz
    have hcV : c ∈ G.G.V := hG ⟨hbdS.symm ▸ hc, hzU⟩
    rw [show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
      drawingInSubspace_embedDrawing_V]
    exact ⟨c, hcV, hfz⟩
  · exfalso
    have : x ∈ C₂ ∩ G'.G.U := ⟨hxC₂, hxU⟩
    rw [hG'_C₂_U] at this
    exact this

private theorem lift_preserves_boundary_vertex_agreement
    (S : Type u)
    [TopologicalSpace S]
    [Nonempty S]
    (C : Set S)
    (H : SurfaceDigraph S)
    (G : SurfaceDigraph S)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    (hbdS : bd S = C)
    (β : S ≃ₜ S)
    (hβ_fix : ∀ x ∈ bd S, β x = x)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (hcap : IsCappedCuff C Z j D₁)
    (hj : IsClosedEmbedding j)
    (C_sub : Set Z) [Nonempty ↥C_sub] :
    let S' : Type u := ↥C_sub
    let C₁ : Set S' := Subtype.val ⁻¹' discBd D₁
    ∀ (C₂ : Set S'),
    (bd S' = C₁ ∪ C₂) →
    let f_H : S → Z := j ∘ ⇑β
    ∀ (hf_H : IsClosedEmbedding f_H),
    ∀ (hUC_H : (embedDrawing hf_H H.G).U ⊆ C_sub),
    ∀ (hUC_G : (embedDrawing hj G.G).U ⊆ C_sub),
    let H' : SurfaceDigraph S' := liftSurfaceDigraph hf_H H C_sub hUC_H
    let G' : SurfaceDigraph S' := liftSurfaceDigraph hj G C_sub hUC_G
    (C₂ ∩ H'.G.U = ∅) →
    (C₂ ∩ G'.G.U = ∅) →
    G'.G.V ∩ bd S' = H'.G.V ∩ bd S' := by
  intro S' C₁ C₂ hbdS' f_H hf_H hUC_H hUC_G H' G' hH'_C₂_U hG'_C₂_U
  ext x
  rw [hbdS']
  constructor
  · rintro ⟨hxV, hxC₁ | hxC₂⟩
    · rw [show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
        drawingInSubspace_embedDrawing_V] at hxV
      obtain ⟨z, hzV, hfz⟩ := hxV
      have hxc : x.val ∈ j '' C := hcap.discBd_eq ▸ hxC₁
      obtain ⟨c, hc, hcx⟩ := hxc
      have hzc : z = c := hj.injective (hfz.trans hcx.symm)
      subst hzc
      have hz_bd : z ∈ bd S := hbdS.symm ▸ hc
      have hz_HV : z ∈ H.G.V := by
        have hmem : z ∈ G.G.V ∩ bd S := ⟨hzV, hz_bd⟩
        rw [hbd_eq] at hmem
        exact hmem.1
      refine ⟨?_, Or.inl hxC₁⟩
      rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C_sub hUC_H from rfl,
        drawingInSubspace_embedDrawing_V]
      refine ⟨z, hz_HV, ?_⟩
      change j (β z) = x.val
      rw [hβ_fix z hz_bd, hfz]
    · exfalso
      have : x ∈ C₂ ∩ G'.G.U := ⟨hxC₂, G'.G.V_subset_U hxV⟩
      rw [hG'_C₂_U] at this
      exact this
  · rintro ⟨hxV, hxC₁ | hxC₂⟩
    · rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C_sub hUC_H from rfl,
        drawingInSubspace_embedDrawing_V] at hxV
      obtain ⟨z, hzV, hfz⟩ := hxV
      have hxc : x.val ∈ j '' C := hcap.discBd_eq ▸ hxC₁
      obtain ⟨c, hc, hcx⟩ := hxc
      have hβz_c : β z = c := hj.injective (hfz.trans hcx.symm)
      have hc_bd : c ∈ bd S := hbdS.symm ▸ hc
      have hzc : z = c := β.injective (hβz_c.trans (hβ_fix c hc_bd).symm)
      subst hzc
      have hz_GV : z ∈ G.G.V := by
        have hmem : z ∈ H.G.V ∩ bd S := ⟨hzV, hc_bd⟩
        rw [← hbd_eq] at hmem
        exact hmem.1
      refine ⟨?_, Or.inl hxC₁⟩
      rw [show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
        drawingInSubspace_embedDrawing_V]
      exact ⟨z, hz_GV, hcx⟩
    · exfalso
      have : x ∈ C₂ ∩ H'.G.U := ⟨hxC₂, H'.G.V_subset_U hxV⟩
      rw [hH'_C₂_U] at this
      exact this

private theorem construct_cylinder_reduction
    (S : Type u)
    [TopologicalSpace S]
    [Nonempty S]
    (C : Set S)
    (H : SurfaceDigraph S)
    (G : SurfaceDigraph S)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    (F₁ : Set S)
    (F₂ : Set S)
    (hLine : ∀ (F : Set S), G.G.IsNormal F → IsLine F → (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty → 2
      * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard)
    (hk12 : rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂)
    (hkC : (G.G.V ∩ C).ncard ≤ maxDisjointPaths G.G F₁ C)
    [this : T2Space S]
    (hbdS : bd S = C)
    (Δ₁ : Set S)
    (Δ₂ : Set S)
    (hb₁ : discBd Δ₁ = F₁)
    (hb₂ : discBd Δ₂ = F₂)
    (hΔ₁_in_Δ₂ : Δ₁ ⊆ discInt Δ₂)
    (hΔ₂_disj_bd : Disjoint Δ₂ (bd S))
    (Δ : Set S)
    (hΔ_in_Δ₁ : Δ ⊆ discInt Δ₁)
    (β : S ≃ₜ S)
    (hβ_fix : ∀ x ∈ bd S, β x = x)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (hcap : IsCappedCuff C Z j D₁)
    (hSphZ : IsSphere Z)
    (hCS_Z : IsClosedSurface Z)
    [this : T2Space Z]
    (hj : IsClosedEmbedding j) :
    let D₂ : Set Z := j '' Δ
    (IsClosedDisc (j '' Δ)) →
    let P : Fin 2 → Set Z := ![D₁, D₂]
    (∀ (i : Fin 2), IsClosedDisc (P i)) →
    (Pairwise fun i k => Disjoint (P i) (P k)) →
    let C_sub : Set Z := discComplement P
    let S' : Type u := ↥C_sub
    (IsSurface S') →
    ∀ [T2Space S'],
    ∀ [Nonempty S'],
    ∀ [Nonempty (S' ≃ₜ SurfaceModel 0 0 2)],
    let C₁ : Set S' := Subtype.val ⁻¹' discBd D₁
    let C₂ : Set S' := Subtype.val ⁻¹' discBd D₂
    (C₁ = liftEdge j C_sub C) →
    (cuffs S' = {C₁, C₂}) →
    (C₁ ∈ cuffs S') →
    (C₂ ∈ cuffs S') →
    (C₁ ≠ C₂) →
    (bd S' = C₁ ∪ C₂) →
    let f_H : S → Z := j ∘ ⇑β
    ∀ (hf_H : IsClosedEmbedding f_H),
    ∀ (hUC_H : (embedDrawing hf_H H.G).U ⊆ C_sub),
    ∀ (hUC_G : (embedDrawing hj G.G).U ⊆ C_sub),
    let H' : SurfaceDigraph S' := liftSurfaceDigraph hf_H H C_sub hUC_H
    let G' : SurfaceDigraph S' := liftSurfaceDigraph hj G C_sub hUC_G
    (C₂ ∩ G'.G.U = ∅) →
    (H'.IsProper) →
    (G'.IsProper) →
    (G'.G.V ∩ bd S' = H'.G.V ∩ bd S') →
    (j '' F₁ ⊆ C_sub) →
    (j '' F₂ ⊆ C_sub) →
    let F₁' : Set S' := liftEdge j C_sub F₁
    let F₂' : Set S' := liftEdge j C_sub F₂
    (G'.G.IsNormal F₁') →
    (G'.G.IsNormal F₂') →
    (IsOArc F₁') →
    (IsOArc F₂') →
    (Disjoint F₁' F₂') →
    (Disjoint F₁' (bd S')) →
    (Disjoint F₂' (bd S')) →
    (discBd (j '' Δ₁) = j '' F₁) →
    (discBd (j '' Δ₂) = j '' F₂) →
    ∀ (E₁ : Set Z),
    (IsClosedDisc E₁) →
    (discBd E₁ = j '' F₁) →
    (E₁ = (discInt (j '' Δ₁))ᶜ) →
    (discInt E₁ = (j '' Δ₁)ᶜ) →
    ∀ (E₂ : Set Z),
    (IsClosedDisc E₂) →
    (discBd E₂ = j '' F₂) →
    (E₂ = (discInt (j '' Δ₂))ᶜ) →
    (discInt E₂ = (j '' Δ₂)ᶜ) →
    ∃ (S' : Type u) (_ : TopologicalSpace S') (_ : T1Space S') (C₁ C₂ : Set S') (H' G' :
      SurfaceDigraph S') (F₁' F₂' : Set S'), IsSurface S' ∧ Nonempty (S' ≃ₜ SurfaceModel 0 0 2) ∧
      cuffs S' = {C₁, C₂} ∧ C₁ ≠ C₂ ∧ H'.IsProper ∧ G'.IsProper ∧ G'.G.V ∩ bd S' = H'.G.V ∩ bd S'
      ∧ G'.G.IsNormal F₁' ∧ G'.G.IsNormal F₂' ∧ CylinderOArcsInOrder C₁ F₂' F₁' C₂ ∧ (∀ x ∈ F₂',
      IsPointInsideSurroundingOArc C₁ F₁' x) ∧ Disjoint F₁' (bd S') ∧ Disjoint F₂' (bd S') ∧ (∀ F
      : Set S', G'.G.IsNormal F → IsLine F → (F ∩ F₁').Nonempty → (F ∩ F₂').Nonempty → 2 *
      (rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard)) ≤ (G'.G.V ∩ F).ncard) ∧
      rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard) ≤ maxDisjointPaths G'.G F₁' F₂' ∧
      (G'.G.V ∩ C₁).ncard ≤ maxDisjointPaths G'.G F₁' C₁ ∧ (G'.G.V ∩ C₂).ncard ≤ maxDisjointPaths
      G'.G F₂' C₂ ∧ (IsBoundaryRootedMinor H' G' → IsBoundaryRootedMinor H G) := by
  intro D₂ hD₂_disc P hP hP_disj C_sub S' hS' this this heS' C₁ C₂ hC₁_eq_lift hcuffs' hC₁_mem
    hC₂_mem hC₁C₂_ne hbdS' f_H hf_H hUC_H hUC_G H' G' hG'_C₂_U hProperLiftH hProperLiftG
    hLiftBoundaryEq hF₁_sub hF₂_sub F₁' F₂' hF₁'_norm hF₂'_norm hO₁' hO₂' hDisj' hbd₁' hbd₂'
    hΔ₁Z_bd hΔ₂Z_bd E₁ hE₁ hbE₁ hE₁_eq hE₁_int E₂ hE₂ hbE₂ hE₂_eq hE₂_int
  classical
  have hD₁_in_E₂ : D₁ ⊆ discInt E₂ := by
    rw [hE₂_int]
    rintro z hz₁ ⟨x, hxΔ₂, rfl⟩
    have hjx : j x ∈ range j ∩ D₁ := ⟨⟨x, rfl⟩, hz₁⟩
    rw [hcap.inter_eq] at hjx
    obtain ⟨c, hc, hcj⟩ := hjx
    have hxc : x = c := hj.injective hcj.symm
    exact disjoint_left.mp hΔ₂_disj_bd hxΔ₂ (hbdS ▸ hxc ▸ hc)
  have hE₂_in_E₁ : E₂ ⊆ discInt E₁ := by
    rw [hE₂_eq, hE₁_int]
    rintro z hz ⟨x, hxΔ₁, rfl⟩
    apply hz
    have hx₂ := hΔ₁_in_Δ₂ hxΔ₁
    refine ⟨⟨x, hx₂.1, rfl⟩, ?_⟩
    rw [hΔ₂Z_bd]
    rintro ⟨y, hyF₂, hyx⟩
    exact hx₂.2 (hb₂ ▸ hj.injective hyx ▸ hyF₂)
  have hE₁_disj_D₂ : Disjoint E₁ D₂ := by
    rw [hE₁_eq, disjoint_left]
    rintro z hz ⟨x, hxΔ, rfl⟩
    apply hz
    have hx₁ := hΔ_in_Δ₁ hxΔ
    refine ⟨⟨x, hx₁.1, rfl⟩, ?_⟩
    rw [hΔ₁Z_bd]
    rintro ⟨y, hyF₁, hyx⟩
    exact hx₁.2 (hb₁ ▸ hj.injective hyx ▸ hyF₁)
  -- Non-null-homotopy and non-planarity of `F₁', F₂'` in `S'`
  obtain ⟨p₁, hp₁⟩ := hcap.isClosedDisc.nonempty_discInt
  obtain ⟨p₂, hp₂⟩ := hD₂_disc.nonempty_discInt
  have hp₁_not_C_sub : p₁ ∉ range (Subtype.val : S' → Z) := by
    rw [Subtype.range_val, mem_discComplement_iff hCS_Z P hP hP_disj]
    intro h
    exact h 0 hp₁
  have hp₂_not_C_sub : p₂ ∉ range (Subtype.val : S' → Z) := by
    rw [Subtype.range_val, mem_discComplement_iff hCS_Z P hP hP_disj]
    intro h
    exact h 1 hp₂
  have hp₁_E₂ : p₁ ∈ E₂ := discInt_subset E₂ (hD₁_in_E₂ (discInt_subset D₁ hp₁))
  have hp₁_E₁ : p₁ ∈ E₁ := discInt_subset E₁ (hE₂_in_E₁ hp₁_E₂)
  have hp₂_not_E₁ : p₂ ∉ E₁ := fun h => disjoint_left.mp hE₁_disj_D₂ h (discInt_subset D₂ hp₂)
  have hp₂_not_E₂ : p₂ ∉ E₂ := fun h => hp₂_not_E₁ (discInt_subset E₁ (hE₂_in_E₁ h))
  have hval_emb : IsClosedEmbedding (Subtype.val : S' → Z) :=
    isClosed_closure.isClosedEmbedding_subtypeVal
  have hval_F₁' : (Subtype.val : S' → Z) '' F₁' = j '' F₁ :=
    subtype_image_liftEdge_of_subset hF₁_sub
  have hval_F₂' : (Subtype.val : S' → Z) '' F₂' = j '' F₂ :=
    subtype_image_liftEdge_of_subset hF₂_sub
  have hnot_null₁ : ¬ IsNullHomotopicOArc F₁' :=
    not_null_of_separating_u hS' hSphZ hval_emb hO₁' hE₁ (hbE₁.trans hval_F₁'.symm)
      hp₁_E₁ hp₂_not_E₁ hp₁_not_C_sub hp₂_not_C_sub
  have hnot_null₂ : ¬ IsNullHomotopicOArc F₂' :=
    not_null_of_separating_u hS' hSphZ hval_emb hO₂' hE₂ (hbE₂.trans hval_F₂'.symm)
      hp₁_E₂ hp₂_not_E₂ hp₁_not_C_sub hp₂_not_C_sub
  have hnot_plan₁ : ¬ IsPlanar F₁' := fun hp =>
    hnot_null₁ ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hS' hO₁').mp hp)
  have hnot_plan₂ : ¬ IsPlanar F₂' := fun hp =>
    hnot_null₂ ((isPlanar_iff_isNullHomotopicOArc_of_isOArc hS' hO₂').mp hp)
  -- Cap `C₁` of `S'` via `exists_cap_discComplement_cuff`
  obtain ⟨j_cap, hcap_C₁, hj_cap_val⟩ := exists_cap_discComplement_cuff hCS_Z P hP hP_disj 0
  let T_cap := discComplement (fun k : {k : Fin 2 // k ≠ 0} => P k.val)
  have hE₁_sub_T : E₁ ⊆ T_cap := by
    change E₁ ⊆ discComplement (fun k : {k : Fin 2 // k ≠ 0} => P k.val)
    rw [discComplement_except_eq_union P hP hP_disj 0]
    intro z hzE₁
    by_cases hzD₁ : z ∈ D₁
    · exact Or.inr hzD₁
    · left
      rw [mem_discComplement_iff hCS_Z P hP hP_disj]
      intro i
      fin_cases i
      · exact fun h => hzD₁ h.1
      · exact fun h => disjoint_left.mp hE₁_disj_D₂ hzE₁ h.1
  have hE₂_sub_T : E₂ ⊆ T_cap := (hE₂_in_E₁.trans (discInt_subset E₁)).trans hE₁_sub_T
  obtain ⟨hE₁T_disc, hE₁T_bd⟩ := isClosedDisc_subtype_preimage hE₁_sub_T hE₁
  obtain ⟨hE₂T_disc, hE₂T_bd⟩ := isClosedDisc_subtype_preimage hE₂_sub_T hE₂
  have hj_cap_F₁' : j_cap '' F₁' = (Subtype.val : T_cap → Z) ⁻¹' (j '' F₁) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_preimage, hj_cap_val]
      exact hx
    · intro hy
      have hyC : y.val ∈ C_sub := hF₁_sub hy
      refine ⟨⟨y.val, hyC⟩, hy, Subtype.ext (hj_cap_val ⟨y.val, hyC⟩)⟩
  have hj_cap_F₂' : j_cap '' F₂' = (Subtype.val : T_cap → Z) ⁻¹' (j '' F₂) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_preimage, hj_cap_val]
      exact hx
    · intro hy
      have hyC : y.val ∈ C_sub := hF₂_sub hy
      refine ⟨⟨y.val, hyC⟩, hy, Subtype.ext (hj_cap_val ⟨y.val, hyC⟩)⟩
  rw [hbE₁, ← hj_cap_F₁'] at hE₁T_bd
  rw [hbE₂, ← hj_cap_F₂'] at hE₂T_bd
  have hplan_cap₁ : IsPlanarInCappedCuff C₁ F₁' :=
    isPlanarInCappedCuff_of_one_cap hS' hcap_C₁
      ⟨(Subtype.val : T_cap → Z) ⁻¹' E₁, hE₁T_disc, hE₁T_bd ▸ Surface.discBd_subset _⟩
  have hplan_cap₂ : IsPlanarInCappedCuff C₁ F₂' :=
    isPlanarInCappedCuff_of_one_cap hS' hcap_C₁
      ⟨(Subtype.val : T_cap → Z) ⁻¹' E₂, hE₂T_disc, hE₂T_bd ▸ Surface.discBd_subset _⟩
  have hSurr₁ : SurroundsCuff F₁' C₁ := ⟨hC₁_mem, hplan_cap₁, hnot_plan₁⟩
  have hSurr₂ : SurroundsCuff F₂' C₁ := ⟨hC₁_mem, hplan_cap₂, hnot_plan₂⟩
  have hInC₁' : ∀ x ∈ F₂', IsPointInsideSurroundingOArc C₁ F₁' x := by
    intro x hx
    apply isPointInsideSurroundingOArc_of_one_cap hS' hO₁' hSurr₁ hcap_C₁
    have hO₁'_cap : IsOArc (j_cap '' F₁') := hE₁T_bd ▸ hE₁T_disc.isOArc_discBd
    have hnull₁'_cap : IsNullHomotopicOArc (j_cap '' F₁') :=
      isNullHomotopicOArcIn_of_subset_disc hO₁'_cap (subset_univ _) hE₁T_disc
        (hE₁T_bd ▸ Surface.discBd_subset _)
    refine ⟨hnull₁'_cap, (Subtype.val : T_cap → Z) ⁻¹' E₁, hE₁T_disc, hE₁T_bd, ?_⟩
    have hx_E₂ : x.val ∈ E₂ := Surface.discBd_subset E₂ (hbE₂.symm ▸ hx)
    have hx_in_E₁ : x.val ∈ discInt E₁ := hE₂_in_E₁ hx_E₂
    refine ⟨by rw [mem_preimage, hj_cap_val]; exact hx_in_E₁.1, ?_⟩
    rw [hj_cap_F₁', mem_preimage, hj_cap_val]
    exact hbE₁ ▸ hx_in_E₁.2
  have hInside' : IsInsideOArc F₂' F₁' := fun x hx => Or.inr ⟨C₁, hC₁_mem, hInC₁' x hx⟩
  have hOrder' : CylinderOArcsInOrder C₁ F₂' F₁' C₂ :=
    ⟨hC₁_mem, hC₂_mem, hC₁C₂_ne, hO₁', hO₂', hDisj', hnot_null₁, hnot_null₂, hSurr₂, hSurr₁,
      hInside'⟩
  have hH'_V_ncard : H'.G.V.ncard = H.G.V.ncard :=
    drawingInSubspace_embedDrawing_V_ncard hf_H H.G C_sub hUC_H
  have hH'_E_ncard : H'.G.E.ncard = H.G.E.ncard :=
    drawingInSubspace_embedDrawing_E_ncard hf_H H.G C_sub hUC_H
  have hr_eq : rCylinderBound H'.G = rCylinderBound H.G := by
    simp only [rCylinderBound, hH'_V_ncard, hH'_E_ncard]
  refine ⟨S', inferInstance, inferInstance, C₁, C₂, H', G', F₁', F₂',
    hS', heS', hcuffs', hC₁C₂_ne, hProperLiftH, hProperLiftG, hLiftBoundaryEq,
    hF₁'_norm, hF₂'_norm, hOrder', hInC₁', hbd₁', hbd₂',
    ?_, ?_, ?_, ?_, ?_⟩
  · intro F' hF'_norm hF'_line hF'₁ hF'₂
    rw [hr_eq, hH'_V_ncard, hH'_E_ncard,
      show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
      drawingInSubspace_embedDrawing_V_inter_unliftEdge_ncard]
    have hF'_range : (Subtype.val : S' → Z) '' F' ⊆ range j := by
      rintro _ ⟨x, -, rfl⟩
      by_contra hnr
      have hxD₁ : x.val ∈ discInt D₁ := by
        have hxU : x.val ∈ range j ∪ D₁ := hcap.union_eq ▸ mem_univ x.val
        refine ⟨hxU.resolve_left hnr, fun hxb => hnr ?_⟩
        rw [hcap.discBd_eq] at hxb
        obtain ⟨c, _, hcj⟩ := hxb
        exact ⟨c, hcj⟩
      exact (mem_discComplement_iff hCS_Z P hP hP_disj x.val).mp x.property 0 hxD₁
    apply hLine (unliftEdge j C_sub F')
    · exact drawingInSubspace_embedDrawing_isNormal_unliftEdge hj G.G C_sub hUC_G hF'_norm
    · exact isLine_unliftEdge hj.isEmbedding hF'_range hF'_line
    · obtain ⟨x, hxF', z, hzF₁, hzx⟩ := hF'₁
      exact ⟨z, ⟨x, hxF', hzx.symm⟩, hzF₁⟩
    · obtain ⟨x, hxF', z, hzF₂, hzx⟩ := hF'₂
      exact ⟨z, ⟨x, hxF', hzx.symm⟩, hzF₂⟩
  · rw [hr_eq, hH'_V_ncard, hH'_E_ncard]
    exact hk12.trans (maxDisjointPaths_le_liftEdge hj G.G C_sub hUC_G F₁ F₂)
  · rw [hC₁_eq_lift,
      show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
      drawingInSubspace_embedDrawing_V_inter_liftEdge_ncard]
    exact hkC.trans (maxDisjointPaths_le_liftEdge hj G.G C_sub hUC_G F₁ C)
  · have hC₂_empty : G'.G.V ∩ C₂ = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hxV, hxC₂⟩
      have : x ∈ C₂ ∩ G'.G.U := ⟨hxC₂, G'.G.V_subset_U hxV⟩
      rw [hG'_C₂_U] at this
      exact this
    rw [hC₂_empty, Set.ncard_empty]
    exact Nat.zero_le _
  · intro hminor'
    refine isBoundaryRootedMinor_of_lift hf_H hj H G C_sub hUC_H hUC_G hbd_eq.symm
      (fun x hx => by change j (β x) = j x; rw [hβ_fix x hx]) ?_ hminor'
    intro v hv
    rw [hbdS']
    left
    change j (β v) ∈ discBd D₁
    rw [hβ_fix v hv.2, hcap.discBd_eq]
    exact ⟨v, hbdS ▸ hv.2, rfl⟩

private theorem cylinder_cuffs_distinct
    (S : Type u)
    [TopologicalSpace S]
    (C : Set S)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (hcap : IsCappedCuff C Z j D₁)
    (hCS_Z : IsClosedSurface Z)
    [T2Space Z] :
    ∀ (D₂ : Set Z),
    (Disjoint D₁ D₂) →
    let P : Fin 2 → Set Z := ![D₁, D₂]
    (∀ (i : Fin 2), IsClosedDisc (P i)) →
    (Pairwise fun i k => Disjoint (P i) (P k)) →
    let C_sub : Set Z := discComplement P
    let S' : Type u := ↥C_sub
    let C₁ : Set S' := Subtype.val ⁻¹' discBd D₁
    let C₂ : Set S' := Subtype.val ⁻¹' discBd D₂
    C₁ ≠ C₂ := by
  intro D₂ hD₁D₂_disj P hP hP_disj C_sub S' C₁ C₂ heq
  obtain ⟨φ₁⟩ := hcap.isClosedDisc.isOArc_discBd
  let z := (φ₁ 1).val
  have hz₁ : z ∈ discBd D₁ := (φ₁ 1).property
  have hzC : z ∈ C_sub := disc_boundary_subset_discComplement hCS_Z P hP hP_disj 0 hz₁
  have hzC₁ : (⟨z, hzC⟩ : S') ∈ C₁ := hz₁
  have hzC₂ : (⟨z, hzC⟩ : S') ∈ C₂ := heq ▸ hzC₁
  exact disjoint_left.mp hD₁D₂_disj (Surface.discBd_subset D₁ hz₁)
    (Surface.discBd_subset D₂ hzC₂)

private theorem first_lift_disjoint_from_inner_cuff
    (S : Type u)
    [TopologicalSpace S]
    [Nonempty S]
    (H : SurfaceDigraph S)
    (Δ : Set S)
    (β : S ≃ₜ S)
    (hΔ_disj_H : Disjoint (⇑β '' H.G.U) Δ)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (hj : IsClosedEmbedding j) :
    let D₂ : Set Z := j '' Δ
    (discBd (j '' Δ) = j '' discBd Δ) →
    ∀ (C_sub : Set Z),
    ∀ [Nonempty ↥C_sub],
    let S' : Type u := ↥C_sub
    let C₂ : Set S' := Subtype.val ⁻¹' discBd D₂
    let f_H : S → Z := j ∘ ⇑β
    ∀ (hf_H : IsClosedEmbedding f_H),
    ∀ (hUC_H : (embedDrawing hf_H H.G).U ⊆ C_sub),
    let H' : SurfaceDigraph S' := liftSurfaceDigraph hf_H H C_sub hUC_H
    C₂ ∩ H'.G.U = ∅ := by
  intro D₂ hD₂_bd C_sub nonemptySubspace S' C₂ f_H hf_H hUC_H H'
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hxC₂, hxU⟩
  rw [show H'.G = drawingInSubspace (embedDrawing hf_H H.G) C_sub hUC_H from rfl,
    drawingInSubspace_embedDrawing_U] at hxU
  obtain ⟨z, hzU, hfz⟩ := hxU
  have hxD₂ : j (β z) ∈ discBd (j '' Δ) := by
    change f_H z ∈ discBd D₂
    rw [hfz]
    exact hxC₂
  rw [hD₂_bd] at hxD₂
  obtain ⟨w, hw, hwz⟩ := hxD₂
  have hw_eq : β z = w := hj.injective hwz.symm
  exact disjoint_left.mp hΔ_disj_H ⟨z, hzU, rfl⟩ (hw_eq ▸ Surface.discBd_subset Δ hw)

private theorem second_lift_disjoint_from_inner_cuff
    (S : Type u)
    [TopologicalSpace S]
    [Nonempty S]
    (G : SurfaceDigraph S)
    (Δ : Set S)
    (hΔ_disj_G : Disjoint Δ G.G.U)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (hj : IsClosedEmbedding j)
    (hD₂_bd : discBd (j '' Δ) = j '' discBd Δ)
    (C_sub : Set Z) [Nonempty ↥C_sub] :
    let S' : Type u := ↥C_sub
    let C₂ : Set S' := Subtype.val ⁻¹' discBd (j '' Δ)
    ∀ (hUC_G : (embedDrawing hj G.G).U ⊆ C_sub),
    let G' : SurfaceDigraph S' := liftSurfaceDigraph hj G C_sub hUC_G
    C₂ ∩ G'.G.U = ∅ := by
  intro S' C₂ hUC_G G'
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hxC₂, hxU⟩
  rw [show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
    drawingInSubspace_embedDrawing_U] at hxU
  obtain ⟨z, hzU, hfz⟩ := hxU
  have hxD₂ : j z ∈ discBd (j '' Δ) := hfz ▸ hxC₂
  rw [hD₂_bd] at hxD₂
  obtain ⟨w, hw, hwz⟩ := hxD₂
  have hw_eq : z = w := hj.injective hwz.symm
  exact disjoint_left.mp hΔ_disj_G (hw_eq ▸ Surface.discBd_subset Δ hw) hzU

/-- **Graph Minors VII, proof of (9.4) from (9.3)** (page 246):
"Choose a closed disc $\Delta \subseteq \Sigma$ with $\Delta$ inside $F_1$ and
$\Delta \cap U(G) = \emptyset$. The result follows by applying (9.3) to the surface obtained from
$\Sigma$ by removing the interior of $\Delta$, and to an isomorphic copy of $(H, H^+, H^-)$ in this
surface." -/
theorem discToCylinderReduction :
    ∀ (S : Type u) [TopologicalSpace S],
      IsSurface S → IsClosedDisc (univ : Set S) →
      ∀ C : Set S, cuffs S = {C} →
      ∀ H G : SurfaceDigraph S, H.IsProper → G.IsProper →
        G.G.V ∩ bd S = H.G.V ∩ bd S →
        ∀ F₁ F₂ : Set S,
          G.G.IsNormal F₁ → G.G.IsNormal F₂ →
          IsOArc F₁ → IsOArc F₂ → Disjoint F₁ F₂ →
          IsInsideOArc F₁ F₂ → Disjoint F₂ (bd S) →
          (∀ F : Set S, G.G.IsNormal F → IsLine F →
            (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
            2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard) →
          rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂ →
          (G.G.V ∩ C).ncard ≤ maxDisjointPaths G.G F₁ C →
          ∃ (S' : Type u) (_ : TopologicalSpace S') (_ : T1Space S')
            (C₁ C₂ : Set S') (H' G' : SurfaceDigraph S') (F₁' F₂' : Set S'),
            IsSurface S' ∧ Nonempty (S' ≃ₜ SurfaceModel 0 0 2) ∧
            cuffs S' = {C₁, C₂} ∧ C₁ ≠ C₂ ∧
            H'.IsProper ∧ G'.IsProper ∧ G'.G.V ∩ bd S' = H'.G.V ∩ bd S' ∧
            G'.G.IsNormal F₁' ∧ G'.G.IsNormal F₂' ∧
            CylinderOArcsInOrder C₁ F₂' F₁' C₂ ∧
            (∀ x ∈ F₂', IsPointInsideSurroundingOArc C₁ F₁' x) ∧
            Disjoint F₁' (bd S') ∧ Disjoint F₂' (bd S') ∧
            (∀ F : Set S', G'.G.IsNormal F → IsLine F →
              (F ∩ F₁').Nonempty → (F ∩ F₂').Nonempty →
              2 * (rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard)) ≤ (G'.G.V ∩ F).ncard) ∧
            rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard) ≤ maxDisjointPaths G'.G F₁' F₂'
              ∧
            (G'.G.V ∩ C₁).ncard ≤ maxDisjointPaths G'.G F₁' C₁ ∧
            (G'.G.V ∩ C₂).ncard ≤ maxDisjointPaths G'.G F₂' C₂ ∧
            (IsBoundaryRootedMinor H' G' → IsBoundaryRootedMinor H G) := by
  intro S _ hS hD C hcuffs H G hH hG hbd_eq F₁ F₂ hF₁ hF₂ hO₁ hO₂ hDisj hInside hbd₂ hLine hk12
    hkC
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  let ⟨φD⟩ := hD
  obtain ⟨eD₀⟩ := nonempty_disc_homeo
  let eS : S ≃ₜ SurfaceModel 0 0 1 :=
    (Homeomorph.Set.univ S).symm.trans (φD.symm.trans eD₀.symm)
  have heS : Nonempty (S ≃ₜ SurfaceModel 0 0 1) := ⟨eS⟩
  have hconnS : ConnectedSpace S := by
    have : ConnectedSpace (SurfaceModel 0 0 1) := (isSurface_model 0 0 1).2
    exact eS.symm.surjective.connectedSpace eS.symm.continuous
  have : Nonempty S := hconnS.toNonempty
  have hC : C ∈ cuffs S := by rw [hcuffs]; exact mem_singleton C
  have hbdS : bd S = C := by rw [← sUnion_cuffs, hcuffs, sUnion_singleton]
  obtain ⟨Δ₁, Δ₂, hΔ₁, hb₁, hΔ₂, hb₂, hΔ₁_in_Δ₂, hΔ₂_disj_bd⟩ :=
    lemma_9_4_claim_1 hS hD hO₁ hO₂ hDisj hInside hbd₂
  have hΔ₁_disj_bd : Disjoint Δ₁ (bd S) :=
    hΔ₂_disj_bd.mono_left (hΔ₁_in_Δ₂.trans (discInt_subset Δ₂))
  have hΔ₁_bd : Δ₁ ∩ bd S = ∅ := hΔ₁_disj_bd.inter_eq
  obtain ⟨Δ, hΔ, hΔ_in_Δ₁, hΔ_disj_G⟩ :=
    exists_subdisc_disjoint_drawing hS G.G hΔ₁ hΔ₁_bd
  have hΔ_disj_bd : Disjoint Δ (bd S) :=
    hΔ₁_disj_bd.mono_left (hΔ_in_Δ₁.trans (discInt_subset Δ₁))
  have hΔ_bd : Δ ∩ bd S = ∅ := hΔ_disj_bd.inter_eq
  obtain ⟨β, hβ_fix, hΔ_disj_H⟩ := exists_move_drawing_off_disc hS H.G hΔ hΔ_bd
  obtain ⟨Z, tZ, j, D₁, hcap, hbdZ⟩ := exists_cappedCuff hS hC
  obtain ⟨-, ⟨eZ⟩⟩ := cappedCuff_homeo_model hS heS hC hcap
  obtain ⟨s₀⟩ := isSphere_model_zero
  have hSphZ : IsSphere Z := ⟨eZ.trans s₀⟩
  obtain ⟨_, hCS_Z, hconnZ, _⟩ := closedSurface_and_connected_of_isSphere hcap.isSurface hSphZ
  have : T2Space Z := hcap.isSurface.2.1
  have : ConnectedSpace Z := hconnZ
  have hj : IsClosedEmbedding j := hcap.isEmbedding.continuous.isClosedEmbedding
    hcap.isEmbedding.injective
  let D₂ : Set Z := j '' Δ
  obtain ⟨hD₂_disc, hD₂_bd⟩ := isClosedDisc_image hΔ hj.continuous.continuousOn hj.injective.injOn
  have hD₁D₂_disj : Disjoint D₁ D₂ := by
    rw [disjoint_left]
    rintro z hz₁ ⟨x, hxΔ, rfl⟩
    have hjx : j x ∈ range j ∩ D₁ := ⟨⟨x, rfl⟩, hz₁⟩
    rw [hcap.inter_eq] at hjx
    obtain ⟨c, hc, hcj⟩ := hjx
    have hxc : x = c := hj.injective hcj.symm
    exact disjoint_left.mp hΔ_disj_bd hxΔ (hbdS ▸ hxc ▸ hc)
  let P : Fin 2 → Set Z := ![D₁, D₂]
  have hP : ∀ i, IsClosedDisc (P i) := fun i => by
    fin_cases i
    · exact hcap.isClosedDisc
    · exact hD₂_disc
  have hP_disj : Pairwise (fun i k => Disjoint (P i) (P k)) := fun i k hik => by
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact hD₁D₂_disj
    · exact hD₁D₂_disj.symm
    · exact (hik rfl).elim
  let C_sub : Set Z := discComplement P
  let S' : Type u := ↥C_sub
  have hS' : IsSurface S' := discComplement_isSurface hCS_Z P hP hP_disj
  have : T2Space S' := hS'.2.1
  have : ConnectedSpace S' := Subtype.connectedSpace (discComplement_isConnected hCS_Z P hP hP_disj)
  have : Nonempty S' := (inferInstance : ConnectedSpace S').toNonempty
  have heS' : Nonempty (S' ≃ₜ SurfaceModel 0 0 2) := by
    have hcard : Nat.card (Fin 2) = 2 := by simp
    exact hcard ▸ discComplement_model_of_closed_model hCS_Z P hP hP_disj eZ
  let C₁ : Set S' := (Subtype.val : S' → Z) ⁻¹' discBd D₁
  let C₂ : Set S' := (Subtype.val : S' → Z) ⁻¹' discBd D₂
  have hC₁_eq_lift : C₁ = liftEdge j C_sub C := by
    simp [C₁, liftEdge, hcap.discBd_eq]
  have hC₂_eq_lift : C₂ = liftEdge j C_sub (discBd Δ) := by
    change (Subtype.val : S' → Z) ⁻¹' discBd (j '' Δ) = liftEdge j C_sub (discBd Δ)
    simp [liftEdge, hD₂_bd]
  have hcuffs' : cuffs S' = {C₁, C₂} := by
    rw [discComplement_cuffs_eq hCS_Z P hP hP_disj]
    ext X
    simp only [mem_range, Fin.exists_fin_two, mem_insert_iff, mem_singleton_iff]
    tauto
  have hC₁_mem : C₁ ∈ cuffs S' := by rw [hcuffs']; exact Or.inl rfl
  have hC₂_mem : C₂ ∈ cuffs S' := by rw [hcuffs']; exact Or.inr rfl
  have hC₁C₂_ne : C₁ ≠ C₂ := by
    exact cylinder_cuffs_distinct S C Z j D₁ hcap hCS_Z D₂ hD₁D₂_disj hP hP_disj
  have hbdS' : bd S' = C₁ ∪ C₂ := by
    rw [discComplement_boundary_eq hCS_Z P hP]
    ext x
    simp [P, C₁, C₂, Fin.exists_fin_two]
  have hj_mem_C_sub : ∀ x : S, x ∉ discInt Δ → j x ∈ C_sub := by
    intro x hx
    rw [mem_discComplement_iff hCS_Z P hP hP_disj]
    intro i
    fin_cases i
    · rintro ⟨hz₁, hnb₁⟩
      have hjx : j x ∈ range j ∩ D₁ := ⟨⟨x, rfl⟩, hz₁⟩
      rw [hcap.inter_eq, ← hcap.discBd_eq] at hjx
      exact hnb₁ hjx
    · rintro ⟨⟨y, hyΔ, hyx⟩, hnb₂⟩
      have hyx' : y = x := hj.injective hyx
      subst hyx'
      apply hx ⟨hyΔ, fun hxb => hnb₂ ?_⟩
      change j y ∈ discBd (j '' Δ)
      rw [hD₂_bd]
      exact ⟨y, hxb, rfl⟩
  let f_H : S → Z := j ∘ β
  have hf_H : IsClosedEmbedding f_H := hj.comp β.isClosedEmbedding
  have hUC_H : (embedDrawing hf_H H.G).U ⊆ C_sub := by
    rintro _ ⟨x, hxU, rfl⟩
    refine hj_mem_C_sub (β x) fun hxΔ => ?_
    exact disjoint_left.mp hΔ_disj_H ⟨x, hxU, rfl⟩ hxΔ.1
  have hUC_G : (embedDrawing hj G.G).U ⊆ C_sub := by
    rintro _ ⟨x, hxU, rfl⟩
    refine hj_mem_C_sub x fun hxΔ => ?_
    exact disjoint_left.mp hΔ_disj_G hxΔ.1 hxU
  let H' : SurfaceDigraph S' := liftSurfaceDigraph hf_H H C_sub hUC_H
  let G' : SurfaceDigraph S' := liftSurfaceDigraph hj G C_sub hUC_G
  have hH'_C₂_U : C₂ ∩ H'.G.U = ∅ := by
    exact first_lift_disjoint_from_inner_cuff S H Δ β hΔ_disj_H Z j hj hD₂_bd C_sub
      hf_H hUC_H
  have hG'_C₂_U : C₂ ∩ G'.G.U = ∅ := by
    exact second_lift_disjoint_from_inner_cuff S G Δ hΔ_disj_G Z j hj hD₂_bd C_sub hUC_G
  have hProperLiftH : H'.IsProper := by
    exact lift_preserves_proper_first_drawing S C H hH hbdS β hβ_fix Z j D₁ hcap hj C_sub C₂
      hbdS'  hf_H hUC_H  hH'_C₂_U
  have hProperLiftG : G'.IsProper := by
    exact lift_preserves_proper_second_drawing S C G hG hbdS Z j D₁ hcap hj C_sub C₂ hbdS'
      hUC_G  hG'_C₂_U
  have hLiftBoundaryEq : G'.G.V ∩ bd S' = H'.G.V ∩ bd S' := by
    exact lift_preserves_boundary_vertex_agreement S C H G hbd_eq hbdS β hβ_fix Z j D₁ hcap hj
      C_sub   C₂ hbdS'  hf_H hUC_H hUC_G   hH'_C₂_U hG'_C₂_U
  have hF₁_disj_Δ : Disjoint F₁ Δ := by
    rw [disjoint_left]
    intro x hx₁ hxΔ
    exact (hΔ_in_Δ₁ hxΔ).2 (hb₁.symm ▸ hx₁)
  have hF₂_disj_Δ : Disjoint F₂ Δ := by
    rw [disjoint_left]
    intro x hx₂ hxΔ
    exact (hΔ₁_in_Δ₂ (discInt_subset Δ₁ (hΔ_in_Δ₁ hxΔ))).2 (hb₂.symm ▸ hx₂)
  have hF₁_sub : j '' F₁ ⊆ C_sub := by
    rintro _ ⟨x, hx₁, rfl⟩
    exact hj_mem_C_sub x fun hxΔ => disjoint_left.mp hF₁_disj_Δ hx₁ hxΔ.1
  have hF₂_sub : j '' F₂ ⊆ C_sub := by
    rintro _ ⟨x, hx₂, rfl⟩
    exact hj_mem_C_sub x fun hxΔ => disjoint_left.mp hF₂_disj_Δ hx₂ hxΔ.1
  let F₁' : Set S' := liftEdge j C_sub F₁
  let F₂' : Set S' := liftEdge j C_sub F₂
  have hF₁'_norm : G'.G.IsNormal F₁' :=
    drawingInSubspace_embedDrawing_isNormal_liftEdge hj G.G C_sub hUC_G hF₁
  have hF₂'_norm : G'.G.IsNormal F₂' :=
    drawingInSubspace_embedDrawing_isNormal_liftEdge hj G.G C_sub hUC_G hF₂
  have hO₁' : IsOArc F₁' := isOArc_liftEdge hj.isEmbedding hF₁_sub hO₁
  have hO₂' : IsOArc F₂' := isOArc_liftEdge hj.isEmbedding hF₂_sub hO₂
  have hDisj' : Disjoint F₁' F₂' := disjoint_liftEdge hj.injective C_sub hDisj
  have hbd₁ : Disjoint F₁ (bd S) :=
    hΔ₁_disj_bd.mono_left (hb₁ ▸ Surface.discBd_subset Δ₁)
  have hbd₁' : Disjoint F₁' (bd S') := by
    rw [hbdS', disjoint_union_right, hC₁_eq_lift, hC₂_eq_lift]
    exact ⟨disjoint_liftEdge hj.injective C_sub (hbdS ▸ hbd₁),
      disjoint_liftEdge hj.injective C_sub (hF₁_disj_Δ.mono_right (Surface.discBd_subset Δ))⟩
  have hbd₂' : Disjoint F₂' (bd S') := by
    rw [hbdS', disjoint_union_right, hC₁_eq_lift, hC₂_eq_lift]
    exact ⟨disjoint_liftEdge hj.injective C_sub (hbdS ▸ hbd₂),
      disjoint_liftEdge hj.injective C_sub (hF₂_disj_Δ.mono_right (Surface.discBd_subset Δ))⟩
  -- Complementary discs `E₁, E₂` in the sphere `Z`
  obtain ⟨hΔ₁Z_disc, hΔ₁Z_bd⟩ := isClosedDisc_image hΔ₁ hj.continuous.continuousOn
    hj.injective.injOn
  obtain ⟨hΔ₂Z_disc, hΔ₂Z_bd⟩ := isClosedDisc_image hΔ₂ hj.continuous.continuousOn
    hj.injective.injOn
  rw [hb₁] at hΔ₁Z_bd
  rw [hb₂] at hΔ₂Z_bd
  obtain ⟨E₁, hE₁, hbE₁, hE₁_eq, hE₁_int⟩ := exists_compl_disc_in_sphere hSphZ hΔ₁Z_disc
  obtain ⟨E₂, hE₂, hbE₂, hE₂_eq, hE₂_int⟩ := exists_compl_disc_in_sphere hSphZ hΔ₂Z_disc
  rw [hΔ₁Z_bd] at hbE₁
  rw [hΔ₂Z_bd] at hbE₂
  have annulus_reduction : ∃ (S' : Type u) (_ : TopologicalSpace S') (_ : T1Space S')
            (C₁ C₂ : Set S') (H' G' : SurfaceDigraph S') (F₁' F₂' : Set S'),
            IsSurface S' ∧ Nonempty (S' ≃ₜ SurfaceModel 0 0 2) ∧
            cuffs S' = {C₁, C₂} ∧ C₁ ≠ C₂ ∧
            H'.IsProper ∧ G'.IsProper ∧ G'.G.V ∩ bd S' = H'.G.V ∩ bd S' ∧
            G'.G.IsNormal F₁' ∧ G'.G.IsNormal F₂' ∧
            CylinderOArcsInOrder C₁ F₂' F₁' C₂ ∧
            (∀ x ∈ F₂', IsPointInsideSurroundingOArc C₁ F₁' x) ∧
            Disjoint F₁' (bd S') ∧ Disjoint F₂' (bd S') ∧
            (∀ F : Set S', G'.G.IsNormal F → IsLine F →
              (F ∩ F₁').Nonempty → (F ∩ F₂').Nonempty →
              2 * (rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard)) ≤ (G'.G.V ∩ F).ncard) ∧
            rCylinderBound H'.G * 5 ^ (H'.G.V.ncard + H'.G.E.ncard) ≤ maxDisjointPaths G'.G F₁' F₂'
              ∧
            (G'.G.V ∩ C₁).ncard ≤ maxDisjointPaths G'.G F₁' C₁ ∧
            (G'.G.V ∩ C₂).ncard ≤ maxDisjointPaths G'.G F₂' C₂ ∧
            (IsBoundaryRootedMinor H' G' → IsBoundaryRootedMinor H G) := by
    exact construct_cylinder_reduction S C H G hbd_eq F₁ F₂ hLine hk12 hkC hbdS Δ₁ Δ₂ hb₁ hb₂
      hΔ₁_in_Δ₂ hΔ₂_disj_bd Δ hΔ_in_Δ₁ β hβ_fix Z j D₁ hcap hSphZ hCS_Z hj  hD₂_disc  hP
      hP_disj   hS'   hC₁_eq_lift hcuffs' hC₁_mem hC₂_mem hC₁C₂_ne hbdS'  hf_H hUC_H
      hUC_G   hG'_C₂_U hProperLiftH hProperLiftG hLiftBoundaryEq hF₁_sub hF₂_sub
      hF₁'_norm hF₂'_norm hO₁' hO₂' hDisj' hbd₁' hbd₂' hΔ₁Z_bd hΔ₂Z_bd E₁ hE₁ hbE₁ hE₁_eq hE₁_int
      E₂ hE₂ hbE₂ hE₂_eq hE₂_int
  exact annulus_reduction

end GraphMinor.GM07
