/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section9CoreProved
import LeanPool.GraphMinor.GM07.Section9Cylinder
import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Section8
import LeanPool.GraphMinor.GM07.CuffForest
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.GM12.Section2ChordGap
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.GM12.Section3NormalPuncturedPaths
import LeanPool.GraphMinor.GM12.Section3BoundaryLinked
import LeanPool.GraphMinor.GM12.Section3CandidateExistence
import LeanPool.GraphMinor.GM12.Section3Alpha
import LeanPool.GraphMinor.GM12.Section3NearPlanarCircle
import LeanPool.GraphMinor.GM12.Section3LoopCuffClassification
import LeanPool.GraphMinor.GM12.Section3ThetaSurrounding

/-!
# The punctured-cylinder deduction of Graph Minors VII, (9.3)

Claims 1 and 2 establish boundary linkage and the required lower bound on
the punctured cylinder. Applying the proved (9.1) gives the boundary-rooted minor.
-/

public section
namespace GraphMinor.GM07
open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12
universe u

private theorem cylinder_has_normal_line_between_boundaries
    (S : Type u)
    [TopologicalSpace S]
    (C₁ : Set S)
    (C₂ : Set S)
    (G : SurfaceDigraph S)
    (hG : G.IsProper)
    (F₁ : Set S)
    (F₂ : Set S)
    (hF₁ : G.G.IsNormal F₁)
    (hF₂ : G.G.IsNormal F₂)
    (hbdS : bd S = C₁ ∪ C₂)
    (hO₁ : IsOArc F₁)
    (hO₂ : IsOArc F₂)
    (hDisj : Disjoint F₁ F₂)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (D₂ : Set Z)
    (hCS_Z : IsClosedSurface Z)
    (hj : IsClosedEmbedding j)
    (hD₁ : IsClosedDisc D₁)
    (hD₂ : IsClosedDisc D₂)
    (hD₁D₂_disj : Disjoint D₁ D₂)
    (hbD₁ : discBd D₁ = j '' C₁)
    (hbD₂ : discBd D₂ = j '' C₂)
    (hinter₁ : range j ∩ D₁ = j '' C₁)
    (hinter₂ : range j ∩ D₂ = j '' C₂)
    (hrange_eq : range j = discComplement ![D₁, D₂])
    [T2Space Z]
    [ConnectedSpace Z] :
    ∃ F, G.G.IsNormal F ∧ IsLine F ∧ (F ∩ F₁).Nonempty ∧ (F ∩ F₂).Nonempty := by
  let Γ₀ := embedDrawing hj G.G
  let P₂ : Fin 2 → Set Z := ![D₁, D₂]
  have hP₂ : ∀ i, IsClosedDisc (P₂ i) := fun i => by
    fin_cases i
    · exact hD₁
    · exact hD₂
  have hP₂_disj : Pairwise (fun i k => Disjoint (P₂ i) (P₂ k)) := fun i k hik => by
    fin_cases i <;> fin_cases k
    · exact (hik rfl).elim
    · exact hD₁D₂_disj
    · exact hD₁D₂_disj.symm
    · exact (hik rfl).elim
  have havoid₂ : ∀ i : Fin 2, Γ₀.U ∩ P₂ i = Γ₀.V ∩ discBd (P₂ i) := by
    intro i
    fin_cases i
    · change j '' G.G.U ∩ D₁ = j '' G.G.V ∩ discBd D₁
      rw [hbD₁]
      ext w
      constructor
      · rintro ⟨⟨x, hxU, rfl⟩, hwD₁⟩
        have hjx : j x ∈ range j ∩ D₁ := ⟨mem_range_self x, hwD₁⟩
        rw [hinter₁] at hjx
        obtain ⟨c, hc, hcj⟩ := hjx
        have hxc : x = c := hj.injective hcj.symm
        have hxV : x ∈ G.G.V := hG ⟨hbdS ▸ Or.inl (hxc ▸ hc), hxU⟩
        exact ⟨⟨x, hxV, rfl⟩, ⟨x, hxc ▸ hc, rfl⟩⟩
      · rintro ⟨⟨x, hxV, rfl⟩, hwC₁⟩
        have hwD₁ : j x ∈ D₁ := Surface.discBd_subset D₁ (hbD₁.symm ▸ hwC₁)
        exact ⟨⟨x, G.G.V_subset_U hxV, rfl⟩, hwD₁⟩
    · change j '' G.G.U ∩ D₂ = j '' G.G.V ∩ discBd D₂
      rw [hbD₂]
      ext w
      constructor
      · rintro ⟨⟨x, hxU, rfl⟩, hwD₂⟩
        have hjx : j x ∈ range j ∩ D₂ := ⟨mem_range_self x, hwD₂⟩
        rw [hinter₂] at hjx
        obtain ⟨c, hc, hcj⟩ := hjx
        have hxc : x = c := hj.injective hcj.symm
        have hxV : x ∈ G.G.V := hG ⟨hbdS ▸ Or.inr (hxc ▸ hc), hxU⟩
        exact ⟨⟨x, hxV, rfl⟩, ⟨x, hxc ▸ hc, rfl⟩⟩
      · rintro ⟨⟨x, hxV, rfl⟩, hwC₂⟩
        have hwD₂ : j x ∈ D₂ := Surface.discBd_subset D₂ (hbD₂.symm ▸ hwC₂)
        exact ⟨⟨x, G.G.V_subset_U hxV, rfl⟩, hwD₂⟩
  obtain ⟨x₁, hx₁⟩ := isOArc_nonempty hO₁
  obtain ⟨x₂, hx₂⟩ := isOArc_nonempty hO₂
  have hjx₁_C : j x₁ ∈ discComplement P₂ := hrange_eq ▸ mem_range_self x₁
  have hjx₂_C : j x₂ ∈ discComplement P₂ := hrange_eq ▸ mem_range_self x₂
  have hjx₁_N : j x₁ ∈ Γ₀.Uᶜ ∪ Γ₀.V := by
    by_cases hxU : x₁ ∈ G.G.U
    · exact Or.inr ⟨x₁, hF₁ ⟨hx₁, hxU⟩, rfl⟩
    · exact Or.inl fun ⟨y, hyU, hyx⟩ => hxU (hj.injective hyx ▸ hyU)
  have hjx₂_N : j x₂ ∈ Γ₀.Uᶜ ∪ Γ₀.V := by
    by_cases hxU : x₂ ∈ G.G.U
    · exact Or.inr ⟨x₂, hF₂ ⟨hx₂, hxU⟩, rfl⟩
    · exact Or.inl fun ⟨y, hyU, hyx⟩ => hxU (hj.injective hyx ▸ hyU)
  obtain ⟨q, hq_sub, hq_norm⟩ := exists_normal_path_in_discComplement hCS_Z Γ₀ P₂ hP₂ hP₂_disj
    havoid₂ hjx₁_C hjx₂_C hjx₁_N hjx₂_N
  have hx₁x₂_ne : j x₁ ≠ j x₂ := fun heq =>
    disjoint_left.mp hDisj hx₁ (hj.injective heq ▸ hx₂)
  have hjoined : JoinedIn (range q) (j x₁) (j x₂) :=
    ⟨q, fun t => mem_range_self t⟩
  have hjx₁_q : j x₁ ∈ range q := ⟨0, q.source⟩
  have hjx₂_q : j x₂ ∈ range q := ⟨1, q.target⟩
  obtain ⟨L_Z, hLZ_sub, hLZ_ends⟩ :=
    ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := range q) hjx₁_q hjx₂_q).mp
      hjoined).resolve_left hx₁x₂_ne
  have hLZ_range : L_Z ⊆ range j := hLZ_sub.trans (hrange_eq ▸ hq_sub)
  let L : Set S := j ⁻¹' L_Z
  have hjL_eq : j '' L = L_Z := image_preimage_eq_iff.mpr hLZ_range
  have hL_norm : G.G.IsNormal L := by
    rintro x ⟨hxL, hxU⟩
    obtain ⟨y, hyV, hyx⟩ := hq_norm ⟨hLZ_sub hxL, ⟨x, hxU, rfl⟩⟩
    exact hj.injective hyx ▸ hyV
  obtain ⟨fZ, _, _⟩ := id hLZ_ends
  exact ⟨L, hL_norm,
    ⟨fZ.trans ((Homeomorph.setCongr hjL_eq.symm).trans (hj.isEmbedding.homeomorphImage L).symm)⟩,
    ⟨x₁, hLZ_ends.left_mem, hx₁⟩, ⟨x₂, hLZ_ends.right_mem, hx₂⟩⟩

private theorem first_half_line_lies_inside_outer_disc
    (S : Type u)
    [TopologicalSpace S]
    (F₁ : Set S)
    (F₂ : Set S)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (E₁ : Set Z)
    (E₂ : Set Z)
    (hj : IsClosedEmbedding j)
    (hE₁ : IsClosedDisc E₁)
    (hbE₁ : discBd E₁ = j '' F₁)
    (hbE₂ : discBd E₂ = j '' F₂)
    (hE₂_in_E₁ : E₂ ⊆ discInt E₁)
    [T2Space Z]
    (hmanZ : ∀ (x : Z), IsManifoldPoint x)
    (barI₁ : Set S)
    (u : S)
    (z : S)
    (hbarI₁_ends : IsLineWithEnds barI₁ u z)
    (hu : u ∈ barI₁ ∩ F₂)
    (hbarI₁_disj : Disjoint barI₁ F₁) :
    j '' barI₁ ⊆ discInt E₁ := by
  have hpc : IsPreconnected (j '' barI₁) :=
    (IsLineWithEnds.isConnected hbarI₁_ends).2.image j hj.continuous.continuousOn
  have hdisj_bd : Disjoint (j '' barI₁) (discBd E₁) := by
    rw [hbE₁]
    exact (disjoint_image_iff hj.injective).mpr hbarI₁_disj
  rcases hE₁.side hmanZ hpc hdisj_bd with hin | hout
  · exact hin
  · have hju_in : j u ∈ discInt E₁ := hE₂_in_E₁ (Surface.discBd_subset E₂
      (hbE₂.symm ▸ mem_image_of_mem j hu.2))
    exact (disjoint_left.mp hout (mem_image_of_mem j hu.1) hju_in.1).elim

private theorem second_half_line_lies_inside_inner_complement
    (S : Type u)
    [TopologicalSpace S]
    (F₁ : Set S)
    (F₂ : Set S)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (E₁' : Set Z)
    (E₂' : Set Z)
    (hj : IsClosedEmbedding j)
    (hbE₁' : discBd E₁' = j '' F₁)
    (hE₂' : IsClosedDisc E₂')
    (hbE₂' : discBd E₂' = j '' F₂)
    (hE₁'_in_E₂' : E₁' ⊆ discInt E₂')
    [T2Space Z]
    (hmanZ : ∀ (x : Z), IsManifoldPoint x)
    (barI₂ : Set S)
    (v : S)
    (z : S)
    (hbarI₂_ends : IsLineWithEnds barI₂ z v)
    (hv : v ∈ barI₂ ∩ F₁)
    (hbarI₂_disj : Disjoint barI₂ F₂) :
    j '' barI₂ ⊆ discInt E₂' := by
  have hpc : IsPreconnected (j '' barI₂) :=
    (IsLineWithEnds.isConnected hbarI₂_ends).2.image j hj.continuous.continuousOn
  have hdisj_bd : Disjoint (j '' barI₂) (discBd E₂') := by
    rw [hbE₂']
    exact (disjoint_image_iff hj.injective).mpr hbarI₂_disj
  rcases hE₂'.side hmanZ hpc hdisj_bd with hin | hout
  · exact hin
  · have hjv_in : j v ∈ discInt E₂' := hE₁'_in_E₂' (Surface.discBd_subset E₁'
      (hbE₁'.symm ▸ mem_image_of_mem j hv.2))
    exact (disjoint_left.mp hout (mem_image_of_mem j hv.1) hjv_in.1).elim

private theorem three_caps_pairwise_disjoint
    (Z : Type u)
    (D₁ : Set Z)
    (D₂ : Set Z)
    (hD₁D₂_disj : Disjoint D₁ D₂)
    (D₃ : Set Z)
    (hD₁D₃_disj : Disjoint D₁ D₃)
    (hD₂D₃_disj : Disjoint D₂ D₃) :
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    ∀ (i k : Fin 3), i ≠ k → Disjoint (P i) (P k) := by
  intro P i k hik
  fin_cases i <;> fin_cases k
  · exact (hik rfl).elim
  · exact hD₁D₂_disj
  · exact hD₁D₃_disj
  · exact hD₁D₂_disj.symm
  · exact (hik rfl).elim
  · exact hD₂D₃_disj
  · exact hD₁D₃_disj.symm
  · exact hD₂D₃_disj.symm
  · exact (hik rfl).elim

private theorem graph_intersects_removed_discs_only_at_boundary_vertices
    (S : Type u)
    [TopologicalSpace S]
    (C₁ : Set S)
    (C₂ : Set S)
    (G : SurfaceDigraph S)
    (hG : G.IsProper)
    (hbdS : bd S = C₁ ∪ C₂)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (D₂ : Set Z)
    (hj : IsClosedEmbedding j)
    (hbD₁ : discBd D₁ = j '' C₁)
    (hbD₂ : discBd D₂ = j '' C₂)
    (hinter₁ : range j ∩ D₁ = j '' C₁)
    (hinter₂ : range j ∩ D₂ = j '' C₂)
    (Δ : Set S)
    (hΔ_disj_G : Disjoint Δ G.G.U) :
    let D₃ : Set Z := j '' Δ
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    ∀ (i : Fin 3), (embedDrawing hj G.G).U ∩ P i = (embedDrawing hj G.G).V ∩ discBd (P i) := by
  intro D₃ P i
  fin_cases i
  · change j '' G.G.U ∩ D₁ = j '' G.G.V ∩ discBd D₁
    rw [hbD₁]
    ext w
    constructor
    · rintro ⟨⟨x, hxU, rfl⟩, hwD₁⟩
      have hjx : j x ∈ range j ∩ D₁ := ⟨mem_range_self x, hwD₁⟩
      rw [hinter₁] at hjx
      obtain ⟨c, hc, hcj⟩ := hjx
      have hxc : x = c := hj.injective hcj.symm
      have hxV : x ∈ G.G.V := hG ⟨hbdS ▸ Or.inl (hxc ▸ hc), hxU⟩
      exact ⟨⟨x, hxV, rfl⟩, ⟨x, hxc ▸ hc, rfl⟩⟩
    · rintro ⟨⟨x, hxV, rfl⟩, hwC₁⟩
      exact ⟨⟨x, G.G.V_subset_U hxV, rfl⟩, Surface.discBd_subset D₁ (hbD₁.symm ▸ hwC₁)⟩
  · change j '' G.G.U ∩ D₂ = j '' G.G.V ∩ discBd D₂
    rw [hbD₂]
    ext w
    constructor
    · rintro ⟨⟨x, hxU, rfl⟩, hwD₂⟩
      have hjx : j x ∈ range j ∩ D₂ := ⟨mem_range_self x, hwD₂⟩
      rw [hinter₂] at hjx
      obtain ⟨c, hc, hcj⟩ := hjx
      have hxc : x = c := hj.injective hcj.symm
      have hxV : x ∈ G.G.V := hG ⟨hbdS ▸ Or.inr (hxc ▸ hc), hxU⟩
      exact ⟨⟨x, hxV, rfl⟩, ⟨x, hxc ▸ hc, rfl⟩⟩
    · rintro ⟨⟨x, hxV, rfl⟩, hwC₂⟩
      exact ⟨⟨x, G.G.V_subset_U hxV, rfl⟩, Surface.discBd_subset D₂ (hbD₂.symm ▸ hwC₂)⟩
  · change j '' G.G.U ∩ D₃ = j '' G.G.V ∩ discBd D₃
    have h1 : j '' G.G.U ∩ D₃ = ∅ :=
      ((disjoint_image_iff hj.injective).mpr hΔ_disj_G.symm).inter_eq
    have h2 : j '' G.G.V ∩ discBd D₃ = ∅ :=
      (Disjoint.mono (image_mono G.G.V_subset_U) (Surface.discBd_subset D₃)
        ((disjoint_image_iff hj.injective).mpr hΔ_disj_G.symm)).inter_eq
    rw [h1, h2]

private theorem moved_model_intersects_removed_discs_only_at_boundary_vertices
    (S : Type u)
    [TopologicalSpace S]
    (C₁ : Set S)
    (C₂ : Set S)
    (H : SurfaceDigraph S)
    (hH : H.IsProper)
    (hbdS : bd S = C₁ ∪ C₂)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (D₂ : Set Z)
    (hj : IsClosedEmbedding j)
    (hbD₁ : discBd D₁ = j '' C₁)
    (hbD₂ : discBd D₂ = j '' C₂)
    (hinter₁ : range j ∩ D₁ = j '' C₁)
    (hinter₂ : range j ∩ D₂ = j '' C₂)
    (Δ : Set S)
    (β : S ≃ₜ S)
    (hβ_fix : ∀ x ∈ bd S, β x = x)
    (hΔ_disj_H : Disjoint (⇑β '' H.G.U) Δ) :
    let D₃ : Set Z := j '' Δ
    let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
    let fH : S → Z := j ∘ ⇑β
    ∀ (hfH : IsClosedEmbedding fH),
    ∀ (i : Fin 3), (embedDrawing hfH H.G).U ∩ P i = (embedDrawing hfH H.G).V ∩ discBd (P i) := by
  intro D₃ P fH hfH i
  fin_cases i
  · change fH '' H.G.U ∩ D₁ = fH '' H.G.V ∩ discBd D₁
    rw [hbD₁]
    ext w
    constructor
    · rintro ⟨⟨x, hxU, rfl⟩, hwD₁⟩
      have hjx : j (β x) ∈ range j ∩ D₁ := ⟨mem_range_self (β x), hwD₁⟩
      rw [hinter₁] at hjx
      obtain ⟨c, hc, hcj⟩ := hjx
      have hβxc : β x = c := hj.injective hcj.symm
      have hxc : x = c := β.injective (hβxc.trans (hβ_fix c (hbdS ▸ Or.inl hc)).symm)
      have hxV : x ∈ H.G.V := hH ⟨hbdS ▸ Or.inl (hxc ▸ hc), hxU⟩
      exact ⟨⟨x, hxV, rfl⟩, ⟨c, hc, hcj⟩⟩
    · rintro ⟨⟨x, hxV, rfl⟩, hwC₁⟩
      exact ⟨⟨x, H.G.V_subset_U hxV, rfl⟩, Surface.discBd_subset D₁ (hbD₁.symm ▸ hwC₁)⟩
  · change fH '' H.G.U ∩ D₂ = fH '' H.G.V ∩ discBd D₂
    rw [hbD₂]
    ext w
    constructor
    · rintro ⟨⟨x, hxU, rfl⟩, hwD₂⟩
      have hjx : j (β x) ∈ range j ∩ D₂ := ⟨mem_range_self (β x), hwD₂⟩
      rw [hinter₂] at hjx
      obtain ⟨c, hc, hcj⟩ := hjx
      have hβxc : β x = c := hj.injective hcj.symm
      have hxc : x = c := β.injective (hβxc.trans (hβ_fix c (hbdS ▸ Or.inr hc)).symm)
      have hxV : x ∈ H.G.V := hH ⟨hbdS ▸ Or.inr (hxc ▸ hc), hxU⟩
      exact ⟨⟨x, hxV, rfl⟩, ⟨c, hc, hcj⟩⟩
    · rintro ⟨⟨x, hxV, rfl⟩, hwC₂⟩
      exact ⟨⟨x, H.G.V_subset_U hxV, rfl⟩, Surface.discBd_subset D₂ (hbD₂.symm ▸ hwC₂)⟩
  · change fH '' H.G.U ∩ D₃ = fH '' H.G.V ∩ discBd D₃
    rw [image_comp, image_comp]
    have h1 : j '' (β '' H.G.U) ∩ D₃ = ∅ :=
      ((disjoint_image_iff hj.injective).mpr hΔ_disj_H).inter_eq
    have h2 : j '' (β '' H.G.V) ∩ discBd D₃ = ∅ :=
      (Disjoint.mono (image_mono (image_mono H.G.V_subset_U)) (Surface.discBd_subset D₃)
        ((disjoint_image_iff hj.injective).mpr hΔ_disj_H)).inter_eq
    rw [h1, h2]

private theorem lifted_drawings_agree_on_three_cuffs
    (S : Type u)
    [TopologicalSpace S]
    (C₁ : Set S)
    (C₂ : Set S)
    (H : SurfaceDigraph S)
    (G : SurfaceDigraph S)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    [Nonempty S]
    (hbdS : bd S = C₁ ∪ C₂)
    (Z : Type u)
    [TopologicalSpace Z]
    (j : S → Z)
    (D₁ : Set Z)
    (D₂ : Set Z)
    (hj : IsClosedEmbedding j)
    (hbD₁ : discBd D₁ = j '' C₁)
    (hbD₂ : discBd D₂ = j '' C₂)
    (β : S ≃ₜ S)
    (hβ_fix : ∀ x ∈ bd S, β x = x) :
    ∀ (D₃ : Set Z),
    ∀ (C_sub : Set Z),
    let S' : Type u := ↥C_sub
    ∀ [Nonempty S'],
    (bd S' = Subtype.val ⁻¹' (discBd D₁ ∪ discBd D₂ ∪ discBd D₃)) →
    let fH : S → Z := j ∘ ⇑β
    ∀ (hfH : IsClosedEmbedding fH),
    ∀ (hUC_G : (embedDrawing hj G.G).U ⊆ C_sub),
    ∀ (hUC_H : (embedDrawing hfH H.G).U ⊆ C_sub),
    let G' : SurfaceDigraph S' := liftSurfaceDigraph hj G C_sub hUC_G
    let H' : SurfaceDigraph S' := liftSurfaceDigraph hfH H C_sub hUC_H
    (Disjoint (j '' G.G.V) (discBd D₃)) →
    (Disjoint (fH '' H.G.V) (discBd D₃)) →
    G'.G.V ∩ bd S' = H'.G.V ∩ bd S' := by
  intro D₃ C_sub S' _ hbdS' fH hfH hUC_G hUC_H G' H' hD₃_disj_GV hD₃_disj_HV
  ext y
  rw [show G'.G = drawingInSubspace (embedDrawing hj G.G) C_sub hUC_G from rfl,
    show H'.G = drawingInSubspace (embedDrawing hfH H.G) C_sub hUC_H from rfl,
    drawingInSubspace_embedDrawing_V, drawingInSubspace_embedDrawing_V, hbdS']
  constructor
  · rintro ⟨⟨x, hxV, hzx⟩, hy_bd⟩
    have hyz : y.val = j x := hzx.symm
    have hjx_bd : j x ∈ discBd D₁ ∪ discBd D₂ := by
      rcases hy_bd with h12 | h3
      · exact hyz ▸ h12
      · exact (disjoint_left.mp hD₃_disj_GV ⟨x, hxV, rfl⟩ (hyz ▸ h3)).elim
    have hx_bd : x ∈ bd S := by
      rw [hbdS]
      rcases hjx_bd with h1 | h2
      · rw [hbD₁] at h1; obtain ⟨c, hc, hcj⟩ := h1; exact Or.inl (hj.injective hcj ▸ hc)
      · rw [hbD₂] at h2; obtain ⟨c, hc, hcj⟩ := h2; exact Or.inr (hj.injective hcj ▸ hc)
    have hxHV : x ∈ H.G.V := by
      have : x ∈ G.G.V ∩ bd S := ⟨hxV, hx_bd⟩
      rw [hbd_eq] at this
      exact this.1
    refine ⟨⟨x, hxHV, ?_⟩, hy_bd⟩
    change j (β x) = y.val
    rw [hβ_fix x hx_bd, hzx]
  · rintro ⟨⟨x, hxHV, hzx⟩, hy_bd⟩
    have hyz : y.val = fH x := hzx.symm
    have hjx_bd : fH x ∈ discBd D₁ ∪ discBd D₂ := by
      rcases hy_bd with h12 | h3
      · exact hyz ▸ h12
      · exact (disjoint_left.mp hD₃_disj_HV ⟨x, hxHV, rfl⟩ (hyz ▸ h3)).elim
    have hx_bd : x ∈ bd S := by
      rw [hbdS]
      rcases hjx_bd with h1 | h2
      · rw [hbD₁] at h1
        obtain ⟨c, hc, hcj⟩ := h1
        have hβxc : β x = c := hj.injective hcj.symm
        have hxc : x = c := β.injective (hβxc.trans (hβ_fix c (hbdS ▸ Or.inl hc)).symm)
        exact Or.inl (hxc ▸ hc)
      · rw [hbD₂] at h2
        obtain ⟨c, hc, hcj⟩ := h2
        have hβxc : β x = c := hj.injective hcj.symm
        have hxc : x = c := β.injective (hβxc.trans (hβ_fix c (hbdS ▸ Or.inr hc)).symm)
        exact Or.inr (hxc ▸ hc)
    have hxGV : x ∈ G.G.V := by
      have : x ∈ H.G.V ∩ bd S := ⟨hxHV, hx_bd⟩
      rw [← hbd_eq] at this
      exact this.1
    refine ⟨⟨x, hxGV, ?_⟩, hy_bd⟩
    have : fH x = j x := congrArg j (hβ_fix x hx_bd)
    rw [← this, hzx]

private theorem lifted_cylinder_alpha_bound
    {S : Type u} {S' : Type u} [TopologicalSpace S] [TopologicalSpace S']
    (H : Drawing S) (G' H' : Drawing S') :
    let t := H.V.ncard + H.E.ncard
    let g' := numInternalIsolatedVertices H'
    rCylinderBound H * 5 ^ t ≤ alpha G' →
    H'.E.ncard = H.E.ncard →
    g' ≤ H.V.ncard →
    42 * (2 * t + 4) * 5 ^ (g' + H'.E.ncard) * vModel 0 0 (t + 4) (2 * t + 4) ≤ alpha G' := by
  intro t g' halpha' hH'_E_ncard hg'_le_V
  have hpow_le : 5 ^ (g' + H'.E.ncard) ≤ 5 ^ t := by
    apply Nat.pow_le_pow_right (by decide)
    rw [hH'_E_ncard]
    omega
  have h42 : 42 * (2 * t + 4) * vModel 0 0 (t + 4) (2 * t + 4) = rCylinderBound H := by
    unfold rCylinderBound
    dsimp
    ring
  calc 42 * (2 * t + 4) * 5 ^ (g' + H'.E.ncard) * vModel 0 0 (t + 4) (2 * t + 4)
      = (42 * (2 * t + 4) * vModel 0 0 (t + 4) (2 * t + 4)) * 5 ^ (g' + H'.E.ncard) := by ring
    _ = rCylinderBound H * 5 ^ (g' + H'.E.ncard) := by rw [h42]
    _ ≤ rCylinderBound H * 5 ^ t := Nat.mul_le_mul_left _ hpow_le
    _ ≤ alpha G' := halpha'

private theorem boundary_subset_card_lt_of_agreement
    {S : Type u} [TopologicalSpace S] {G H : Drawing S} {C : Set S} {r : ℕ}
    (hC : C ⊆ bd S) (hbd : G.V ∩ bd S = H.V ∩ bd S)
    (hr : H.V.ncard < r) : (G.V ∩ C).ncard < r := by
  have hsub : G.V ∩ C ⊆ H.V := fun x hx => by
    have hmem : x ∈ G.V ∩ bd S := ⟨hx.1, hC hx.2⟩
    rw [hbd] at hmem
    exact hmem.1
  exact (Set.ncard_le_ncard hsub H.finite_V).trans_lt hr

private theorem cylinder_bound_exceeds_size {S : Type u} [TopologicalSpace S]
    (H : Drawing S) :
    let t := H.V.ncard + H.E.ncard
    t < rCylinderBound H * 5 ^ t := by
  intro t
  have hv_ge : 2 * (2 * t + 4) ≤ vModel 0 0 (t + 4) (2 * t + 4) :=
    two_mul_k_le_vModel 0 0 (t + 4) (2 * t + 4)
  have h5_pos : 1 ≤ 5 ^ t := Nat.one_le_pow t 5 (by decide)
  have h1 : 1 ≤ vModel 0 0 (t + 4) (2 * t + 4) := by omega
  have h2 : 1 ≤ vModel 0 0 (t + 4) (2 * t + 4) * 5 ^ t := Nat.mul_le_mul h1 h5_pos
  have h3 : 84 * (t + 2) ≤ 84 * (t + 2) * (vModel 0 0 (t + 4) (2 * t + 4) * 5 ^ t) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h4 : rCylinderBound H * 5 ^ t = 84 * (t + 2) * (vModel 0 0 (t + 4) (2 * t + 4) * 5 ^ t) := by
    dsimp [rCylinderBound, t]
    ring
  rw [h4]
  omega

/-- **Graph Minors VII, proof of (9.3) from (9.1)** (pages 244–245):
"Because of Claims 1 and 2, we can apply (9.1) with $\Sigma, a, b, c, c_0, k$ replaced by
$\Sigma', 0, 0, 3, t+4, 2t+4$, respectively; and we deduce that $(H, H^+, H^-)$ is a
boundary-rooted minor of $(G, G^+, G^-)$ in $\Sigma'$, and therefore also in $\Sigma$, as
required." -/
theorem cylinderPunctureReduction :
    ∀ (S : Type u) [TopologicalSpace S],
      IsSurface S → Nonempty (S ≃ₜ SurfaceModel 0 0 2) →
      ∀ C₁ C₂ : Set S, cuffs S = {C₁, C₂} → C₁ ≠ C₂ →
      ∀ H G : SurfaceDigraph S, H.IsProper → G.IsProper →
        G.G.V ∩ bd S = H.G.V ∩ bd S →
        ∀ F₁ F₂ : Set S,
          G.G.IsNormal F₁ → G.G.IsNormal F₂ →
          CylinderOArcsInOrder C₁ F₂ F₁ C₂ →
          (∀ x ∈ F₂, IsPointInsideSurroundingOArc C₁ F₁ x) →
          Disjoint F₁ (bd S) → Disjoint F₂ (bd S) →
          (∀ F : Set S, G.G.IsNormal F → IsLine F →
            (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
            2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard) →
          rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂ →
          (G.G.V ∩ C₁).ncard ≤ maxDisjointPaths G.G F₁ C₁ →
          (G.G.V ∩ C₂).ncard ≤ maxDisjointPaths G.G F₂ C₂ →
          IsBoundaryRootedMinor H G := by
  intro S _ hS he C₁ C₂ hcuffs hne H G hH hG hbd_eq F₁ F₂ hF₁ hF₂ hOrd hInside₁₂ hbd₁ hbd₂
    hLine hk12 hkC₁ hkC₂
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  obtain ⟨e₀⟩ := id he
  have : ConnectedSpace S := by
    have := (isSurface_model 0 0 2).2
    exact e₀.symm.surjective.connectedSpace e₀.symm.continuous
  have : Nonempty S := (inferInstance : ConnectedSpace S).toNonempty
  have hC₁ : C₁ ∈ cuffs S := by rw [hcuffs]; simp
  have hC₂ : C₂ ∈ cuffs S := by rw [hcuffs]; simp
  have hbdS : bd S = C₁ ∪ C₂ := by rw [← sUnion_cuffs, hcuffs, sUnion_pair]
  have hO₁ : IsOArc F₁ := hOrd.2.2.2.1
  have hO₂ : IsOArc F₂ := hOrd.2.2.2.2.1
  have hDisj : Disjoint F₁ F₂ := hOrd.2.2.2.2.2.1
  let t : ℕ := H.G.V.ncard + H.G.E.ncard
  let r : ℕ := rCylinderBound H.G * 5 ^ t
  have hr_gt_t : t < r := cylinder_bound_exceeds_size H.G
  have hr_pos : 1 ≤ r := by omega
  -- Step 1: Cap cuffs C₁, C₂ to get sphere Z and nested discs E₁, E₂, E₁', E₂'
  obtain ⟨Z, tZ, eZ, j, D₁, D₂, E₁, E₂, E₁', E₂', hCS_Z, hSphZ, hconnZ, hj, hD₁, hD₂, hD₁D₂_disj,
    hbD₁, hbD₂, hunion, hinter₁, hinter₂, hrange_eq, hE₁, hbE₁, hE₂, hbE₂,
    hE₁', hbE₁', hE₁'_compl, hE₁'_int, hE₂', hbE₂', hE₂'_compl, hE₂'_int,
    hD₁_in_E₂, hE₂_in_E₁, hE₁_disj_D₂, hD₂_in_E₁', hE₁'_in_E₂', hE₂'_disj_D₁⟩ :=
    exists_sphere_cap_and_nested_discs hS he hcuffs hne hOrd hInside₁₂ hbd₁ hbd₂
  have : T2Space Z := hCS_Z.2.1
  have : ConnectedSpace Z := hconnZ
  have hmanZ : ∀ x : Z, IsManifoldPoint x := fun x => (hCS_Z.2.2 x).isManifoldPoint
  -- Step 2: Show a G.G-normal line exists between F₁ and F₂, and choose minimal I and z
  have hex_line : ∃ F : Set S, G.G.IsNormal F ∧ IsLine F ∧ (F ∩ F₁).Nonempty ∧ (F ∩ F₂).Nonempty
    := by
    exact cylinder_has_normal_line_between_boundaries S C₁ C₂ G hG F₁ F₂ hF₁ hF₂ hbdS hO₁ hO₂
      hDisj Z j D₁ D₂ hCS_Z hj hD₁ hD₂ hD₁D₂_disj hbD₁ hbD₂ hinter₁ hinter₂ hrange_eq
  obtain ⟨I, barI₁, barI₂, u, v, z, m, hI_ends, huF₂, hvF₁, hI_disj,
    hI_norm, hbarI₁_norm, hbarI₂_norm, hbarI₁_ends, hbarI₂_ends, hbarI₁_sub, hbarI₂_sub, hbar_union,
    hz_mem, hu, hbarI₁_disj, hv, hbarI₂_disj, h2r, hI_ncard, hbarI₁_ncard, hbarI₂_ncard, hmin⟩ :=
    exists_minimal_line_and_split G.G hO₁ hO₂ hDisj hr_pos hex_line hLine
  -- Step 3: Show j '' barI₁ ⊆ discInt E₁ and j '' barI₂ ⊆ discInt E₂'
  have hbarI₁_in_E₁ : j '' barI₁ ⊆ discInt E₁ := by
    exact first_half_line_lies_inside_outer_disc S F₁ F₂ Z j E₁ E₂ hj hE₁ hbE₁ hbE₂ hE₂_in_E₁
      hmanZ barI₁ u z hbarI₁_ends hu hbarI₁_disj
  have hbarI₂_in_E₂' : j '' barI₂ ⊆ discInt E₂' := by
    exact second_half_line_lies_inside_inner_complement S F₁ F₂ Z j E₁' E₂' hj hbE₁' hE₂' hbE₂'
      hE₁'_in_E₂' hmanZ barI₂ v z hbarI₂_ends hv hbarI₂_disj
  have hjz_in_E₁ : j z ∈ discInt E₁ := hbarI₁_in_E₁ (mem_image_of_mem j hbarI₁_ends.right_mem)
  have hjz_in_E₂' : j z ∈ discInt E₂' := hbarI₂_in_E₂' (mem_image_of_mem j hbarI₂_ends.left_mem)
  -- Step 4: Construct Δ around z and move H off Δ
  have hz_not_bd : z ∉ bd S := by
    intro hz_bd
    rcases hbdS ▸ hz_bd with hzC₁ | hzC₂
    · have hjz_D₁ : j z ∈ D₁ := Surface.discBd_subset D₁ (hbD₁.symm ▸ mem_image_of_mem j hzC₁)
      exact disjoint_left.mp hE₂'_disj_D₁ hjz_in_E₂'.1 hjz_D₁
    · have hjz_D₂ : j z ∈ D₂ := Surface.discBd_subset D₂ (hbD₂.symm ▸ mem_image_of_mem j hzC₂)
      exact disjoint_left.mp hE₁_disj_D₂ hjz_in_E₁.1 hjz_D₂
  have hz_int : IsInteriorPoint z := by
    by_contra h
    exact hz_not_bd h
  let W : Set S := j ⁻¹' (discInt E₁ ∩ discInt E₂') ∩ G.G.Uᶜ ∩ (bd S)ᶜ
  have hW_open : IsOpen W :=
    ((((hE₁.isOpen_discInt hmanZ).inter (hE₂'.isOpen_discInt hmanZ)).preimage hj.continuous).inter
      G.G.isClosed_U.isOpen_compl).inter (isClosed_bd S).isOpen_compl
  have hzW : z ∈ W := ⟨⟨⟨hjz_in_E₁, hjz_in_E₂'⟩, fun hzU => hz_mem.2 (Or.inl hzU)⟩, hz_not_bd⟩
  obtain ⟨Δ, hΔ, hzΔ, hΔ_sub⟩ := exists_disc_in_open hz_int hW_open hzW
  have hΔ_disj_G : Disjoint Δ G.G.U := disjoint_left.mpr fun x hxΔ hxU => (hΔ_sub hxΔ).1.2 hxU
  have hΔ_disj_bd : Disjoint Δ (bd S) := disjoint_left.mpr fun x hxΔ hxbd => (hΔ_sub hxΔ).2 hxbd
  have hΔ_bd : Δ ∩ bd S = ∅ := hΔ_disj_bd.inter_eq
  obtain ⟨β, hβ_fix, hΔ_disj_H⟩ := exists_move_drawing_off_disc hS H.G hΔ hΔ_bd
  let D₃ : Set Z := j '' Δ
  obtain ⟨hD₃, hbD₃⟩ := isClosedDisc_image hΔ hj.continuous.continuousOn hj.injective.injOn
  have hjz_D₃ : j z ∈ discInt D₃ := by
    refine ⟨mem_image_of_mem j hzΔ.1, ?_⟩
    rw [hbD₃]
    rintro ⟨x, hx, hxz⟩
    exact hzΔ.2 (hj.injective hxz ▸ hx)
  have hD₃_in_E₁ : D₃ ⊆ discInt E₁ := by
    rintro _ ⟨x, hxΔ, rfl⟩
    exact (hΔ_sub hxΔ).1.1.1
  have hD₃_in_E₂' : D₃ ⊆ discInt E₂' := by
    rintro _ ⟨x, hxΔ, rfl⟩
    exact (hΔ_sub hxΔ).1.1.2
  have hD₁D₃_disj : Disjoint D₁ D₃ :=
    hE₂'_disj_D₁.symm.mono_right (hD₃_in_E₂'.trans (discInt_subset E₂'))
  have hD₂D₃_disj : Disjoint D₂ D₃ :=
    hE₁_disj_D₂.symm.mono_right (hD₃_in_E₁.trans (discInt_subset E₁))
  let P : Fin 3 → Set Z := ![D₁, D₂, D₃]
  have hP : ∀ i, IsClosedDisc (P i) := fun i => by
    fin_cases i
    · exact hD₁
    · exact hD₂
    · exact hD₃
  have hP_disj : Pairwise (fun i k => Disjoint (P i) (P k)) := fun i k hik => by
    exact three_caps_pairwise_disjoint Z D₁ D₂ hD₁D₂_disj D₃ hD₁D₃_disj hD₂D₃_disj i k hik
  let C_sub : Set Z := discComplement P
  let S' : Type u := ↥C_sub
  have hS' : IsSurface S' := discComplement_isSurface hCS_Z P hP hP_disj
  have : T2Space S' := hS'.2.1
  have : ConnectedSpace S' := Subtype.connectedSpace (discComplement_isConnected hCS_Z P hP hP_disj)
  have : Nonempty S' := (inferInstance : ConnectedSpace S').toNonempty
  have heS' : Nonempty (S' ≃ₜ SurfaceModel 0 0 3) := by
    have hcard : Nat.card (Fin 3) = 3 := by simp
    exact hcard ▸ discComplement_model_of_closed_model hCS_Z P hP hP_disj eZ
  have hbdS' : bd S' = (Subtype.val : S' → Z) ⁻¹' (discBd D₁ ∪ discBd D₂ ∪ discBd D₃) := by
    rw [discComplement_boundary_eq hCS_Z P hP]
    ext y
    simp only [mem_preimage, mem_iUnion, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false, P,
      Matrix.cons_val_zero, mem_union]
    tauto
  -- Step 5: Lift H and G to S'
  let fH : S → Z := j ∘ β
  have hfH : IsClosedEmbedding fH := hj.comp β.isClosedEmbedding
  have havoid_G : ∀ i : Fin 3, (embedDrawing hj G.G).U ∩ P i = (embedDrawing hj G.G).V ∩ discBd
    (P i) := by
    exact graph_intersects_removed_discs_only_at_boundary_vertices S C₁ C₂ G hG hbdS Z j D₁ D₂ hj
      hbD₁ hbD₂ hinter₁ hinter₂ Δ hΔ_disj_G
  have havoid_H : ∀ i : Fin 3, (embedDrawing hfH H.G).U ∩ P i = (embedDrawing hfH H.G).V ∩ discBd
    (P i) := by
    exact moved_model_intersects_removed_discs_only_at_boundary_vertices S C₁ C₂ H hH hbdS Z j D₁
      D₂ hj hbD₁ hbD₂ hinter₁ hinter₂ Δ β hβ_fix hΔ_disj_H    hfH
  have hUC_G := drawing_support_subset_discComplement hCS_Z (embedDrawing hj G.G) P hP hP_disj
    havoid_G
  have hUC_H := drawing_support_subset_discComplement hCS_Z (embedDrawing hfH H.G) P hP hP_disj
    havoid_H
  let G' : SurfaceDigraph S' := liftSurfaceDigraph hj G C_sub hUC_G
  let H' : SurfaceDigraph S' := liftSurfaceDigraph hfH H C_sub hUC_H
  have hH'_prop : H'.IsProper :=
    drawingInDiscComplement_isProper hCS_Z (embedDrawing hfH H.G) P hP hP_disj havoid_H
  have hG'_prop : G'.IsProper :=
    drawingInDiscComplement_isProper hCS_Z (embedDrawing hj G.G) P hP hP_disj havoid_G
  have hD₃_disj_GV : Disjoint (j '' G.G.V) (discBd D₃) :=
    Disjoint.mono (image_mono G.G.V_subset_U) (Surface.discBd_subset D₃)
      ((disjoint_image_iff hj.injective).mpr hΔ_disj_G.symm)
  have hD₃_disj_HV : Disjoint (fH '' H.G.V) (discBd D₃) := by
    rw [image_comp]
    exact Disjoint.mono (image_mono (image_mono H.G.V_subset_U)) (Surface.discBd_subset D₃)
      ((disjoint_image_iff hj.injective).mpr hΔ_disj_H)
  have hbd_eq' : G'.G.V ∩ bd S' = H'.G.V ∩ bd S' := by
    exact lifted_drawings_agree_on_three_cuffs S C₁ C₂ H G hbd_eq hbdS Z j D₁ D₂ hj hbD₁ hbD₂ β
      hβ_fix D₃ C_sub hbdS'  hfH hUC_G hUC_H   hD₃_disj_GV hD₃_disj_HV
  -- Step 6: Verify Claims 1 and 2 and apply (9.1)
  have hsize : H.G.V.ncard < r := (Nat.le_add_right _ _).trans_lt hr_gt_t
  have hC₁_lt_r := boundary_subset_card_lt_of_agreement
    (hbdS ▸ subset_union_left : C₁ ⊆ bd S) hbd_eq hsize
  have hC₂_lt_r := boundary_subset_card_lt_of_agreement
    (hbdS ▸ subset_union_right : C₂ ⊆ bd S) hbd_eq hsize
  have hBL' : IsBoundaryLinked G'.G :=
    lemma_9_3_claim_1 hCS_Z hSphZ hj G.G hDisj hbarI₁_norm hbarI₂_norm hbarI₁_ends hbarI₂_ends
      hu hbarI₁_disj hv hbarI₂_disj h2r hbarI₁_ncard hbarI₂_ncard hmin
      hD₁ hbD₁ hD₂ hbD₂ hD₃ hD₃_disj_GV hP_disj havoid_G hrange_eq
      hE₁ hbE₁ hE₂ hbE₂ hE₁' hbE₁' hE₁'_compl hE₂' hE₂'_compl
      hD₁_in_E₂ hE₂_in_E₁ hD₂_in_E₁' hE₁'_in_E₂' hbarI₁_in_E₁ hbarI₂_in_E₂' hjz_D₃
      hC₁_lt_r hC₂_lt_r hkC₁ hkC₂
  have halpha' : r ≤ alpha G'.G :=
    lemma_9_3_claim_2 hCS_Z hSphZ hj G.G hDisj hbarI₁_norm hbarI₂_norm hbarI₁_ends hbarI₂_ends
      hu hbarI₁_disj hv hbarI₂_disj h2r hbarI₁_ncard hbarI₂_ncard hmin
      hD₁ hD₂ hD₃ hP_disj havoid_G hrange_eq
      hE₁ hbE₁ hE₂ hbE₂ hE₁' hbE₁' hE₁'_compl hE₂' hE₂'_compl
      hD₁_in_E₂ hE₂_in_E₁ hD₂_in_E₁' hE₁'_in_E₂' hbarI₁_in_E₁ hbarI₂_in_E₂' hjz_D₃ hk12
  have hH'_V_ncard : H'.G.V.ncard = H.G.V.ncard :=
    drawingInSubspace_embedDrawing_V_ncard hfH H.G C_sub hUC_H
  have hH'_E_ncard : H'.G.E.ncard = H.G.E.ncard :=
    drawingInSubspace_embedDrawing_E_ncard hfH H.G C_sub hUC_H
  let g' : ℕ := numInternalIsolatedVertices H'.G
  have hg'_le_diff : g' ≤ (H'.G.V \ bd S').ncard :=
    Set.ncard_le_ncard (sep_subset _ _) H'.G.finite_V.sdiff
  have hdiff_inter : (H'.G.V \ bd S').ncard + (H'.G.V ∩ bd S').ncard = H.G.V.ncard := by
    have hdisj_diff : Disjoint (H'.G.V \ bd S') (H'.G.V ∩ bd S') :=
      disjoint_sdiff_left.mono_right inter_subset_right
    rw [← hH'_V_ncard, ← Set.ncard_union_eq hdisj_diff H'.G.finite_V.sdiff
      (H'.G.finite_V.inter_of_left _),
      sdiff_union_inter]
  have hg'_le_V : g' ≤ H.G.V.ncard := by omega
  have hk_bound : 2 * (2 * t + 4) ≥ 4 * H'.G.E.ncard + 4 * g' + (H'.G.V ∩ bd S').ncard + 2 * 3 + 2
    := by
    rw [hH'_E_ncard]
    omega
  have hc₀_bound : t + 4 ≥ 3 + H'.G.E.ncard + g' + 1 := by
    rw [hH'_E_ncard]
    omega
  have halpha_bound : alpha G'.G ≥ 42 * (2 * t + 4) * 5 ^ (g' + H'.G.E.ncard) * vModel 0 0 (t + 4)
    (2 * t + 4) := by
    exact lifted_cylinder_alpha_bound H.G G'.G H'.G halpha' hH'_E_ncard hg'_le_V
  have hminor' : IsBoundaryRootedMinor H' G' :=
    gm07_theorem_9_1.{u} S' hS' 0 0 3 (by decide) heS' H' hH'_prop (2 * t + 4)
      (t + 4) hk_bound hc₀_bound
      G' hG'_prop hbd_eq' hBL' halpha_bound
  refine isBoundaryRootedMinor_of_lift hfH hj H G C_sub hUC_H hUC_G hbd_eq.symm
    (fun x hx => congrArg j (hβ_fix x hx))
    (fun v ⟨hvV, hv_bd⟩ => ?_) hminor'
  rw [hbdS']
  change fH v ∈ discBd D₁ ∪ discBd D₂ ∪ discBd D₃
  have hfv : fH v = j v := congrArg j (hβ_fix v hv_bd)
  rw [hfv]
  rcases hbdS ▸ hv_bd with hvC₁ | hvC₂
  · exact Or.inl (Or.inl (hbD₁.symm ▸ mem_image_of_mem j hvC₁))
  · exact Or.inl (Or.inr (hbD₂.symm ▸ mem_image_of_mem j hvC₂))

end GraphMinor.GM07
