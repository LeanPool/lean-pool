/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46Matching
public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM07.Section46LongEdges
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46CentralEnds
import LeanPool.GraphMinor.GM07.Section46EdgeSegments
import LeanPool.GraphMinor.GM07.Section46OldVertices
import LeanPool.GraphMinor.GM07.Section46RetainedLinking
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.NetExists
import LeanPool.GraphMinor.GM07.NetSwapBasic

/-!
# The central edges in `Σ′`

Over the open central edge the map `θ` has one point, because the edge
misses `U(L)` and `bd(Σ)`. So `ψ` agrees on the two sides of `Δ` over this
open edge, and by continuity over its ends as well. Hence `θ` is one-to-one
over `U(K)`, which is what the matching claim of VII (4.6), page 226, needs.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']

theorem mem_U_iff_edge (Γ : Drawing S) {x : S} : x ∈ Γ.U ↔ x ∈ Γ.V ∨ ∃ e ∈ Γ.E, x ∈ e := by
  constructor
  · intro hx
    by_cases hV : x ∈ Γ.V
    · exact .inl hV
    · have h : x ∈ Γ.U \ Γ.V := ⟨hx, hV⟩
      exact .inr ⟨_, pathComponentIn_mem_arcComponentsIn h, mem_pathComponentIn_self h⟩
  · rintro (h | ⟨e, he, hx⟩)
    · exact Γ.V_subset_U h
    · exact (he.2.1 hx).1

/-- The two sides of `Δ` agree under `ψ` over a closed central segment, in VII (4.6), page 226. -/
theorem Net.psi_sides_eq (N : Net S) {L : Drawing S} {θ : S' → S} {ψ : N.D → S'}
    (hθ : IsCutAlongGraph L S' θ) (hψc : Continuous ψ) (hψ : ∀ x, θ (ψ x) = N.φ x)
    (i : Fin N.r) {s t : unitInterval} (hst : s < t)
    (hoff : ∀ r ∈ Ioo s t, N.φ (N.f i r) ∉ bd S ∪ L.U) :
    ∀ r ∈ Icc s t, ψ (N.f i r) = ψ (N.g i r) := by
  have hS' := hθ.isSurface
  have : T2Space S' := hS'.2.1
  have hcl : IsClosed {r : unitInterval | ψ (N.f i r) = ψ (N.g i r)} :=
    isClosed_eq (hψc.comp (N.f i).continuous) (hψc.comp (N.g i).continuous)
  have hsub : Ioo s t ⊆ {r : unitInterval | ψ (N.f i r) = ψ (N.g i r)} := by
    intro r hr
    apply hθ.interior_inj
    · intro hb
      rw [← hθ.preimage_bd_union_U] at hb
      apply hoff r hr
      have h := hψ (N.f i r)
      rw [mem_preimage, h] at hb
      exact hb
    · rw [hψ, hψ, N.pasting_eq]
  have hc : closure (Ioo s t) = Icc s t := closure_Ioo hst.ne
  rw [← hc]
  exact closure_minimal hsub hcl

section Central

variable {G J J' K L : Drawing S} {γ : Set S → unitInterval → S} {μ w : ℕ}
  {s t : longSeamEdges G J μ w → unitInterval} {W : longSeamEdges G J μ w → Set S}

/-- All the local properties of `K` in `Σ` on page 226 of VII (4.6). -/
theorem central_K_facts [T2Space S] (hS : IsSurface S) (N : Net S)
    (hJ : N.IsSeamGraphFor J) (hγ : EdgePar J γ)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)} ∧ (W e).ncard = 2)
    (hsmall : (G.V ∩ bd S).ncard < 2 * μ + w + 2)
    (hlong : ∀ e : longSeamEdges G J μ w, Disjoint e.1 (bd S))
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hKsub : K.IsSubdrawing J') (hKV : K.V = ⋃ e, W e)
    (hKE : K.E = centralEdges G J μ w γ s t)
    (hLsub : L.IsSubdrawing J') (hLV : L.V = J'.V)
    (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t)) :
    IsPairing K ∧ K.IsProper ∧ K.V ⊆ L.U ∧ K.IsNormal L.U ∧ K.U ⊆ ⋃ e, γ e.1 '' Icc (s e) (t e) ∧
      bd S ∪ L.U ∪ K.U = N.seamU ∧
      ∀ e : longSeamEdges G J μ w, ∀ r ∈ Ioo (s e) (t e), γ e.1 r ∉ bd S ∪ L.U := by
  have hcuts' : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)} := fun e =>
    ⟨(hcuts e).1, (hcuts e).2.1, (hcuts e).2.2.1, (hcuts e).2.2.2.1⟩
  have hclC : ∀ e : longSeamEdges G J μ w, closure (γ e.1 '' Ioo (s e) (t e)) =
      γ e.1 '' Icc (s e) (t e) := fun e =>
    closure_image_Ioo_eq_Icc hγ e.2.1 (hcuts e).2.2.1 (.inl (hcuts e).1.1)
  have hCe : ∀ e : longSeamEdges G J μ w, γ e.1 '' Icc (s e) (t e) ⊆ e.1 := fun e => by
    rw [← hclC e]
    exact central_closure_subset_old_edge hγ e.2.1 (hcuts e).1 (hcuts e).2.1 (hcuts e).2.2.1
  have hWC : ∀ e : longSeamEdges G J μ w, W e ⊆ γ e.1 '' Icc (s e) (t e) := by
    intro e x hx
    rw [(hcuts e).2.2.2.1] at hx
    have hle := (hcuts e).2.2.1.le
    rcases hx with rfl | rfl
    · exact ⟨s e, ⟨le_rfl, hle⟩, rfl⟩
    · exact ⟨t e, ⟨hle, le_rfl⟩, rfl⟩
  have hWe : ∀ e : longSeamEdges G J μ w, W e ⊆ e.1 := fun e => (hWC e).trans (hCe e)
  have hKUsub : K.U ⊆ ⋃ e, γ e.1 '' Icc (s e) (t e) := by
    intro x hx
    rcases (mem_U_iff_edge K).mp hx with h | ⟨f, hf, hxf⟩
    · rw [hKV] at h
      obtain ⟨e, he⟩ := mem_iUnion.mp h
      exact mem_iUnion.mpr ⟨e, hWC e he⟩
    · rw [hKE] at hf
      obtain ⟨e, rfl⟩ := hf
      exact mem_iUnion.mpr ⟨e, hclC e ▸ subset_closure hxf⟩
  have hclK : ∀ f ∈ K.E, closure f ∩ K.V ⊆ closure f ∩ J'.V := fun f _ x hx =>
    ⟨hx.1, hKsub.1 hx.2⟩
  have hCE : ∀ e : longSeamEdges G J μ w, γ e.1 '' Ioo (s e) (t e) ∈ K.E := fun e => by
    rw [hKE]
    exact ⟨e, rfl⟩
  have hends : ∀ e, closure (γ e.1 '' Ioo (s e) (t e)) ∩ K.V = W e := by
    intro e
    apply Subset.antisymm
    · rw [← central_edge_ends hγ W hWe hV e (hcuts e).1 (hcuts e).2.1 (hcuts e).2.2.1
        (hcuts e).2.2.2.1]
      exact hclK _ (hCE e)
    · intro x hx
      refine ⟨hclC e ▸ hWC e hx, ?_⟩
      rw [hKV]
      exact mem_iUnion.mpr ⟨e, hx⟩
  have hpair : IsPairing K := by
    intro v hv
    rw [hKV] at hv
    obtain ⟨e, he⟩ := mem_iUnion.mp hv
    refine ⟨_, hCE e, hclC e ▸ hWC e he, ?_, ?_⟩
    · rw [tilde_eq_closure_inter_V K (hCE e), hends e]
      exact (hcuts e).2.2.2.2
    · intro f hf hvf
      have hf' := hf
      rw [hKE] at hf'
      obtain ⟨e', rfl⟩ := hf'
      have h1 : v ∈ e'.1 := hCe e' (hclC e' ▸ hvf)
      have h2 : v ∈ e.1 := hWe e he
      have hee : e' = e := Subtype.ext (arcComponentsIn_eq_of_mem e'.2.1 e.2.1 h1 h2)
      rw [hee]
  have hprop : K.IsProper := by
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp (hKUsub hx.2)
    exact (disjoint_left.mp (hlong e) (hCe e he) hx.1).elim
  have hVL : K.V ⊆ L.U := by
    intro x hx
    rw [hKV] at hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    have hx' := he
    rw [(hcuts e).2.2.2.1] at hx'
    have hs := hcuts e
    have hL1 : γ e.1 '' Ioo 0 (s e) ∈ L.E := by
      rw [hLE]
      exact linking_edge_mem_forestSeamEdges hS N hJ hγ s t W hcuts' hsmall hU hV (.inl ⟨e, rfl⟩)
    have hL2 : γ e.1 '' Ioo (t e) 1 ∈ L.E := by
      rw [hLE]
      exact linking_edge_mem_forestSeamEdges hS N hJ hγ s t W hcuts' hsmall hU hV (.inr ⟨e, rfl⟩)
    rcases hx' with rfl | rfl
    · apply L.closure_subset_U hL1
      rw [closure_image_Ioo_eq_Icc hγ e.2.1 hs.1.1 (.inr hs.1.2)]
      exact ⟨s e, ⟨bot_le, le_rfl⟩, rfl⟩
    · apply L.closure_subset_U hL2
      rw [closure_image_Ioo_eq_Icc hγ e.2.1 hs.2.1.2 (.inl hs.2.1.1)]
      exact ⟨t e, ⟨le_rfl, le_top⟩, rfl⟩
  have hoffL : ∀ e, ∀ x ∈ γ e.1 '' Ioo (s e) (t e), x ∉ L.U := by
    intro e x hx hxL
    have hC : γ e.1 '' Ioo (s e) (t e) ∈ J'.E := hKsub.2 (hCE e)
    have hxU := hC.2.1 hx
    rcases (mem_U_iff_edge L).mp hxL with h | ⟨f, hf, hxf⟩
    · rw [hLV] at h
      exact hxU.2 h
    · have hfE : f ∈ forestSeamEdges J' (centralEdges G J μ w γ s t) := hLE ▸ hf
      have heq := arcComponentsIn_eq_of_mem hfE.1 hC hxf hx
      exact hfE.2.1 (heq ▸ ⟨e, rfl⟩)
  have hnormal : K.IsNormal L.U := by
    rintro x ⟨hxL, hxK⟩
    rcases (mem_U_iff_edge K).mp hxK with h | ⟨f, hf, hxf⟩
    · exact h
    · have hf' := hf
      rw [hKE] at hf'
      obtain ⟨e, rfl⟩ := hf'
      exact (hoffL e x hxf hxL).elim
  have hcover : bd S ∪ L.U ∪ K.U = N.seamU := by
    apply Subset.antisymm
    · have hJ'U : ∀ x, x ∈ J'.U → x ∈ N.seamU := fun x hx => by
        rw [hU, hJ.2.1] at hx
        exact hx
      have hsubU : ∀ {P : Drawing S}, P.IsSubdrawing J' → ∀ x ∈ P.U, x ∈ N.seamU := by
        intro P hP x hx
        apply hJ'U
        rcases (mem_U_iff_edge P).mp hx with h | ⟨f, hf, hxf⟩
        · exact J'.V_subset_U (hP.1 h)
        · exact ((hP.2 hf).2.1 hxf).1
      rintro x ((h | h) | h)
      · exact N.bd_subset_seamU h
      · exact hsubU hLsub x h
      · exact hsubU hKsub x h
    · intro x hx
      have hx' : x ∈ J'.U := by
        rw [hU, hJ.2.1]
        exact hx
      rcases (mem_U_iff_edge J').mp hx' with h | ⟨f, hf, hxf⟩
      · exact .inl (.inr (L.V_subset_U (hLV ▸ h)))
      · by_cases hc : f ∈ centralEdges G J μ w γ s t
        · have hfK : f ∈ K.E := hKE ▸ hc
          exact .inr (hfK.2.1 hxf).1
        · by_cases hb : f ⊆ bd S
          · exact .inl (.inl (hb hxf))
          · have hfL : f ∈ L.E := hLE ▸ ⟨hf, hc, hb⟩
            exact .inl (.inr (hfL.2.1 hxf).1)
  refine ⟨hpair, hprop, hVL, hnormal, hKUsub, hcover, ?_⟩
  rintro e r hr (hb | hb)
  · exact disjoint_left.mp (hlong e) (hCe e (image_mono Ioo_subset_Icc_self ⟨r, hr, rfl⟩)) hb
  · exact hoffL e _ ⟨r, hr, rfl⟩ hb

end Central

end GraphMinor.GM07
