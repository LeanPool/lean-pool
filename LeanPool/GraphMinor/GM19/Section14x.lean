/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14w
public import LeanPool.GraphMinor.GM19.Section5n
public import LeanPool.GraphMinor.GM19.Section5o
public import LeanPool.GraphMinor.GM19.FeatureOrient

/-!
# Graph Minors XIX, Section 14: the painting `Γ'`

The painting `Γ'` in `Σ'` is the pull-back of `Γ` by the inclusion of `Σ'` in `Σ`, with the boundary
of `Σ'` added. It is a fragment of `Σ` in the sense of Section 5, for the
drawing `K` with `U(K) = bd(Σ')` and with the vertices of `Γ` on it as vertices.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace Slice

variable {T : Set S} {D : TangleDatum cap χ} (s : Slice T D)
include s

/-- The painting in `Σ` with the wheels in the fixed place. -/
noncomputable def Q : ColouredPainting χ := D.P.image s.f.symm s.hf.symm

theorem isImage : IsColouredImage s.f.symm D.P s.Q := ColouredPainting.isImage_image _ _ _

theorem mem_QV {x : S} : x ∈ s.Q.Γ.V ↔ cap.emb (s.f x) ∈ D.P.Γ.hatV cap := by
  rw [s.isImage.V]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, by simp⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [cap.isEmbedding.injective h]; simp⟩

theorem mem_QU {x : S} : x ∈ s.Q.Γ.U ↔ cap.emb (s.f x) ∈ D.P.Γ.hatU cap := by
  rw [s.isImage.U]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, by simp⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [cap.isEmbedding.injective h]; simp⟩

theorem image_bd : Subtype.val '' bd ↥Tᶜ = cutF (cap.emb ∘ s.f) s.𝒲 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [s.facts.2.2.1] at hy
    exact hy
  · intro hx
    obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hy, e⟩ := s.exists_pt hW hxW
    exact ⟨y, s.cf_sub_bd hW hy, s.f.injective (cap.isEmbedding.injective e)⟩

theorem bd_sub_T : bd S ⊆ T := s.hT ▸ s.cut.bd_subset_T

theorem isOpen_T : IsOpen T := isClosed_compl_iff.mp s.facts.1

theorem isClosedEmbedding : IsClosedEmbedding (Subtype.val : ↥Tᶜ → S)
  := s.facts.1.isClosedEmbedding_subtypeVal

/-- `T` and the boundary together are closed. -/
theorem isClosed_T_F : IsClosed (T ∪ cutF (cap.emb ∘ s.f) s.𝒲) := by
  have hc : IsClosed (⋃ W ∈ s.𝒲, W) := s.cut.finite.isClosed_biUnion fun W hW ↦
    (s.cut.disc W hW).isClosed
  have he : T ∪ cutF (cap.emb ∘ s.f) s.𝒲 = (cap.emb ∘ s.f) ⁻¹' ⋃ W ∈ s.𝒲, W := by
    ext x
    have hT' := Set.ext_iff.mp s.hT x
    simp only [mem_union, ← hT']
    simp only [cutT, cutF, mem_preimage, mem_iUnion₂, exists_prop]
    constructor
    · rintro (⟨W, hW, h⟩ | ⟨W, hW, h⟩)
      · exact ⟨W, hW, h.1⟩
      · exact ⟨W, hW, Surface.discBd_subset _ h⟩
    · rintro ⟨W, hW, h⟩
      by_cases hb : (cap.emb ∘ s.f) x ∈ discBd W
      · exact .inr ⟨W, hW, hb⟩
      · exact .inl ⟨W, hW, h, hb⟩
  rw [he]
  exact hc.preimage s.cut.emb.continuous

theorem exists_K : ∃ K : Drawing S, K.U = cutF (cap.emb ∘ s.f) s.𝒲 ∧ K.V = Subtype.val '' s.Nb
  ∧ FrameData χ.Φ s.Q.Γ K (Subtype.val : ↥Tᶜ → S) ∧ IsAnchored s.Q.Γ K := by
  classical
  have hX := s.isSurface
  have hconn := s.connected
  have hS := χ.isSurface
  obtain ⟨K, hU, hV, -⟩ := exists_boundaryDrawing hX s.isClosedEmbedding s.finite_Nb
    inter_subset_right s.two
  rw [s.image_bd] at hU
  have hNQ : ∀ x : ↥Tᶜ, x ∈ s.N ↔ x.1 ∈ s.Q.Γ.V := fun x ↦ s.mem_QV.symm
  have hVNb : ∀ x : ↥Tᶜ, x.1 ∈ K.V ↔ x ∈ s.Nb := fun x ↦ by
    rw [hV]
    exact ⟨fun ⟨y, hy, e⟩ ↦ Subtype.ext e ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩
  have hUb : ∀ x : ↥Tᶜ, x.1 ∈ K.U ↔ x ∈ bd ↥Tᶜ := fun x ↦ by
    rw [s.facts.2.2.1, hU]
    rfl
  have hfrag : IsCuttingFragment S K ↥Tᶜ Subtype.val := by
    have hoff : ∀ x : ↥Tᶜ, x ∉ bd ↥Tᶜ → x.1 ∉ bd S ∪ K.U := fun x hx ↦ by
      rintro (h | h)
      · exact x.2 (s.bd_sub_T h)
      · exact hx ((hUb x).mp h)
    refine ⟨hX, hconn, continuous_subtype_val, Subtype.val_injective.injOn, fun x ↦
      Set.Subsingleton.finite fun a ha b hb ↦ Subtype.ext (ha.trans hb.symm), ?_, ?_, ?_⟩
    · refine disjoint_left.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hoff x hx
    · rintro _ ⟨x, hx, rfl⟩
      exact .inr ((hUb x).mpr hx)
    · obtain ⟨z, hz⟩ := nonempty_interior hX
      refine ⟨z.1, hoff z hz, ?_⟩
      have hI : IsOpen (Subtype.val '' (bd ↥Tᶜ)ᶜ : Set S) := by
        have he : (Subtype.val '' (bd ↥Tᶜ)ᶜ : Set S) = (T ∪ cutF (cap.emb ∘ s.f) s.𝒲)ᶜ := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩ (h | h)
            · exact y.2 h
            · exact hy ((hUb y).mp (hU ▸ h))
          · intro hx
            have hxT : x ∈ Tᶜ := fun h ↦ hx (.inl h)
            exact ⟨⟨x, hxT⟩, fun h ↦ hx (.inr (hU ▸ (hUb ⟨x, hxT⟩).mpr h)), rfl⟩
        rw [he]
        exact s.isClosed_T_F.isOpen_compl
      have hpre : IsPreconnected (Subtype.val '' (bd ↥Tᶜ)ᶜ : Set S) :=
        (isPreconnected_compl_bd hX).image _ continuous_subtype_val.continuousOn
      have hsubF : (Subtype.val '' (bd ↥Tᶜ)ᶜ : Set S) ⊆ (bd S ∪ K.U)ᶜ := by
        rintro _ ⟨x, hx, rfl⟩
        exact hoff x hx
      refine Subset.antisymm ?_ (hpre.subset_connectedComponentIn ⟨z, hz, rfl⟩ hsubF)
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hI s.isOpen_T ?_ ?_
        ⟨z.1, mem_connectedComponentIn (hoff z hz), z, hz, rfl⟩
      · refine disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ h
        exact x.2 h
      · intro x hx
        have hx' := connectedComponentIn_subset _ _ hx
        by_cases hT : x ∈ T
        · exact .inr hT
        · refine .inl ⟨⟨x, hT⟩, fun h ↦ hx' (.inr ((hUb ⟨x, hT⟩).mpr h)), rfl⟩
  have hd : PullData s.Q.Γ K (Subtype.val : ↥Tᶜ → S) := by
    refine ⟨hS, hfrag, ?_, fun C ↦ ?_⟩
    · rintro x ⟨hx₁, hx₂⟩
      have hb : cap.emb (s.f x) ∈ ⋃ W ∈ s.𝒲, discBd W := by
        have : x ∈ cutF (cap.emb ∘ s.f) s.𝒲 := hU ▸ hx₂
        exact this
      obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp hb
      have hU' : cap.emb (s.f x) ∈ D.rad.G.U := (s.fr ⟨W, hW⟩).R.G_sub hxW
      have hh : cap.emb (s.f x) ∈ D.P.Γ.hatV cap := by
        rw [← D.rad.isPreRadial.1]
        exact ⟨s.mem_QU.mp hx₁, hU'⟩
      refine ⟨s.mem_QV.mpr hh, ?_⟩
      obtain ⟨y, hy, e⟩ := s.exists_pt hW hxW
      have hyx : y.1 = x := s.f.injective (cap.isEmbedding.injective e)
      exact hyx ▸ (hVNb y).mpr ⟨show s.e y ∈ D.P.Γ.hatV cap by rw [e]; exact hh, s.cf_sub_bd hW hy⟩
    · obtain ⟨p, hp, q, hq, hne⟩ := s.two C
      exact ⟨p, ⟨.inr ((hVNb p).mpr hp.1), hp.2⟩, q, ⟨.inr ((hVNb q).mpr hq.1), hq.2⟩, hne⟩
  refine ⟨K, hU, hV, ⟨hd, s.Q.fits, fun C ↦ ?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp, q, hq, hne⟩ := s.two C
    exact ⟨p, ⟨.inr ((hVNb p).mpr hp.1), hp.2⟩, q, ⟨.inr ((hVNb q).mpr hq.1), hq.2⟩, hne⟩
  · rintro x ⟨h₁, h₂⟩
    exfalso
    obtain ⟨y, hy, rfl⟩ := (show x ∈ Subtype.val '' bd ↥Tᶜ by rw [s.image_bd, ← hU]; exact h₁)
    exact y.2 (s.bd_sub_T h₂)
  · intro u x hx hxu
    rw [hU] at hx
    obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp hx
    have hO : IsOArc (discBd W) := (s.cut.disc W hW).isOArc_discBd
    have hem : IsEmbedding (cap.emb ∘ s.f) := s.cut.emb.isEmbedding
    set C := (cap.emb ∘ s.f) ⁻¹' (discBd W \ {cap.emb (s.f u)}) with hC
    have hsubr : discBd W \ {cap.emb (s.f u)} ⊆ range (cap.emb ∘ s.f) := fun y hy ↦ by
      obtain ⟨z, -, e⟩ := s.exists_pt hW hy.1
      exact ⟨z.1, e⟩
    have hsubK : C ⊆ K.U \ {u} := fun y hy ↦
      ⟨by rw [hU]; exact mem_iUnion₂.mpr ⟨W, hW, hy.1⟩,
        fun e ↦ hy.2 (by rw [mem_singleton_iff.mp e]; rfl)⟩
    refine ⟨C, hsubK, ⟨hxW, fun e ↦ hxu (s.f.injective (cap.isEmbedding.injective e))⟩, ?_, ?_⟩
    · have : IsPreconnected ((cap.emb ∘ s.f) '' C) := by
        rw [hC, image_preimage_eq_of_subset hsubr]
        exact hO.twoConn _
      exact hem.isInducing.isPreconnected_image.mp this
    · have h3 := (s.fr ⟨W, hW⟩).k_three
      obtain ⟨i, hi, hne⟩ : ∃ i, i < 2 ∧ (s.fr ⟨W, hW⟩).R.vert i ≠ cap.emb (s.f u) := by
        by_contra hn
        push Not at hn
        have e₀ := hn 0 (by omega)
        have e₁ := hn 1 (by omega)
        exact absurd ((s.fr ⟨W, hW⟩).R.vert_inj (by omega) (by omega) (e₀.trans e₁.symm)) (by omega)
      obtain ⟨y, hy, e⟩ := s.exists_pt hW (s.vert_bd ⟨W, hW⟩ i)
      exact ⟨y.1, ⟨show s.e y ∈ discBd W by rw [e]; exact s.vert_bd ⟨W, hW⟩ i,
          fun h' ↦ hne (e.symm.trans h')⟩,
        s.mem_QV.mpr (show s.e y ∈ D.P.Γ.hatV cap by
          rw [e]
          exact ((s.fr ⟨W, hW⟩).R.vert_mem i).1)⟩

end Slice

end GraphMinor.GM19
