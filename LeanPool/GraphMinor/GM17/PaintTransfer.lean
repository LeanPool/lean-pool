/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CutSide

/-!
# Moving part of a painting to another surface

Let `K` be a closed part of the painted set `U(Γ)` of a surface `S` that is a union of connected
parts of `U(Γ)`. Suppose an injection `ι` of `S`
into a surface `T` is continuous on `K`, and the boundary of `T` is the image of the part of the
boundary of `S` in `K`. Then `K` carries a
painting of `T` (`Painting.transfer`), and this is a cut-side painting for the cells in `K` with
nothing cut (`cutSide_of_part`). We use it for
a curve off `U(Γ)`, in the proof of (5.4) of Graph Minors XVII (page 173).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S T K : Type} [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace K]

theorem isClosedDisc_swap {v : K → S} {f : K → T} (hv : IsEmbedding v)
  (hf : IsEmbedding f) {D : Set K} (h : IsClosedDisc (v '' D)) : IsClosedDisc (f '' D) := by
  obtain ⟨φ⟩ := h
  exact ⟨(φ.trans (hv.homeomorphImage D).symm).trans (hf.homeomorphImage D)⟩

theorem isLine_swap {v : K → S} {f : K → T} (hv : IsEmbedding v) (hf : IsEmbedding f) {D : Set K}
  (h : IsLine (v '' D)) : IsLine (f '' D) := by
  obtain ⟨φ⟩ := h
  exact ⟨(φ.trans (hv.homeomorphImage D).symm).trans (hf.homeomorphImage D)⟩

/-- The cells of a part of a painted set are cells of the painting. -/
theorem image_mem_C {Γ : Painting S} {v : K → S} (hv : IsEmbedding v)
  (hconn : ∀ D : Set S, IsPreconnected D → D ⊆ Γ.U → (D ∩ range v).Nonempty → D ⊆ range v)
    (hr : range v ⊆ Γ.U) {c : Set K} (hc : c ∈ arcComponentsIn (univ \ v ⁻¹' Γ.N)) : v '' c ∈ Γ.C
      := by
  have h1 := mem_image_of_mem (fun c => v '' c) hc
  rw [← arcComps_image hv] at h1
  refine ⟨h1.1, ?_, h1.2.2.1, fun D hDF hD hsub => ?_⟩
  · refine h1.2.1.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hr ⟨x, rfl⟩, hx.2⟩
  · obtain ⟨y, hy⟩ := h1.1
    have h2 := hconn D hD.isConnected.isPreconnected (fun x hx => (hDF hx).1) ⟨y, hsub hy,
      (image_subset_range _ _ (h1.2.1 hy)).elim fun x hx => ⟨x, hx⟩⟩
    refine h1.2.2.2 D (fun x hx => ?_) hD hsub
    obtain ⟨z, rfl⟩ := h2 hx
    exact ⟨z, ⟨mem_univ _, (hDF hx).2⟩, rfl⟩

/-- The cells of the painting that meet a part of the painted set come from cells of the part. -/
theorem exists_arc_of_C {Γ : Painting S} {v : K → S} (hv : IsEmbedding v)
  (hconn : ∀ D : Set S, IsPreconnected D → D ⊆ Γ.U → (D ∩ range v).Nonempty → D ⊆ range v)
    (hr : range v ⊆ Γ.U) {c : Set S} (hc : c ∈ Γ.C) (hs : (c ∩ range v).Nonempty) : ∃ c₁ ∈
      arcComponentsIn (univ \ v ⁻¹' Γ.N), v '' c₁ = c := by
  obtain ⟨_, hxc, x, rfl⟩ := hs
  obtain ⟨c₁, hc₁, hx⟩ := exists_mem_arcComponentsIn (F := univ \ v ⁻¹' Γ.N) (x := x) ⟨mem_univ _,
    (arcComponentsIn_subset hc hxc).2⟩
  exact ⟨c₁, hc₁, arcComponentsIn_eq_of_mem (image_mem_C hv hconn hr hc₁) hc
    (mem_image_of_mem _ hx) hxc⟩

/-- Part of a painting moves to another surface. -/
noncomputable def Painting.transfer (Γ : Painting S) {v : K → S} {f : K → T}
  (hv : IsClosedEmbedding v) (hf : IsClosedEmbedding f)
    (hconn : ∀ D : Set S, IsPreconnected D → D ⊆ Γ.U → (D ∩ range v).Nonempty → D ⊆ range v)
      (hr : range v ⊆ Γ.U) (hb : bd T ⊆ range f)
    (hbd : ∀ x, f x ∈ bd T ↔ v x ∈ bd S) : Painting T where
  U := range f
  N := f '' (v ⁻¹' Γ.N)
  isClosed_U := hf.isClosed_range
  N_subset := image_subset_range _ _
  finite_N := (Γ.finite_N.preimage hv.injective.injOn).image _
  finite_cells := by
    rw [← image_univ, ← image_sdiff hf.injective, arcComps_image hf.isEmbedding]
    refine Set.Finite.image _ (Set.Finite.of_finite_image (f := fun c => v '' c)
      (Γ.finite_cells.subset ?_) ?_)
    · rintro _ ⟨c, hc, rfl⟩
      exact image_mem_C hv.isEmbedding hconn hr hc
    · exact fun c _ c' _ he => (image_eq_image hv.injective).mp he
  cell_disc := by
    rw [← image_univ, ← image_sdiff hf.injective, arcComps_image hf.isEmbedding]
    rintro _ ⟨c₁, hc₁, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := Γ.cell_disc _ (image_mem_C hv.isEmbedding hconn hr hc₁)
    rw [tilde_image_emb hv, hv.closure_image_eq, discBd_image hv.isEmbedding,
      ncard_image_of_injective _ hv.injective] at *
    simp only
    rw [tilde_image_emb hf, hf.closure_image_eq, discBd_image hf.isEmbedding,
      ncard_image_of_injective _ hf.injective]
    exact ⟨isClosedDisc_swap hv.isEmbedding hf.isEmbedding h1, image_mono
      ((image_subset_image_iff hv.injective).mp h2),
      ((h3.preimage hv.injective.injOn).subset (by rw [preimage_image_eq _ hv.injective])).image _,
        h4⟩
  bd_subset := hb
  border_cell := by
    rw [← image_univ, ← image_sdiff hf.injective, arcComps_image hf.isEmbedding]
    rintro _ ⟨c₁, hc₁, rfl⟩ ⟨_, ⟨x, hx, rfl⟩, hxb⟩
    have hmem := image_mem_C hv.isEmbedding hconn hr hc₁
    obtain ⟨h1, h2, h3, h4⟩ := Γ.border_cell _ hmem ⟨v x, mem_image_of_mem _ hx, (hbd x).mp hxb⟩
    have h5 : closure c₁ ∩ v ⁻¹' bd S = closure c₁ ∩ f ⁻¹' bd T := by
      ext y
      exact and_congr_right fun _ => (hbd y).symm
    have h6 : closure (v '' c₁) ∩ bd S = v '' (closure c₁ ∩ v ⁻¹' bd S) := by
      rw [hv.closure_image_eq, image_inter_preimage]
    have h7 : closure (f '' c₁) ∩ bd T = f '' (closure c₁ ∩ v ⁻¹' bd S) := by
      rw [h5, hf.closure_image_eq, image_inter_preimage]
    rw [tilde_image_emb hv, ncard_image_of_injective _ hv.injective] at h1
    rw [tilde_image_emb hv] at h2
    rw [h6] at h3
    rw [h6, tilde_image_emb hv, lineEnds_image hv.isEmbedding] at h4
    simp only
    rw [h7, tilde_image_emb hf, ncard_image_of_injective _ hf.injective,
      lineEnds_image hf.isEmbedding, (image_eq_image hv.injective).mp h4]
    exact ⟨h1, ((h2.preimage hv.injective.injOn).subset (by rw [preimage_image_eq _
      hv.injective])).image _, isLine_swap hv.isEmbedding hf.isEmbedding h3, rfl⟩

theorem Painting.transfer_C (Γ : Painting S) {v : K → S} {f : K → T} (hv : IsClosedEmbedding v)
  (hf : IsClosedEmbedding f)
    (hconn : ∀ D : Set S, IsPreconnected D → D ⊆ Γ.U → (D ∩ range v).Nonempty → D ⊆ range v)
      (hr : range v ⊆ Γ.U) (hb : bd T ⊆ range f)
    (hbd : ∀ x, f x ∈ bd T ↔ v x ∈ bd S) : (Γ.transfer hv hf hconn hr hb hbd).C = (fun c
      => f '' c) '' arcComponentsIn (univ \ v ⁻¹' Γ.N) := by
  change arcComponentsIn (range f \ f '' (v ⁻¹' Γ.N)) = _
  rw [← image_univ, ← image_sdiff hf.injective, arcComps_image hf.isEmbedding]

/-- A cuff is closed. -/
theorem isClosed_of_cuff [T2Space S] (hS : IsSurface S) {Θ : Set S} (hΘ : Θ ∈ cuffs S) : IsClosed Θ
  := by
  obtain ⟨φ⟩ := (cuff_statement.{0} S hS).2.2 Θ hΘ
  have hc : IsCompact Θ := by
    rw [isCompact_iff_compactSpace]
    exact φ.compactSpace
  exact hc.isClosed

/-- The order of points on a cuff moves along an injection that is continuous on the cuff. -/
theorem inOrderOn_of_image {Θ : Set S} {Φ : Set T} [CompactSpace Θ] [T2Space T] {ι : S → T}
  (hι : Function.Injective ι) (hc : ContinuousOn ι Θ) (he : ι '' Θ = Φ)
    {a b c d : S} (h : GM19.InOrderOn Φ (ι a) (ι b) (ι c) (ι d)) : GM19.InOrderOn Θ a b c d := by
  obtain ⟨g, t₁, t₂, t₃, t₄, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hcont : Continuous fun x : Θ => ι x.1 := continuousOn_iff_continuous_domRestrict.mp hc
  have hemb : IsEmbedding fun x : Θ => ι x.1 := (hcont.isClosedEmbedding fun x y h => Subtype.ext
    (hι h)).isEmbedding
  have hr : Φ = range fun x : Θ => ι x.1 := by
    rw [← he]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
  let g' : Circle ≃ₜ Θ := (g.trans (Homeomorph.setCongr hr)).trans hemb.toHomeomorph.symm
  have hg : ∀ t, ι (GM19.cuffPoint g' t) = GM19.cuffPoint g t := fun t => by
    have h9 := hemb.toHomeomorph.apply_symm_apply (Homeomorph.setCongr hr (g (Circle.exp t)))
    exact congrArg Subtype.val h9
  refine ⟨g', t₁, t₂, t₃, t₄, h1, h2, h3, h4, hι ?_, hι ?_, hι ?_, hι ?_⟩
  · rw [hg, h5]
  · rw [hg, h6]
  · rw [hg, h7]
  · rw [hg, h8]

/-- A part of a painted set gives a cut-side painting for the cells in it. -/
theorem cutSide_of_part [CompactSpace S] [T2Space S] [T2Space T]
  (hS : IsSurface S) {Γ : Painting S} {A : Set S} (hA : IsClosed A) (hAU : A ⊆ Γ.U)
    (hconn : ∀ D : Set S, IsPreconnected D → D ⊆ Γ.U → (D ∩ A).Nonempty → D ⊆ A) {ι : S → T}
      (hι : Function.Injective ι) (hcont : ContinuousOn ι A) (hb : bd T ⊆ ι '' A)
    (hbd : ∀ x ∈ A, ι x ∈ bd T ↔ x ∈ bd S) (hne : ∃ c ∈ Γ.C, c ⊆ A) : ∃ Γ' : Painting T,
      IsCutSidePainting S Γ ∅ {c ∈ Γ.C | c ⊆ A} T ι Γ' := by
  classical
  have hcK : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  have hv : IsClosedEmbedding (Subtype.val : A → S) := hA.isClosedEmbedding_subtypeVal
  have hf0 : Continuous fun x : A => ι x.1 := continuousOn_iff_continuous_domRestrict.mp hcont
  have hf : IsClosedEmbedding fun x : A => ι x.1 := hf0.isClosedEmbedding fun x y h => Subtype.ext
    (hι h)
  have hrv : range (Subtype.val : A → S) = A := Subtype.range_val
  have hrf : range (fun x : A => ι x.1) = ι '' A := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hconn' : ∀ D : Set S, IsPreconnected D → D ⊆ Γ.U → (D ∩ range (Subtype.val : A
    → S)).Nonempty → D ⊆ range (Subtype.val : A → S) := by
    rw [hrv]
    exact hconn
  have hr : range (Subtype.val : A → S) ⊆ Γ.U := hrv.subset.trans hAU
  have hb' : bd T ⊆ range fun x : A => ι x.1 := hrf ▸ hb
  have hbd' : ∀ x : A, ι x.1 ∈ bd T ↔ x.1 ∈ bd S := fun x => hbd x.1 x.2
  let Γ' := Γ.transfer hv hf hconn' hr hb' hbd'
  have hC : Γ'.C = (fun c => ι '' c) '' {c ∈ Γ.C | c ⊆ A} := by
    rw [Painting.transfer_C]
    ext d
    constructor
    · rintro ⟨c₁, hc₁, rfl⟩
      refine ⟨Subtype.val '' c₁, ⟨image_mem_C hv.isEmbedding hconn' hr hc₁, ?_⟩, image_image _ _ _⟩
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rintro ⟨c, ⟨hc, hs⟩, rfl⟩
      obtain ⟨x, hx⟩ := arcComponentsIn_nonempty hc
      have hx' : x ∈ range (Subtype.val : A → S) := by
        rw [hrv]
        exact hs hx
      obtain ⟨c₁, hc₁, rfl⟩ := exists_arc_of_C hv.isEmbedding hconn' hr hc ⟨x, hx, hx'⟩
      exact ⟨c₁, hc₁, (image_image _ _ _).symm⟩
  have hN : Γ'.N = ι '' (Γ.N ∩ A) := by
    change (fun x : A => ι x.1) '' (Subtype.val ⁻¹' Γ.N) = _
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have htil : ∀ c ⊆ A, tilde (ι '' c) = ι '' tilde c := fun c hs => by
    have h1 : c = Subtype.val '' (Subtype.val ⁻¹' c : Set A) := by
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr hs]
    have h2 : ι '' c = (fun x : A => ι x.1) '' (Subtype.val ⁻¹' c : Set A) := by
      conv_lhs => rw [h1]
      rw [image_image]
    rw [h2, tilde_image_emb hf]
    conv_rhs => rw [h1, tilde_image_emb hv]
    rw [image_image]
  have hcl : ∀ c ⊆ A, closure c ⊆ A := fun c hs => closure_minimal hs hA
  have hcuffb : ∀ {Θ : Set S}, Θ ∈ cuffs S → Θ ⊆ bd S := fun {Θ} hΘ => by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  have hcuffc : ∀ {Θ : Set S}, Θ ∈ cuffs S → IsPreconnected Θ := fun {Θ} hΘ => by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact isPreconnected_connectedComponentIn
  have hΦ : ∀ Φ ∈ cuffs T, ∃ Θ ∈ cuffs S, Θ ⊆ A ∧ ι '' Θ = Φ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hyA, rfl⟩ := hb hx
    have hyb : y ∈ bd S := (hbd y hyA).mp hx
    have hΘ : connectedComponentIn (bd S) y ∈ cuffs S := ⟨y, hyb, rfl⟩
    have hsA := hconn _ (hcuffc hΘ) ((hcuffb hΘ).trans Γ.bd_subset) ⟨y, mem_connectedComponentIn
      hyb, hyA⟩
    refine ⟨_, hΘ, hsA, subset_antisymm ?_ ?_⟩
    · refine IsPreconnected.subset_connectedComponentIn ((hcuffc hΘ).image _
      (hcont.mono hsA)) ⟨y, mem_connectedComponentIn hyb, rfl⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      exact (hbd z (hsA hz)).mpr (hcuffb hΘ hz)
    · have hQ : connectedComponentIn (bd T) (ι y) ⊆ range fun x : A => ι x.1 :=
      (connectedComponentIn_subset _ _).trans hb'
      have h3 := image_preimage_eq_of_subset hQ
      have h4 : IsPreconnected ((fun x : A => ι x.1) ⁻¹' connectedComponentIn (bd T) (ι y)) := by
        rw [← hf.isEmbedding.isInducing.isPreconnected_image, h3]
        exact isPreconnected_connectedComponentIn
      have h5 := h4.image _ continuous_subtype_val.continuousOn
      have h6 := h5.subset_connectedComponentIn (x := y) ⟨⟨y, hyA⟩, mem_connectedComponentIn hx,
        rfl⟩ (by
        rintro _ ⟨z, hz, rfl⟩
        exact (hbd' z).mp (connectedComponentIn_subset _ _ hz))
      rw [← h3]
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z.1, h6 ⟨z, hz, rfl⟩, rfl⟩
  have hactive : ∀ n ∈ Γ.N, n ∈ A → n ∈ bd S →
      n ∈ {n ∈ Γ.N \ (∅ : Set S) | ∃ c ∈ {c ∈ Γ.C | c ⊆ A}, n ∈ tilde c} := fun n hn hnA hnb => by
    obtain ⟨c, hc, hnt⟩ := exists_cell_node hS hn hnb
    refine ⟨⟨hn, notMem_empty _⟩, c, ⟨hc, ?_⟩, hnt⟩
    have h1 : IsPreconnected (insert n c) := (arcComponentsIn_isPathConnected
      hc).isConnected.isPreconnected.subset_closure (subset_insert _ _)
        (insert_subset hnt.1 subset_closure)
    exact (subset_insert _ _).trans (hconn _ h1 (insert_subset (Γ.N_subset hn) fun x hx =>
      (arcComponentsIn_subset hc hx).1) ⟨n, mem_insert _ _, hnA⟩)
  have hkA : ∀ n ∈ {n ∈ Γ.N \ (∅ : Set S) | ∃ c ∈ {c ∈ Γ.C | c ⊆ A}, n ∈ tilde c}, n ∈ A := by
    rintro n ⟨-, c, hc, hnt⟩
    exact hcl c hc.2 hnt.1
  have hmemN : ∀ {Θ : Set S}, Θ ∈ cuffs S → Θ ⊆ A → ∀ x ∈ Γ'.N ∩ ι '' Θ, ∃ n ∈ {n ∈ Γ.N \
    (∅ : Set S) | ∃ c ∈ {c ∈ Γ.C | c ⊆ A}, n ∈ tilde c} ∩ Θ, x = ι n := by
    rintro Θ hΘ hs x ⟨hx, n, hn, rfl⟩
    rw [hN] at hx
    obtain ⟨m, hm, he⟩ := hx
    obtain rfl := hι he
    exact ⟨m, ⟨hactive m hm.1 hm.2 (hcuffb hΘ hn), hn⟩, rfl⟩
  refine ⟨Γ', ?_⟩
  obtain ⟨c₀, hc₀, hs₀⟩ := hne
  refine ⟨hι, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hC.symm.subset
  · exact ⟨ι '' c₀, by rw [hC]; exact mem_image_of_mem _ (⟨hc₀, hs₀⟩ : c₀ ∈ {c ∈ Γ.C | c ⊆ A})⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [hN]
    exact mem_image_of_mem _ ⟨hn.1.1, hkA n hn⟩
  · rintro c hc n -
    rw [htil c hc.2]
    exact hι.mem_set_image
  · rintro c ⟨hc, hs⟩
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxb⟩
      exact ⟨x, hx, (hbd x (hs hx)).mp hxb⟩
    · rintro ⟨x, hx, hxb⟩
      exact ⟨ι x, mem_image_of_mem _ hx, (hbd x (hs hx)).mpr hxb⟩
  · intro n hn
    exact hbd n (hkA n hn)
  · intro d hd hn
    exact absurd (hC.subset hd) hn
  · intro Φ hΦ' n₁ hn₁ h₁ n₂ hn₂ h₂
    obtain ⟨Θ, hΘ, hsA, rfl⟩ := hΦ Φ hΦ'
    refine ⟨Θ, hΘ, hι.mem_set_image.mp h₁, .inl fun h => h₂ (mem_image_of_mem _ h)⟩
  · intro Φ hΦ' x₁ hx₁ x₂ hx₂ x₃ _ x₄ hx₄ hord n₁ hn₁ h₁ n₃ hn₃ h₃ Θ hΘ hnΘ hnΘ'
    obtain ⟨Θ₀, hΘ₀, hsA, rfl⟩ := hΦ Φ hΦ'
    have hn₁0 : n₁ ∈ Θ₀ := by
      have h9 : x₁ ∈ ι '' Θ₀ := hx₁.2
      rw [h₁] at h9
      exact hι.mem_set_image.mp h9
    obtain rfl := cuffs_disjoint_eq hΘ hΘ₀ hnΘ hn₁0
    obtain ⟨n₂, hn₂, rfl⟩ := hmemN hΘ hsA _ hx₂
    obtain ⟨n₄, hn₄, rfl⟩ := hmemN hΘ hsA _ hx₄
    have hcK : CompactSpace Θ := isCompact_iff_compactSpace.mp (isClosed_of_cuff hS hΘ).isCompact
    subst h₁ h₃
    exact .inr (.inl ⟨n₂, hn₂, rfl, n₄, .inr ⟨hn₄, rfl⟩, inOrderOn_of_image hι
      (hcont.mono hsA) rfl hord⟩)

end GraphMinor.GM17
