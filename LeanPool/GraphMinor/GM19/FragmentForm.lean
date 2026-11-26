/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentSides
public import LeanPool.GraphMinor.GM19.Conditional2

/-!
# A line of a cuff and the disc it closes

Let `F` be the boundary of a closed disc `Δ` of `Σ̂`, made of a line `K` of `Σ` with both ends on a
cuff `Θ` and of a line `β` in the
disc pasted onto `Θ`. Then `β` cuts the pasted disc `E` in two. One half lies in `Δ` and the other
half outside (`exists_split`).
Taking the first half out of `Δ`, or adding the second, gives closed discs with the same part of
`Σ`, and with boundaries in `Σ`
(`exists_form_discs`). So the case of a line reduces to the case of a disc with boundary in `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric Filter GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
private theorem component_pair_covers (A A' U : Set T)
  (hcomp : componentsIn U = {A, A'}) : U ⊆ A ∪ A' := by
  intro x hx
  have : connectedComponentIn (U) x ∈ componentsIn (U)
    := mem_image_of_mem _ hx
  rw [hcomp] at this
  have hm := mem_connectedComponentIn hx
  rcases this with h | h
  · exact Or.inl (h ▸ hm)
  · exact Or.inr ((mem_singleton_iff.1 h) ▸ hm)

/-- A line `β` of the boundary of `Δ` crosses a closed disc `E` that meets the boundary of `Δ` only
in `β`. Taking out of `Δ` the half
of `E` in `Δ`, or adding the other half, gives closed discs `Δ₁` and `Δ₂`. -/
theorem exists_split (hT : IsClosedSurface T) {Δ E β : Set T} (hΔ : IsClosedDisc Δ)
  (hE : IsClosedDisc E) {s t : T}
    (hst : s ≠ t) (hl : IsLineWithEnds β s t) (hβΔ : β ⊆ discBd Δ) (hβE : β ⊆ E)
      (hmeet : β ∩ discBd E = {s, t})
    (hEΔ : E ∩ discBd Δ ⊆ β) :
    ∃ (Δ₁ Δ₂ A₁ A₂ : Set T), IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ A₁ ⊆ discBd E ∧ A₂ ⊆ discBd E ∧
      discBd Δ₁ = (discBd Δ \ (β \ {s, t})) ∪ A₁ ∧ discBd Δ₂ = (discBd Δ \ (β \ {s, t})) ∪ A₂ ∧
      A₂.Nonempty ∧ Disjoint A₂ Δ₁ ∧ E ⊆ Δ₂ ∧ Δ ⊆ Δ₂ ∧ Δ₁ ⊆ Δ ∧ Δ \ Δ₁ ⊆ E ∧ Δ ∩ discBd E ⊆ Δ₁ ∧
      (∀ x ∉ discInt E, x ∈ discInt Δ₂ ↔ x ∈ discInt Δ) := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hsβ : s ∈ β := by
    have : s ∈ β ∩ discBd E := by rw [hmeet]; exact mem_insert _ _
    exact this.1
  have htβ : t ∈ β := by
    have : t ∈ β ∩ discBd E := by rw [hmeet]; exact mem_insert_of_mem _ rfl
    exact this.1
  obtain ⟨A, A', D, D', hAne, hcomp, hD, hD', hun, hint, hbd, hbd', hcomp'⟩
    := disc_iArc E β s t hE hβE hst hl hmeet
  have hmemc : ∀ {B}, B ∈ componentsIn (discBd E \ {s, t}) → B ⊆ discBd E \ {s, t} := by
    rintro _ ⟨x, -, rfl⟩
    exact connectedComponentIn_subset _ _
  have hAs : A ⊆ discBd E \ {s, t} := hmemc (by rw [hcomp]; exact mem_insert _ _)
  have hAs' : A' ⊆ discBd E \ {s, t} := hmemc (by rw [hcomp]; exact mem_insert_of_mem _ rfl)
  have hcov := component_pair_covers A A' (discBd E \ {s, t}) hcomp
  have hA'ne : A'.Nonempty := by
    have : A' ∈ componentsIn (discBd E \ {s, t}) := by rw [hcomp]; exact mem_insert_of_mem _ rfl
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hAne' : A.Nonempty := by
    have : A ∈ componentsIn (discBd E \ {s, t}) := by rw [hcomp]; exact mem_insert _ _
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hoffβ : ∀ {x}, x ∈ discBd E \ {s, t} → x ∉ β := fun {x} hx hxβ ↦ hx.2 (hmeet ▸ ⟨hxβ, hx.1⟩)
  have core : ∀ {D D' A A' : Set T}, IsClosedDisc D → IsClosedDisc D' → D ∪ D' = E → D ∩ D' = β
    → discBd D = A ∪ β →
      discBd D' = A' ∪ β → A ⊆ discBd E \ {s, t} → A' ⊆ discBd E \ {s, t}
        → discBd E \ {s, t} ⊆ A ∪ A' → A'.Nonempty →
      D \ β ⊆ discInt Δ → Disjoint (D' \ β) Δ →
      ∃ (Δ₁ Δ₂ A₁ A₂ : Set T), IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧ A₁ ⊆ discBd E ∧ A₂ ⊆ discBd E ∧
        discBd Δ₁ = (discBd Δ \ (β \ {s, t})) ∪ A₁ ∧ discBd Δ₂ = (discBd Δ \ (β \ {s, t})) ∪ A₂ ∧
        A₂.Nonempty ∧ Disjoint A₂ Δ₁ ∧ E ⊆ Δ₂ ∧ Δ ⊆ Δ₂ ∧ Δ₁ ⊆ Δ ∧ Δ \ Δ₁ ⊆ E ∧ Δ ∩ discBd E ⊆ Δ₁ ∧
        (∀ x ∉ discInt E, x ∈ discInt Δ₂ ↔ x ∈ discInt Δ) := by
    intro D D' A A' hD hD' hun hint hbd hbd' hAs hAs' hcov hA'ne hin hout
    have hsubb : ∀ {x}, x ∈ β → x ∈ Δ := fun hx ↦ Surface.discBd_subset _ (hβΔ hx)
    have hβD : β ⊆ discBd D := fun x hx ↦ hbd ▸ Or.inr hx
    have hβD' : β ⊆ discBd D' := fun x hx ↦ hbd' ▸ Or.inr hx
    have hDΔ : D ⊆ Δ := fun x hx ↦ by
      by_cases h : x ∈ β
      · exact hsubb h
      · exact discInt_subset Δ (hin ⟨hx, h⟩)
    have hsE : ∀ {B}, B ⊆ discBd E \ {s, t} → B ⊆ E := fun hB x hx ↦ Surface.discBd_subset _
      (hB hx).1
    have hmd : discBd D ∩ discBd Δ = β := by
      apply Subset.antisymm
      · rintro x ⟨hx, hxb⟩
        rw [hbd] at hx
        rcases hx with h | h
        · exact hEΔ ⟨hsE hAs h, hxb⟩
        · exact h
      · exact fun x hx ↦ ⟨hβD hx, hβΔ hx⟩
    obtain ⟨hc, hb, hi⟩ := disc_difference D Δ β s t hD hΔ hDΔ hl hmd
    have hmd2 : Δ ∩ D' = β := by
      apply Subset.antisymm
      · rintro x ⟨hx, hx'⟩
        by_contra hn
        exact disjoint_left.1 hout ⟨hx', hn⟩ hx
      · exact fun x hx ↦ ⟨hsubb hx, Surface.discBd_subset _ (hβD' hx)⟩
    obtain ⟨hu, hub⟩ := disc_union Δ D' β s t hΔ hD' hl hmd2 hβΔ hβD'
    have hoffA : ∀ {B}, B ⊆ discBd E \ {s, t} → ∀ {x}, x ∈ B → x ∉ β := fun hB _ hx ↦ hoffβ (hB hx)
    have hsub1 : closure (Δ \ D) ⊆ Δ := closure_minimal sdiff_subset hΔ.isClosed
    have hA'D' : A' ⊆ D' := fun x hx ↦ Surface.discBd_subset _ (hbd' ▸ Or.inl hx)
    have hAD : A ⊆ D := fun x hx ↦ Surface.discBd_subset _ (hbd ▸ Or.inl hx)
    have hA₂out : Disjoint A' Δ := disjoint_left.2 fun x hx hxΔ ↦ disjoint_left.1 hout ⟨hA'D' hx,
      hoffA hAs' hx⟩ hxΔ
    have hbd₁ : discBd (closure (Δ \ D)) = (discBd Δ \ (β \ {s, t})) ∪ A := by
      rw [hb]
      ext x
      constructor
      · rintro ⟨hx | hx, hn⟩
        · rw [hbd] at hx
          rcases hx with h | h
          · exact Or.inr h
          · exact Or.inl ⟨hβΔ h, hn⟩
        · exact Or.inl ⟨hx, hn⟩
      · rintro (⟨hx, hn⟩ | hx)
        · exact ⟨Or.inr hx, hn⟩
        · exact ⟨Or.inl (hbd ▸ Or.inl hx), fun h ↦ hoffA hAs hx h.1⟩
    have hbd₂ : discBd (Δ ∪ D') = (discBd Δ \ (β \ {s, t})) ∪ A' := by
      rw [hub]
      ext x
      constructor
      · rintro ⟨hx | hx, hn⟩
        · exact Or.inl ⟨hx, hn⟩
        · rw [hbd'] at hx
          rcases hx with h | h
          · exact Or.inr h
          · exact Or.inl ⟨hβΔ h, hn⟩
      · rintro (⟨hx, hn⟩ | hx)
        · exact ⟨Or.inl hx, hn⟩
        · exact ⟨Or.inr (hbd' ▸ Or.inl hx), fun h ↦ hoffA hAs' hx h.1⟩
    have hEsub : E ⊆ Δ ∪ D' := by
      rw [← hun]
      rintro x (h | h)
      · exact Or.inl (hDΔ h)
      · exact Or.inr h
    refine ⟨closure (Δ \ D), Δ ∪ D', A, A', hc, hu, fun x hx ↦ (hAs hx).1,
      fun x hx ↦ (hAs' hx).1, hbd₁, hbd₂, hA'ne,
      hA₂out.mono_right hsub1, hEsub, subset_union_left, hsub1, ?_, ?_, ?_⟩
    · rintro x ⟨hx, hn⟩
      by_contra hxE
      exact hn (subset_closure ⟨hx, fun h ↦ hxE (hun ▸ Or.inl h)⟩)
    · rintro x ⟨hxΔ, hxb⟩
      have hinD : x ∈ D → x ∉ β \ {s, t} → x ∈ discBd D → x ∈ closure (Δ \ D) := fun _ hn hb' ↦ by
        have : x ∈ closure (Δ \ D) ∩ D := hi ▸ ⟨hb', hn⟩
        exact this.1
      by_cases hxβ : x ∈ β
      · have hxe : x ∈ ({s, t} : Set T) := hmeet ▸ ⟨hxβ, hxb⟩
        exact hinD (Surface.discBd_subset _ (hβD hxβ)) (fun h ↦ h.2 hxe) (hβD hxβ)
      · have hxn : x ∈ discBd E \ {s, t} := ⟨hxb, fun h ↦ hxβ (by
          rcases h with h | h
          · exact h ▸ hsβ
          · exact (mem_singleton_iff.1 h) ▸ htβ)⟩
        rcases hcov hxn with h | h
        · exact hinD (hAD h) (fun h' ↦ hxβ h'.1) (hbd ▸ Or.inl h)
        · exact absurd hxΔ (disjoint_left.1 hA₂out h)
    · intro x hx
      constructor
      · rintro ⟨hxu, hn⟩
        have hxΔ : x ∈ Δ := by
          rcases hxu with h | h
          · exact h
          · by_contra hxΔ
            have hxb : x ∈ discBd E := by
              by_contra hb'
              exact hx ⟨hun ▸ Or.inr h, hb'⟩
            by_cases hxe : x ∈ ({s, t} : Set T)
            · rcases hxe with h' | h'
              · exact hxΔ (h' ▸ hsubb hsβ)
              · exact hxΔ ((mem_singleton_iff.1 h') ▸ hsubb htβ)
            · rcases hcov ⟨hxb, hxe⟩ with h' | h'
              · exact hxΔ (hDΔ (hAD h'))
              · exact hn (hbd₂ ▸ Or.inr h')
        refine ⟨hxΔ, fun hb' ↦ hn ?_⟩
        rw [hbd₂]
        refine Or.inl ⟨hb', fun h ↦ hx ⟨hβE h.1, fun hE' ↦ h.2 (hmeet ▸ ⟨h.1, hE'⟩)⟩⟩
      · rintro ⟨hxΔ, hn⟩
        refine ⟨Or.inl hxΔ, fun hb' ↦ ?_⟩
        rw [hbd₂] at hb'
        rcases hb' with h | h
        · exact hn h.1
        · exact disjoint_left.1 hA₂out h hxΔ
  have hEun : E = D ∪ D' := hun.symm
  have hpre : ∀ {B}, B ∈ componentsIn (E \ β) → IsPreconnected B := by
    rintro _ ⟨x, -, rfl⟩
    exact isPreconnected_connectedComponentIn
  have hc₁ : IsPreconnected (D \ β) := hpre (by rw [hcomp']; exact mem_insert _ _)
  have hc₂ : IsPreconnected (D' \ β) := hpre (by rw [hcomp']; exact mem_insert_of_mem _ rfl)
  have hbdj : ∀ {D}, D ⊆ E → Disjoint (D \ β) (discBd Δ) := fun hD' ↦
    disjoint_left.2 fun x hx hb ↦ hx.2 (hEΔ ⟨hD' hx.1, hb⟩)
  have hDE : D ⊆ E := by rw [hEun]; exact subset_union_left
  have hDE' : D' ⊆ E := by rw [hEun]; exact subset_union_right
  obtain ⟨f, hf0, hf1⟩ := hl
  let b : T := (f (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).1
  have hbβ : b ∈ β := (f _).2
  have hb_ne : ∀ {r : unitInterval}, r ≠ ⟨1 / 2, by norm_num, by norm_num⟩ → (f r).1 ≠ b
    := fun hr he ↦ hr (f.injective (Subtype.ext he))
  have hbs : b ≠ s := fun he ↦
    hb_ne (r := 0) (fun h ↦ by have := congrArg Subtype.val h; norm_num at this) (hf0.trans he.symm)
  have hbt : b ≠ t := fun he ↦
    hb_ne (r := 1) (fun h ↦ by have := congrArg Subtype.val h; norm_num at this) (hf1.trans he.symm)
  have hl' : IsLineWithEnds β s t := ⟨f, hf0, hf1⟩
  have hbE : b ∈ discInt E := ⟨hβE hbβ, fun hb' ↦ by
    have : b ∈ ({s, t} : Set T) := hmeet ▸ ⟨hbβ, hb'⟩
    rcases this with h | h
    · exact hbs h
    · exact hbt h⟩
  have hEopen : IsOpen (discInt E) := hE.isOpen_discInt hman
  rcases hΔ.side hman hc₁ (hbdj hDE) with h₁ | h₁ <;> rcases hΔ.side hman hc₂
    (hbdj hDE') with h₂ | h₂
  · exfalso
    have hsub : E ⊆ Δ := by
      rw [hEun]
      rintro x hx
      by_cases hxβ : x ∈ β
      · exact Surface.discBd_subset _ (hβΔ hxβ)
      · rcases hx with h | h
        · exact discInt_subset Δ (h₁ ⟨h, hxβ⟩)
        · exact discInt_subset Δ (h₂ ⟨h, hxβ⟩)
    have := subset_discInt_of_isOpen (fun y _ ↦ hT.2.2 y) hEopen ((discInt_subset E).trans hsub) hbE
    exact this.2 (hβΔ hbβ)
  · exact core hD hD' hun hint hbd hbd' hAs hAs' hcov hA'ne h₁ h₂
  · refine core hD' hD (by rw [union_comm, hun]) (by rw [inter_comm,
      hint]) hbd' hbd hAs' hAs ?_ hAne' h₂ h₁
    rw [union_comm]
    exact hcov
  · exfalso
    have hbcl := hΔ.subset_closure_discInt (Surface.discBd_subset _ (hβΔ hbβ))
    obtain ⟨w, hw, hwi⟩ := _root_.mem_closure_iff.1 hbcl _ hEopen hbE
    have hwE : w ∈ E := discInt_subset E hw
    by_cases hwβ : w ∈ β
    · exact hwi.2 (hβΔ hwβ)
    · rw [hEun] at hwE
      rcases hwE with h | h
      · exact disjoint_left.1 h₁ ⟨h, hwβ⟩ (discInt_subset Δ hwi)
      · exact disjoint_left.1 h₂ ⟨h, hwβ⟩ (discInt_subset Δ hwi)

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]

omit [T2Space S] in
/-- A form with a line of a cuff reduces to two closed discs with boundary in `S`, one with the same
part of `S` as `Δ` and one with
the same part of `S` in its inside. -/
theorem exists_form_discs (cap : IsCappedSurface S Shat) {K : Drawing S} {Δ :
  Set Shat} (hΔ : IsClosedDisc Δ)
    {s t : S} {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hst : s ≠ t) (hs : s ∈ Θ) (ht : t ∈ Θ)
      (hKb : K.U ∩ bd S = {s, t})
    (hl : IsLineWithEnds K.U s t) (hsub : cap.emb '' K.U ⊆ discBd Δ) (hrest : discBd Δ \ cap.emb ''
      K.U ⊆ cap.cuffDisc Θ) :
    ∃ Δ₁ Δ₂ : Set Shat, IsClosedDisc Δ₁ ∧ IsClosedDisc Δ₂ ∧
      cap.emb '' K.U ⊆ discBd Δ₁ ∧ cap.emb '' K.U ⊆ discBd Δ₂ ∧
      discBd Δ₁ ⊆ range cap.emb ∧ discBd Δ₂ ⊆ range cap.emb ∧
      discBd Δ₁ ⊆ cap.emb '' K.U ∪ cap.emb '' Θ ∧ discBd Δ₂ ⊆ cap.emb '' K.U ∪ cap.emb '' Θ ∧
      ¬ closure (cap.cuffDisc Θ) ⊆ Δ₁ ∧ closure (cap.cuffDisc Θ) ⊆ Δ₂ ∧ Δ ⊆ Δ₂ ∧
      cap.emb ⁻¹' Δ₁ = cap.emb ⁻¹' Δ ∧ cap.emb ⁻¹' discInt Δ₂ = cap.emb ⁻¹' discInt Δ := by
  classical
  have hT := cap.isClosedSurface
  have hE := cap.cuffDisc_closedDisc Θ hΘ
  set E := closure (cap.cuffDisc Θ) with hEdef
  have hbE : discBd E = cap.emb '' Θ := cap.cuffDisc_bd Θ hΘ
  have hcl : E = cap.cuffDisc Θ ∪ cap.emb '' Θ := cap.closure_cuffDisc hΘ
  have hEr : ∀ {z}, cap.emb z ∈ E → z ∈ Θ := fun {z} hz ↦ by
    rw [hcl] at hz
    rcases hz with h | ⟨y, hy, he⟩
    · exact absurd (mem_range_self z) (cap.notMem_range hΘ h)
    · exact cap.isEmbedding.injective he ▸ hy
  have hline := hl.map_of_embedding cap.isEmbedding
  obtain ⟨u, v, htw, hru, hu0, hu1, hun⟩ := exists_arcs_of_line hΔ.isOArc_discBd hline hsub
  have hv0 : v 0 = cap.emb s := htw.zero.trans hu0
  have hv1 : v 1 = cap.emb t := htw.one.trans hu1
  set β := range v with hβ
  have hβl : IsLineWithEnds β (cap.emb s) (cap.emb t) := by
    have := htw.arc_right.isLineWithEnds
    rwa [hv0, hv1] at this
  have hne : cap.emb s ≠ cap.emb t := fun h ↦ hst (cap.isEmbedding.injective h)
  have hβsub : β ⊆ discBd Δ := fun x hx ↦ hun ▸ Or.inr hx
  have hsE : cap.emb s ∈ E := hbE ▸ mem_image_of_mem _ hs |> Surface.discBd_subset _
  have htE : cap.emb t ∈ E := hbE ▸ mem_image_of_mem _ ht |> Surface.discBd_subset _
  have hsβ : cap.emb s ∈ β := ⟨0, hv0⟩
  have htβ : cap.emb t ∈ β := ⟨1, hv1⟩
  have hβK : ∀ {x}, x ∈ β → x ∈ cap.emb '' K.U → x = cap.emb s ∨ x = cap.emb t := by
    rintro _ ⟨r, rfl⟩ hx
    rw [← hru] at hx
    obtain ⟨a, ha⟩ := hx
    rcases htw.meet a r ha with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl hv0
    · exact Or.inr hv1
  have hmem : ∀ {x}, x ∈ β → x ∈ cap.emb '' K.U ∨ x ∈ cap.cuffDisc Θ := fun {x} hx ↦ by
    by_cases h : x ∈ cap.emb '' K.U
    · exact Or.inl h
    · exact Or.inr (hrest ⟨hβsub hx, h⟩)
  have hβE : β ⊆ E := fun x hx ↦ by
    rcases hmem hx with h | h
    · rcases hβK hx h with rfl | rfl
      · exact hsE
      · exact htE
    · exact subset_closure h
  have hmeet : β ∩ discBd E = {cap.emb s, cap.emb t} := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxb⟩
      rw [hbE] at hxb
      obtain ⟨z, -, rfl⟩ := hxb
      rcases hmem hx with h | h
      · rcases hβK hx h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      · exact absurd (mem_range_self z) (cap.notMem_range hΘ h)
    · rintro x (rfl | rfl)
      · exact ⟨hsβ, hbE ▸ mem_image_of_mem _ hs⟩
      · exact ⟨htβ, hbE ▸ mem_image_of_mem _ ht⟩
  have hEΔ : E ∩ discBd Δ ⊆ β := by
    rintro x ⟨hxE, hxb⟩
    rw [← hun] at hxb
    rcases hxb with h | h
    · rw [hru] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hzb : z ∈ K.U ∩ bd S := ⟨hz, cuff_subset_bd ⟨Θ, hΘ⟩ (hEr hxE)⟩
      rw [hKb] at hzb
      rcases hzb with rfl | h'
      · exact hsβ
      · rw [mem_singleton_iff.1 h']
        exact htβ
    · exact h
  obtain ⟨Δ₁, Δ₂, A₁, A₂, h₁, h₂, hA₁, hA₂, hb₁, hb₂, hne₂, hdj, hEΔ₂, hΔΔ₂, hΔ₁Δ, hdiff, hbdΔ₁,
    hint⟩ :=
    exists_split hT hΔ hE hne hβl hβsub hβE hmeet hEΔ
  have hoff : discBd Δ \ (β \ {cap.emb s, cap.emb t}) ⊆ cap.emb '' K.U := by
    rintro x ⟨hxb, hn⟩
    rw [← hun] at hxb
    rcases hxb with h | h
    · exact hru ▸ h
    · have hxe : x ∈ ({cap.emb s, cap.emb t} : Set Shat) := by
        by_contra hne'
        exact hn ⟨h, hne'⟩
      rw [← hru]
      rcases hxe with rfl | h'
      · exact ⟨0, hu0⟩
      · exact ⟨1, hu1.trans (mem_singleton_iff.1 h').symm⟩
  have hKin : cap.emb '' K.U ⊆ discBd Δ \ (β \ {cap.emb s, cap.emb t}) := fun x hx ↦
    ⟨hsub hx, fun h ↦ h.2 (by rcases hβK h.1 hx with h' | h'; exacts [Or.inl h', Or.inr h'])⟩
  have hbdsub : ∀ {B D}, B ⊆ discBd E → discBd D = (discBd Δ \ (β \ {cap.emb s, cap.emb t})) ∪ B →
      discBd D ⊆ cap.emb '' K.U ∪ cap.emb '' Θ := fun hB hD x hx ↦ by
    rw [hD] at hx
    rcases hx with h | h
    · exact Or.inl (hoff h)
    · exact Or.inr (hbE ▸ hB h)
  have hr : ∀ {D}, discBd D ⊆ cap.emb '' K.U ∪ cap.emb '' Θ → discBd D ⊆ range cap.emb
    := fun hD x hx ↦ by
    rcases hD hx with ⟨z, -, rfl⟩ | ⟨z, -, rfl⟩ <;> exact mem_range_self z
  have hs₁ := hbdsub hA₁ hb₁
  have hs₂ := hbdsub hA₂ hb₂
  refine ⟨Δ₁, Δ₂, h₁, h₂, fun x hx ↦ hb₁ ▸ Or.inl (hKin hx), fun x hx ↦ hb₂ ▸ Or.inl (hKin hx),
    hr hs₁, hr hs₂, hs₁, hs₂, ?_, hEΔ₂,
    hΔΔ₂, ?_, ?_⟩
  · intro hn
    obtain ⟨x, hx⟩ := hne₂
    exact disjoint_left.1 hdj hx (hn (Surface.discBd_subset _ (hA₂ hx)))
  · ext z
    constructor
    · exact fun h ↦ hΔ₁Δ h
    · intro hz
      by_contra hn
      have hzE : cap.emb z ∈ E := hdiff ⟨hz, hn⟩
      exact hn (hbdΔ₁ ⟨hz, hbE ▸ mem_image_of_mem _ (hEr hzE)⟩)
  · ext z
    refine hint (cap.emb z) fun h ↦ h.2 ?_
    exact hbE ▸ mem_image_of_mem _ (hEr h.1)

omit [T2Space Shat] in
omit [T2Space S] in
theorem IsCappedSurface.mem_of_emb_mem (cap : IsCappedSurface S Shat) {Θ : Set
  S} (hΘ : Θ ∈ cuffs S) {z : S}
    (hz : cap.emb z ∈ closure (cap.cuffDisc Θ)) : z ∈ Θ := by
  rw [cap.closure_cuffDisc hΘ] at hz
  rcases hz with h | ⟨y, hy, he⟩
  · exact absurd (mem_range_self z) (cap.notMem_range hΘ h)
  · exact cap.isEmbedding.injective he ▸ hy

omit [T2Space S] in
theorem cuffs_eq_of_mem {Θ Θ' : Set S} (hΘ : Θ ∈ cuffs S) (hΘ' : Θ' ∈ cuffs S) {z : S} (h : z ∈ Θ)
  (h' : z ∈ Θ') : Θ = Θ' := by
  obtain ⟨a, -, rfl⟩ := hΘ
  obtain ⟨b, -, rfl⟩ := hΘ'
  exact (connectedComponentIn_eq h).trans (connectedComponentIn_eq h').symm

/-- The step of the proof of (10.2), Graph Minors XIX, pages 354-355. -/
theorem discSide : DiscSideStatement := by
  intro S Shat _ _ _ _ cap K F Δ hS hf hΔ hb Y _ _ ψ hY hψ
  subst hb
  rcases hf with ⟨hF, -, hsing⟩ | ⟨s, t, Θ, hΘ, hst, hs, ht, hKb, hl, hsub, hrest⟩
  · refine exists_inner_fragment hS cap hY hψ hΔ hF.ge (hF.le.trans subset_union_right)
      (hF.le.trans (image_subset_range _ _)) ?_
    rintro x ⟨hx, hxb⟩ y ⟨hy, hyb⟩
    obtain ⟨Θ₁, h₁, hxΘ⟩ := mem_iUnion₂.1 hx
    obtain ⟨Θ₂, h₂, hyΘ⟩ := mem_iUnion₂.1 hy
    rw [hF] at hxb hyb
    obtain ⟨a, ha, rfl⟩ := hxb
    obtain ⟨b, hb, rfl⟩ := hyb
    rw [hsing ⟨ha, cuff_subset_bd ⟨Θ₁, h₁.1⟩ (cap.mem_of_emb_mem h₁.1 hxΘ)⟩
      ⟨hb, cuff_subset_bd ⟨Θ₂, h₂.1⟩ (cap.mem_of_emb_mem h₂.1 hyΘ)⟩]
  · obtain ⟨Δ₁, -, h₁, -, hK₁, -, hr₁, -, hs₁, -, hnE, -, -, hpre, -⟩
    := exists_form_discs cap hΔ hΘ hst hs ht hKb hl hsub hrest
    rw [← hpre]
    refine exists_inner_fragment hS cap hY hψ h₁ hK₁ (fun x hx ↦ ?_) hr₁ ?_
    · rcases hs₁ hx with h | h
      · exact Or.inr h
      · refine Or.inl (mem_biUnion hΘ ?_)
        rw [cap.closure_cuffDisc hΘ]
        exact Or.inr h
    · rintro x ⟨hx, hxb⟩
      exfalso
      obtain ⟨Θ₁, h, hxΘ⟩ := mem_iUnion₂.1 hx
      have hne : Θ₁ ≠ Θ := fun he ↦ hnE (he ▸ h.2)
      rcases hs₁ hxb with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
      · have hzΘ := cap.mem_of_emb_mem h.1 hxΘ
        have hzb : z ∈ K.U ∩ bd S := ⟨hz, cuff_subset_bd ⟨Θ₁, h.1⟩ hzΘ⟩
        rw [hKb] at hzb
        rcases hzb with rfl | h'
        · exact hne (cuffs_eq_of_mem h.1 hΘ hzΘ hs)
        · exact hne (cuffs_eq_of_mem h.1 hΘ hzΘ (mem_singleton_iff.1 h' ▸ ht))
      · exact hne (cuffs_eq_of_mem h.1 hΘ (cap.mem_of_emb_mem h.1 hxΘ) hz)

end GraphMinor.GM19
