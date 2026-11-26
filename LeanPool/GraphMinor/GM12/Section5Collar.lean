/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section5Cap
public import LeanPool.GraphMinor.GM12.Section5Curve
import LeanPool.GraphMinor.Surface.MoveCuff
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# A collar of the common boundary

In the setting of Graph Minors XII, Section 5, each `O`-arc `C k` is a cuff of `Σ₁`, so it has a
collar
in `Σ₁`. We take these collars disjoint, and put them together in one map `b`, with level zero on
the
`O`-arcs and with the other levels outside `Σ₂` (`exists_outerCollar`).
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface

local notation "𝕀" => unitInterval

universe u

variable {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
  {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : P₁ → T} {D : Fin n → Set T}

omit [T2Space T] in
/-- Each `C k`, seen in `Σ₁`, is a cuff of `Σ₁`. -/
theorem isCuff_preimage (h : IsCappedSplit C P₁ P₂ ι D) (k : Fin n) :
    IsCuff (((↑) ⁻¹' C k : Set P₁)) := by
  classical
  have hbd : bd P₁ = (↑) ⁻¹' ⋃ i, C i := by
    rw [← h.bd₁]
    exact (preimage_image_eq _ Subtype.val_injective).symm
  have hO : ∀ i, IsOArc ((↑) ⁻¹' C i : Set P₁) := fun i => by
    apply isOArc_of_image IsEmbedding.subtypeVal
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (h.C_sub₁ i)]
    exact h.isOArc i
  have hcl : ∀ i, IsClosed ((↑) ⁻¹' C i : Set P₁) := fun i => by
    obtain ⟨f⟩ := hO i
    have : CompactSpace ((↑) ⁻¹' C i : Set P₁) := f.compactSpace
    exact (isCompact_iff_compactSpace.mpr this).isClosed
  have hconn : ∀ i, IsPreconnected ((↑) ⁻¹' C i : Set P₁) := fun i => by
    obtain ⟨f⟩ := hO i
    have hr : range (fun x : Circle => (f x).1) = (↑) ⁻¹' C i := by
      ext x
      constructor
      · rintro ⟨w, rfl⟩
        exact (f w).2
      · intro hx
        refine ⟨f.symm ⟨x, hx⟩, ?_⟩
        simp
    rw [← hr]
    exact isPreconnected_range (continuous_subtype_val.comp f.continuous)
  obtain ⟨g⟩ := hO k
  let x := (g 1)
  have hxk : x.1 ∈ ((↑) ⁻¹' C k : Set P₁) := x.2
  have hxbd : x.1 ∈ bd P₁ := by
    rw [hbd]
    exact mem_iUnion.mpr ⟨k, hxk⟩
  refine ⟨x.1, hxbd, ?_⟩
  apply Subset.antisymm
  · have hsub : connectedComponentIn (bd P₁) x.1 ⊆ (↑) ⁻¹' C k ∪ (⋃ i ∈ {i | i ≠ k}, (↑) ⁻¹' C i)
      := by
      intro y hy
      have hyb := connectedComponentIn_subset _ _ hy
      rw [hbd] at hyb
      obtain ⟨i, hi⟩ := mem_iUnion.mp hyb
      by_cases hik : i = k
      · subst hik
        exact .inl hi
      · exact .inr (mem_biUnion hik hi)
    have hcl' : IsClosed (⋃ i ∈ {i | i ≠ k}, ((↑) ⁻¹' C i : Set P₁)) :=
      (Set.toFinite _).isClosed_biUnion fun i _ => hcl i
    by_contra hns
    obtain ⟨y, hy, hyn⟩ := not_subset.mp hns
    have hy2 := (hsub hy).resolve_left hyn
    obtain ⟨z, hz, hzz⟩ := (isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn) _ _
      (hcl k) hcl' hsub
      ⟨x.1, mem_connectedComponentIn hxbd, hxk⟩ ⟨y, hy, hy2⟩
    obtain ⟨i, hik, hi⟩ := mem_iUnion₂.mp hzz.2
    exact Set.disjoint_left.mp (h.disjoint k i (Ne.symm hik)) hzz.1 hi
  · apply (hconn k).subset_connectedComponentIn hxk
    rw [hbd]
    exact preimage_mono (subset_iUnion C k)

omit [T2Space T] in
/-- Disjoint open neighbourhoods of the `O`-arcs in `Σ₁`. -/
theorem exists_disjoint_nhds (h : IsCappedSplit C P₁ P₂ ι D) :
    ∃ U : Fin n → Set P₁, (∀ k, IsOpen (U k)) ∧ (∀ k, ((↑) ⁻¹' C k : Set P₁) ⊆ U k) ∧
      ∀ k l, k ≠ l → Disjoint (U k) (U l) := by
  classical
  have : CompactSpace P₁ := h.manifold₁.1
  have hcomp : ∀ i, IsCompact ((↑) ⁻¹' C i : Set P₁) := fun i => by
    apply (isCompact_iff_compactSpace.mpr ?_ : IsCompact _)
    obtain ⟨f⟩ := id (show IsOArc ((↑) ⁻¹' C i : Set P₁) from by
      apply isOArc_of_image IsEmbedding.subtypeVal
      rw [Subtype.image_preimage_coe, inter_eq_right.mpr (h.C_sub₁ i)]
      exact h.isOArc i)
    exact f.compactSpace
  have hsep : ∀ k l, k ≠ l → SeparatedNhds ((↑) ⁻¹' C k : Set P₁) ((↑) ⁻¹' C l) := fun k l hkl =>
    SeparatedNhds.of_isCompact_isCompact (hcomp k) (hcomp l)
      (Set.disjoint_left.mpr fun x hx hx' => Set.disjoint_left.mp (h.disjoint k l hkl) hx hx')
  choose! u v hu hv hCu hCv hd using hsep
  let V : Fin n → Fin n → Set P₁ := fun k l => if k < l then u k l else v l k
  refine ⟨fun k => ⋂ l ∈ {l | l ≠ k}, V k l, ?_, ?_, ?_⟩
  · intro k
    refine (Set.toFinite _).isOpen_biInter fun l hl => ?_
    simp only [V]
    split_ifs with hlt
    · exact hu k l (Ne.symm hl)
    · exact hv l k hl
  · intro k x hx
    refine mem_iInter₂.mpr fun l hl => ?_
    simp only [V]
    split_ifs with hlt
    · exact hCu k l (Ne.symm hl) hx
    · exact hCv l k hl hx
  · intro k l hkl
    refine Set.disjoint_left.mpr fun x hk hl => ?_
    have h1 := mem_iInter₂.mp hk l (Ne.symm hkl)
    have h2 := mem_iInter₂.mp hl k hkl
    simp only [V] at h1 h2
    rcases lt_or_gt_of_ne hkl with hlt | hlt
    · rw [ite_eq_left hlt] at h1
      rw [ite_eq_right (not_lt.mpr hlt.le)] at h2
      exact Set.disjoint_left.mp (hd k l hkl) h1 h2
    · rw [ite_eq_right (not_lt.mpr hlt.le)] at h1
      rw [ite_eq_left hlt] at h2
      exact Set.disjoint_left.mp (hd l k hkl.symm) h2 h1

omit [T2Space T] in
/-- A collar of the common boundary of `Σ₁` and `Σ₂` in `Σ₁`. -/
theorem exists_outerCollar (h : IsCappedSplit C P₁ P₂ ι D) :
    ∃ b : (Fin n × Circle) × 𝕀 → S, IsOuterCollar P₂ b ∧ (∀ p, b p ∈ P₁) ∧
      (∀ k, ∀ x ∈ C k, ∃ w, b ((k, w), 0) = x) ∧ (∀ y, b (y, 0) ∈ C y.1) ∧
      ∀ ε : 𝕀, ε ≠ 0 → IsOpen (P₂ ∪ b '' {p | p.2 < ε}) := by
  classical
  obtain ⟨U, hUo, hCU, hUd⟩ := exists_disjoint_nhds h
  have hO : ∀ i, IsOArc ((↑) ⁻¹' C i : Set P₁) := fun i => by
    apply isOArc_of_image IsEmbedding.subtypeVal
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (h.C_sub₁ i)]
    exact h.isOArc i
  have hO' : ∀ i, Nonempty (Circle ≃ₜ ((↑) ⁻¹' C i : Set P₁)) := hO
  let φ : ∀ i, Circle ≃ₜ ((↑) ⁻¹' C i : Set P₁) := fun i => Classical.choice (hO' i)
  have hcoll := fun k => exists_collar h.manifold₁ (isCuff_preimage h k) (φ k) (hUo k) (hCU k)
  choose β hβc hβi hβU hβ0 hβo using hcoll
  let b' : Fin n × (Circle × 𝕀) → S := fun q => (β q.1 q.2).1
  have hb'c : Continuous b' := by
    apply continuous_prod_of_discrete_left.mpr
    intro k
    exact continuous_subtype_val.comp (hβc k)
  let e : (Fin n × Circle) × 𝕀 ≃ₜ Fin n × (Circle × 𝕀) := Homeomorph.prodAssoc _ _ _
  let b : (Fin n × Circle) × 𝕀 → S := fun p => (β p.1.1 (p.1.2, p.2)).1
  have hbc : Continuous b := hb'c.comp e.continuous
  have hbi : Function.Injective b := by
    rintro ⟨⟨k, w⟩, s⟩ ⟨⟨l, w'⟩, s'⟩ he
    have he' : β k (w, s) = β l (w', s') := Subtype.ext he
    by_cases hkl : k = l
    · subst hkl
      have := hβi k he'
      simp only [Prod.mk.injEq] at this
      rw [this.1, this.2]
    · exact (Set.disjoint_left.mp (hUd k l hkl) (hβU k ⟨_, rfl⟩) (he' ▸ hβU l ⟨_, rfl⟩)).elim
  have hb0 : ∀ y, b (y, 0) ∈ C y.1 := fun y => by
    change (β y.1 (y.2, 0)).1 ∈ _
    rw [hβ0]
    exact (φ y.1 y.2).2
  have hsurj : ∀ k, ∀ x ∈ C k, ∃ w, b ((k, w), 0) = x := by
    intro k x hx
    have hxk : (⟨x, h.C_sub₁ k hx⟩ : P₁) ∈ ((↑) ⁻¹' C k : Set P₁) := hx
    refine ⟨(φ k).symm ⟨_, hxk⟩, ?_⟩
    change (β k (_, 0)).1 = x
    rw [hβ0]
    simp
  have hP₂ : ∀ p, b p ∈ P₂ → p.2 = 0 := by
    rintro ⟨⟨k, w⟩, s⟩ hp
    have hmem : b ((k, w), s) ∈ P₁ ∩ P₂ := ⟨(β k (w, s)).2, hp⟩
    rw [h.inter] at hmem
    obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
    obtain ⟨w', hw'⟩ := hsurj l _ hl
    have hinj := hbi hw'
    exact (congrArg Prod.snd hinj).symm
  have hcol : IsOuterCollar P₂ b :=
    ⟨hbc, hbi, fun y => h.C_sub₂ y.1 (hb0 y), fun y s hs hm => hs (hP₂ (y, s) hm)⟩
  refine ⟨b, hcol, fun p => (β p.1.1 (p.1.2, p.2)).2, hsurj, hb0, ?_⟩
  intro ε hε
  have hP₁ := h.isClosed₁
  have hε0 : (0 : 𝕀) < ε := unitInterval.pos_iff_ne_zero.mpr hε
  let O : Fin n → Set P₁ := fun k => β k '' {p | p.2 < ε}
  have hOo : ∀ k, IsOpen (O k) := by
    intro k
    have hcl : IsClosed (β k '' {p | ε ≤ p.2}) := by
      have hc : IsClosed {p : Circle × 𝕀 | ε ≤ p.2} := isClosed_le continuous_const continuous_snd
      have : CompactSpace P₁ := h.manifold₁.1
      exact (hc.isCompact.image (hβc k)).isClosed
    have he : O k = (range (β k) \ β k '' {x | x.2 = 1}) \ β k '' {p | ε ≤ p.2} := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨⟨⟨p, rfl⟩, ?_⟩, ?_⟩
        · rintro ⟨q, hq, he⟩
          have := hβi k he
          subst this
          have h1 : q.2 = 1 := hq
          have h2 : q.2 < ε := hp
          rw [h1] at h2
          exact absurd h2 (not_lt.mpr unitInterval.le_one')
        · rintro ⟨q, hq, he⟩
          have := hβi k he
          subst this
          exact absurd (show q.2 < ε from hp) (not_lt.mpr (show ε ≤ q.2 from hq))
      · rintro ⟨⟨⟨p, rfl⟩, -⟩, hn⟩
        refine ⟨p, ?_, rfl⟩
        by_contra hge
        exact hn ⟨p, (not_lt.mp (show ¬ p.2 < ε from hge) : ε ≤ p.2), rfl⟩
    rw [he]
    exact (hβo k).sdiff hcl
  have hTc : IsClosed (⋃ k, O k)ᶜ := (isOpen_iUnion hOo).isClosed_compl
  have hcl : IsClosed (((↑) : P₁ → S) '' (⋃ k, O k)ᶜ) :=
    hP₁.isClosedEmbedding_subtypeVal.isClosedMap _ hTc
  have hcompl : (P₂ ∪ b '' {p | p.2 < ε}) = (((↑) : P₁ → S) '' (⋃ k, O k)ᶜ)ᶜ := by
    ext x
    constructor
    · rintro hx ⟨p, hp, rfl⟩
      rcases hx with hx | ⟨⟨⟨k, w⟩, s⟩, hs, he⟩
      · have hmem : p.1 ∈ P₁ ∩ P₂ := ⟨p.2, hx⟩
        rw [h.inter] at hmem
        obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
        obtain ⟨w, hw⟩ := hsurj l _ hl
        refine hp (mem_iUnion.mpr ⟨l, (w, 0), hε0, ?_⟩)
        exact Subtype.ext hw
      · exact hp (mem_iUnion.mpr ⟨k, (w, s), hs, Subtype.ext he⟩)
    · intro hx
      by_contra hn
      have hn1 : x ∉ P₂ := fun h' => hn (.inl h')
      have hn2 : x ∉ b '' {p | p.2 < ε} := fun h' => hn (.inr h')
      have hx₁ : x ∈ P₁ := by
        have : x ∈ P₁ ∪ P₂ := h.union ▸ mem_univ x
        exact this.resolve_right hn1
      refine hx ⟨⟨x, hx₁⟩, ?_, rfl⟩
      intro hO'
      obtain ⟨k, ⟨w, s⟩, hs, he⟩ := mem_iUnion.mp hO'
      exact hn2 ⟨((k, w), s), hs, congrArg Subtype.val he⟩
  rw [hcompl]
  exact hcl.isOpen_compl

end GraphMinor.GM12
