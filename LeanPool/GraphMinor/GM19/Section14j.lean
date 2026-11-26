/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14i
public import LeanPool.GraphMinor.Surface.DiscRemove

/-!
# Graph Minors XIX, Section 14: removing several discs from a surface

The proof of (14.1) deletes the inside of each wheel from `Σ`. "Then $\Sigma'$ is a surface since
the $W$'s are disjoint and each $bd(W)$ is disjoint from
$bd(\Sigma_\chi)$." Here is that fact for a finite family of disjoint closed discs.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {R : Type} [TopologicalSpace R]

/-- Two subspaces that agree on an open set have the same local shape there. -/
theorem local_congr_of_open {A B O : Set R} (hO : IsOpen O) (h : A ∩ O = B ∩ O) {x : R}
  (hxA : x ∈ A) (hxB : x ∈ B) (hxO : x ∈ O) :
    (IsInteriorPoint (⟨x, hxA⟩ : ↥A) ↔ IsInteriorPoint (⟨x, hxB⟩ : ↥B)) ∧ (IsManifoldPoint
      (⟨x, hxA⟩ : ↥A) ↔ IsManifoldPoint (⟨x, hxB⟩ : ↥B)) := by
  have hOA : IsOpen (Subtype.val ⁻¹' O : Set ↥A) := hO.preimage continuous_subtype_val
  have hOB : IsOpen (Subtype.val ⁻¹' O : Set ↥B) := hO.preimage continuous_subtype_val
  have hab : ∀ z : (Subtype.val ⁻¹' O : Set ↥A), z.1.1 ∈ B := fun z ↦ by
    have : z.1.1 ∈ A ∩ O := ⟨z.1.2, z.2⟩
    rw [h] at this
    exact this.1
  have hba : ∀ z : (Subtype.val ⁻¹' O : Set ↥B), z.1.1 ∈ A := fun z ↦ by
    have : z.1.1 ∈ B ∩ O := ⟨z.1.2, z.2⟩
    rw [← h] at this
    exact this.1
  let φ : (Subtype.val ⁻¹' O : Set ↥A) ≃ₜ (Subtype.val ⁻¹' O : Set ↥B) :=
    { toFun := fun z ↦ ⟨⟨z.1.1, hab z⟩, z.2⟩
      invFun := fun z ↦ ⟨⟨z.1.1, hba z⟩, z.2⟩
      left_inv := fun z ↦ rfl
      right_inv := fun z ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let a : (Subtype.val ⁻¹' O : Set ↥A) := ⟨⟨x, hxA⟩, hxO⟩
  let b : (Subtype.val ⁻¹' O : Set ↥B) := ⟨⟨x, hxB⟩, hxO⟩
  have hφ : φ a = b := rfl
  have hφ' : φ.symm b = a := rfl
  constructor
  · rw [show (⟨x, hxA⟩ : ↥A) = a.1 from rfl, show (⟨x, hxB⟩ : ↥B) = b.1 from rfl,
      ← isInteriorPoint_sub hOA, ← isInteriorPoint_sub hOB]
    refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · exact hφ ▸ isInteriorPoint_of_isOpenEmbedding φ.isOpenEmbedding h'
    · exact hφ' ▸ isInteriorPoint_of_isOpenEmbedding φ.symm.isOpenEmbedding h'
  · rw [show (⟨x, hxA⟩ : ↥A) = a.1 from rfl, show (⟨x, hxB⟩ : ↥B) = b.1 from rfl]
    rw [show a.1 = Subtype.val a from rfl, show b.1 = Subtype.val b from rfl,
      isManifoldPoint_iff_of_isOpenEmbedding hOA.isOpenEmbedding_subtypeVal,
      isManifoldPoint_iff_of_isOpenEmbedding hOB.isOpenEmbedding_subtypeVal]
    refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · exact hφ ▸ isManifoldPoint_of_isOpenEmbedding φ.isOpenEmbedding h'
    · exact hφ' ▸ isManifoldPoint_of_isOpenEmbedding φ.symm.isOpenEmbedding h'

/-- **Removing the insides of finitely many disjoint closed discs from a surface.** -/
theorem remove_discs [ConnectedSpace R] (hR : IsSurface R) {ℱ : Set (Set R)} (hf : ℱ.Finite)
  (hd : ∀ E ∈ ℱ, IsClosedDisc E) (hint : ∀ E ∈ ℱ, ∀ x ∈ discBd E, IsInteriorPoint x)
    (hdis : ℱ.PairwiseDisjoint id) :
    IsClosed (⋃ E ∈ ℱ, discInt E)ᶜ ∧ IsSurface ↥(⋃ E ∈ ℱ, discInt E)ᶜ ∧ bd ↥(⋃ E ∈ ℱ, discInt E)ᶜ
      = Subtype.val ⁻¹' (bd R ∪ ⋃ E ∈ ℱ, discBd E) ∧
      ConnectedSpace ↥(⋃ E ∈ ℱ, discInt E)ᶜ := by
  classical
  have ht2 : T2Space R := hR.2.1
  have hcR : CompactSpace R := hR.1
  have hman := hR.2.2
  set X := (⋃ E ∈ ℱ, discInt E)ᶜ with hX
  have hop : IsOpen (⋃ E ∈ ℱ, discInt E) := isOpen_biUnion fun E hE ↦ (hd E hE).isOpen_discInt hman
  have hcl : IsClosed X := hop.isClosed_compl
  have hcS : CompactSpace ↥X := isCompact_iff_compactSpace.mp hcl.isCompact
  have hrest : ∀ {E : Set R}, E ∈ ℱ → IsOpen (⋃ E' ∈ ℱ \ {E}, E')ᶜ := fun {E} hE ↦
    (hf.sdiff.isClosed_biUnion fun E' hE' ↦ (hd E' hE'.1).isClosed).isOpen_compl
  have hagree : ∀ {E : Set R}, E ∈ ℱ → X ∩ (⋃ E' ∈ ℱ \ {E}, E')ᶜ = (discInt E)ᶜ ∩
    (⋃ E' ∈ ℱ \ {E}, E')ᶜ := by
    intro E hE
    ext y
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun h' ↦ h₁ (mem_biUnion hE h'), h₂⟩
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun h' ↦ ?_, h₂⟩
      obtain ⟨E', hE', hy⟩ := mem_iUnion₂.mp h'
      by_cases he : E' = E
      · exact h₁ (he ▸ hy)
      · exact h₂ (mem_biUnion (show E' ∈ ℱ \ {E} from ⟨hE', he⟩) hy.1)
  have hbdcase : ∀ {E : Set R} (hE : E ∈ ℱ) (x : ↥X), x.1 ∈ discBd E → IsManifoldPoint x
    ∧ x ∈ bd ↥X := by
    intro E hE x hxb
    obtain ⟨-, hsurf, hbd⟩ := remove_disc hR (hd E hE) (hint E hE)
    have hxE : x.1 ∈ (discInt E)ᶜ := fun h' ↦ h'.2 hxb
    have hxO : x.1 ∈ (⋃ E' ∈ ℱ \ {E}, E')ᶜ := by
      intro h'
      obtain ⟨E', hE', hy⟩ := mem_iUnion₂.mp h'
      exact disjoint_left.mp (hdis hE'.1 hE hE'.2) hy (Surface.discBd_subset _ hxb)
    obtain ⟨h₁, h₂⟩ := local_congr_of_open (hrest hE) (hagree hE) x.2 hxE hxO
    refine ⟨h₂.mpr (hsurf.2.2 _), fun h' ↦ ?_⟩
    have hm : (⟨x.1, hxE⟩ : ↥(discInt E)ᶜ) ∈ bd ↥(discInt E)ᶜ := by
      rw [hbd]
      exact .inr hxb
    exact hm (h₁.mp h')
  have hoff : ∀ x : ↥X, (∀ E ∈ ℱ, x.1 ∉ discBd E) → x.1 ∈ (⋃ E ∈ ℱ, E)ᶜ := by
    intro x hx h'
    obtain ⟨E, hE, hy⟩ := mem_iUnion₂.mp h'
    exact x.2 (mem_biUnion hE ⟨hy, hx E hE⟩)
  have hsubO : (⋃ E ∈ ℱ, E)ᶜ ⊆ X := by
    intro y hy h'
    obtain ⟨E, hE, hz⟩ := mem_iUnion₂.mp h'
    exact hy (mem_biUnion hE hz.1)
  have hOo : IsOpen (⋃ E ∈ ℱ, E)ᶜ := (hf.isClosed_biUnion fun E hE ↦ (hd E
    hE).isClosed).isOpen_compl
  have hsurf : IsSurface ↥X := by
    refine ⟨hcS, inferInstance, fun x ↦ ?_⟩
    by_cases hx : ∃ E ∈ ℱ, x.1 ∈ discBd E
    · obtain ⟨E, hE, hb⟩ := hx
      exact (hbdcase hE x hb).1
    · push Not at hx
      exact (sub_open_iff hOo hsubO (hoff x hx)).2 (hman _)
  refine ⟨hcl, hsurf, ?_, ?_⟩
  · ext x
    by_cases hx : ∃ E ∈ ℱ, x.1 ∈ discBd E
    · obtain ⟨E, hE, hb⟩ := hx
      exact ⟨fun _ ↦ .inr (mem_biUnion hE hb), fun _ ↦ (hbdcase hE x hb).2⟩
    · push Not at hx
      have h1 := (sub_open_iff hOo hsubO (hoff x hx)).1
      constructor
      · intro h
        exact .inl fun h2 ↦ h (h1.mpr h2)
      · rintro (h | h)
        · exact fun h2 ↦ h (h1.mp h2)
        · obtain ⟨E, hE, hb⟩ := mem_iUnion₂.mp h
          exact absurd hb (hx E hE)
  · have hprec : IsPreconnected X := by
      rw [isPreconnected_closed_iff]
      intro t t' ht ht' hsub hne hne'
      by_contra hnone
      have hdisj : Disjoint (X ∩ t) (X ∩ t') := by
        refine disjoint_left.mpr fun y h₁ h₂ ↦ hnone ⟨y, h₁.1, h₁.2, h₂.2⟩
      have hbdE : ∀ E ∈ ℱ, discBd E ⊆ X ∩ t ∨ discBd E ⊆ X ∩ t' := by
        intro E hE
        have hsubX : discBd E ⊆ X := fun y hy h' ↦ by
          obtain ⟨E', hE', hz⟩ := mem_iUnion₂.mp h'
          by_cases he : E' = E
          · exact hz.2 (he ▸ hy)
          · exact disjoint_left.mp (hdis hE' hE he) hz.1 (Surface.discBd_subset _ hy)
        have hp := (hd E hE).isOArc_discBd.isPreconnected
        by_contra hn
        push Not at hn
        obtain ⟨a, ha, ha'⟩ := not_subset.mp hn.1
        obtain ⟨b, hb, hb'⟩ := not_subset.mp hn.2
        have hat : a ∈ t' := (hsub (hsubX ha)).resolve_left fun h' ↦ ha' ⟨hsubX ha, h'⟩
        have hbt : b ∈ t := (hsub (hsubX hb)).resolve_right fun h' ↦ hb' ⟨hsubX hb, h'⟩
        obtain ⟨z, hz, hz₁, hz₂⟩ := (isPreconnected_closed_iff.mp hp) t t' ht ht' (fun y hy ↦ hsub
          (hsubX hy)) ⟨b, hb, hbt⟩ ⟨a, ha, hat⟩
        exact hnone ⟨z, hsubX hz, hz₁, hz₂⟩
      set ℱ₁ := {E ∈ ℱ | discBd E ⊆ X ∩ t} with hℱ₁
      set ℱ₂ := {E ∈ ℱ | discBd E ⊆ X ∩ t'} with hℱ₂
      have hcl₁ : IsClosed ((X ∩ t) ∪ ⋃ E ∈ ℱ₁, E) := (hcl.inter ht).union ((hf.subset
        (sep_subset _ _)).isClosed_biUnion fun E hE ↦ (hd E hE.1).isClosed)
      have hcl₂ : IsClosed ((X ∩ t') ∪ ⋃ E ∈ ℱ₂, E) := (hcl.inter ht').union ((hf.subset
        (sep_subset _ _)).isClosed_biUnion fun E hE ↦ (hd E hE.1).isClosed)
      have hcover : (univ : Set R) ⊆ ((X ∩ t) ∪ ⋃ E ∈ ℱ₁, E) ∪ ((X ∩ t') ∪ ⋃ E ∈ ℱ₂, E) := by
        intro y _
        by_cases hy : y ∈ X
        · rcases hsub hy with h' | h'
          · exact .inl (.inl ⟨hy, h'⟩)
          · exact .inr (.inl ⟨hy, h'⟩)
        · obtain ⟨E, hE, hz⟩ := mem_iUnion₂.mp (not_not.mp hy)
          rcases hbdE E hE with h' | h'
          · exact .inl (.inr (mem_biUnion (show E ∈ ℱ₁ from ⟨hE, h'⟩) hz.1))
          · exact .inr (.inr (mem_biUnion (show E ∈ ℱ₂ from ⟨hE, h'⟩) hz.1))
      obtain ⟨a, ha, hat⟩ := hne
      obtain ⟨b, hb, hbt⟩ := hne'
      obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp (isPreconnected_univ (α
        := R)) _ _ hcl₁ hcl₂ hcover ⟨a, trivial, .inl ⟨ha, hat⟩⟩ ⟨b, trivial, .inl ⟨hb, hbt⟩⟩
      have hedge : ∀ {E}, E ∈ ℱ → z ∈ E → z ∈ X → z ∈ discBd E := fun {E} hE hzE hzX ↦ by
        by_contra hn
        exact hzX (mem_biUnion hE ⟨hzE, hn⟩)
      rcases hz₁ with h₁ | h₁ <;> rcases hz₂ with h₂ | h₂
      · exact disjoint_left.mp hdisj h₁ h₂
      · obtain ⟨E, hE, hzE⟩ := mem_iUnion₂.mp h₂
        exact disjoint_left.mp hdisj h₁ (hE.2 (hedge hE.1 hzE h₁.1))
      · obtain ⟨E, hE, hzE⟩ := mem_iUnion₂.mp h₁
        exact disjoint_left.mp hdisj (hE.2 (hedge hE.1 hzE h₂.1)) h₂
      · obtain ⟨E, hE, hzE⟩ := mem_iUnion₂.mp h₁
        obtain ⟨E', hE', hzE'⟩ := mem_iUnion₂.mp h₂
        by_cases he : E = E'
        · subst he
          obtain ⟨y, hy, -⟩ := (hd E hE.1).isOArc_discBd.exists_ne (Classical.arbitrary R)
          exact disjoint_left.mp hdisj (hE.2 hy) (hE'.2 hy)
        · exact disjoint_left.mp (hdis hE.1 hE'.1 he) hzE hzE'
    have hne : Nonempty ↥X := by
      by_cases hemp : ℱ.Nonempty
      · obtain ⟨E, hE⟩ := hemp
        obtain ⟨y, hy, -⟩ := (hd E hE).isOArc_discBd.exists_ne (Classical.arbitrary R)
        refine ⟨⟨y, fun h' ↦ ?_⟩⟩
        obtain ⟨E', hE', hz⟩ := mem_iUnion₂.mp h'
        by_cases he : E' = E
        · exact hz.2 (he ▸ hy)
        · exact disjoint_left.mp (hdis hE' hE he) hz.1 (Surface.discBd_subset _ hy)
      · rw [not_nonempty_iff_eq_empty.mp hemp] at hX
        obtain ⟨y⟩ := (inferInstance : Nonempty R)
        exact ⟨⟨y, by simp [hX]⟩⟩
    obtain ⟨y⟩ := hne
    exact Subtype.connectedSpace ⟨⟨y.1, y.2⟩, hprec⟩

end GraphMinor.GM19
