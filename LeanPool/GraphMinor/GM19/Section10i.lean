/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10h

/-!
# The location of a finite family of separations

The location of the proofs of (10.4), (10.5) and (11.1): one arm for each member of a family of
separations `(Γ ∩ A, Γ ∩ B)`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


/-- A family of `λ`-linked separations of `Γ`, by pairs of sets of `Σ`, of order `< θ`, with `Γ ∩ A
⊆ Γ ∩ B'` for two different
members. -/
structure IsLinkedFamily (D : TangleDatum cap χ) (θ : ℕ) (𝓟 : Set (Set S × Set S)) : Prop where
  finite : 𝓟.Finite
  linked : ∀ p ∈ 𝓟, GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (D.P.Γ.restrict p.1)
    (D.P.Γ.restrict p.2)
  order : ∀ p ∈ 𝓟, Hypergraph.separationOrder (D.P.Γ.restrict p.1) (D.P.Γ.restrict p.2) < θ
  disjoint : ∀ p ∈ 𝓟, ∀ q ∈ 𝓟, p ≠ q → D.P.Γ.restrict p.1 ≤ D.P.Γ.restrict q.2
  closed : ∀ p ∈ 𝓟, IsClosed p.2

variable {D : TangleDatum cap χ} {θ : ℕ} {𝓟 : Set (Set S × Set S)}

/-- The arm of a member of the family. -/
noncomputable def IsLinkedFamily.arm (h : IsLinkedFamily D θ 𝓟) (p : 𝓟) : Arm D.P.Γ :=
  have hf := (D.P.Γ.restrict p.1.1 ∩ D.P.Γ.restrict p.1.2).vertexSet_finite
  restrictArm D.P.Γ p.1.1 p.1.2 (D.isTangle.isSeparation (h.linked p.1 p.2).1) hf.toFinset.toList
    (Finset.nodup_toList _) (by ext v; simp)

/-- The rooted location of the family. -/
noncomputable def IsLinkedFamily.location (h : IsLinkedFamily D θ 𝓟) : RootedLocation D.P.Γ where
  arms := range h.arm
  finite_arms := by
    have := h.finite.to_subtype
    exact finite_range _
  disjoint_arms := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hne
    exact h.disjoint p.1 p.2 q.1 q.2 fun heq ↦ hne (congrArg h.arm (Subtype.ext heq))

omit [T2Space S] [T2Space Shat] in
theorem IsLinkedFamily.M_V (h : IsLinkedFamily D θ 𝓟) :
    h.location.M.vertexSet = D.P.Γ.V ∩ ⋂ p ∈ 𝓟, Prod.snd p := by
  ext v
  simp only [RootedLocation.M, IsLinkedFamily.location, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hv, ha⟩
    exact ⟨hv, fun p hp ↦ (ha _ ⟨⟨p, hp⟩, rfl⟩).2⟩
  · rintro ⟨hv, ha⟩
    refine ⟨hv, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact ⟨hv, ha p.1 p.2⟩

omit [T2Space S] [T2Space Shat] in
theorem IsLinkedFamily.M_E (h : IsLinkedFamily D θ 𝓟) :
    h.location.M.edgeSet = {e ∈ D.P.Γ.E | e ⊆ ⋂ p ∈ 𝓟, Prod.snd p} := by
  ext e
  simp only [RootedLocation.M, IsLinkedFamily.location, mem_ofPred_eq, subset_iInter_iff]
  constructor
  · rintro ⟨he, ha⟩
    exact ⟨he, fun p hp ↦ (ha _ ⟨⟨p, hp⟩, rfl⟩).2.1⟩
  · rintro ⟨he, ha⟩
    refine ⟨he, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact ⟨he, ha p.1 p.2, fun x hx ↦ closure_minimal (ha p.1 p.2) (h.closed p.1 p.2) hx.1.1⟩

omit [T2Space Shat] in
/-- The location isolates `𝒯`, by (8.8). -/
theorem IsLinkedFamily.isolates (h : IsLinkedFamily D θ 𝓟) (hS : IsSurface S) (hθ : 0 < θ) (hle : θ
  ≤ D.ord) :
    h.location.Isolates D.tb θ D.ord D.𝒯 := by
  refine theorem_8_8_proof D.tb hS D.P.fits.internally_three_connected D.isTangle ⟨?_, ?_⟩ ?_ hle
  · rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact (h.linked p.1 p.2).1
  · rintro _ ⟨p, rfl⟩
    exact h.linked p.1 p.2
  · rcases (h.location.arms).eq_empty_or_nonempty with he | hne
    · change sSup (Arm.order '' _) < θ
      rw [he, image_empty, csSup_empty]
      exact hθ
    · have hb : BddAbove (Arm.order '' h.location.arms) := (h.location.finite_arms.image _).bddAbove
      obtain ⟨_, ⟨p, rfl⟩, hA⟩ := Nat.sSup_mem (hne.image _) hb
      change sSup (Arm.order '' _) < θ
      rw [← hA]
      exact h.order p.1 p.2

variable {K : Drawing S} {Z : Type} [TopologicalSpace Z] {ψ : Z → S}

omit [T2Space S] [T2Space Shat] [TopologicalSpace Z] in
/-- The location of a family gives a place of a fragment over `f⁻¹` of the common side of the
family. -/
theorem IsLinkedFamily.exists_place (h : IsLinkedFamily D θ 𝓟) (hd : χ.IsDisjoint) {f : S ≃ₜ S}
  (hf : IsFramePreservingHomeo χ.Φ f)
    {Q : ColouredPainting χ} (I : IsColouredImage f Q D.P) (hrange : range ψ
      = f ⁻¹' ⋂ p ∈ 𝓟, Prod.snd p)
    (hinter : Q.Γ.U ∩ K.U ⊆ Q.Γ.V ∩ K.V) (han : IsAnchored Q.Γ K) {l : List S}
      (hl : ∀ v, v ∈ l ↔ v ∈ K.V ∩ Q.Γ.V)
    (hr : ∀ v, v ∈ K.U → v ∈ range ψ)
    (hπ : ∀ p ∈ 𝓟, ∀ v ∈ D.P.Γ.V, v ∈ p.1 → v ∈ p.2 → f.symm v ∈ K.U) {m : ℕ} (hm : 𝓟.ncard ≤ m) :
    ∃ X : Place χ, X.P = Q ∧ IsCutPlace χ K ψ l m X ∧ IsPlaceHomeoImage X ⟨hd, D.P, h.location⟩ f
      := by
  refine exists_cut_place hd hf I h.location h.M_V h.M_E hrange hinter han hl hr ?_ ?_
  · rintro _ ⟨p, rfl⟩ v hv
    have hv' : v ∈ (D.P.Γ.restrict p.1.1 ∩ D.P.Γ.restrict p.1.2).vertexSet := (h.arm p).π_set ▸ hv
    exact hπ p.1 p.2 v hv'.1.1 hv'.1.2 hv'.2.2
  · have := h.finite.to_subtype
    have h₁ : h.location.arms.ncard ≤ (univ : Set 𝓟).ncard := by
      change (range h.arm).ncard ≤ _
      rw [← image_univ]
      exact ncard_image_le (toFinite _)
    rw [Set.ncard_univ, Nat.card_coe_set_eq] at h₁
    exact h₁.trans hm

end GraphMinor.GM19
