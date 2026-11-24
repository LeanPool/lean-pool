/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section5Collar
import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.Surface.SurfacePull
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.PlaneFacts

/-!
# Lines in `Σ₁` with ends on the common boundary

We move edges and closed discs between `Σ` and the capped surface `Σ̂₁`, and read the capped form of
Graph Minors XII, (5.4) (page 255), back in `Σ₁` (`exists_piece`).
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

variable {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
  {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : P₁ → T} {D : Fin n → Set T}
  {Γ : Drawing S} {Γ₁ : Drawing T}

omit [T2Space S] [T2Space T] in
theorem capUp_inter_V (hι : Function.Injective ι) (hΓ : IsCappedDrawing ι Γ Γ₁) (X : Set S) :
    capUp ι (X ∩ Γ.V) = capUp ι X ∩ Γ₁.V := by
  rw [hΓ.2]
  ext y
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨p, h1, rfl⟩, ⟨p, h2, rfl⟩⟩
  · rintro ⟨⟨p, h1, rfl⟩, h2⟩
    exact ⟨p, ⟨h1, (mem_capUp_val hι).mp h2⟩, rfl⟩

omit [T2Space T] in
/-- An edge of `Γ` that does not meet the common boundary lies on one side. -/
theorem edge_side (h : IsCappedSplit C P₁ P₂ ι D) (hN : ∀ k, Γ.IsNormal (C k)) {f : Set S}
    (hf : f ∈ Γ.E) : (f ⊆ P₁ ∧ Disjoint f P₂) ∨ (f ⊆ P₂ ∧ Disjoint f P₁) := by
  have hdis : ∀ x ∈ f, x ∈ P₁ → x ∈ P₂ → False := by
    intro x hx h₁ h₂
    have hm : x ∈ P₁ ∩ P₂ := ⟨h₁, h₂⟩
    rw [h.inter] at hm
    obtain ⟨k, hk⟩ := mem_iUnion.mp hm
    exact (hf.2.1 hx).2 (hN k ⟨hk, (hf.2.1 hx).1⟩)
  have hcov : f ⊆ P₁ ∪ P₂ := fun x _ => h.union ▸ mem_univ x
  have hpre : IsPreconnected f := hf.2.2.1.isConnected.isPreconnected
  obtain ⟨x, hx⟩ := hf.1
  have hsub : ∀ {A B : Set S}, IsClosed A → IsClosed B → f ⊆ A ∪ B → (∀ y ∈ f, y ∈ A → y ∈ B
    → False) →
      x ∈ A → f ⊆ A := by
    intro A B hA hB hc hd hxA
    by_contra hn
    obtain ⟨y, hy, hyA⟩ := not_subset.mp hn
    obtain ⟨z, hzf, hzA, hzB⟩ := isPreconnected_closed_iff.mp hpre A B hA hB hc ⟨x, hx, hxA⟩
      ⟨y, hy, (hc hy).resolve_left hyA⟩
    exact hd z hzf hzA hzB
  rcases hcov hx with hx₁ | hx₂
  · have := hsub h.isClosed₁ h.isClosed₂ hcov hdis hx₁
    exact .inl ⟨this, Set.disjoint_left.mpr fun y hy hy₂ => hdis y hy (this hy) hy₂⟩
  · have := hsub h.isClosed₂ h.isClosed₁ (by rwa [Set.union_comm]) (fun y hy a b
      => hdis y hy b a) hx₂
    exact .inr ⟨this, Set.disjoint_left.mpr fun y hy hy₁ => hdis y hy hy₁ (this hy)⟩

omit [T2Space S] in
/-- An edge in `Σ₁` moves to an edge of `Γ₁`. -/
theorem edge_capUp (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁) {f : Set S}
    (hf : f ∈ Γ.E) (hP : f ⊆ P₁) : capUp ι f ∈ Γ₁.E := by
  have hι := h.isEmbedding
  have hsubU : capUp ι f ⊆ Γ₁.U \ Γ₁.V := by
    rw [hΓ.1, hΓ.2]
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨⟨p, (hf.2.1 hp).1, rfl⟩, ?_⟩
    rintro ⟨q, hq, he⟩
    rw [hι.injective he] at hq
    exact (hf.2.1 hp).2 hq
  have hpc : IsPathConnected (capUp ι f) :=
    (hf.2.2.1.preimage_coe hP).image hι.continuous
  refine ⟨?_, hsubU, hpc, ?_⟩
  · obtain ⟨x, hx⟩ := hf.1
    exact ⟨_, val_mem_capUp (hP hx) hx⟩
  · intro E hE hEc hsub
    have : Nonempty P₁ := by
      obtain ⟨x, hx⟩ := hf.1
      exact ⟨⟨x, hP hx⟩⟩
    have hcP : CompactSpace P₁ := h.manifold₁.1
    obtain ⟨r, hr, hri⟩ := exists_continuousOn_inv hι.continuous hι.injective
    have hEr : E ⊆ range ι := fun y hy => by
      have := hE hy
      rw [hΓ.1] at this
      exact capUp_subset_range _ this.1
    have heq : capDown ι E = (fun y => (r y).1) '' E := by
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨ι p, hp, by simp [hri]⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨p, rfl⟩ := hEr hy
        exact ⟨p, hy, by simp [hri]⟩
    have hpcD : IsPathConnected (capDown ι E) := by
      rw [heq]
      exact hEc.image' (continuous_subtype_val.comp_continuousOn (hr.mono hEr))
    have hsubD : capDown ι E ⊆ Γ.U \ Γ.V := by
      rintro _ ⟨p, hp, rfl⟩
      have hx := hE hp
      rw [hΓ.1, hΓ.2] at hx
      refine ⟨(mem_capUp_val hι.injective).mp hx.1, fun hV => hx.2 ⟨p, hV, rfl⟩⟩
    have hfD : f ⊆ capDown ι E := by
      intro x hx
      have := hsub (val_mem_capUp (hP hx) hx)
      exact ⟨⟨x, hP hx⟩, this, rfl⟩
    have := hf.2.2.2 _ hsubD hpcD hfD
    rw [← this, capUp_capDown hEr]

/-- Each edge of `Γ₁` comes from an edge of `Γ` in `Σ₁`. -/
theorem exists_edge_capUp (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) {e : Set T} (he : e ∈ Γ₁.E) :
    ∃ f ∈ Γ.E, f ⊆ P₁ ∧ e = capUp ι f := by
  have hι := h.isEmbedding
  obtain ⟨y, hy⟩ := he.1
  have hyU := he.2.1 hy
  have hy1 := hyU.1
  rw [hΓ.1] at hy1
  obtain ⟨p, hp, rfl⟩ := hy1
  have hpV : p.1 ∉ Γ.V := fun hV => hyU.2 (by rw [hΓ.2]; exact ⟨p, hV, rfl⟩)
  obtain ⟨f, hf, hpf⟩ := Γ.exists_edge_of_mem hp hpV
  have hP : f ⊆ P₁ := by
    rcases edge_side h hN hf with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact (Set.disjoint_left.mp h2 hpf p.2).elim
  have hup := edge_capUp h hΓ hf hP
  exact ⟨f, hf, hP, Γ₁.edge_eq_of_mem he hup hy ⟨p, hpf, rfl⟩⟩

omit [T2Space S] in
/-- Moving a closed disc of `Σ̂₁` off the open caps back to `Σ`. -/
theorem disc_capDown [Nonempty T] (h : IsCappedSplit C P₁ P₂ ι D) {Δ : Set T} (hΔ : IsClosedDisc Δ)
    (hr : Δ ⊆ range ι) :
    IsClosedDisc (capDown ι Δ) ∧ discBd (capDown ι Δ) = capDown ι (discBd Δ) := by
  classical
  have hι := h.isEmbedding
  obtain ⟨t₀⟩ := ‹Nonempty T›
  have hne : Nonempty P₁ := by
    obtain ⟨x, hx⟩ := (show Δ.Nonempty from hΔ.isPathConnected.nonempty)
    exact ⟨(hr hx).choose⟩
  have hcP : CompactSpace P₁ := h.manifold₁.1
  obtain ⟨r, hrc, hri⟩ := exists_continuousOn_inv hι.continuous hι.injective
  let f : T → S := fun y => (r y).1
  let f' : S → T := fun x => if hx : x ∈ P₁ then ι ⟨x, hx⟩ else t₀
  have hf : ContinuousOn f Δ := continuous_subtype_val.comp_continuousOn (hrc.mono hr)
  have hfi : ∀ X : Set T, X ⊆ range ι → f '' X = capDown ι X := by
    intro X hX
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨p, rfl⟩ := hX hy
      exact ⟨p, hy, by simp [f, hri]⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨ι p, hp, by simp [f, hri]⟩
  have hf'c : ContinuousOn f' P₁ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : P₁.domRestrict f' = ι := by
      funext ⟨x, hx⟩
      change f' x = ι ⟨x, hx⟩
      simp [f', hx]
    rw [this]
    exact hι.continuous
  have himg : f '' Δ ⊆ P₁ := by
    rw [hfi Δ hr]
    exact capDown_subset _
  have hl : LeftInvOn f' f Δ := by
    intro y hy
    obtain ⟨p, rfl⟩ := hr hy
    simp [f, f', hri]
  have := IsClosedDisc.image hΔ hf (hf'c.mono himg) hl
  rw [hfi Δ hr, hfi _ ((GraphMinor.Surface.discBd_subset Δ).trans hr)] at this
  exact this

/-- The output of (5.4), read in `Σ`, for a line `L` of `Σ₁` with ends `s, t`. The line `R` is the
line `FTilde` of the paper and `Δ` is its disc. The closed disc `Δ₁` is the disc of `Σ̂₁` chosen by
the
tangle, which includes `Δ`. -/
structure PieceData (C : Fin n → Set S) (ι : P₁ → T) (Γ : Drawing S) (Γ₁ : Drawing T)
    (𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))) (L : Set S) (s t : S)
    (R : Set S) (Δ₁ : Set T) (Δ : Set S) : Prop where
  /-- `R` is a line with ends `s, t`. -/
  line : IsLineWithEnds R s t
  /-- It lies in one of the `O`-arcs. -/
  on : ∃ k, R ⊆ C k
  /-- `L` and `R` meet just in their ends. -/
  meet : L ∩ R = {s, t}
  /-- `R` is as short as `L`. -/
  count : (R ∩ Γ.V).ncard ≤ (L ∩ Γ.V).ncard
  /-- `Δ` is a closed disc. -/
  disc : IsClosedDisc Δ
  /-- It is bounded by `L ∪ R`. -/
  bd : discBd Δ = L ∪ R
  /-- It includes `L`. -/
  sub_L : L ⊆ Δ
  /-- It includes `R`. -/
  sub_R : R ⊆ Δ
  /-- It lies in `Σ₁`. -/
  sub_P : Δ ⊆ P₁
  /-- `Δ₁` is a closed disc. -/
  disc₁ : IsClosedDisc Δ₁
  /-- It includes `Δ`. -/
  sub₁ : capUp ι Δ ⊆ Δ₁
  /-- Its frontier meets `Σ₁` just in `L`. -/
  frontier₁ : ∀ x ∈ frontier Δ₁, x ∈ range ι → x ∈ capUp ι L
  /-- The tangle puts it on the small side. -/
  mem : ((PaintingOrDrawing.drawing Γ₁).inter Δ₁, (PaintingOrDrawing.drawing Γ₁).interOutside Δ₁) ∈
    𝒯

variable {θ : ℕ} {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))}

/-- **Graph Minors XII, (5.4)** (page 255), for a line `L` of `Σ₁` with ends `s, t` on the common
boundary and no other point on it. -/
theorem exists_piece [ConnectedSpace T] (h : IsCappedSplit C P₁ P₂ ι D)
  (hΓ : IsCappedDrawing ι Γ Γ₁)
    (_hN : ∀ k, Γ.IsNormal (C k)) (H : CapSetup (fun k => closure (D k)) Γ₁ θ 𝒯)
    {L : Set S} {s t : S} (hL : IsLineWithEnds L s t) (hst : s ≠ t) (hLN : Γ.IsNormal L)
    (hsmall : (L ∩ Γ.V).ncard < θ) (hLP : L ⊆ P₁) (hs : s ∈ P₂) (ht : t ∈ P₂)
    (hmeet : ∀ x ∈ L, x ∈ P₂ → x = s ∨ x = t) :
    ∃ R Δ₁ Δ, PieceData C ι Γ Γ₁ 𝒯 L s t R Δ₁ Δ := by
  have hι := h.isEmbedding
  have hιi := hι.injective
  have hrange : L ⊆ range ((↑) : P₁ → S) := by
    rw [Subtype.range_coe]
    exact hLP
  obtain ⟨u, v, hu, hv, hLp⟩ := hL.pull IsEmbedding.subtypeVal hrange
  have hLT : IsLineWithEnds (capUp ι L) (ι u) (ι v) := hLp.map_of_embedding hι
  have hne : ι u ≠ ι v := fun he => hst (by rw [← hu, ← hv, hιi he])
  have hC : ∀ {x : S} {p : P₁}, p.1 = x → x ∈ P₂ → ∃ k, ι p ∈ discBd (closure (D k)) := by
    intro x p hp hx
    have hm : x ∈ P₁ ∩ P₂ := ⟨hp ▸ p.2, hx⟩
    rw [h.inter] at hm
    obtain ⟨k, hk⟩ := mem_iUnion.mp hm
    refine ⟨k, ?_⟩
    rw [(cap_closure h k).2.1]
    exact ⟨p, by change p.1 ∈ C k; rw [hp]; exact hk, rfl⟩
  obtain ⟨i, hi⟩ := hC hu hs
  obtain ⟨j, hj⟩ := hC hv ht
  have hNT : Γ₁.IsNormal (capUp ι L) := by
    rintro _ ⟨⟨p, hp, rfl⟩, hpU⟩
    rw [hΓ.1] at hpU
    have hU := (mem_capUp_val hιi).mp hpU
    rw [hΓ.2]
    exact ⟨p, hLN ⟨hp, hU⟩, rfl⟩
  have hcount : ∀ X : Set S, X ⊆ P₁ → (capUp ι X ∩ Γ₁.V).ncard = (X ∩ Γ.V).ncard := by
    intro X hX
    rw [← capUp_inter_V hιi hΓ, ncard_capUp hιi (inter_subset_left.trans hX)]
  have hsmallT : (capUp ι L ∩ Γ₁.V).ncard < θ := by rwa [hcount L hLP]
  have hmeetT : ∀ k, capUp ι L ∩ closure (D k) ⊆ {ι u, ι v} := by
    rintro k _ ⟨⟨p, hp, rfl⟩, hpc⟩
    have hdiff : ι p ∈ capUp ι (C k) := closure_diff_eq h k ▸
      ⟨hpc, fun hd => Set.disjoint_left.mp (h.D_off k) hd ⟨p, rfl⟩⟩
    have hpC : p.1 ∈ C k := (mem_capUp_val hιi).mp hdiff
    rcases hmeet p.1 hp (h.C_sub₂ k hpC) with he | he
    · exact .inl (by rw [Subtype.ext (he.trans hu.symm)])
    · exact .inr (by rw [Subtype.ext (he.trans hv.symm)]; rfl)
  obtain ⟨R', Δ₁, Δ', hd⟩ := exists_sideData H h.surface_hat hLT hne hNT hsmallT hi hj hmeetT
  obtain ⟨k, hk⟩ := hd.on_cap
  rw [(cap_closure h k).2.1] at hk
  have hRr : R' ⊆ range ι := hk.trans (capUp_subset_range _)
  have hΔr : Δ' ⊆ range ι := by
    intro x hx
    by_contra hn
    have : x ∈ ⋃ m, D m := h.compl ▸ hn
    obtain ⟨m, hm⟩ := mem_iUnion.mp this
    exact Set.disjoint_left.mp (hd.off m) hx ((cap_closure h m).2.2.symm ▸ hm)
  obtain ⟨u', v', hu', hv', hRp⟩ := hd.line.pull hι hRr
  have hu'' : u' = u := hιi hu'
  have hv'' : v' = v := hιi hv'
  subst hu'' hv''
  have hRl : IsLineWithEnds (capDown ι R') s t := by
    have := hRp.map_of_embedding (j := ((↑) : P₁ → S)) IsEmbedding.subtypeVal
    rwa [hu, hv] at this
  have hUR : capUp ι (capDown ι R') = R' := capUp_capDown hRr
  have hRP : capDown ι R' ⊆ P₁ := capDown_subset _
  obtain ⟨hΔd, hΔb⟩ := disc_capDown h hd.disc hΔr
  have hbd_eq : discBd (capDown ι Δ') = L ∪ capDown ι R' := by
    rw [hΔb, hd.bd, capDown, preimage_union, image_union, ← capDown, ← capDown,
      capDown_capUp hιi hLP]
  have hbdsub := GraphMinor.Surface.discBd_subset Δ'
  rw [hd.bd] at hbdsub
  refine ⟨capDown ι R', Δ₁, capDown ι Δ', ⟨hRl, ⟨k, ?_⟩, ?_, ?_, hΔd, hbd_eq, ?_, ?_,
    capDown_subset _, hd.disc₁, ?_, ?_, hd.mem⟩⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (mem_capUp_val hιi).mp (hk hp)
  · apply Subset.antisymm
    · rintro x ⟨hxL, p, hp, rfl⟩
      have : ι p ∈ capUp ι L ∩ R' := ⟨(mem_capUp_val hιi).mpr hxL, hp⟩
      rw [hd.meet] at this
      rcases this with he | he
      · exact .inl (by rw [hιi he, hu])
      · exact .inr (by rw [hιi he, hv]; rfl)
    · rintro x (rfl | rfl)
      · exact ⟨hL.left_mem, hRl.left_mem⟩
      · exact ⟨hL.right_mem, hRl.right_mem⟩
  · rw [← hcount _ hRP, ← hcount _ hLP, hUR]
    exact hd.count
  · intro x hx
    exact ⟨⟨x, hLP hx⟩, hbdsub (.inl ⟨⟨x, hLP hx⟩, hx, rfl⟩), rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, hbdsub (.inr hp), rfl⟩
  · rintro _ ⟨p, ⟨q, hq, he⟩, rfl⟩
    have : p = q := Subtype.ext he.symm
    subst this
    exact hd.sub hq
  · intro x hx hr
    apply hd.frontier₁ x hx
    intro m hm
    rw [(cap_closure h m).2.2] at hm
    exact Set.disjoint_left.mp (h.D_off m) hm hr

end GraphMinor.GM12
