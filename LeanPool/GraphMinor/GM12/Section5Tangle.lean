/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section5Replace
public import LeanPool.GraphMinor.GM11.Section6Pretangle
public import LeanPool.GraphMinor.GM11.Theorem66
import LeanPool.GraphMinor.GM14.DiscSlope

/-!
# The tangle step of Graph Minors XII, (5.3)

The proof of (5.3) compares separations of `Γ` with separations of `Γ₁`. Here we show that two
closed
sets that cover `U(Γ₁)` and meet only in vertices give a separation (`isSeparation_cover`), we read
membership in the induced tangle from such a pair (`mem_inducedAcross`), and we use [5, Theorem
(6.2)]
in the form the proof wants (`mem_of_cover`).
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 Hypergraph

universe u

variable {S T : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [T2Space T]
  {n : ℕ} {C : Fin n → Set S} {P₁ P₂ : Set S} {ι : P₁ → T} {D : Fin n → Set T}
  {Γ : Drawing S} {Γ₁ : Drawing T} {θ : ℕ}
  {𝒯 : Set (Hypergraph T (Set T) × Hypergraph T (Set T))}

omit [T2Space T] in
/-- Two closed sets that cover the drawing and meet in it only in vertices give a separation. -/
theorem isSeparation_cover {Γ : PaintingOrDrawing T} {Q₁ Q₂ : Set T} (h₁ : IsClosed Q₁)
    (h₂ : IsClosed Q₂) (hV : Γ.V ⊆ Q₁ ∪ Q₂) (hE : ∀ e ∈ Γ.E, e ⊆ Q₁ ∪ Q₂)
    (hn : ∀ e ∈ Γ.E, ∀ x ∈ e, x ∈ Q₁ → x ∈ Q₂ → False) :
    Γ.toHypergraph.IsSeparation (Γ.inter Q₁) (Γ.inter Q₂) := by
  have hedge : ∀ e ∈ Γ.E, e ⊆ Q₁ ∨ e ⊆ Q₂ := fun e he => by
    by_cases he₁ : e ⊆ Q₁
    · exact .inl he₁
    · right
      by_contra he₂
      obtain ⟨x, hx, hx₁⟩ := not_subset.mp he₁
      obtain ⟨y, hy, hy₂⟩ := not_subset.mp he₂
      have hx₂ := (hE e he hx).resolve_left hx₁
      have hy₁ := (hE e he hy).resolve_right hy₂
      obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp (Γ.edge_props he).1 Q₁ Q₂ h₁ h₂
        (hE e he)
        ⟨y, hy, hy₁⟩ ⟨x, hx, hx₂⟩
      exact hn e he z hz hz₁ hz₂
  refine ⟨inter_le h₁, inter_le h₂, ?_, ?_⟩
  · apply Hypergraph.ext
    · change (Γ.V ∩ Q₁) ∪ (Γ.V ∩ Q₂) = Γ.toHypergraph.vertexSet
      rw [Γ.toHypergraph_vertexSet]
      ext x
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        exact (hV h).imp (fun h' => ⟨h, h'⟩) fun h' => ⟨h, h'⟩
    · change {e | e ∈ Γ.E ∧ e ⊆ Q₁} ∪ {e | e ∈ Γ.E ∧ e ⊆ Q₂} = Γ.toHypergraph.edgeSet
      rw [Γ.toHypergraph_edgeSet]
      ext e
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        exact (hedge e h).imp (fun h' => ⟨h, h'⟩) fun h' => ⟨h, h'⟩
    · funext e v
      apply propext
      change (Γ.toHypergraph.Inc e v ∧ e ⊆ Q₁ ∧ v ∈ Q₁) ∨
        (Γ.toHypergraph.Inc e v ∧ e ⊆ Q₂ ∧ v ∈ Q₂) ↔ Γ.toHypergraph.Inc e v
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        have hi := PaintingOrDrawing.toHypergraph_inc.mp h
        rcases hedge e hi.1 with h' | h'
        · exact Or.inl ⟨h, h', h₁.closure_subset_iff.mpr h' hi.2.2⟩
        · exact Or.inr ⟨h, h', h₂.closure_subset_iff.mpr h' hi.2.2⟩
  · refine eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨⟨he₁, h₁'⟩, ⟨-, h₂'⟩⟩ := he
    obtain ⟨y, hy⟩ := (Γ.edge_props he₁).2.2.2
    exact hn e he₁ y hy (h₁' hy) (h₂' hy)

/-- An edge of `Γ₁` lies in a set of `Σ̂₁` just when the edge of `Γ` it comes from lies in the
matching
set of `Σ`. -/
theorem edge_subset_iff (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) {Q : Set T} {X : Set S} (hQ : ∀ p : P₁, ι p ∈ Q ↔ p.1 ∈ X)
    {e : Set T} (he : e ∈ Γ₁.E) : e ⊆ Q ↔ ∃ f, (f ∈ Γ.E ∧ f ⊆ X) ∧ e = capUp ι f := by
  constructor
  · intro heQ
    obtain ⟨f, hf, hP, rfl⟩ := exists_edge_capUp h hΓ hN he
    refine ⟨f, ⟨hf, fun x hx => ?_⟩, rfl⟩
    exact (hQ ⟨x, hP hx⟩).mp (heQ (val_mem_capUp (hP hx) hx))
  · rintro ⟨f, ⟨-, hf⟩, rfl⟩ _ ⟨p, hp, rfl⟩
    exact (hQ p).mpr (hf hp)

omit [T2Space S] [T2Space T] in
theorem vertex_iff (hΓ : IsCappedDrawing ι Γ Γ₁) {Q : Set T} {X : Set S}
    (hQ : ∀ p : P₁, ι p ∈ Q ↔ p.1 ∈ X) : Γ₁.V ∩ Q = capUp ι (Γ.V ∩ X) := by
  rw [hΓ.2]
  ext y
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hq⟩
    exact ⟨p, ⟨hp, (hQ p).mp hq⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hx⟩, rfl⟩
    exact ⟨⟨p, hp, rfl⟩, (hQ p).mpr hx⟩

/-- Membership in the induced tangle. -/
theorem mem_inducedAcross (h : IsCappedSplit C P₁ P₂ ι D) (hΓ : IsCappedDrawing ι Γ Γ₁)
    (hN : ∀ k, Γ.IsNormal (C k)) {Δ : Set S} (hΔ : IsClosed Δ) (hn : frontier Δ ∩ Γ.U ⊆ Γ.V)
    (hord : (frontier Δ ∩ Γ.V).ncard < θ) {Q₁ Q₂ : Set T} (h₁ : ∀ p : P₁, ι p ∈ Q₁ ↔ p.1 ∈ Δ)
    (h₂ : ∀ p : P₁, ι p ∈ Q₂ ↔ p.1 ∈ closure (univ \ Δ))
    (hq : ((PaintingOrDrawing.drawing Γ₁).inter Q₁, (PaintingOrDrawing.drawing Γ₁).inter Q₂) ∈ 𝒯) :
    ((PaintingOrDrawing.drawing Γ).inter Δ, (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈
      inducedAcross ι Γ Γ₁ θ 𝒯 := by
  refine ⟨isSeparation_inter (Γ := PaintingOrDrawing.drawing Γ) hΔ hn, ?_, _, hq, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (ncard_le_ncard (fun _ hx => inter_outside_subset hx)
      (Γ.finite_V.subset inter_subset_right)) hord
  · exact vertex_iff hΓ h₁
  · exact vertex_iff hΓ h₂
  · intro e he
    exact (and_iff_right he).trans (edge_subset_iff h hΓ hN h₁ he)
  · intro e he
    exact (and_iff_right he).trans (edge_subset_iff h hΓ hN h₂ he)

omit [T2Space T] in
/-- A separation whose small sides, taken from `𝒯`, cover one of its sides is in `𝒯`. This is the
use
of [5, Theorem (6.2)] in the proof of (5.3). -/
theorem mem_of_cover (hT : IsTangle Γ₁.toHypergraph θ 𝒯) {Q₁ Q₂ : Set T} (h₁ : IsClosed Q₁)
    (h₂ : IsClosed Q₂) (hV : Γ₁.V ⊆ Q₁ ∪ Q₂) (hE : ∀ e ∈ Γ₁.E, e ⊆ Q₁ ∪ Q₂)
    (hn : ∀ e ∈ Γ₁.E, ∀ x ∈ e, x ∈ Q₁ → x ∈ Q₂ → False)
    (hord : (Γ₁.V ∩ (Q₁ ∩ Q₂)).ncard < θ)
    (L : List (Hypergraph T (Set T) × Hypergraph T (Set T))) (hL : ∀ p ∈ L, p ∈ 𝒯)
    (hLW : ∀ p ∈ L, (p.1 ∩ p.2).vertexSet ⊆ Γ₁.V ∩ (Q₁ ∩ Q₂))
    (hcV : ∀ v ∈ Γ₁.V ∩ Q₁, ∃ p ∈ L, v ∈ p.1.vertexSet)
    (hcE : ∀ e ∈ Γ₁.E, e ⊆ Q₁ → ∃ p ∈ L, e ∈ p.1.edgeSet) :
    ((PaintingOrDrawing.drawing Γ₁).inter Q₁, (PaintingOrDrawing.drawing Γ₁).inter Q₂) ∈ 𝒯 := by
  have hsep := isSeparation_cover (Γ := PaintingOrDrawing.drawing Γ₁) h₁ h₂ hV hE hn
  have hinter : ((PaintingOrDrawing.drawing Γ₁).inter Q₂ ∩ (PaintingOrDrawing.drawing Γ₁).inter
    Q₁).vertexSet =
      Γ₁.V ∩ (Q₁ ∩ Q₂) := by
    ext x
    constructor
    · rintro ⟨⟨hx, h2⟩, -, h1⟩
      exact ⟨hx, h1, h2⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨⟨hx, h2⟩, hx, h1⟩
  have hinter' : ((PaintingOrDrawing.drawing Γ₁).inter Q₁ ∩ (PaintingOrDrawing.drawing Γ₁).inter
    Q₂).vertexSet =
      Γ₁.V ∩ (Q₁ ∩ Q₂) := by
    ext x
    constructor
    · rintro ⟨⟨hx, h1⟩, -, h2⟩
      exact ⟨hx, h1, h2⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨⟨hx, h1⟩, hx, h2⟩
  have hord' : separationOrder ((PaintingOrDrawing.drawing Γ₁).inter Q₁)
      ((PaintingOrDrawing.drawing Γ₁).inter Q₂) < θ := by
    unfold separationOrder
    rwa [hinter']
  rcases hT.axiom1 hsep hord' with h | h
  · exact h
  · exfalso
    exact theorem_6_2_proof (IsTangle.isPretangle hT) h L hL
      (fun p hp => (hLW p hp).trans_eq hinter.symm) hcV (fun e he => hcE e he.1 he.2)

/-- The first side `(A₀, B₀)` of the proof of (5.3): a set of few vertices. -/
theorem mem_vertices (hT : IsTangle Γ₁.toHypergraph θ 𝒯) {Q : Set T} (hQ : Q ⊆ Γ₁.V)
    (hc : Q.ncard < θ) :
    ((PaintingOrDrawing.drawing Γ₁).inter Q, (PaintingOrDrawing.drawing Γ₁).inter univ) ∈ 𝒯 := by
  have hfin : Q.Finite := Γ₁.finite_V.subset hQ
  have hsep := isSeparation_cover (Γ := PaintingOrDrawing.drawing Γ₁) hfin.isClosed isClosed_univ
    (fun _ _ => .inr trivial) (fun _ _ _ _ => .inr trivial)
    (fun e he x hx hQx _ => Set.disjoint_left.mp ((PaintingOrDrawing.drawing Γ₁).edge_props he).2.1
      hx (hQ hQx))
  have hord : separationOrder ((PaintingOrDrawing.drawing Γ₁).inter Q)
      ((PaintingOrDrawing.drawing Γ₁).inter univ) < θ := by
    refine lt_of_le_of_lt (ncard_le_ncard ?_ hfin) hc
    rintro x ⟨⟨-, hx⟩, -⟩
    exact hx
  rcases hT.axiom1 hsep hord with h | h
  · exact h
  · exfalso
    apply hT.axiom3 h
    change Γ₁.V ∩ univ = Γ₁.toHypergraph.vertexSet
    rw [inter_univ]
    rfl

/-- A closed disc whose boundary misses an open cap, and which is small for the tangle, misses it.
-/
theorem off_cap {E : Fin n → Set T} (H : CapSetup E Γ₁ θ 𝒯) (hS : IsClosedSurface T)
    {Δ₁ : Set T} (hΔ₁ : IsClosedDisc Δ₁)
    (hmem : ((PaintingOrDrawing.drawing Γ₁).inter Δ₁, (PaintingOrDrawing.drawing Γ₁).interOutside
      Δ₁) ∈ 𝒯)
    (hsmall : (frontier Δ₁ ∩ Γ₁.V).ncard < θ) (k : Fin n)
    (hdj : Disjoint (discInt (E k)) (discBd Δ₁)) : Disjoint Δ₁ (discInt (E k)) := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  rcases hΔ₁.side hman (H.disc k).isPreconnected_discInt hdj with h | h
  · exfalso
    have hEk : E k ⊆ Δ₁ := (H.disc k).subset_closure_discInt.trans
      (closure_minimal (h.trans (discInt_subset _)) hΔ₁.isClosed)
    obtain ⟨X, hXK, hXc⟩ := exists_subset_card_eq (s := discBd (E k) ∩ Γ₁.V) (H.many k)
    have hf := H.free k X hXK hXc.le
    have := card_le_of_free hf hmem (fun x hx => hEk (GraphMinor.Surface.discBd_subset _
      (hXK hx).1))
      (fun x hx => (hXK hx).2)
    omega
  · exact h.symm

end GraphMinor.GM12
