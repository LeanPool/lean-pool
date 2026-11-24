/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.FlatCover

/-!
# Cutting the edges of a drawing near some vertices

The proof of (6.4) of Graph Minors XI (pages 90–91) passes from `Γ` to `Γ \ V(A ∩ B)`. That set is
not closed, so
we remove instead a small piece of each edge near the deleted vertices. `exists_cut_edges` gives a
closed nice set `Q`
in `U(Γ)` that avoids a set `A` of vertices, and whose complement in `U(Γ)` lies in given
neighbourhoods of `A`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}

omit [T2Space S] in
theorem EdgePar.end_mem {γ : Set S → I → S} (hγ : EdgePar Γ γ) {e : Set S} (he : e ∈ Γ.E)
  (b : Bool) :
    γ e (endOf b) ∈ Γ.V := by
  cases b
  · exact hγ.zero e he
  · exact hγ.one e he

/-- The part of a half-edge from the parameter `t` to the midpoint of the edge is a line. -/
theorem isLine_spoke_end {γ : Set S → I → S} (hγ : EdgePar Γ γ) {x : Set S × Bool}
  (hx : x.1 ∈ Γ.E) {τ : I}
    (hτ : τ < 1) : IsLineWithEnds (spoke γ x '' Icc τ 1) (spoke γ x τ) (spoke γ x 1) := by
  have hc := continuous_spoke hγ hx
  let p : ℝ → S := fun u => spoke γ x (Set.projIcc 0 1 zero_le_one u)
  have hp : ∀ u : I, p u.1 = spoke γ x u := fun u => by
    simp only [p]
    congr 1
    exact Set.projIcc_val zero_le_one u
  have hsub : ∀ u ∈ Icc τ.1 1, u ∈ Icc (0 : ℝ) 1 := fun u hu => ⟨τ.2.1.trans hu.1, hu.2⟩
  have hl := isLine_of_injOn (p := p) (a := τ.1) (b := 1) (hc.comp continuous_projIcc)
    (lt_of_le_of_ne τ.2.2 fun h => hτ.ne (Subtype.ext h)) (fun u hu v hv h => by
      have := spoke_injective hγ hx h
      have h' := congrArg Subtype.val this
      rwa [Set.projIcc_of_mem zero_le_one (hsub u hu), Set.projIcc_of_mem zero_le_one
        (hsub v hv)] at h')
  have h1 := hp 1
  rw [hp τ] at hl
  have h1' : p 1 = spoke γ x 1 := h1
  rw [h1'] at hl
  have hi : p '' Icc τ.1 1 = spoke γ x '' Icc τ 1 := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hsub u hu⟩, hu, (hp ⟨u, hsub u hu⟩).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.1, hu, hp u⟩
  rwa [hi] at hl

/-- Each parameter is on one of the two halves. -/
theorem exists_halfPar_eq (w : I) : ∃ b u, halfPar b u = w := by
  rcases le_total w.1 (1 / 2) with h | h
  · refine ⟨false, ⟨2 * w.1, by have := w.2.1; positivity, by linarith⟩, Subtype.ext ?_⟩
    rw [halfPar_coe]
    simp
  · refine ⟨true, ⟨2 * (1 - w.1), by have := w.2.2; linarith, by linarith⟩, Subtype.ext ?_⟩
    rw [halfPar_coe]
    simp

/-- Cut the edges of `Γ` near a set `A` of vertices. -/
theorem exists_cut_edges {γ : Set S → I → S}
  (hγ : EdgePar Γ γ) {A : Set S} (hA : A ⊆ Γ.V)
    {D : S → Set S} (hDo : ∀ s ∈ A, IsOpen (D s)) (hD : ∀ s ∈ A, s ∈ D s) :
    ∃ Q : Set S, IsClosed Q ∧ IsNice Q ∧ Q ⊆ Γ.U \ A ∧ Γ.U \ Q ⊆ ⋃ s ∈ A, D s := by
  classical
  -- The parameter at which the half-edge `x` is cut.
  have hex : ∀ x : Set S × Bool, x.1 ∈ Γ.E → ∃ t : I, t < 1 ∧ (t = 0 ↔ spoke γ x 0 ∉ A) ∧
      ∀ u, u < t → spoke γ x u ∈ ⋃ s ∈ A, D s := by
    intro x hx
    by_cases hs : spoke γ x 0 ∈ A
    · obtain ⟨u, hu, hu1, hle⟩ := exists_pos_le (continuous_spoke hγ hx) (hDo _ hs) (hD _ hs)
        (a := ⟨1 / 2, by norm_num, by norm_num⟩) (by exact Subtype.mk_lt_mk.mpr (by norm_num))
      refine ⟨u, lt_of_le_of_lt hu1 (Subtype.mk_lt_mk.mpr (by norm_num)),
        ⟨fun h => absurd h hu.ne', fun h => absurd hs h⟩,
        fun v hv => mem_iUnion₂.mpr ⟨_, hs, hle v hv.le⟩⟩
    · exact ⟨0, zero_lt_one, ⟨fun _ => hs, fun _ => rfl⟩, fun u hu => absurd hu (not_lt.mpr
        (unitInterval.nonneg u))⟩
  choose! t ht1 ht0 htD using hex
  let L : Set S × Bool → Set S := fun x => spoke γ x '' Icc (t x) 1
  let E₀ : Finset (Set S × Bool) := (Γ.finite_edges.toFinset ×ˢ Finset.univ)
  have hE₀ : ∀ x, x ∈ E₀ ↔ x.1 ∈ Γ.E := fun x => by
    simp only [E₀, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_univ, and_true]
    rfl
  have hmain : ∀ F : Finset (Set S × Bool), (∀ x ∈ F, x.1 ∈ Γ.E) → ∃ G : Drawing S,
      G.U = (Γ.V \ A) ∪ ⋃ x ∈ F, L x ∧
      G.V = (Γ.V \ A) ∪ ⋃ x ∈ F, {spoke γ x (t x), spoke γ x 1} := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      have h : (Γ.V \ A) ∩ Γ.V = Γ.V \ A := inter_eq_left.mpr sdiff_subset
      refine ⟨Γ.span (Γ.V \ A) ∅, ?_, ?_⟩
      · simp [Drawing.span_U, Drawing.spanU, Drawing.spanV]
      · simp [Drawing.span_V, Drawing.spanV]
    | insert x F hxF ih =>
      intro hall
      have hx := hall x (Finset.mem_insert_self _ _)
      obtain ⟨G, hU, hV⟩ := ih fun y hy => hall y (Finset.mem_insert_of_mem hy)
      have hline := isLine_spoke_end hγ hx (ht1 x hx)
      have hne : spoke γ x (t x) ≠ spoke γ x 1 := fun h => (ht1 x hx).ne (spoke_injective hγ hx h)
      have hmeet : G.U ∩ (lineDrawing hline hne).U ⊆ G.V ∩ (lineDrawing hline hne).V := by
        rintro z ⟨hzG, u, hu, rfl⟩
        have hvert : u = 0 → spoke γ x u ∈ G.V ∩ (lineDrawing hline hne).V := by
          rintro rfl
          have h0 : t x = 0 := le_antisymm hu.1 (unitInterval.nonneg _)
          refine ⟨?_, Or.inl (by rw [h0])⟩
          rw [hV]
          refine Or.inl ⟨?_, (ht0 x hx).mp h0⟩
          rw [spoke_zero]
          exact hγ.end_mem hx _
        rcases eq_or_lt_of_le (unitInterval.nonneg u) with h0 | h0
        · exact hvert (Subtype.ext h0.symm)
        have hue := spoke_mem_edge hγ hx h0
        rw [hU] at hzG
        rcases hzG with ⟨hzV, -⟩ | hz
        · exact absurd hzV (edge_notMem_V hx hue)
        obtain ⟨y, hy, u', hu', e⟩ := mem_iUnion₂.mp hz
        have hyE := hall y (Finset.mem_insert_of_mem hy)
        rcases eq_or_lt_of_le (unitInterval.nonneg u') with h0' | h0'
        · have : u' = 0 := Subtype.ext h0'.symm
          rw [this, spoke_zero] at e
          exact absurd (e ▸ hγ.end_mem hyE _) (edge_notMem_V hx hue)
        have hxy : x ≠ y := fun h => hxF (h ▸ hy)
        obtain ⟨rfl, rfl⟩ := spoke_eq_of_ne hγ hx hyE hxy h0 h0' e.symm
        refine ⟨?_, Or.inr rfl⟩
        rw [hV]
        exact Or.inr (mem_iUnion₂.mpr ⟨y, hy, Or.inr e.symm⟩)
      refine ⟨G.glue (lineDrawing hline hne) hmeet, ?_, ?_⟩
      · change G.U ∪ L x = _
        rw [hU, Finset.set_biUnion_insert, union_assoc, union_comm (⋃ y ∈ F, L y) (L x)]
      · change G.V ∪ {spoke γ x (t x), spoke γ x 1} = _
        rw [hV, Finset.set_biUnion_insert, union_assoc, union_comm (⋃ y ∈ F, {spoke γ y (t y),
          spoke γ y 1})]
  obtain ⟨G, hU, hV⟩ := hmain E₀ fun x hx => (hE₀ x).mp hx
  have hc := G.isClosed_U
  refine ⟨G.U, hc, ⟨G, isGammaNice_of_frontier (Drawing.IsSubdrawing.refl G) subset_rfl
    (hc.frontier_eq.subset.trans sdiff_subset)⟩, ?_, ?_⟩
  · rw [hU]
    rintro z (hz | hz)
    · exact ⟨Γ.V_subset_U hz.1, hz.2⟩
    obtain ⟨y, hy, u, hu, rfl⟩ := mem_iUnion₂.mp hz
    have hyE := (hE₀ y).mp hy
    rcases eq_or_lt_of_le (unitInterval.nonneg u) with h0 | h0
    · have h0' : u = 0 := Subtype.ext h0.symm
      subst h0'
      have ht : t y = 0 := le_antisymm hu.1 (unitInterval.nonneg _)
      refine ⟨Γ.V_subset_U ?_, (ht0 y hyE).mp ht⟩
      rw [spoke_zero]
      exact hγ.end_mem hyE _
    · have hue := spoke_mem_edge hγ hyE h0
      exact ⟨(hyE.2.1 hue).1, fun h => edge_notMem_V hyE hue (hA h)⟩
  · rintro z ⟨hzU, hzQ⟩
    by_cases hzV : z ∈ Γ.V
    · by_cases hzA : z ∈ A
      · exact mem_iUnion₂.mpr ⟨z, hzA, hD z hzA⟩
      · exact (hzQ (hU ▸ Or.inl ⟨hzV, hzA⟩)).elim
    obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hzU hzV
    obtain ⟨w, hw, rfl⟩ : z ∈ γ e '' Ioo 0 1 := (hγ.image e he).symm ▸ hze
    obtain ⟨b, u, hu⟩ := exists_halfPar_eq w
    let x : Set S × Bool := (e, b)
    by_cases hut : t x ≤ u
    · refine (hzQ (hU ▸ Or.inr (mem_iUnion₂.mpr ⟨x, (hE₀ x).mpr he, u, ⟨hut, u.2.2⟩, ?_⟩))).elim
      simp only [spoke, x, hu]
    · have := htD x he u (not_le.mp hut)
      simpa only [spoke, x, hu] using this

end GraphMinor.GM11
