/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.PaintingFacts

/-!
# Every 2-cell painting or drawing has a radial drawing

Graph Minors XI, Section 3 (page 75): "It is not difficult to show that every 2-cell painting or
drawing
$\Gamma$ has a radial drawing $\Gamma'$". This is `exists_radialDrawing`.

Choose one point in each region. These points and the vertices of `Γ`, with no edges, satisfy
conditions
(i)–(iv). A drawing that satisfies (i)–(iv) has a bounded number of edges (`ncard_spokes_le`): in
the
rotation at a vertex of `Γ` no two edges of `Γ'` are next to each other (`corner_has_edge`), so we
can
send each edge of `Γ'` to the half-edge of `Γ` after it. So a drawing with the most edges exists.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

section Bound

variable [T2Space S] {Γ Γ' : Drawing S}

/-- **A drawing that satisfies (i)–(iv) has a bounded number of edges.** -/
theorem ncard_spokes_le (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ') (hS : IsClosedSurface S) :
    Γ'.E.ncard ≤ Γ.V.ncard + 2 * Γ.E.ncard := by
  classical
  by_cases hemp : Γ'.E = ∅
  · simp [hemp]
  obtain ⟨s₀, hs₀⟩ := nonempty_iff_ne_empty.mpr hemp
  obtain ⟨y₀, -⟩ := hs₀.1
  have hne : Nonempty S := ⟨y₀⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  let H := radialUnion hrad
  let Half := Σ y : Γ.V, halfEdges H γ y.1
  have hspoke : ∀ s : Γ'.E, ∃ p : Half, p.2.1.1 = s.1 := fun s => by
    obtain ⟨x, φ, h, -⟩ := spoke_half_unique hrad hS s.2 hγ
    exact ⟨⟨x, φ⟩, h⟩
  choose p hp using hspoke
  have hpinj : Function.Injective p := fun s t h => Subtype.ext (by rw [← hp, ← hp, h])
  have hsec : ∀ y : Γ.V, 2 ≤ Nat.card (halfEdges H γ y.1) →
      ∃ next ρ P W Q τ, IsSectors H γ y.1 next ρ P W Q τ := fun y h2 =>
    exists_sectors hS _ hγ
      (by rw [show H.V = Γ'.V from radialUnion_V hrad]; exact radial_V hrad y.2) h2
  let succ : ∀ y : Γ.V, halfEdges H γ y.1 → halfEdges H γ y.1 := fun y =>
    if h : 2 ≤ Nat.card (halfEdges H γ y.1) then (hsec y h).choose else id
  have hsucc : ∀ y (h : 2 ≤ Nat.card (halfEdges H γ y.1)),
      ∃ ρ P W Q τ, IsSectors H γ y.1 (succ y) ρ P W Q τ := fun y h => by
    simp only [succ, h, dite_true]
    exact (hsec y h).choose_spec
  let Φ : Half → S ⊕ (Set S × Bool) := fun q =>
    if 2 ≤ Nat.card (halfEdges H γ q.1.1) then Sum.inr (succ q.1 q.2).1 else Sum.inl q.1.1
  have hinj : Function.Injective Φ := by
    rintro ⟨y, a⟩ ⟨z, b⟩ hst
    by_cases hs : 2 ≤ Nat.card (halfEdges H γ y.1) <;> by_cases ht : 2 ≤ Nat.card
      (halfEdges H γ z.1)
    · simp only [Φ, hs, ht, ite_true, Sum.inr.injEq] at hst
      have hvx : y = z := by
        have h₁ := (succ y a).2.2
        have h₂ := (succ z b).2.2
        rw [hst] at h₁
        exact Subtype.ext (h₁.symm.trans h₂)
      subst hvx
      obtain ⟨ρ, P, W, Q, τ, hc⟩ := hsucc y hs
      have := hc.corners.inj (Subtype.ext hst)
      rw [this]
    · have h₁ : Φ ⟨y, a⟩ = Sum.inr (succ y a).1 := ite_eq_left_iff.mpr fun h => absurd hs h
      have h₂ : Φ ⟨z, b⟩ = Sum.inl z.1 := ite_eq_right_iff.mpr fun h => absurd h ht
      rw [h₁, h₂] at hst
      cases hst
    · have h₁ : Φ ⟨y, a⟩ = Sum.inl y.1 := ite_eq_right_iff.mpr fun h => absurd h hs
      have h₂ : Φ ⟨z, b⟩ = Sum.inr (succ z b).1 := ite_eq_left_iff.mpr fun h => absurd ht h
      rw [h₁, h₂] at hst
      cases hst
    · simp only [Φ, hs, ht, ite_false, Sum.inl.injEq] at hst
      have hvx : y = z := Subtype.ext hst
      subst hvx
      have hfin : Finite (halfEdges H γ y.1) := finite_halfEdges H γ y.1
      have : Subsingleton (halfEdges H γ y.1) := by
        rw [← Finite.card_le_one_iff_subsingleton]
        omega
      rw [Subsingleton.elim a b]
  let T : Set (S ⊕ (Set S × Bool)) := Sum.inl '' Γ.V ∪ Sum.inr '' (Γ.E ×ˢ univ)
  have hmaps : ∀ s, Φ (p s) ∈ T := by
    intro s
    by_cases h : 2 ≤ Nat.card (halfEdges H γ (p s).1.1)
    · simp only [Φ, h, ite_true]
      refine Or.inr ⟨(succ (p s).1 (p s).2).1, ⟨?_, mem_univ _⟩, rfl⟩
      obtain ⟨ρ, P, W, Q, τ, hc⟩ := hsucc _ h
      refine (edge_cases hrad (succ (p s).1 (p s).2)).resolve_right fun h' => ?_
      exact corner_has_edge hrad hS hγ (p s).1.2 hc (p s).2 (by rw [hp]; exact s.2) h'
    · simp only [Φ, h, ite_false]
      exact Or.inl ⟨_, (p s).1.2, rfl⟩
  have hVf : Γ.V.Finite := Γ.finite_V
  have hEf : Γ.E.Finite := Γ.finite_edges
  have hEf' : Γ'.E.Finite := Γ'.finite_edges
  have hTf : T.Finite := (hVf.image _).union ((hEf.prod finite_univ).image _)
  have hle : Γ'.E.ncard ≤ T.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have := hTf.to_subtype
    exact Nat.card_le_card_of_injective (fun s => (⟨Φ (p s), hmaps s⟩ : T))
      fun s t h => hpinj (hinj (congrArg Subtype.val h))
  refine hle.trans ((ncard_union_le _ _).trans ?_)
  have h₁ : (Sum.inl '' Γ.V : Set (S ⊕ (Set S × Bool))).ncard ≤ Γ.V.ncard := ncard_image_le hVf
  have h₂ : (Sum.inr '' (Γ.E ×ˢ univ) : Set (S ⊕ (Set S × Bool))).ncard ≤ (Γ.E ×ˢ
    (univ : Set Bool)).ncard :=
    ncard_image_le (hEf.prod finite_univ)
  have h₃ : (Γ.E ×ˢ (univ : Set Bool)).ncard = Γ.E.ncard * 2 := by
    rw [ncard_prod]
    simp
  omega

/-- A 2-cell drawing has only boundedly many edges in a drawing that satisfies (i)–(iv). -/
theorem exists_spoke_bound_drawing (hT : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    (hS : IsClosedSurface S) :
    ∃ N : ℕ, ∀ Γ' : Drawing S, (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing Γ' →
      Γ'.E.ncard ≤ N :=
  ⟨Γ.V.ncard + 2 * Γ.E.ncard, fun _ h => ncard_spokes_le ⟨hT, h⟩ hS⟩

end Bound

section BoundPainting

variable [T2Space S] {Γ : Painting S}

/-- The cells of a painting, and the bound for paintings. Each drawing that satisfies (i)–(iv) lies
in a drawing that satisfies them for the drawing `D` of the boundaries of the cells, by adding the
stars of the cells, and `D` does not depend on the drawing. -/
theorem exists_spoke_bound_painting (hT : (PaintingOrDrawing.painting Γ).IsTwoCell)
    (hS : IsClosedSurface S) :
    Γ.R.Finite ∧ ∃ N : ℕ, ∀ Γ' : Drawing S, (PaintingOrDrawing.painting Γ).IsPreRadialDrawing Γ' →
      Γ'.E.ncard ≤ N := by
  classical
  obtain ⟨hconn, hP⟩ := hT
  have hP' : ∀ r ∈ Γ.R, IsOpenDisc r := hP
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hne : Nonempty S := hconn.toNonempty
  by_cases hfree : ∃ e ∈ Γ.E, closure e ∩ Γ.V = ∅
  · obtain ⟨e, he, hf⟩ := hfree
    obtain ⟨hV, hE⟩ := free_cell hS hP' he hf
    refine ⟨?_, 0, fun Γ' hpre => ?_⟩
    · have hU : IsClosed Γ.U := Cell.isClosed_U Γ fun r hr => (hP' r hr).1
      have hd := Cell.isClosedDisc_closure he
      obtain ⟨a, ha⟩ : (discBd (closure e)).Nonempty :=
        hd.isOArc_discBd.elim fun f => ⟨(f (Classical.arbitrary _)).1, (f _).2⟩
      have hcl : closure e ⊆ Γ.U := closure_minimal (fun x hx => (he.2.1 hx).1) hU
      have haU : a ∈ Γ.U := hcl (discBd_subset _ ha)
      have hsub : Γ.V ⊆ {a} := by rw [hV]; exact empty_subset _
      obtain ⟨D, hDU, hDV⟩ := exists_boundary_drawing hS hU (finite_singleton a) hsub fun f hf => by
        rw [hE] at hf
        rw [mem_singleton_iff.mp hf]
        exact ⟨a, rfl, ha⟩
      have hbd : ∀ f ∈ Γ.E, ({a} : Set S) ∩ closure f ⊆ discBd (closure f) := by
        intro f hf x hx
        rw [hE] at hf
        rw [mem_singleton_iff.mp hf, mem_singleton_iff.mp hx.1]
        exact ha
      have hDR := boundary_R hS hP' hsub (singleton_subset_iff.mpr haU) hbd hDU
      exact (finite_R hS D).subset (hDR ▸ subset_union_left)
    · have : Γ'.E = ∅ := by
        refine eq_empty_of_forall_notMem fun s hs => ?_
        obtain ⟨v, hv, -⟩ := hpre.2.2.2.2.1 s hs
        have hv' : v ∈ Γ.V := hv
        rw [hV] at hv'
        exact hv'
      simp [this]
  have hv : ∀ e ∈ Γ.E, (closure e ∩ Γ.V).Nonempty := fun e he => by
    by_contra h
    exact hfree ⟨e, he, not_nonempty_iff_eq_empty.mp h⟩
  have hU : IsClosed Γ.U := Cell.isClosed_U Γ fun r hr => (hP' r hr).1
  obtain ⟨c, K, hst⟩ := exists_cellStars (Γ := Γ)
  have hbd : ∀ e ∈ Γ.E, Γ.V ∩ closure e ⊆ discBd (closure e) := fun e he x hx =>
    Cell.closure_inter_V_subset hS he ⟨hx.2, hx.1⟩
  obtain ⟨D, hDU, hDV⟩ := exists_boundary_drawing hS hU Γ.finite_V Subset.rfl fun e he => by
    obtain ⟨x, hx, hxV⟩ := hv e he
    exact ⟨x, hxV, hbd e he ⟨hxV, hx⟩⟩
  have hDR : D.R = Γ.R ∪ cellInt '' Γ.E := boundary_R hS hP' Subset.rfl Γ.V_subset_U hbd hDU
  have hRf : D.R.Finite := finite_R hS D
  refine ⟨hRf.subset (hDR ▸ subset_union_left), ?_⟩
  obtain ⟨N, hN⟩ := exists_spoke_bound_drawing (boundary_twoCell hS hP' hDR) hS
  refine ⟨N, fun Γ' hpre => ?_⟩
  have hrad : PreRad (PaintingOrDrawing.painting Γ) Γ' := ⟨⟨hconn, hP⟩, hpre⟩
  obtain ⟨G, hG⟩ := exists_star_drawing hrad hst hS
  have hb := hN G (star_preRadial hrad hst hS hG hDU hDV hv hDR)
  have hsub : Γ'.E ⊆ G.E := fun s hs => hG.E ▸ Or.inl hs
  exact (ncard_le_ncard hsub G.finite_edges).trans hb

end BoundPainting

section Existence

variable [T2Space S] {Γ : PaintingOrDrawing S}

omit [T2Space S] in
theorem not_mem_U_of_region {r : Set S} (hr : r ∈ Γ.R) {x : S} (hx : x ∈ r) : x ∉ Γ.U := by
  cases Γ with
  | painting Γ =>
    obtain ⟨y, -, rfl⟩ := hr
    exact (connectedComponentIn_subset _ _ hx).2
  | drawing Γ =>
    obtain ⟨y, -, rfl⟩ := hr
    exact (connectedComponentIn_subset _ _ hx).2

omit [T2Space S] in
theorem region_eq_of_common {r₁ r₂ : Set S} (h₁ : r₁ ∈ Γ.R) (h₂ : r₂ ∈ Γ.R) {x : S} (hx₁ : x ∈ r₁)
    (hx₂ : x ∈ r₂) : r₁ = r₂ := by
  have key : ∀ {F : Set S} {r₁ r₂ : Set S}, r₁ ∈ componentsIn F → r₂ ∈ componentsIn F → x ∈ r₁ →
      x ∈ r₂ → r₁ = r₂ := by
    rintro F _ _ ⟨a, -, rfl⟩ ⟨b, -, rfl⟩ ha hb
    rw [connectedComponentIn_eq ha, connectedComponentIn_eq hb]
  cases Γ with
  | painting Γ => exact key h₁ h₂ hx₁ hx₂
  | drawing Γ => exact key h₁ h₂ hx₁ hx₂

omit [T2Space S] in
theorem V_subset_U' : Γ.V ⊆ Γ.U := by
  cases Γ with
  | painting Γ => exact Γ.V_subset_U
  | drawing Γ => exact Γ.V_subset_U

omit [T2Space S] in
theorem finite_V' : Γ.V.Finite := by
  cases Γ with
  | painting Γ => exact Γ.finite_V
  | drawing Γ => exact Γ.finite_V

theorem pointsDrawing_E {A : Set S} (hA : A.Finite) : (pointsDrawing hA).E = ∅ := by
  refine eq_empty_of_forall_notMem ?_
  rintro C ⟨⟨x, hx⟩, hsub, -⟩
  simpa [pointsDrawing] using hsub hx

/-- **There is a drawing that satisfies (i)–(iv).** Take the vertices and one point in each region,
with no edges. -/
theorem exists_preRadial [Nonempty S] (hR : Γ.R.Finite) (hne : ∀ r ∈ Γ.R, r.Nonempty) :
    ∃ Γ' : Drawing S, Γ.IsPreRadialDrawing Γ' := by
  classical
  choose! hub hhub using hne
  have hA : (Γ.V ∪ hub '' Γ.R).Finite := finite_V'.union (hR.image _)
  have hV : (pointsDrawing hA).V = Γ.V ∪ hub '' Γ.R := rfl
  have hU : (pointsDrawing hA).U = Γ.V ∪ hub '' Γ.R := rfl
  have hE := pointsDrawing_E hA
  refine ⟨pointsDrawing hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    ext x
    constructor
    · rintro ⟨hxU, hx | ⟨r, hr, rfl⟩⟩
      · exact hx
      · exact absurd hxU (not_mem_U_of_region hr (hhub r hr))
    · exact fun hx => ⟨V_subset_U' hx, Or.inl hx⟩
  · rw [hV]
    exact subset_union_left
  · intro r hr
    refine ⟨hub r, ⟨hhub r hr, Or.inr ⟨r, hr, rfl⟩⟩, ?_⟩
    rintro w ⟨hwr, hw | ⟨r', hr', rfl⟩⟩
    · exact absurd (V_subset_U' hw) (not_mem_U_of_region hr hwr)
    · rw [region_eq_of_common hr hr' hwr (hhub r' hr')]
  · rintro w ⟨hw | ⟨r, hr, rfl⟩, hn⟩
    · exact absurd hw hn
    · exact ⟨r, hr, hhub r hr⟩
  · intro e he
    rw [hE] at he
    exact absurd he (notMem_empty _)
  · intro e he
    rw [hE] at he
    exact absurd he (notMem_empty _)

/-- **A drawing with the most edges among those that satisfy (i)–(iv) is a radial drawing.** -/
theorem exists_radial_of_bound (hT : Γ.IsTwoCell) (hR : Γ.R.Finite) (hne : ∀ r ∈ Γ.R, r.Nonempty)
    {N : ℕ} (hN : ∀ Γ' : Drawing S, Γ.IsPreRadialDrawing Γ' → Γ'.E.ncard ≤ N) :
    ∃ Γ' : Drawing S, Γ.IsRadialDrawing Γ' := by
  classical
  have hS' : Nonempty S := hT.1.toNonempty
  let A : Set ℕ := {n | ∃ Γ' : Drawing S, Γ.IsPreRadialDrawing Γ' ∧ Γ'.E.ncard = n}
  have hAne : A.Nonempty := by
    obtain ⟨Γ', h⟩ := exists_preRadial hR hne
    exact ⟨_, Γ', h, rfl⟩
  have hbdd : BddAbove A := ⟨N, by rintro _ ⟨Γ', h, rfl⟩; exact hN Γ' h⟩
  obtain ⟨Γ', hpre, hc⟩ := Nat.sSup_mem hAne hbdd
  refine ⟨Γ', hT, hpre, ?_⟩
  rintro Γ'' hpre' ⟨hV, hE⟩
  refine ⟨?_, ?_⟩
  · intro w hw
    by_cases hwV : w ∈ Γ.V
    · exact hpre.2.1 hwV
    obtain ⟨r, hr, hwr⟩ := hpre'.2.2.2.1 w ⟨hw, hwV⟩
    obtain ⟨w', ⟨hw'r, hw'⟩, -⟩ := hpre.2.2.1 r hr
    rw [(hpre'.2.2.1 r hr).unique ⟨hwr, hw⟩ ⟨hw'r, hV hw'⟩]
    exact hw'
  · have hle : Γ''.E.ncard ≤ Γ'.E.ncard := by
      rw [hc]
      exact le_csSup hbdd ⟨Γ'', hpre', rfl⟩
    exact (eq_of_subset_of_ncard_le hE hle Γ''.finite_edges).ge

omit [T2Space S] in
theorem region_nonempty' {r : Set S} (hr : r ∈ Γ.R) : r.Nonempty := by
  cases Γ with
  | painting Γ =>
    obtain ⟨y, hy, rfl⟩ := hr
    exact ⟨y, mem_connectedComponentIn hy⟩
  | drawing Γ =>
    obtain ⟨y, hy, rfl⟩ := hr
    exact ⟨y, mem_connectedComponentIn hy⟩

/-- **Every 2-cell painting or drawing has a radial drawing.** Graph Minors XI, Section 3 (page 75):
"every 2-cell painting or drawing $\Gamma$ has a radial drawing $\Gamma'$". -/
theorem exists_radialDrawing (hS : IsClosedSurface S) (hT : Γ.IsTwoCell) :
    ∃ Γ' : Drawing S, Γ.IsRadialDrawing Γ' := by
  cases Γ with
  | painting Γ =>
    obtain ⟨hR, N, hN⟩ := exists_spoke_bound_painting hT hS
    exact exists_radial_of_bound hT hR (fun _ h => region_nonempty' h) hN
  | drawing Γ =>
    obtain ⟨N, hN⟩ := exists_spoke_bound_drawing hT hS
    have : ConnectedSpace S := hT.1
    exact exists_radial_of_bound hT (finite_R hS Γ)
      (fun _ h => region_nonempty' h) hN

end Existence

end GraphMinor.GM11
