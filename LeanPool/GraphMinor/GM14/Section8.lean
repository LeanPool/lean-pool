/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section5
public import LeanPool.GraphMinor.GM14.Section6c
public import LeanPool.GraphMinor.GM14.Section8a
public import LeanPool.GraphMinor.GM14.Section83Proof
public import LeanPool.GraphMinor.GM14.CylinderParts
public import LeanPool.GraphMinor.GM14.Form84
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Bridge
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM16.CircleListing
import LeanPool.GraphMinor.GM16.FiniteCircleCycle
import LeanPool.GraphMinor.GM16.CyclicOrderTransport
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith


/-!
# Graph Minors XIV, Section 8: Segregation in a Rural Neighbourhood

This file completes the formalization of Section 8 ("Segregation in a Rural Neighbourhood",
pages 39–42) of N. Robertson and P. D. Seymour, *Graph Minors. XIV. Extending an embedding*,
J. Combin. Theory Ser. B **65** (1995) 23–50, re-exporting `GraphMinor.GM14.Section8a` and proving:

- `restrictSpan` and `restrictCleared`: restriction of a `SpanEmbedding H G` to `H.span V' E'` and
  `clearedSubdrawing H Λ`.
- `exists_cyclicPerm_agrees_injOn`, `exists_natural_order_injOn`, `exists_pullbackPerm`, and
  `exists_natural_order_spanEmbedding_subBd`: construction of natural orders on `O`-arcs and
  pullback permutations `α⁻¹(F)`.
- `theorem_8_4` (Graph Minors XIV, (8.4), pages 41–42). Claim (1) is `exists_reduced` in
  `ClaimOneReduction.lean` and Claim (2) is `claim_2_of_8_4` in `ForestClaim.lean`. The drawing of
  `G_1` is `exists_reduced_drawing` in `PieceFacts.lean`, and the rest of the proof is `drawn_8_4`.
-/

@[expose] public section

namespace GraphMinor.GM14

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11
  GraphMinor.GM16

universe u v w

variable {S : Type w} [TopologicalSpace S] [T1Space S]

/-! ## 1. Restriction of `SpanEmbedding` and Construction of Natural / Pullback Orders -/

/-- Restriction of a `SpanEmbedding H G` to a spanned subdrawing `H.span V' E'`. -/
def restrictSpan {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (V' : Set S) (E' : Set (Set S)) :
    SpanEmbedding (H.span V' E') G where
  imageGraph :=
    (η.imageGraph.induce (η.vMap '' (H.span V' E').V)).restrict (η.eMap '' (H.span V' E').E)
  vMap := η.vMap
  eMap := η.eMap
  imageGraph_le := by
    have hV_sub : η.vMap '' (H.span V' E').V ⊆ V(η.imageGraph) := by
      rw [← η.bijOn_v.image_eq]
      exact image_mono (H.spanV_subset V' E')
    exact (Graph.restrict_le.trans (Graph.induce_le hV_sub)).trans η.imageGraph_le
  bijOn_v := by
    have hV_eq :
        V((η.imageGraph.induce (η.vMap '' (H.span V' E').V)).restrict
          (η.eMap '' (H.span V' E').E)) = η.vMap '' (H.span V' E').V := by
      simp
    rw [hV_eq]
    exact (η.bijOn_v.injOn.mono (H.spanV_subset V' E')).bijOn_image
  bijOn_e := by
    have hE_eq :
        E((η.imageGraph.induce (η.vMap '' (H.span V' E').V)).restrict
          (η.eMap '' (H.span V' E').E)) = η.eMap '' (H.span V' E').E := by
      apply Subset.antisymm
      · intro b hb
        rw [edge_mem_iff_exists_isLink] at hb
        obtain ⟨x, y, hb, _⟩ := hb
        exact hb
      · rintro b ⟨e, he, rfl⟩
        have he_span : e ∈ E' ∩ H.E := by rwa [← H.span_E V' E']
        have he_img : η.eMap e ∈ E(η.imageGraph) := η.bijOn_e.mapsTo he_span.2
        rw [edge_mem_iff_exists_isLink] at he_img ⊢
        obtain ⟨x, y, hlink⟩ := he_img
        have hx_V : x ∈ V(η.imageGraph) := η.imageGraph.left_mem_of_isLink hlink
        have hy_V : y ∈ V(η.imageGraph) := η.imageGraph.left_mem_of_isLink hlink.symm
        rw [← η.bijOn_v.image_eq] at hx_V hy_V
        obtain ⟨u, huH, rfl⟩ := hx_V
        obtain ⟨v, hvH, rfl⟩ := hy_V
        have hu_cl : u ∈ closure e := (η.inc_iff e he_span.2 u huH).mp ⟨η.vMap v, hlink⟩
        have hv_cl : v ∈ closure e := (η.inc_iff e he_span.2 v hvH).mp ⟨η.vMap u, hlink.symm⟩
        have hu_span : u ∈ (H.span V' E').V :=
          Or.inr (mem_iUnion₂.mpr ⟨e, he_span, hu_cl, huH⟩)
        have hv_span : v ∈ (H.span V' E').V :=
          Or.inr (mem_iUnion₂.mpr ⟨e, he_span, hv_cl, hvH⟩)
        exact ⟨η.vMap u, η.vMap v, ⟨e, he, rfl⟩, hlink,
          ⟨u, hu_span, rfl⟩, ⟨v, hv_span, rfl⟩⟩
    rw [hE_eq]
    have hE_sub : (H.span V' E').E ⊆ H.E := by
      rw [H.span_E V' E']
      exact inter_subset_right
    exact (η.bijOn_e.injOn.mono hE_sub).bijOn_image
  inc_iff e he v hv := by
    have he_span : e ∈ E' ∩ H.E := by rwa [← H.span_E V' E']
    have hv_H : v ∈ H.V := H.spanV_subset V' E' hv
    rw [← η.inc_iff e he_span.2 v hv_H]
    constructor
    · rintro ⟨w, _, hlink, _, _⟩
      exact ⟨w, hlink⟩
    · rintro ⟨w, hlink⟩
      have hw_V : w ∈ V(η.imageGraph) := η.imageGraph.left_mem_of_isLink hlink.symm
      rw [← η.bijOn_v.image_eq] at hw_V
      obtain ⟨u, huH, rfl⟩ := hw_V
      have hu_cl : u ∈ closure e := (η.inc_iff e he_span.2 u huH).mp ⟨η.vMap v, hlink.symm⟩
      have hu_span : u ∈ (H.span V' E').V :=
        Or.inr (mem_iUnion₂.mpr ⟨e, he_span, hu_cl, huH⟩)
      exact ⟨η.vMap u, ⟨e, he, rfl⟩, hlink, ⟨v, hv, rfl⟩, ⟨u, hu_span, rfl⟩⟩

/-- Restriction of a `SpanEmbedding H G` to `clearedSubdrawing H Λ = H.interSet (univ \ Λ)`. -/
def restrictCleared {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    SpanEmbedding (clearedSubdrawing H Λ) G :=
  restrictSpan η (H.V ∩ (univ \ Λ)) {e | e ∈ H.E ∧ e ⊆ univ \ Λ}

@[simp]
theorem restrictCleared_vMap {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).vMap = η.vMap := rfl

@[simp]
theorem restrictCleared_eMap {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).eMap = η.eMap := rfl

theorem restrictCleared_imageGraph_le {α : Type u} {β : Type v} {H : Drawing S} {G : Graph α β}
    (η : SpanEmbedding H G) (Λ : Set S) :
    (restrictCleared η Λ).imageGraph ≤ η.imageGraph := by
  have hV_sub : η.vMap '' (clearedSubdrawing H Λ).V ⊆ V(η.imageGraph) := by
    rw [← η.bijOn_v.image_eq]
    exact image_mono (H.spanV_subset _ _)
  exact Graph.restrict_le.trans (Graph.induce_le hV_sub)

omit [T1Space S] in
/-- Any finite subset `Y : Set α` injected into an `O`-arc `F` by `α_pt : α → S` has a cyclic
permutation `Ω : CyclicPerm α` with `Ω.bar = Y` agreeing with a given homeomorphism
`φ : Circle ≃ₜ F`. -/
theorem exists_cyclicPerm_agrees_injOn {α : Type u} {F : Set S} (φ : Circle ≃ₜ F)
    {Y : Set α} (hY : Y.Finite) {α_pt : α → S} (hinj : InjOn α_pt Y) (hYF : MapsTo α_pt Y F) :
    ∃ Ω : CyclicPerm α, Ω.bar = Y ∧ AgreesWithOArcHomeo α_pt Ω F φ := by
  classical
  rcases Y.eq_empty_or_nonempty with rfl | hNe
  · let Ω₀ : CyclicPerm α := ⟨∅, id, finite_empty, bijOn_empty id, fun _ hx => False.elim hx⟩
    refine ⟨Ω₀, rfl, fun _ hx => False.elim hx, ?_⟩
    intro x y z hCW
    exact False.elim (CyclicPerm.isClockwise3_iff.mp hCW).2.2.2.1
  · let _ : Fintype Y := hY.fintype
    have hCard : Fintype.card Y = Y.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    let e₀ : Fin Y.ncard ≃ Y := (finCongr hCard.symm).trans (Fintype.equivFin Y).symm
    let ν₀ : Fin Y.ncard → S := fun i => α_pt (e₀ i).val
    have hν₀ : Injective ν₀ := by
      intro i j hij
      exact e₀.injective (Subtype.ext (hinj (e₀ i).property (e₀ j).property hij))
    obtain ⟨perm, τ, hPerm, hτ, hBounds, hEq⟩ := exists_increasing_circle_angles φ ν₀ hν₀
      (fun i => hYF (e₀ i).property)
    let e : Fin Y.ncard ≃ Y := (Equiv.ofBijective perm hPerm).trans e₀
    let Ω := cyclicPermOnSet hY e
    have hNeCard : 0 < Y.ncard := (Set.ncard_pos hY).mpr hNe
    have hEq' : ∀ i, (φ (Circle.exp (τ i))).val = α_pt (e i).val := hEq
    have hTurn : ∀ i, τ i < τ ⟨0, hNeCard⟩ + 2 * Real.pi := by
      intro i
      have hi := hBounds i
      have hzero := hBounds ⟨0, hNeCard⟩
      linarith
    have hAgreeFin :=
      finCyclicPerm_agrees_of_angles φ hNeCard (fun i => α_pt (e i).val) τ hτ hTurn hEq'
    refine ⟨Ω, rfl, fun x hx => hYF hx, ?_⟩
    intro x y z hCW
    have hMem := CyclicPerm.isClockwise3_iff.mp hCW
    let i := e.symm ⟨x, hMem.2.2.2.1⟩
    let j := e.symm ⟨y, hMem.2.2.2.2.1⟩
    let k := e.symm ⟨z, hMem.2.2.2.2.2.1⟩
    have hi : (e i).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hMem.2.2.2.1⟩)
    have hj : (e j).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hMem.2.2.2.2.1⟩)
    have hk : (e k).val = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hMem.2.2.2.2.2.1⟩)
    have hCW' : (cyclicPermOnSet hY e).IsClockwise3 (e i).val (e j).val (e k).val := by
      rw [hi, hj, hk]
      exact hCW
    have hFin := (cyclicPermOnSet_clockwise3_iff hY e i j k).mp hCW'
    simpa only [hi, hj, hk] using hAgreeFin.2 i j k hFin

omit [T1Space S] in
/-- Any finite subset `Y : Set α` injected into an `O`-arc `F` by `α_pt : α → S` has a natural
order `Ω : CyclicPerm α` from `F` with `Ω.bar = Y`. -/
theorem exists_natural_order_injOn {α : Type u} {F : Set S} (hF : IsOArc F)
    {Y : Set α} (hY : Y.Finite) {α_pt : α → S} (hinj : InjOn α_pt Y) (hYF : MapsTo α_pt Y F) :
    ∃ Ω : CyclicPerm α, Ω.bar = Y ∧ IsNaturalOrderFrom α_pt Ω F := by
  obtain ⟨φ⟩ := hF
  obtain ⟨Ω, hbar, hAgree⟩ := exists_cyclicPerm_agrees_injOn φ hY hinj hYF
  exact ⟨Ω, hbar, ⟨φ⟩, φ, hAgree⟩

omit [T1Space S] in
/-- For any segregation `S_seg` with a surface arrangement `(α_disc, α_pt)` and any `O`-arc `F`,
there exists a pullback cyclic permutation `Ω = α⁻¹(F)` on `{v ∈ V(S_seg) | α_pt v ∈ F}`. -/
theorem exists_pullbackPerm {α : Type u} {β : Type v}
    {G : Graph α β} {S_seg : Set (Society α β)} (hseg : IsGraphSegregation G S_seg)
    {α_disc : Society α β → Set S} {α_pt : α → S} (harr : IsSurfaceArrangement S_seg α_disc α_pt)
    {F : Set S} (hF : IsOArc F) :
    ∃ Ω : CyclicPerm α, IsPullbackPerm S_seg α_pt F Ω := by
  have hsegV_fin : (segregationVertices S_seg).Finite :=
    hseg.finite.biUnion fun S₀ _ => S₀.Ω.finite_bar
  let Y : Set α := {v ∈ segregationVertices S_seg | α_pt v ∈ F}
  have hY_fin : Y.Finite := hsegV_fin.subset (fun _ hv => hv.1)
  have hinj : InjOn α_pt Y := harr.injOn_pts.mono (fun _ hv => hv.1)
  have hYF : MapsTo α_pt Y F := fun _ hv => hv.2
  obtain ⟨Ω, hbar, hNat⟩ := exists_natural_order_injOn hF hY_fin hinj hYF
  exact ⟨Ω, hbar, hNat⟩

omit [T1Space S] in
/-- Given a `SpanEmbedding clearedEmbedding` of a drawing `H_Λ` into `G_amb` and an `O`-arc `F`,
there is a
cyclic permutation `Ω` on `clearedEmbedding.vMap '' (H_Λ.V ∩ F)` and a right-inverse map `inv_v : α
→ S` on
`Ω.bar` such that `Ω` is a natural order from `F` under `inv_v`. -/
theorem exists_natural_order_spanEmbedding_subBd {α : Type u} {β : Type v}
    {H_Λ : Drawing S} {G_amb : Graph α β} (clearedEmbedding : SpanEmbedding H_Λ G_amb)
    {F : Set S} (hF : IsOArc F) :
    ∃ (Ω : CyclicPerm α) (inv_v : α → S),
      Ω.bar = clearedEmbedding.vMap '' (H_Λ.V ∩ F) ∧
      (∀ x ∈ Ω.bar, inv_v x ∈ H_Λ.V ∩ F ∧ clearedEmbedding.vMap (inv_v x) = x) ∧
      IsNaturalOrderFrom inv_v Ω F := by
  classical
  obtain ⟨φ_F⟩ := hF
  let p₀ : S := (φ_F 1).1
  have hp₀ : IsOArc F := ⟨φ_F⟩
  let V_bd : Set S := H_Λ.V ∩ F
  let Y : Set α := clearedEmbedding.vMap '' V_bd
  have hY_fin : Y.Finite := (H_Λ.finite_V.subset inter_subset_left).image clearedEmbedding.vMap
  let inv_v : α → S := fun x =>
    if hx : ∃ v ∈ V_bd, clearedEmbedding.vMap v = x then Classical.choose hx else p₀
  have hinv_prop : ∀ x ∈ Y, inv_v x ∈ V_bd ∧ clearedEmbedding.vMap (inv_v x) = x := by
    intro x hx
    have hx' : ∃ v ∈ V_bd, clearedEmbedding.vMap v = x := by
      rcases hx with ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    simp only [inv_v, hx', ↓reduceDIte]
    exact Classical.choose_spec hx'
  have hinj : InjOn inv_v Y := by
    intro x₁ hx₁ x₂ hx₂ heq
    rw [← (hinv_prop x₁ hx₁).2, ← (hinv_prop x₂ hx₂).2, heq]
  have hYF : MapsTo inv_v Y F := fun x hx => (hinv_prop x hx).1.2
  obtain ⟨Ω, hbar, hNat⟩ := exists_natural_order_injOn hp₀ hY_fin hinj hYF
  exact ⟨Ω, inv_v, hbar, fun x hx => hinv_prop x (hbar ▸ hx), hNat⟩

/-! ## 2. Proof of Claim (2) of (8.4) and (8.4) (pages 41–42) -/

private theorem nested_circuits_lie_in_outer_neighborhood
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {H : Drawing S}
    {C₂ : Drawing S}
    {E₁ : Set S}
    {E₂ : Set S}
    (hE₂ : IsClosedDisc E₂)
    {pi : ℕ}
    {N : Neighborhood α β}
    (η : SpanEmbedding H N.G)
    (Y : GraphDrawing N.G S)
    {ν : α → S}
    (hη : ∀ v ∈ H.V, ν (η.vMap v) = v)
    (hηe : ∀ e ∈ H.E, graphDrawingEdgeSet Y (η.eMap e) = e)
    (hman : ∀ (x : S), IsManifoldPoint x)
    (hVU : ∀ {R : Drawing S} {v : S}, v ∈ R.V → v ∈ R.U)
    (hRG : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → R.toGraph ≤ H.toGraph)
    (Nin : Neighborhood α β)
    (Yin : GraphDrawing Nin.G S)
    (hei : ∀ e ∈ E(Nin.G), graphDrawingEdgeSet Yin e = graphDrawingEdgeSet Y e)
    (hKin : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → R.U ⊆ E₁ → (fun R : Drawing S =>
      η.gmap.sub R.toGraph) R ≤ Nin.G)
    (Nout₂ : Neighborhood α β)
    (Nin₂ : Neighborhood α β)
    (hOutle₂ : Nout₂.G ≤ Nin.G)
    (hOutV₂ : V(Nout₂.G) = {v | v ∈ V(Nin.G) ∧ ν v ∉ discInt E₂})
    (hTO₂ : E((fun R : Drawing S => η.gmap.sub R.toGraph) C₂) ⊆ E(Nout₂.G))
    (hEun₂ : E(Nin₂.G) ∪ E(Nout₂.G) = E(Nin.G))
    (hIc₂ : ∀ e ∈ E(Nin₂.G), closure (graphDrawingEdgeSet Yin e) ⊆ E₂)
    (R : Fin (pi + 3 + 2) → Drawing S)
    (A' : Fin (pi + 3 + 2) → Set S)
    (hRA : ∀ (i : Fin (pi + 3 + 2)), (R i).IsCircuit ∧ (R i).IsSubdrawing H ∧ IsClosedDisc (A' i)
      ∧ discBd (A' i) = (R i).U ∧ E₂ ⊆ A' i ∧ A' i ⊆ E₁)
    (hlt : ∀ (i j : Fin (pi + 3 + 2)), i < j → A' i ⊆ A' j \ (R j).U)
    (hR0 : R 0 = C₂)
    (hA0 : A' 0 = E₂)
    (hRU : ∀ (i : Fin (pi + 3 + 2)), (R i).U ⊆ A' i) :
    ∀ (i : Fin (pi + 3 + 2)), (fun R : Drawing S => η.gmap.sub R.toGraph) (R i) ≤ Nout₂.G := by
  let K := fun R : Drawing S => η.gmap.sub R.toGraph
  intro i
  obtain ⟨hc, hs, hdi, hb, h₂, h₁⟩ := hRA i
  have hin : K (R i) ≤ Nin.G := hKin hc hs ((hRU i).trans h₁)
  refine le_of_subset_of_subset (hin.trans (le_refl _)) (hOutle₂) ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    rw [hOutV₂]
    refine ⟨hin.vertexSet_mono (mem_image_of_mem _ hv), ?_⟩
    rw [hη v (hs.1 hv)]
    intro hi
    refine (discInt_mono hman hE₂ h₂ hi).2 ?_
    rw [hb]
    exact hVU hv
  · intro a ha
    by_cases hi : i = 0
    · subst hi
      rw [hR0] at ha
      exact hTO₂ ha
    · have ha' := ha
      rw [show E(K (R i)) = _ from η.gmap.edgeSet_sub (hRG hc hs)] at ha'
      obtain ⟨e, he, rfl⟩ := ha'
      rcases hEun₂.superset (hin.edgeSet_mono ha) with h | h
      · exfalso
        have hcl := hIc₂ _ h
        rw [hei _ (hin.edgeSet_mono ha), hηe e (hs.2 he)] at hcl
        obtain ⟨x, hx⟩ := (hs.2 he).2.2.1.isConnected.nonempty
        have hx₂ : x ∈ E₂ := hcl (subset_closure hx)
        have hpos : (0 : Fin (pi + 3 + 2)) < i := Fin.pos_iff_ne_zero.mpr hi
        have h₃ := hlt 0 i hpos (hA0.symm ▸ hx₂)
        exact h₃.2 (edge_subset_U he hx)
      · exact h

private theorem nested_circuits_give_neighborhood_breadth
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {H : Drawing S}
    {E₁ : Set S}
    {E₂ : Set S}
    {pi : ℕ}
    {N : Neighborhood α β}
    (η : SpanEmbedding H N.G)
    (Y : GraphDrawing N.G S)
    (hVU : ∀ {R : Drawing S} {v : S}, v ∈ R.V → v ∈ R.U)
    (hKU : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → graphDrawingSubgraphU Y ((fun R :
      Drawing S => η.gmap.sub R.toGraph) R) = R.U)
    (Nin : Neighborhood α β)
    (Yin : GraphDrawing Nin.G S)
    (hpi' : ∀ P ≤ Nin.G, graphDrawingSubgraphU Yin P = graphDrawingSubgraphU Y P)
    (Nout₂ : Neighborhood α β)
    (Yout₂ : GraphDrawing Nout₂.G S)
    (hOutle₂ : Nout₂.G ≤ Nin.G)
    (hpo₂ : ∀ P ≤ Nout₂.G, graphDrawingSubgraphU Yout₂ P = graphDrawingSubgraphU Yin P)
    (Pr₂ : Presentation Nout₂)
    (f : S → EuclideanPlane)
    (hΔ : Pr₂.Δ = f '' E₁)
    (hΔ₀ : Pr₂.Δ₀ = f '' E₂)
    (hdisc : ∀ E ⊆ E₁, IsClosedDisc E → IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E)
    (hpts : ∀ (J : Graph α β), graphDrawingSubgraphU Pr₂.Γ J = f '' graphDrawingSubgraphU Yout₂ J)
    (R : Fin (pi + 3 + 2) → Drawing S)
    (A' : Fin (pi + 3 + 2) → Set S)
    (hRA : ∀ (i : Fin (pi + 3 + 2)), (R i).IsCircuit ∧ (R i).IsSubdrawing H ∧ IsClosedDisc (A' i)
      ∧ discBd (A' i) = (R i).U ∧ E₂ ⊆ A' i ∧ A' i ⊆ E₁)
    (hlt : ∀ (i j : Fin (pi + 3 + 2)), i < j → A' i ⊆ A' j \ (R j).U)
    (hKR : ∀ (i : Fin (pi + 3 + 2)), (fun R : Drawing S => η.gmap.sub R.toGraph) (R i) ≤ Nout₂.G)
    (hdjU : ∀ (i j : Fin (pi + 3 + 2)), i < j → Disjoint (R i).U (R j).U) :
    Nout₂.HasBreadthGe (pi + 5) := by
  let K := fun R : Drawing S => η.gmap.sub R.toGraph
  have hdis : Pairwise fun i j => Disjoint V(K (R i)) V(K (R j)) := by
    have hone : ∀ i j, i < j → Disjoint V(K (R i)) V(K (R j)) := by
      intro i j h
      refine disjoint_left.mpr ?_
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hba : b = a := η.gmap.bijV.injOn ((hRA j).2.1.1 hb) ((hRA i).2.1.1 ha) hab
      exact disjoint_left.mp (hdjU i j h) (hVU ha) (hba ▸ hVU hb)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hone i j h
    · exact (hone j i h).symm
  refine hasBreadthGe_of_presentation (s := pi + 3 + 2) Pr₂ Yout₂ hΔ hΔ₀ hdisc hpts
    (fun i => K (R i)) A' (fun i => ⟨hKR i, (η.gmap.circuit
      (isGraphCircuit_of_isCircuit (hRA i).1 (hRA i).2.1)).2⟩) hdis (fun i => ?_) ?_
  · obtain ⟨hc, hs, hdi, hb, h₂, h₁⟩ := hRA i
    refine ⟨hdi, ?_, h₂, h₁⟩
    rw [hpo₂ _ (hKR i), hpi' _ ((hKR i).trans hOutle₂), hKU hc hs, hb]
  · intro i j hij
    rcases eq_or_lt_of_le hij with rfl | h
    · exact Subset.rfl
    · exact (hlt i j h).trans sdiff_subset

private theorem inner_and_outer_neighborhoods_meet_in_first_circuit
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {H : Drawing S}
    {C₁ : Drawing S}
    {E₁ : Set S}
    {S_G0 : Society α β}
    {N : Neighborhood α β}
    (η : SpanEmbedding H N.G)
    {ν : α → S}
    (hΩ₀ : S_G0.Ω.bar = η.vMap '' C₁.V)
    (hbarE₁ : ∀ v ∈ V(N.G), ν v ∈ discBd E₁ ↔ v ∈ S_G0.Ω.bar)
    (Nout : Neighborhood α β)
    (Nin : Neighborhood α β)
    (hInV : V(Nin.G) = {v | v ∈ V(N.G) ∧ ν v ∈ E₁})
    (hOutV : V(Nout.G) = {v | v ∈ V(N.G) ∧ ν v ∉ discInt E₁}) :
    V(Nin.G) ∩ V(Nout.G) ⊆ η.vMap '' C₁.V := by
  rintro v ⟨h₁, h₂⟩
  rw [hInV] at h₁
  rw [hOutV] at h₂
  have hb : ν v ∈ discBd E₁ := by
    by_contra hn
    exact h₂.2 ⟨h₁.2, hn⟩
  have := (hbarE₁ v h₁.1).mp hb
  rwa [hΩ₀] at this

private theorem inner_and_outer_neighborhoods_meet_in_second_circuit
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {C₂ : Drawing S}
    {E₂ : Set S}
    {N : Neighborhood α β}
    {ν : α → S}
    (K : Drawing S → Graph α β)
    (hbdE₂ : ∀ v ∈ V(N.G), ν v ∈ discBd E₂ ↔ v ∈ V(K C₂))
    (Nin : Neighborhood α β)
    (hInle : Nin.G ≤ N.G)
    (Nout₂ : Neighborhood α β)
    (Nin₂ : Neighborhood α β)
    (hInV₂ : V(Nin₂.G) = {v | v ∈ V(Nin.G) ∧ ν v ∈ E₂})
    (hOutV₂ : V(Nout₂.G) = {v | v ∈ V(Nin.G) ∧ ν v ∉ discInt E₂}) :
    V(Nout₂.G) ∩ V(Nin₂.G) ⊆ V(K C₂) := by
  rintro v ⟨h₁, h₂⟩
  rw [hOutV₂] at h₁
  rw [hInV₂] at h₂
  refine (hbdE₂ v (hInle.vertexSet_mono h₂.1)).mp ?_
  by_contra hn
  exact h₁.2 ⟨h₂.2, hn⟩

private theorem path_to_second_circuit_lies_in_inner_neighborhood
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {H : Drawing S}
    {C₁ : Drawing S}
    {C₂ : Drawing S}
    {E₁ : Set S}
    {pi : ℕ}
    {N : Neighborhood α β}
    (η : SpanEmbedding H N.G)
    {ν : α → S}
    (hη : ∀ v ∈ H.V, ν (η.vMap v) = v)
    (hs₂ : C₂.IsSubdrawing H)
    (hVU : ∀ {R : Drawing S} {v : S}, v ∈ R.V → v ∈ R.U)
    (hηN : ∀ {v : S}, v ∈ H.V → η.vMap v ∈ V(N.G))
    (Nout : Neighborhood α β)
    (Nin : Neighborhood α β)
    (hInle : Nin.G ≤ N.G)
    (hOutle : Nout.G ≤ N.G)
    (hInV : V(Nin.G) = {v | v ∈ V(N.G) ∧ ν v ∈ E₁})
    (hEun : E(Nin.G) ∪ E(Nout.G) = E(N.G))
    (hC₂U : C₂.U ⊆ E₁)
    (x : Fin (2 * pi + 8) → S)
    (y : Fin (2 * pi + 8) → S)
    (Q' : Fin (2 * pi + 8) → Graph α β)
    (hQ'f : ∀ (i : Fin (2 * pi + 8)), IsFromToPathWithEnds η.imageGraph (Q' i) (η.vMap '' C₁.V)
      (η.vMap '' C₂.V) (η.vMap (x i)) (η.vMap (y i)))
    (hyH : ∀ (i : Fin (2 * pi + 8)), y i ∈ C₂.V)
    (hZ₁ : V(Nin.G) ∩ V(Nout.G) ⊆ η.vMap '' C₁.V) :
    ∀ (i : Fin (2 * pi + 8)), Q' i ≤ Nin.G := by
  intro i
  refine path_in_side hOutle hInle hEun.superset hZ₁
    (((hQ'f i).1.symm).mono η.imageGraph_le) ?_ (hQ'f i).2.1.subset
  rw [hInV]
  refine ⟨hηN (hs₂.1 (hyH i)), ?_⟩
  rw [hη _ (hs₂.1 (hyH i))]
  exact hC₂U (hVU (hyH i))

private theorem path_to_second_circuit_stays_in_outer_neighborhood
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {H : Drawing S}
    {C₁ : Drawing S}
    {C₂ : Drawing S}
    {E₁ : Set S}
    {E₂ : Set S}
    (hbd₁ : discBd E₁ = C₁.U)
    (hE₂E₁ : E₂ ⊆ E₁ \ C₁.U)
    {pi : ℕ}
    {N : Neighborhood α β}
    (η : SpanEmbedding H N.G)
    {ν : α → S}
    (hη : ∀ v ∈ H.V, ν (η.vMap v) = v)
    (hs₁ : C₁.IsSubdrawing H)
    (hVU : ∀ {R : Drawing S} {v : S}, v ∈ R.V → v ∈ R.U)
    (hηN : ∀ {v : S}, v ∈ H.V → η.vMap v ∈ V(N.G))
    (Nin : Neighborhood α β)
    (hInV : V(Nin.G) = {v | v ∈ V(N.G) ∧ ν v ∈ E₁})
    (Nout₂ : Neighborhood α β)
    (Nin₂ : Neighborhood α β)
    (hInle₂ : Nin₂.G ≤ Nin.G)
    (hOutle₂ : Nout₂.G ≤ Nin.G)
    (hOutV₂ : V(Nout₂.G) = {v | v ∈ V(Nin.G) ∧ ν v ∉ discInt E₂})
    (hEun₂ : E(Nin₂.G) ∪ E(Nout₂.G) = E(Nin.G))
    (x : Fin (2 * pi + 8) → S)
    (y : Fin (2 * pi + 8) → S)
    (Q' : Fin (2 * pi + 8) → Graph α β)
    (hQ'f : ∀ (i : Fin (2 * pi + 8)), IsFromToPathWithEnds η.imageGraph (Q' i) (η.vMap '' C₁.V)
      (η.vMap '' C₂.V) (η.vMap (x i)) (η.vMap (y i)))
    (hxH : ∀ (i : Fin (2 * pi + 8)), x i ∈ C₁.V)
    (hZ₂ : V(Nout₂.G) ∩ V(Nin₂.G) ⊆ η.vMap '' C₂.V)
    (hinNin : ∀ (i : Fin (2 * pi + 8)), Q' i ≤ Nin.G) :
    ∀ (i : Fin (2 * pi + 8)), Q' i ≤ Nout₂.G := by
  intro i
  refine path_in_side (G := Nin.G) hInle₂ hOutle₂ (fun e he => Or.symm (hEun₂.superset he)) hZ₂
    (⟨hinNin i, (hQ'f i).1.2⟩ : IsGraphPathWithEnds Nin.G _ _ _) ?_ (hQ'f i).2.2.subset
  rw [hOutV₂]
  have hx₀ := hVU (hxH i)
  refine ⟨?_, ?_⟩
  · rw [hInV]
    refine ⟨hηN (hs₁.1 (hxH i)), ?_⟩
    rw [hη _ (hs₁.1 (hxH i))]
    rw [← hbd₁] at hx₀
    exact GraphMinor.Surface.discBd_subset E₁ hx₀
  · rw [hη _ (hs₁.1 (hxH i))]
    exact fun hi => (hE₂E₁ hi.1).2 hx₀

private theorem transaction_path_has_only_endpoints_on_society_boundary
    {α : Type u}
    {β : Type v}
    {S_G0 : Society α β}
    (Ω₀' : CyclicPerm α)
    (hΩ₀'_bar : Ω₀'.bar = S_G0.Ω.bar)
    (Sm : Society α β)
    (hSmΩ : Sm.Ω = Ω₀')
    (p : Graph α β)
    (a : α)
    (b : α)
    (hint : Disjoint (pathInternalVerts Sm.G p) Sm.Ω.bar)
    (hpe : pathEnds Sm.G p = {a, b}) :
    ∀ z ∈ V(p), z ∈ S_G0.Ω.bar → z = a ∨ z = b := by
  intro z hz hb
  by_contra hn
  refine disjoint_left.mp hint ⟨hz, ?_⟩ (hSmΩ.symm ▸ hΩ₀'_bar.symm ▸ hb)
  rw [hpe]
  simpa using hn

private theorem interior_society_vertices_lie_in_first_disc
    {S : Type w}
    {α : Type u}
    {β : Type v}
    {E₁ : Set S}
    {E₂ : Set S}
    {S₂ : Society α β}
    {N : Neighborhood α β}
    {ν : α → S}
    (hbarE₂ : ∀ v ∈ N.Ω₀.bar, ν v ∈ E₂)
    (hE₂sub : E₂ ⊆ E₁)
    (Sm : Society α β)
    (Nin : Neighborhood α β)
    (hInV : V(Nin.G) = {v | v ∈ V(N.G) ∧ ν v ∈ E₁})
    (hSmV : V(Sm.G) = V(S₂.G) ∪ V(Nin.G))
    (hN₀ : N.Ω₀ = S₂.Ω)
    (hS₂b : S₂.Ω.bar = V(S₂.G) ∩ V(N.G)) :
    ∀ u ∈ V(N.G), u ∈ V(Sm.G) → ν u ∈ E₁ := by
  intro u hu hm
  rw [hSmV] at hm
  rcases hm with h | h
  · have hb : u ∈ N.Ω₀.bar := by
      rw [hN₀, hS₂b]
      exact ⟨h, hu⟩
    exact hE₂sub (hbarE₂ u hb)
  · rw [hInV] at h
    exact h.2

private theorem crooked_transaction_paths_restrict_to_first_disc
    {S : Type w}
    [TopologicalSpace S]
    {α : Type u}
    {β : Type v}
    {H : Drawing S}
    {C₁ : Drawing S}
    {E₁ : Set S}
    {E₂ : Set S}
    (hbd₁ : discBd E₁ = C₁.U)
    {S_G : Society α β}
    {S₂ : Society α β}
    {S_G0 : Society α β}
    {N : Neighborhood α β}
    (η : SpanEmbedding H N.G)
    (hcomp : S_G.IsComposition S₂ N)
    (Y : GraphDrawing N.G S)
    {ν : α → S}
    (hν : ∀ v : V(N.G), (Y.iso.vertexEquiv v).1 = ν v.1)
    (hη : ∀ v ∈ H.V, ν (η.vMap v) = v)
    (hηe : ∀ e ∈ H.E, graphDrawingEdgeSet Y (η.eMap e) = e)
    (hbarE₂ : ∀ v ∈ N.Ω₀.bar, ν v ∈ E₂)
    (hΩ₀ : S_G0.Ω.bar = η.vMap '' C₁.V)
    (hc₁ : C₁.IsCircuit)
    (hs₁ : C₁.IsSubdrawing H)
    (hE₂sub : E₂ ⊆ E₁)
    (hRG : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → R.toGraph ≤ H.toGraph)
    (hKle : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → (fun R : Drawing S => η.gmap.sub
      R.toGraph) R ≤ N.G)
    (hKU : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → graphDrawingSubgraphU Y ((fun R :
      Drawing S => η.gmap.sub R.toGraph) R) = R.U)
    (hηN : ∀ {v : S}, v ∈ H.V → η.vMap v ∈ V(N.G))
    (hηEN : ∀ {e : Set S}, e ∈ H.E → η.eMap e ∈ E(N.G))
    (hbarE₁ : ∀ v ∈ V(N.G), ν v ∈ discBd E₁ ↔ v ∈ S_G0.Ω.bar)
    (Ω₀' : CyclicPerm α)
    (hΩ₀'_bar : Ω₀'.bar = S_G0.Ω.bar)
    (hnat₀' : IsNaturalOrderFrom ν Ω₀' (discBd E₁))
    (hΩ₀' : Ω₀'.bar = η.vMap '' C₁.V)
    (Sm : Society α β)
    (Nin : Neighborhood α β)
    (hSmΩ : Sm.Ω = Ω₀')
    (hSmle : Sm.G ≤ S_G.G)
    (hInV : V(Nin.G) = {v | v ∈ V(N.G) ∧ ν v ∈ E₁})
    (hIc : ∀ e ∈ E(Nin.G), closure (graphDrawingEdgeSet Y e) ⊆ E₁)
    (hSmV : V(Sm.G) = V(S₂.G) ∪ V(Nin.G))
    (hSmE : E(Sm.G) = E(S₂.G) ∪ E(Nin.G))
    (P₂ : Set (Graph α β))
    (hcr₂ : Sm.IsCrookedTransaction P₂)
    (hint₂ : ∀ Q ∈ P₂, Disjoint (pathInternalVerts Sm.G Q) Sm.Ω.bar)
    (hle : Sm.G ≤ S_G0.G) :
    ∀ p ∈ P₂, ∃ a b, S_G0.IsOmegaPathWithEnds p a b ∧ (∀ v ∈ H.V, η.vMap v ∈ V(p) → η.vMap v = a ∨
      η.vMap v = b ∨ v ∈ E₁ \ C₁.U) ∧ ∀ e ∈ H.E, η.eMap e ∈ E(p) → e ⊆ E₁ \ C₁.U := by
  let K := fun R : Drawing S => η.gmap.sub R.toGraph
  intro p hp
  obtain ⟨_, _, hfence⟩ := hcr₂.1
  obtain ⟨a, b, hω⟩ := hfence.1.1 p hp
  have hint := hint₂ p hp
  have hpe : pathEnds Sm.G p = {a, b} := hω.1.pathEnds_eq
  have hoff : ∀ z ∈ V(p), z ∈ S_G0.Ω.bar → z = a ∨ z = b := by
    exact transaction_path_has_only_endpoints_on_society_boundary (α := α) (β := β) (S_G0 := S_G0)
      Ω₀' hΩ₀'_bar Sm hSmΩ p a b hint hpe
  have hpG : p ≤ Sm.G := hω.1.1
  obtain ⟨⟨⟨-, hNG, -, -, hEd⟩, -⟩, -, hN₀, hS₂b⟩ := hcomp
  have hSmE₁ : ∀ u ∈ V(N.G), u ∈ V(Sm.G) → ν u ∈ E₁ := by
    exact interior_society_vertices_lie_in_first_disc (S := S) (α := α) (β := β) (E₁ := E₁) (E₂ :=
      E₂) (S₂ := S₂) (N := N) (ν := ν) hbarE₂ hE₂sub Sm Nin hInV hSmV hN₀ hS₂b
  refine ⟨a, b, ⟨hω.1.mono hle, hω.2.1, hΩ₀'_bar ▸ hSmΩ ▸ hω.2.2.1, hΩ₀'_bar ▸ hSmΩ ▸ hω.2.2.2⟩,
    ?_, ?_⟩
  · intro v hv hm
    have hmN := hηN hv
    have hvE : v ∈ E₁ := by
      have := hSmE₁ _ hmN (hpG.vertexSet_mono hm)
      rwa [hη v hv] at this
    by_cases hc : v ∈ C₁.U
    · have hb : η.vMap v ∈ S_G0.Ω.bar := (hbarE₁ _ hmN).mp (by
        rw [hη v hv, hbd₁]
        exact hc)
      rcases hoff _ hm hb with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hvE, hc⟩)
  · intro e he hm x hx
    have haE := hηEN he
    have hmSm : η.eMap e ∈ E(Nin.G) := by
      have h := hpG.edgeSet_mono hm
      rw [hSmE] at h
      rcases h with h | h
      · exact absurd haE (disjoint_left.mp hEd h)
      · exact h
    have hcl := hIc _ hmSm
    have heE : e ⊆ E₁ := by
      have := subset_closure.trans hcl
      rwa [hηe e he] at this
    refine ⟨heE hx, fun hxC => ?_⟩
    -- The edge is an edge of `C₁`, joining the two ends of `p`. Then `p` is peripheral.
    have hxV : x ∉ H.V := (he.2.1 hx).2
    have heC : e ∈ C₁.E := by
      rw [C₁.U_eq] at hxC
      rcases hxC with h | h
      · exact absurd (hs₁.1 h) hxV
      · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
        have hx' : x ∈ g := by
          rw [← H.closure_diff_V (hs₁.2 hg)]
          exact ⟨hxg, hxV⟩
        have := H.edge_eq_of_mem he (hs₁.2 hg) hx hx'
        exact this ▸ hg
    obtain ⟨c, d, hl⟩ := C₁.toGraph.exists_isLink_of_mem_edgeSet heC
    have hlK : (K C₁).IsLink (η.eMap e) (η.vMap c) (η.vMap d) := η.gmap.sub_isLink (hRG hc₁ hs₁) hl
    have hlN : N.G.IsLink (η.eMap e) (η.vMap c) (η.vMap d) := hlK.mono (hKle hc₁ hs₁)
    have hlS : S_G.G.IsLink (η.eMap e) (η.vMap c) (η.vMap d) := hlN.mono hNG
    obtain ⟨c', d', hlp⟩ := p.exists_isLink_of_mem_edgeSet hm
    have hlp' : S_G.G.IsLink (η.eMap e) c' d' := hlp.mono (hpG.trans hSmle)
    have hlp₂ : p.IsLink (η.eMap e) (η.vMap c) (η.vMap d) := by
      rcases hlS.eq_and_eq_or_eq_and_eq hlp' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
        exact hlp
      · rw [h₁, h₂]
        exact hlp.symm
    have hcb : η.vMap c ∈ S_G0.Ω.bar := by
      rw [hΩ₀]
      exact mem_image_of_mem _ hl.left_mem
    have hdb : η.vMap d ∈ S_G0.Ω.bar := by
      rw [hΩ₀]
      exact mem_image_of_mem _ hl.right_mem
    have hcd : η.vMap c ≠ η.vMap d := fun h => by
      rw [h] at hlp₂
      exact IsGraphPathWithEnds.no_loop hω.1 hlp₂
    have hab : (η.vMap c = a ∧ η.vMap d = b) ∨ (η.vMap c = b ∧ η.vMap d = a) := by
      rcases hoff _ hlp₂.left_mem hcb with h₁ | h₁ <;>
        rcases hoff _ hlp₂.right_mem hdb with h₂ | h₂
      · exact absurd (h₁.trans h₂.symm) hcd
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
      · exact absurd (h₁.trans h₂.symm) hcd
    have hends := ends_of_drawing hν hlN
    have hcL : ν (η.vMap c) ∈ closure (graphDrawingEdgeSet Y (η.eMap e)) :=
      (hends.superset (mem_insert _ _)).1
    have hdL : ν (η.vMap d) ∈ closure (graphDrawingEdgeSet Y (η.eMap e)) :=
      (hends.superset (mem_insert_of_mem _ rfl)).1
    have hLsub : closure (graphDrawingEdgeSet Y (η.eMap e)) ⊆ discBd E₁ := by
      rw [hbd₁, ← hKU hc₁ hs₁]
      intro y hy
      exact Or.inr (mem_iUnion₂.mpr ⟨η.eMap e, hlK.edge_mem, hy⟩)
    have hLpre : IsPreconnected (closure (graphDrawingEdgeSet Y (η.eMap e))) :=
      (edge_mem_of_drawing (Y := Y) haE).2.2.1.isConnected.isPreconnected.closure
    have hoffL : ∀ v ∈ Ω₀'.bar, ν v ∈ closure (graphDrawingEdgeSet Y (η.eMap e)) →
        v = a ∨ v = b := by
      intro v hvb hvL
      have hvN : v ∈ V(N.G) := by
        rw [hΩ₀'] at hvb
        obtain ⟨w, hw, rfl⟩ := hvb
        exact hηN (hs₁.1 hw)
      have hm' : ν v ∈ closure (graphDrawingEdgeSet Y (η.eMap e)) ∩ Y.drawing.V :=
        ⟨hvL, mem_V_of_drawing hν hvN⟩
      rw [hends] at hm'
      have hinj := inj_of_drawing hν
      rcases hm' with h | h
      · have := hinj hvN hlN.left_mem h
        rcases hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl (this.trans h₁)
        · exact Or.inr (this.trans h₁)
      · have := hinj hvN hlN.right_mem h
        rcases hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inr (this.trans h₂)
        · exact Or.inl (this.trans h₂)
    have haL : ν a ∈ closure (graphDrawingEdgeSet Y (η.eMap e)) := by
      rcases hab with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact h₁ ▸ hcL
      · exact h₂ ▸ hdL
    have hbL : ν b ∈ closure (graphDrawingEdgeSet Y (η.eMap e)) := by
      rcases hab with ⟨-, h₂⟩ | ⟨h₁, -⟩
      · exact h₂ ▸ hdL
      · exact h₁ ▸ hcL
    have hemp := interval_empty_of_arc hnat₀' hLsub hLpre haL hbL hoffL
    refine hcr₂.2 p hp ⟨hp, a, b, hω, ?_⟩
    rw [hSmΩ]
    rcases hemp with h | h
    · exact Or.inl (by
        rw [h]
        exact empty_disjoint _)
    · exact Or.inr (by
        rw [h]
        exact empty_disjoint _)

omit [T1Space S] in
/-- The part of the proof of (8.4) after "we may assume, to simplify notation, that $G_1$ is a
drawing in $\Sigma$". Here `Y` is that drawing of `N.G`, and `ν` gives the point of each vertex.

We cut at `C₁` and get the separation `(A, B)` of the paper. Then we cut at `C₂` and apply (8.2) to
the part between `C₁` and `C₂`, with `V(C₂)` in place of `ΩBar₂`. The paths of the hypothesis end in
`V(C₂)`, so this is the neighbourhood they cross. -/
theorem drawn_8_4 [T2Space S] [ConnectedSpace S] {α : Type u} {β : Type v}
    (hS : IsClosedSurface S) {H C₁ C₂ : Drawing S} {D E₁ E₂ : Set S}
    (hD : IsClosedDisc D) (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂)
    (hC₁ : C₁.IsCircuit ∧ C₁.IsSubdrawing H) (hC₂ : C₂.IsCircuit ∧ C₂.IsSubdrawing H)
    (hbd₁ : discBd E₁ = C₁.U) (hbd₂ : discBd E₂ = C₂.U) (hE₂E₁ : E₂ ⊆ E₁ \ C₁.U) (hE₁D : E₁ ⊆ D)
    {pi : ℕ} (hpi1 : pi ≠ 1) (hpi3 : pi ≠ 3) (hdist : pi + 4 ≤ regionalDistance H C₂.U C₁.U)
    {X : Set S} (hX : X ⊆ C₁.V) (P : Fin (2 * pi + 8) → Graph S (Set S))
    (hP : ∀ i, ∃ x ∈ X, ∃ y ∈ C₂.V, IsGraphPathWithEnds H.toGraph (P i) x y ∧ V(P i) ∩ C₁.V = {x})
    (hPd : Pairwise fun i j => Disjoint V(P i) V(P j))
    {S_G S₂ S_G0 : Society α β} {N : Neighborhood α β} (η : SpanEmbedding H N.G)
    (hcomp : S_G.IsComposition S₂ N) (Y : GraphDrawing N.G S) {ν : α → S}
    (hν : ∀ v : V(N.G), (Y.iso.vertexEquiv v).1 = ν v.1) (hYU : Y.drawing.U ⊆ D)
    (hη : ∀ v ∈ H.V, ν (η.vMap v) = v)
    (hηe : ∀ e ∈ H.E, graphDrawingEdgeSet Y (η.eMap e) = e)
    (hbarD : ∀ v ∈ V(N.G), ν v ∈ discBd D ↔ v ∈ N.Ω.bar)
    (hbarE₂ : ∀ v ∈ N.Ω₀.bar, ν v ∈ E₂) (hnat₁ : IsNaturalOrderFrom ν N.Ω (discBd D))
    (hΩ₀ : S_G0.Ω.bar = η.vMap '' C₁.V) (hnat₀ : IsNaturalOrderFrom ν S_G0.Ω (discBd E₁))
    (hG0 : S_G0.G = S_G.G)
    (hcr : ∃ P_set : Set (Graph α β), S_G.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard) :
    ∃ P_set : Set (Graph α β), S_G0.IsCrookedTransaction P_set ∧ pi ≤ P_set.ncard ∧
      S_G0.transactionEnds P_set ⊆ η.vMap '' X ∧
      ∀ p ∈ P_set, ∃ a b : α, S_G0.IsOmegaPathWithEnds p a b ∧
        (∀ v ∈ H.V, η.vMap v ∈ V(p) → η.vMap v = a ∨ η.vMap v = b ∨ v ∈ E₁ \ C₁.U) ∧
        (∀ e ∈ H.E, η.eMap e ∈ E(p) → e ⊆ E₁ \ C₁.U) := by
  classical
  have : CompactSpace S := hS.1
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  obtain ⟨hc₁, hs₁⟩ := id hC₁
  obtain ⟨hc₂, hs₂⟩ := id hC₂
  have hE₂sub : E₂ ⊆ E₁ := hE₂E₁.trans sdiff_subset
  have hVU : ∀ {R : Drawing S} {v : S}, v ∈ R.V → v ∈ R.U := fun {R v} hv => by
    rw [R.U_eq]
    exact Or.inl hv
  -- The circuits of `H`, as subgraphs of `N.G`.
  let K : Drawing S → Graph α β := fun R => η.gmap.sub R.toGraph
  have hRG : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → R.toGraph ≤ H.toGraph :=
    fun hc hs => (isGraphCircuit_of_isCircuit hc hs).1
  have hKle : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → K R ≤ N.G :=
    fun hc hs => (η.gmap.sub_le (hRG hc hs)).trans η.imageGraph_le
  have hKU : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H →
      graphDrawingSubgraphU Y (K R) = R.U := fun hc hs =>
    subgraphU_image hs η Y hν η.imageGraph_le hη hηe (hRG hc hs)
  have hηN : ∀ {v : S}, v ∈ H.V → η.vMap v ∈ V(N.G) := fun hv =>
    η.imageGraph_le.vertexSet_mono (η.gmap.bijV.mapsTo hv)
  have hηEN : ∀ {e : Set S}, e ∈ H.E → η.eMap e ∈ E(N.G) := fun he =>
    η.imageGraph_le.edgeSet_mono (η.gmap.bijE.mapsTo he)
  have hbarE₁ : ∀ v ∈ V(N.G), ν v ∈ discBd E₁ ↔ v ∈ S_G0.Ω.bar := by
    intro v hv
    rw [hbd₁, ← hKU hc₁ hs₁, hΩ₀]
    exact mem_subgraphU_iff hν (hKle hc₁ hs₁) hv
  have hbdE₂ : ∀ v ∈ V(N.G), ν v ∈ discBd E₂ ↔ v ∈ V(K C₂) := by
    intro v hv
    rw [hbd₂, ← hKU hc₂ hs₂]
    exact mem_subgraphU_iff hν (hKle hc₂ hs₂) hv
  -- The separation `(A, B)` at `C₁`. Then `(G, Ω_1)` is the composition of `(A ∪ G_2, Ω_0)` with
  -- `(B, Ω_1, Ω_0)`, and the latter is rural.
  obtain ⟨Ω₀', hΩ₀'_or, hΩ₀'_bar, hnat₀', hpres₁⟩ :=
    exists_presentation_of_drawing hD hE₁ hE₁D hnat₁ hnat₀
  have hΩ₀' : Ω₀'.bar = η.vMap '' C₁.V := hΩ₀'_bar.trans hΩ₀
  obtain ⟨Sm, Nout, Nin, Yin, Yout, hSmΩ, hOutΩ, hOutΩ₀, hInΩ, hInΩ₀, hInle, hOutle, hSmle, hInV,
    hOutV, -, -, hEun, hIc, hOT, hSmV, hSmE, hcomp₁, hcomp₂, hνi, hνo, hUi, hUo, hei, -, hpi', -⟩ :=
    exists_cut_society hS hcomp Y hν hD hE₁ hE₂sub hE₁D
      (fun v hv => (hbarD v (N.bar_subset hv)).mpr hv) hbarE₂ (C := K C₁) (hKle hc₁ hs₁)
      (hbd₁.trans (hKU hc₁ hs₁).symm) (T := ∅) (empty_subset _) Ω₀' hΩ₀'
  have hIn₁ : ∀ a ∈ E(N.G), graphDrawingEdgeSet Y a ⊆ E₁ → a ∈ E(Nin.G) := by
    intro a ha hsub
    rcases hEun.superset ha with h | h
    · exact h
    · rcases hOT a h with h' | h'
      · exact absurd h' (notMem_empty a)
      · exact absurd hsub h'
  have hKin : ∀ {R : Drawing S}, R.IsCircuit → R.IsSubdrawing H → R.U ⊆ E₁ → K R ≤ Nin.G := by
    intro R hc hs hU
    refine le_of_subset_of_subset (hKle hc hs) hInle ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      rw [hInV]
      refine ⟨hηN (hs.1 hv), ?_⟩
      rw [hη v (hs.1 hv)]
      exact hU (hVU hv)
    · intro a ha
      rw [show E(K R) = _ from η.gmap.edgeSet_sub (hRG hc hs)] at ha
      obtain ⟨e, he, rfl⟩ := ha
      refine hIn₁ _ (hηEN (hs.2 he)) ?_
      rw [hηe e (hs.2 he)]
      exact (edge_subset_U he).trans hU
  have hrural : Nout.IsRural := by
    obtain ⟨Pr, -, -, -, -, -, -, -⟩ := hpres₁ Nout Yout hOutΩ hOutΩ₀
      (fun x hx => ⟨hYU (hUo hx).1, (hUo hx).2⟩) hνo
      (fun v hv => by
        rw [hOutΩ]
        exact hbarD v (hOutle.vertexSet_mono hv))
      (fun v hv => by
        rw [hOutΩ₀, hΩ₀'_bar]
        exact hbarE₁ v (hOutle.vertexSet_mono hv))
    exact ⟨Pr.Γ, Pr.Δ, Pr.Δ₀, Pr.isClosedDisc_Δ, Pr.Δ₀_subset_Δ, Pr.U_subset, Pr.mem_bd_Δ_iff,
      Pr.mem_bd_Δ₀_iff, Pr.agrees_Δ, Pr.agrees_Δ₀⟩
  -- By [3, theorem (9.1)], `(A ∪ G_2, Ω_0)` has a crooked transaction of order `≥ π`.
  obtain ⟨P₀, hcr₀, hcard₀⟩ := hcr
  obtain ⟨P₁, hcr₁, hcard₁⟩ := GM09.gm14_theorem_9_1 S_G Sm Nout pi P₀ hrural hcomp₁ hcr₀ hcard₀
  -- The cut at `C₂`. The edges of `C₂` stay with the outer part.
  have hC₂U : C₂.U ⊆ E₁ := by
    rw [← hbd₂]
    exact (GraphMinor.Surface.discBd_subset E₂).trans hE₂sub
  have hC₂in : K C₂ ≤ Nin.G := hKin hc₂ hs₂ hC₂U
  have hfin : V(K C₂).Finite := N.finite_V.subset (hKle hc₂ hs₂).vertexSet_mono
  obtain ⟨Ω₂_raw, hbar₂_raw, hnat₂_raw⟩ := exists_natural_order_injOn hE₂.isOArc_discBd hfin
    ((inj_of_drawing hν).mono (hKle hc₂ hs₂).vertexSet_mono)
    (fun v hv => (hbdE₂ v ((hKle hc₂ hs₂).vertexSet_mono hv)).mpr hv)
  obtain ⟨Ω₂', -, hbar₂'_eq, hnat₂', hpres₂⟩ :=
    exists_presentation_of_drawing hE₁ hE₂ hE₂sub hnat₀' hnat₂_raw
  have hbar₂' : Ω₂'.bar = V(K C₂) := hbar₂'_eq.trans hbar₂_raw
  obtain ⟨Sm₂, Nout₂, Nin₂, -, Yout₂, -, hOutΩ', hOutΩ₀', -, -, hInle₂, hOutle₂, -, hInV₂, hOutV₂,
    -, hTO₂, hEun₂, hIc₂, -, -, -, hcomp₂₁, -, -, hνo₂, -, hUo₂, -, -, -, hpo₂⟩ :=
    exists_cut_society hS hcomp₂ Yin hνi hE₁ hE₂ Subset.rfl hE₂sub
      (fun v hv => (hbarE₁ v (hInle.vertexSet_mono (Nin.bar_subset hv))).mpr (hΩ₀'_bar ▸ hInΩ ▸ hv))
      (fun v hv => hbarE₂ v (hInΩ₀ ▸ hv)) (C := K C₂) hC₂in
      (hbd₂.trans (((hpi' _ hC₂in).trans (hKU hc₂ hs₂)).symm)) (T := E(K C₂)) Subset.rfl Ω₂' hbar₂'
  have hNout₂V : ∀ v ∈ V(Nout₂.G), v ∈ V(N.G) := fun v hv =>
    hInle.vertexSet_mono (hOutle₂.vertexSet_mono hv)
  obtain ⟨Pr₂, f, -, -, hΔ, hΔ₀, hdisc, hpts⟩ := hpres₂ Nout₂ Yout₂ (hOutΩ'.trans hInΩ) hOutΩ₀'
    (fun x hx => ⟨(hUi (hUo₂ hx).1).2, (hUo₂ hx).2⟩) hνo₂
    (fun v hv => by
      rw [hOutΩ', hInΩ, hΩ₀'_bar]
      exact hbarE₁ v (hNout₂V v hv))
    (fun v hv => by
      rw [hOutΩ₀', hbar₂']
      exact hbdE₂ v (hNout₂V v hv))
  -- The neighbourhood has breadth `≥ π + 5`, because `C₁, C₂` have regional distance `≥ π + 4`.
  obtain ⟨R, A', hRA, ⟨hR0, hA0⟩, hlt⟩ :=
    exists_nest_between hS H hE₁ hE₂ hC₁ hC₂ hbd₁ hbd₂ hE₂E₁ (m := pi + 3) hdist
  have hRU : ∀ i, (R i).U ⊆ A' i := fun i => by
    rw [← (hRA i).2.2.2.1]
    exact GraphMinor.Surface.discBd_subset _
  have hKR : ∀ i, K (R i) ≤ Nout₂.G := by
    exact nested_circuits_lie_in_outer_neighborhood (S := S) (α := α) (β := β) (H := H) (C₂ := C₂)
      (E₁ := E₁) (E₂ := E₂) hE₂ (pi := pi) (N := N) η Y (ν := ν) hη hηe hman hVU hRG Nin Yin hei
      hKin Nout₂ Nin₂ hOutle₂ hOutV₂ hTO₂ hEun₂ hIc₂ R A' hRA hlt hR0 hA0 hRU
  have hdjU : ∀ i j, i < j → Disjoint (R i).U (R j).U := fun i j h =>
    disjoint_left.mpr fun x h₁ h₂ => (hlt i j h (hRU i h₁)).2 h₂
  have hbreadth : Nout₂.HasBreadthGe (pi + 5) := by
    exact nested_circuits_give_neighborhood_breadth (S := S) (α := α) (β := β) (H := H) (E₁ := E₁)
      (E₂ := E₂) (pi := pi) (N := N) η Y hVU hKU Nin Yin hpi' Nout₂ Yout₂ hOutle₂ hpo₂ Pr₂ f hΔ
      hΔ₀ hdisc hpts R A' hRA hlt hKR hdjU
  -- The paths, cut at their first vertex of `C₂`.
  have hQ : ∀ i, ∃ (Q : Graph S (Set S)) (x y : S), Q ≤ P i ∧
      IsFromToPathWithEnds H.toGraph Q C₁.V C₂.V x y ∧ x ∈ X := by
    intro i
    obtain ⟨x, hx, y, hy, hp, hcap⟩ := hP i
    obtain ⟨x', hx', y', -, Q, hle, hQ⟩ := hp.exists_isFromToPathWithEnds (hX hx) hy
    have hxx : x' = x := hcap.subset ⟨hle.vertexSet_mono hQ.1.left_mem, hx'⟩
    exact ⟨Q, x', y', hle, hQ, hxx ▸ hx⟩
  choose Q x y hQP hQf hxX using hQ
  let Q' : Fin (2 * pi + 8) → Graph α β := fun i => η.gmap.sub (Q i)
  have hQ'f : ∀ i, IsFromToPathWithEnds η.imageGraph (Q' i) (η.vMap '' C₁.V) (η.vMap '' C₂.V)
      (η.vMap (x i)) (η.vMap (y i)) := fun i => η.gmap.fromTo hs₁.1 hs₂.1 (hQf i)
  have hxH : ∀ i, x i ∈ C₁.V := fun i => (hQf i).left_mem_X
  have hyH : ∀ i, y i ∈ C₂.V := fun i => (hQf i).right_mem_Y
  have hZ₁ : V(Nin.G) ∩ V(Nout.G) ⊆ V(K C₁) := by
    exact inner_and_outer_neighborhoods_meet_in_first_circuit (S := S) (α := α) (β := β) (H := H)
      (C₁ := C₁) (E₁ := E₁) (S_G0 := S_G0) (N := N) η (ν := ν) hΩ₀ hbarE₁ Nout Nin hInV hOutV
  have hZ₂ : V(Nout₂.G) ∩ V(Nin₂.G) ⊆ V(K C₂) := by
    exact inner_and_outer_neighborhoods_meet_in_second_circuit (S := S) (α := α) (β := β) (C₂ :=
      C₂) (E₂ := E₂) (N := N) (ν := ν) K hbdE₂ Nin hInle Nout₂ Nin₂ hInV₂ hOutV₂
  have hinNin : ∀ i, Q' i ≤ Nin.G := by
    exact path_to_second_circuit_lies_in_inner_neighborhood (S := S) (α := α) (β := β) (H := H)
      (C₁ := C₁) (C₂ := C₂) (E₁ := E₁) (pi := pi) (N := N) η (ν := ν) hη hs₂ hVU hηN Nout Nin
      hInle hOutle hInV hEun hC₂U x y Q' hQ'f hyH hZ₁
  have hinOut : ∀ i, Q' i ≤ Nout₂.G := by
    exact path_to_second_circuit_stays_in_outer_neighborhood (S := S) (α := α) (β := β) (H := H)
      (C₁ := C₁) (C₂ := C₂) (E₁ := E₁) (E₂ := E₂) hbd₁ hE₂E₁ (pi := pi) (N := N) η (ν := ν) hη hs₁
      hVU hηN Nin hInV Nout₂ Nin₂ hInle₂ hOutle₂ hOutV₂ hEun₂ x y Q' hQ'f hxH hZ₂ hinNin
  have hpaths : ∀ i, IsFromToPathWithEnds Nout₂.G (Q' i) Nout₂.Ω.bar Nout₂.Ω₀.bar
      (η.vMap (x i)) (η.vMap (y i)) ∧ η.vMap (x i) ∈ η.vMap '' X := by
    intro i
    refine ⟨⟨⟨hinOut i, (hQ'f i).1.2⟩, ?_, ?_⟩, mem_image_of_mem _ (hxX i)⟩
    · rw [hOutΩ', hInΩ, hΩ₀']
      exact (hQ'f i).2.1
    · rw [hOutΩ₀', hbar₂']
      exact (hQ'f i).2.2
  have hdisj : Pairwise fun i j => Disjoint V(Q' i) V(Q' j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba : b = a := η.gmap.bijV.injOn ((hQf j).1.1.vertexSet_mono hb)
      ((hQf i).1.1.vertexSet_mono ha) hab
    exact disjoint_left.mp (hPd hij) ((hQP i).vertexSet_mono ha)
      ((hQP j).vertexSet_mono (hba ▸ hb))
  have hX' : η.vMap '' X ⊆ Nout₂.Ω.bar := by
    rw [hOutΩ', hInΩ, hΩ₀']
    exact image_mono hX
  -- By (8.2), `(A ∪ G_2, Ω_0)` has a crooked transaction with ends in `X` and no internal vertex
  -- in `ΩBar_0`.
  obtain ⟨P₂, hcr₂, hcard₂, hends₂, hint₂⟩ := theorem_8_2_proof pi Sm Sm₂ Nout₂ (η.vMap '' X) Q'
    (fun i => η.vMap (x i)) (fun i => η.vMap (y i)) P₁ hpi1 hpi3 hcomp₂₁ hbreadth hX' hpaths hdisj
    hcr₁ hcard₁
  -- Then `P_set` is a crooked transaction in `(G, Ω_0)`.
  have hle : Sm.G ≤ S_G0.G := hSmle.trans hG0.ge
  let S_G0' : Society α β :=
    { G := S_G0.G
      Ω := Ω₀'
      finite_V := S_G0.finite_V
      finite_E := S_G0.finite_E
      bar_subset := hΩ₀'_bar ▸ S_G0.bar_subset }
  obtain ⟨hcrG', hendsG'⟩ := IsCrookedTransaction.mono (S_sup := S_G0') hle hSmΩ hcr₂
  have hcrG : S_G0.IsCrookedTransaction P₂ :=
    (isCrookedTransaction_of_eq_or_reverse (S₁ := S_G0') (S₂ := S_G0) rfl hΩ₀'_or).mp hcrG'
  have hendsG : S_G0.transactionEnds P₂ = Sm.transactionEnds P₂ :=
    (transactionEnds_of_eq_or_reverse (S₁ := S_G0') (S₂ := S_G0) rfl hΩ₀'_or P₂).symm.trans hendsG'
  have hpathsRegion : ∀ p ∈ P₂, ∃ a b : α, S_G0.IsOmegaPathWithEnds p a b ∧
      (∀ v ∈ H.V, η.vMap v ∈ V(p) → η.vMap v = a ∨ η.vMap v = b ∨ v ∈ E₁ \ C₁.U) ∧
      (∀ e ∈ H.E, η.eMap e ∈ E(p) → e ⊆ E₁ \ C₁.U) := by
    exact crooked_transaction_paths_restrict_to_first_disc (S := S) (α := α) (β := β) (H := H) (C₁
      := C₁) (E₁ := E₁) (E₂ := E₂) hbd₁ (S_G := S_G) (S₂ := S₂) (S_G0 := S_G0) (N := N) η hcomp Y
      (ν := ν) hν hη hηe hbarE₂ hΩ₀ hc₁ hs₁ hE₂sub hRG hKle hKU hηN hηEN hbarE₁ Ω₀' hΩ₀'_bar
      hnat₀' hΩ₀' Sm Nin hSmΩ hSmle hInV hIc hSmV hSmE P₂ hcr₂ hint₂ hle
  exact ⟨P₂, hcrG, hcard₂, hendsG.symm ▸ hends₂, hpathsRegion⟩

omit [T1Space S] in
/-- Graph Minors XIV, (8.4) (pages 41–42):
"Let $\Sigma$ be a closed cylinder with ends $F_1, F_2$, and let $H$ be a rigid drawing in
$\Sigma$. Let $C_1, C_2$ be disjoint circuits of $H$, both winding around $\Sigma$, and such
that $F_2$ and $U(C_2)$ both lie in the same component of $\Sigma - U(C_1)$. Let $\pi \ge 0$
with $\pi \ne 1, 3$ and let the regional distance between $U(C_1)$ and $U(C_2)$ be at least
$\pi + 4$. Let $X \subseteq V(C_1)$, and let there be $2\pi + 8$ mutually disjoint paths of
$H$ from $X$ to $V(C_2)$, each with no vertex in $C_1$ except its initial vertex. Let $H$ be
a subgraph of $G_1$, let $\mathscr{S}$ be a 3-segregation of $G_1$, and let $\alpha$ be an
arrangement of $\mathscr{S}$ in $\Sigma$ compatible with $H$. Let $\Omega_i =
\alpha^{-1}(F_i) \, (i = 1, 2)$, and let $\Omega_0$ be a natural order of $V(C_1)$ from
$U(C_1)$. Now let $(G, \Omega_1)$ be a society which is the composition of a society $(G_2,
\Omega_2)$ and the neighbourhood $(G_1, \Omega_1, \Omega_2)$, and let $(G, \Omega_1)$ have a
crooked transaction of cardinality $\ge \pi$. Then $(G, \Omega_0)$ has a crooked transaction
$\mathscr{P}$ of cardinality $\ge \pi$ such that for each $P \in \mathscr{P}$ with ends $u,
v$ say, $u, v \in X$ and $U(P \cap H) - \{u, v\}$ is included in the component of $\Sigma -
U(C_1)$ which includes $U(C_2)$." -/
theorem theorem_8_4_proof : Theorem84DiscStatement.{u, v, w} := by
  intro S _ _ _ α β H C₁ C₂ D D₂ E₁ E₂ X pi N S_seg α_disc α_pt S_G S₂ S_G0 μ P η hS hD _ hE₁ hE₂
    hD₂E₂ hE₂E₁ hE₁D hrig hC₁ hC₂ hbd₁ hbd₂ hpi1 hpi3 hdist hX hP hPd hseg harr hcompat hdiscs
    hpull₁ hpull₂ hcomp hG0 hΩ₀ hμ hnat₀ hcr
  classical
  have hman : ∀ x : S, IsManifoldPoint x := (IsClosedSurface.isSurface hS).2.2
  have hCyl : D \ discInt D₂ ⊆ D := sdiff_subset
  -- Claim (1): we pass to a smaller graph for which (1) holds, by induction on
  -- `|V(G_1)| + |E(G_1)|`.
  have hbar₁ : N.Ω.bar ⊆ segregationVertices S_seg := fun v hv => by
    rw [hpull₁.1] at hv
    exact hv.1
  have hbar₂ : N.Ω₀.bar ⊆ segregationVertices S_seg := fun v hv => by
    rw [hpull₂.1] at hv
    exact hv.1
  obtain ⟨N', S_G', η', S_seg', α_disc', -, hΩ, hΩ₂, -, hGle, hseg', harr', hcompat', hsv, -, hvm,
    hem, hdisc', hcomp', hcr', hone⟩ := exists_reduced _ S_G N η S_seg α_disc rfl hseg harr hcompat
      hbar₁ hbar₂ hcomp hcr
  have hdisc'' : ∀ S₀ ∈ S_seg', α_disc' S₀ ⊆ D \ discInt D₂ := fun S' hS' => by
    obtain ⟨S₁, hS₁, he⟩ := hdisc' S' hS'
    rw [he]
    exact hdiscs S₁ hS₁
  -- By (2) and the rigidity of `H`, we may assume that `G_1` is a drawing in `Σ`.
  obtain ⟨Y, ν, hYU, hν, hνα, hνη, hνe, hlast⟩ :=
    exists_reduced_drawing hS hD hCyl hrig hseg' harr' hcompat' hdisc'' hone
  have hYD : Y.drawing.U ⊆ D := hYU.trans (iUnion₂_subset fun S₀ h => (hdisc'' S₀ h).trans hCyl)
  have hsv' : ∀ {v : α}, v ∈ segregationVertices S_seg → ν v = α_pt v := fun {v} hv =>
    hνα v (hsv ▸ hv)
  have hbarD : ∀ v ∈ V(N'.G), ν v ∈ discBd D ↔ v ∈ N'.Ω.bar := by
    intro v hv
    rw [hΩ, hpull₁.1]
    constructor
    · intro hb
      obtain ⟨S₀, hS₀, hd, hin⟩ := hlast v hv
      have hdi := (harr'.isClosedDisc S₀ hS₀).1
      have hb' : ν v ∈ subBd (α_disc' S₀) := by
        rw [IsClosedDisc.subBd_eq_discBd hS hdi]
        exact mem_discBd_of_subset hman hdi ((hdisc'' S₀ hS₀).trans hCyl) hd hb
      have hm : v ∈ segregationVertices S_seg := by
        rw [← hsv]
        exact mem_iUnion₂.mpr ⟨S₀, hS₀, hin hb'⟩
      exact ⟨hm, hsv' hm ▸ hb⟩
    · rintro ⟨hm, hb⟩
      rw [hsv' hm]
      exact hb
  have hbarE₂ : ∀ v ∈ N'.Ω₀.bar, ν v ∈ E₂ := by
    intro v hv
    rw [hΩ₂, hpull₂.1] at hv
    rw [hsv' hv.1]
    exact hD₂E₂ (GraphMinor.Surface.discBd_subset D₂ hv.2)
  have hnat₁ : IsNaturalOrderFrom ν N'.Ω (discBd D) := by
    rw [hΩ]
    exact hpull₁.2.congr fun v hv => hsv' (hbar₁ hv)
  have hsoc : S_G0.Ω.bar ⊆ V(S_G'.G) := by
    rw [hΩ₀]
    rintro _ ⟨v, hv, rfl⟩
    have h : η'.vMap v ∈ V(N'.G) :=
      η'.imageGraph_le.vertexSet_mono (η'.gmap.bijV.mapsTo (hC₁.2.1 hv))
    rw [hvm] at h
    exact hcomp'.1.1.2.1.vertexSet_mono h
  let soc : Society α β := ⟨S_G'.G, S_G0.Ω, S_G'.finite_V, S_G'.finite_E, hsoc⟩
  have hΩ₀' : soc.Ω.bar = η'.vMap '' C₁.V := by
    rw [hvm]
    exact hΩ₀
  have hnat' : IsNaturalOrderFrom ν soc.Ω (discBd E₁) := by
    refine hnat₀.congr fun v hv => ?_
    rw [hΩ₀] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [hμ w hw, ← hvm]
    exact hνη w (hC₁.2.1 hw)
  obtain ⟨P_set, hcrs, hcard, hends, hrest⟩ := drawn_8_4 hS hD hE₁ hE₂ hC₁ hC₂ hbd₁ hbd₂
    hE₂E₁ hE₁D hpi1 hpi3 hdist hX P hP hPd (S_G0 := soc) η' hcomp' Y hν hYD hνη hνe hbarD hbarE₂
    hnat₁ hΩ₀' hnat' rfl hcr'
  -- A crooked transaction in the smaller graph is one in `G`.
  have hle : soc.G ≤ S_G0.G := hGle.trans hG0.ge
  obtain ⟨hcrG, hendsG⟩ := IsCrookedTransaction.mono hle rfl hcrs
  refine ⟨P_set, hcrG, hcard, ?_, ?_⟩
  · rw [hendsG, ← hvm]
    exact hends
  · intro p hp
    obtain ⟨a, b, hω, hv, he⟩ := hrest p hp
    refine ⟨a, b, ⟨hω.1.mono hle, hω.2.1, hω.2.2.1, hω.2.2.2⟩, ?_, ?_⟩
    · intro w hw hm
      have := hv w hw (by
        rw [hvm]
        exact hm)
      rwa [hvm] at this
    · intro e heH hm
      exact he e heH (by
        rw [hem]
        exact hm)

end GraphMinor.GM14
