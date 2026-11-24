/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section9b

/-!
# An outline gives a simulation of hearts

The inflation in an outline may use edges inside the arms of the larger painting that the outline
misses. These become groupings of the new edges of those arms.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface
open GraphMinor.GM04 (Patchwork freePatch IsGrouping IsComponent)
open GraphMinor.GM18 (ConnectedIn connectedIn_iff connectedIn_of_adj)

universe u w

variable {S : Type u} [TopologicalSpace S] {α : Type w}

/-- The grouping on `U` in which two vertices are adjacent if they are related both ways. -/
def rGroup (U : Set S) (r : S → S → Prop) : (⊤ : SimpleGraph S).Subgraph where
  verts := U
  Adj x y := x ∈ U ∧ y ∈ U ∧ x ≠ y ∧ r x y ∧ r y x
  adj_sub h := h.2.2.1
  edge_vert h := h.1
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩⟩

omit [TopologicalSpace S] in
theorem rGroup_isGrouping {U : Set S} {r : S → S → Prop}
    (ht : ∀ a b c, r a b → r b c → r a c) : IsGrouping U (rGroup U r) :=
  GM04.isGrouping_iff.mpr ⟨Subset.rfl, fun _ _ _ hac hab hbc ↦
    ⟨hab.1, hbc.2.1, hac, ht _ _ _ hab.2.2.2.1 hbc.2.2.2.1, ht _ _ _ hbc.2.2.2.2 hab.2.2.2.2⟩⟩

omit [TopologicalSpace S] in
/-- Induction along connectivity in a subgraph. -/
theorem connectedIn_induct {H : (⊤ : SimpleGraph S).Subgraph} {T : S → S → Prop}
    (hrefl : ∀ a, T a a) (htrans : ∀ a b c, T a b → T b c → T a c)
    (hadj : ∀ a b, H.Adj a b → T a b) {x y : S} (h : ConnectedIn H x y) : T x y := by
  obtain ⟨hx, hy, ⟨w⟩⟩ := connectedIn_iff.1 h
  have key : ∀ (a b : H.verts) (w : H.coe.Walk a b), T a b := by
    intro a b w
    induction w with
    | nil => exact hrefl _
    | cons hac _ ih => exact htrans _ _ _ (hadj _ _ hac) ih
  exact key _ _ w

namespace Arm

variable {Γ : Painting S} (A : Arm Γ) (r : S → S → Prop)

/-- The realization of `A⁻` grouping the ends of each edge by `r`. -/
def real : (⊤ : SimpleGraph S).Subgraph :=
  GM04.realizationOf A.minus fun f ↦ rGroup (tilde f) r

theorem real_verts : (A.real r).verts = A.minus.vertexSet :=
  GM04.realizationOf_verts fun _ he ↦ (A.minus_ends he).symm

theorem real_adj {x y : S} : (A.real r).Adj x y ↔
    ∃ f ∈ A.minus.edgeSet, (rGroup (tilde f) r).Adj x y :=
  GM04.realizationOf_adj

/-- The grouping on `πBar(A)` by connectivity in `A.real r`. -/
def group : (⊤ : SimpleGraph S).Subgraph := rGroup {v | v ∈ A.π} (ConnectedIn (A.real r))

variable {χ : ColourScheme S α}

theorem group_feasible {hd : χ.IsDisjoint} {P : ColouredPainting χ} (A : Arm P.Γ)
    (r : S → S → Prop) (ht : ∀ a b c, r a b → r b c → r a c) :
    GM18.IsFeasibleGrouping
      ((GM18.toPartialPatchwork (P.toPatchwork hd)).restrict A.toRootedHypergraph)
      (A.group r) := by
  classical
  refine ⟨rGroup_isGrouping fun _ _ _ ↦ GM18.ConnectedIn.trans, rfl, A.real r, ?_, ?_⟩
  · refine ⟨fun f ↦ rGroup (tilde f) r, fun e he ↦ ?_, rfl⟩
    have heG : e ∈ P.Γ.E := A.edge_mem he
    have hends : A.minus.ends e = tilde e := A.minus_ends he
    change rGroup (tilde e) r ∈ (if _ then _ else _ : GM04.Patch S)
    have hg : IsGrouping (tilde e) (rGroup (tilde e) r) := rGroup_isGrouping ht
    split_ifs with h
    · change _ ∈ freePatch _
      rw [P.Γ.ends_eq heG]
      exact ⟨hg, rfl⟩
    · change _ ∈ freePatch _
      change rGroup (tilde e) r ∈ freePatch (A.minus.ends e)
      rw [hends]
      exact ⟨hg, rfl⟩
  · intro x hx y hy hne
    refine ⟨fun h ↦ ⟨hx, hy, hne, h, h.symm⟩, fun h ↦ h.2.2.2.1⟩

end Arm

variable {χ : ColourScheme S α}

/-- `Q` is a completion of the heart of the `χ`-place `X`, with new edges `new`. -/
structure IsCompletedHeart (hd : χ.IsDisjoint) (X : Place χ) {Ω' : Type*} [Preorder Ω']
    (ι : ColourScheme.Colour hd ↪o Ω') (new : RootedHypergraph S (Set S) → Set S)
    (Q : Patchwork Ω' S (Set S)) : Prop where
  V_eq : Q.G.vertexSet = X.L.M.vertexSet
  E_eq : Q.G.edgeSet = X.L.M.edgeSet ∪ new '' X.L.rooted
  inj : InjOn new X.L.rooted
  fresh : ∀ A ∈ X.L.rooted, new A ∉ X.L.M.edgeSet
  roots : Q.G.roots = []
  ends_core : ∀ f ∈ X.L.M.edgeSet, Q.G.ends f = tilde f
  dom_eq : Q.dom = Q.G.edgeSet
  μ_core : ∀ f ∈ X.L.M.edgeSet, Q.μ f = X.P.Γ.γ f
  μ_new : ∀ A ∈ X.L.rooted, Q.μ (new A) = A.roots
  Δ_core : ∀ f ∈ X.L.M.edgeSet, Q.Δ f = freePatch (tilde f)
  Δ_new : ∀ A ∈ X.L.rooted, Q.Δ (new A) =
    GM18.feasibleGroupings ((GM18.toPartialPatchwork (X.P.toPatchwork hd)).restrict A)
  φ_core : ∀ f ∈ X.L.M.edgeSet, Q.φ f = ι (X.P.colour hd f)

/-- A completion of a heart of a place has the form recorded by `IsCompletedHeart`. -/
theorem isCompletedHeart_of (hd : χ.IsDisjoint) {X : Place χ} {Ω' : Type*} [Preorder Ω']
    {ι : ColourScheme.Colour hd ↪o Ω'} {new : RootedHypergraph S (Set S) → Set S}
    {H : GM18.PartialPatchwork (ColourScheme.Colour hd) S (Set S)} {Q : Patchwork Ω' S (Set S)}
    (hh : GM18.IsPlaceHeart (GM18.toPartialPatchwork (X.P.toPatchwork hd)) X.L.rooted new H)
    (hc : GM18.IsCompletion ι H Q) : IsCompletedHeart hd X ι new Q := by
  have hcore : GM18.rootedLocationCore (GM18.toPartialPatchwork (X.P.toPatchwork hd)).G
      X.L.rooted = X.L.M := X.L.core_eq
  have hV := hh.vertexSet_eq
  have hE := hh.edgeSet_eq
  have hdom := hh.dom_eq
  rw [hcore] at hV hE hdom
  have hdomG : (GM18.toPartialPatchwork (X.P.toPatchwork hd)).dom = X.P.Γ.E := rfl
  have hEdge : X.L.M.edgeSet ⊆ X.P.Γ.E := fun _ he => he.1
  rw [hdomG, inter_eq_left.mpr hEdge] at hdom
  have hmem : ∀ {f}, f ∈ X.L.M.edgeSet →
      f ∈ (GM18.rootedLocationCore (GM18.toPartialPatchwork (X.P.toPatchwork hd)).G
        X.L.rooted).edgeSet := fun {f} hf ↦ by rw [hcore]; exact hf
  have hHG : ∀ {f}, f ∈ X.L.M.edgeSet → f ∈ H.G.edgeSet := fun {f} hf ↦ by
    rw [hE]; exact Or.inl hf
  have hHN : ∀ {A}, A ∈ X.L.rooted → new A ∈ H.G.edgeSet := fun {A} hA ↦ by
    rw [hE]; exact Or.inr ⟨A, hA, rfl⟩
  refine ⟨?_, ?_, hh.injOn_newEdge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.G_eq, hV]
  · rw [hc.G_eq, hE]
  · intro A hA h
    exact hh.newEdge_notMem_core hA (hmem h)
  · rw [hc.G_eq, hh.roots_eq]
    rfl
  · intro f hf
    rw [hc.G_eq, hh.ends_core (hmem hf)]
    exact X.P.Γ.ends_eq hf.1
  · rw [hc.dom_eq, hc.G_eq, hdom, hE]
  · intro f hf
    rw [hc.μ_eq (by rw [hdom]; exact Or.inl hf), hh.μ_core ⟨hmem hf, hf.1⟩]
    rfl
  · intro A hA
    rw [hc.μ_eq (by rw [hdom]; exact Or.inr ⟨A, hA, rfl⟩), hh.μ_newEdge hA]
  · intro f hf
    rw [hc.Δ_eq (hHG hf), hh.Δ_core (hmem hf)]
    change freePatch (X.P.Γ.toHypergraph.ends f) = _
    rw [X.P.Γ.ends_eq hf.1]
  · intro A hA
    rw [hc.Δ_eq (hHN hA), hh.Δ_newEdge hA]
  · intro f hf
    exact hc.φ_eq (hHG hf) (hh.φ_core (hmem hf))

omit [TopologicalSpace S] in
/-- The march map from a free patch lands in the free patch. -/
theorem marchMap_free {π π' : List S} (hπ : π.Nodup) (hπ' : π'.Nodup)
    (hlen : π.length = π'.length) {U U' : Set S} (hU : {v | v ∈ π} = U)
    (hU' : {v | v ∈ π'} = U') : MapsTo (GM04.marchMapSubgraph π π') (freePatch U).groupings
      (freePatch U').groupings := by
  intro δ hδ
  have hδv : δ.verts = U := hδ.2
  have hcorr : ∀ {x x' y}, GM04.MarchCorresponds π π' x y → GM04.MarchCorresponds π π' x' y →
      x = x' := by
    rintro x x' y ⟨i, hi, hi', rfl, h⟩ ⟨j, hj, hj', rfl, h'⟩
    have hij : i = j := (List.Nodup.getElem_inj_iff hπ').1 (h.trans h'.symm)
    subst hij
    rfl
  have hv : (GM04.marchMapSubgraph π π' δ).verts = U' := by
    ext y
    constructor
    · rintro ⟨x, -, i, hi, hi', -, rfl⟩
      rw [← hU']
      exact List.getElem_mem hi'
    · intro hy
      rw [← hU'] at hy
      obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.1 hy
      have hi : i < π.length := hlen ▸ hi'
      refine ⟨π[i], ?_, i, hi, hi', rfl, rfl⟩
      rw [hδv, ← hU]
      exact List.getElem_mem hi
  refine ⟨GM04.isGrouping_iff.mpr ⟨hv.subset, ?_⟩, hv⟩
  rintro a b c hac ⟨hab, x₁, x₂, h₁, h₂, hadj⟩ ⟨hbc, x₂', x₃, h₂', h₃, hadj'⟩
  have hx : x₂ = x₂' := hcorr h₂ h₂'
  subst hx
  have hne : x₁ ≠ x₃ := by
    rintro rfl
    obtain ⟨i, hi, hi', rfl, rfl⟩ := h₁
    obtain ⟨j, hj, hj', hij, rfl⟩ := h₃
    have : j = i := (List.Nodup.getElem_inj_iff hπ).1 hij
    subst this
    exact hac rfl
  exact ⟨hac, x₁, x₃, h₁, h₃, (GM04.isGrouping_iff.1 hδ.1).2 _ _ _ hne hadj hadj'⟩

private theorem realization_of_outline {X Y : Place χ} {τ : Arm X.P.Γ → Arm Y.P.Γ}
    {hd : χ.IsDisjoint} {Ω' : Type*} [Preorder Ω'] {ι : ColourScheme.Colour hd ↪o Ω'}
    {new₂ : RootedHypergraph S (Set S) → Set S} {Q₁ Q₂ : Patchwork Ω' S (Set S)}
    (h₂ : IsCompletedHeart hd Y ι new₂ Q₂)
    {σv : S → Set S} {σe ηe : Set S → Set S}
    (hσ : IsSubInflationIn X.P.Γ X.L.M Y.P.Γ σv σe)
    (hmem : ∀ A ∈ X.L.arms, τ A ∈ Y.L.arms)
    (hEM : ∀ f ∈ X.L.M.edgeSet, σe f ∈ Y.L.M.edgeSet)
    (hcap : ∀ A ∈ X.L.arms, ∀ v ∈ X.L.M.vertexSet, (σv v ∩ (τ A).V).ncard ≤ 1)
    {new₁ : RootedHypergraph S (Set S) → Set S}
    (hηc : ∀ f ∈ X.L.M.edgeSet, ηe f = σe f)
    (hηn : ∀ A ∈ X.L.arms, ηe (new₁ A.toRootedHypergraph) = new₂ (τ A).toRootedHypergraph)
    (hE₁ : ∀ {P : Set S → Prop}, (∀ f ∈ X.L.M.edgeSet, P f) →
      (∀ A ∈ X.L.arms, P (new₁ A.toRootedHypergraph)) → ∀ f ∈ Q₁.G.edgeSet, P f)
    (hlen : ∀ g ∈ X.L.M.edgeSet, (X.P.Γ.γ g).length = (Y.P.Γ.γ (σe g)).length)
    (hhave : ∀ v ∈ X.L.M.vertexSet, ∃ x₀, x₀ ∈ σv v ∧ x₀ ∈ Y.L.M.vertexSet) :
    ∃ H, (Q₂.deleteEdges (ηe '' Q₁.G.edgeSet)).IsRealization H ∧
      ∀ v ∈ X.L.M.vertexSet, ∃ D, IsComponent H D ∧ D.verts = σv v ∩ Y.L.M.vertexSet := by
  classical
  let r : S → S → Prop := fun x y ↦ ∃ v ∈ X.L.M.vertexSet, x ∈ σv v ∧ y ∈ σv v
  have hdisj : ∀ {x v v'}, v ∈ X.L.M.vertexSet → v' ∈ X.L.M.vertexSet → x ∈ σv v → x ∈ σv v' →
      v = v' := by
    intro x v v' hv hv' hx hx'
    by_contra hne
    exact disjoint_left.1 (hσ.vertex_disjoint v hv v' hv' hne) hx hx'
  have hrt : ∀ a b c, r a b → r b c → r a c := by
    rintro a b c ⟨v, hv, ha, hb⟩ ⟨v', hv', hb', hc⟩
    obtain rfl := hdisj hv hv' hb hb'
    exact ⟨v, hv, ha, hc⟩
  have hrs : ∀ a b, r a b → r b a := fun a b ⟨v, hv, ha, hb⟩ ↦ ⟨v, hv, hb, ha⟩
  let F : Set (Set S) := ηe '' Q₁.G.edgeSet
  let U : Set (Arm Y.P.Γ) := {A' ∈ Y.L.arms | ∀ A ∈ X.L.arms, τ A ≠ A'}
  let δ : Set S → (⊤ : SimpleGraph S).Subgraph := fun f ↦
    if h : ∃ A' ∈ Y.L.arms, new₂ A'.toRootedHypergraph = f then h.choose.group r
    else rGroup (tilde f) r
  have hδc : ∀ f ∈ Y.L.M.edgeSet, δ f = rGroup (tilde f) r := by
    intro f hf
    refine dite_eq_right ?_
    rintro ⟨A', hA', rfl⟩
    exact h₂.fresh _ ⟨A', hA', rfl⟩ hf
  have hδn : ∀ A' ∈ Y.L.arms, δ (new₂ A'.toRootedHypergraph) = A'.group r := by
    intro A' hA'
    have hex : ∃ B ∈ Y.L.arms, new₂ B.toRootedHypergraph = new₂ A'.toRootedHypergraph :=
      ⟨A', hA', rfl⟩
    have hch := hex.choose_spec
    have hc : hex.choose = A' :=
      Arm.toRooted_injective (h₂.inj ⟨_, hch.1, rfl⟩ ⟨_, hA', rfl⟩ hch.2)
    simp only [δ, dite_eq_left hex, hc]
  have hreal : (Q₂.deleteEdges F).IsRealization
      (GM04.realizationOf (Q₂.deleteEdges F).G.toHypergraph δ) := by
    refine ⟨δ, fun e he ↦ ?_, rfl⟩
    have he' : e ∈ Q₂.G.edgeSet := he.1
    change δ e ∈ Q₂.Δ e
    rw [h₂.E_eq] at he'
    rcases he' with hc | ⟨_, ⟨A', hA', rfl⟩, rfl⟩
    · rw [hδc e hc, h₂.Δ_core e hc]
      exact ⟨rGroup_isGrouping hrt, rfl⟩
    · rw [hδn A' hA', h₂.Δ_new _ ⟨A', hA', rfl⟩]
      exact A'.group_feasible r hrt
  set H := GM04.realizationOf (Q₂.deleteEdges F).G.toHypergraph δ with hHdef
  have hHverts : H.verts = Y.L.M.vertexSet := hreal.verts_eq.trans h₂.V_eq
  have hnewF : ∀ A' ∈ U, new₂ A'.toRootedHypergraph ∉ F := by
    rintro A' hA' ⟨f, hf, hfe⟩
    refine (hE₁ (P := fun f ↦ ηe f ≠ new₂ A'.toRootedHypergraph) ?_ ?_ f hf) hfe
    · intro f hf h
      rw [hηc f hf] at h
      exact h₂.fresh _ ⟨A', hA'.1, rfl⟩ (h ▸ hEM f hf)
    · intro A hA h
      rw [hηn A hA] at h
      exact hA'.2 A hA (Arm.toRooted_injective
        (h₂.inj ⟨_, hmem A hA, rfl⟩ ⟨_, hA'.1, rfl⟩ h))
  have hcoreF : ∀ f ∈ Y.L.M.edgeSet, ∀ x y, x ∈ tilde f → y ∈ tilde f → x ≠ y → r x y →
      f ∉ F := by
    rintro f hf x y hx hy hne ⟨v, hv, hxv, hyv⟩ ⟨g, hg, rfl⟩
    refine hE₁ (P := fun g ↦ x ∈ tilde (ηe g) → y ∈ tilde (ηe g) → ηe g ∈ Y.L.M.edgeSet → False)
      ?_ ?_ g hg hx hy hf
    · intro g hg hx hy _
      rw [hηc g hg] at hx hy
      have hgE := hσ.edge_mem g hg
      have hxm : x ∈ Y.P.Γ.γ (σe g) := by
        have : x ∈ {v | v ∈ Y.P.Γ.γ (σe g)} := by rw [Y.P.Γ.γ_set _ hgE]; exact hx
        exact this
      have hym : y ∈ Y.P.Γ.γ (σe g) := by
        have : y ∈ {v | v ∈ Y.P.Γ.γ (σe g)} := by rw [Y.P.Γ.γ_set _ hgE]; exact hy
        exact this
      obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.1 hxm
      obtain ⟨j, hj', rfl⟩ := List.mem_iff_getElem.1 hym
      have hi : i < (X.P.Γ.γ g).length := by rw [hlen g hg]; exact hi'
      have hj : j < (X.P.Γ.γ g).length := by rw [hlen g hg]; exact hj'
      have hγ : ∀ {k} (hk : k < (X.P.Γ.γ g).length), (X.P.Γ.γ g)[k] ∈ X.L.M.vertexSet := by
        intro k hk
        refine RootedLocation.tilde_mem_M hg ?_
        rw [← X.P.Γ.γ_set g hg.1]
        exact List.getElem_mem hk
      have h₁' := hdisj (hγ hi) hv (hσ.ends g hg i hi hi') hxv
      have h₂' := hdisj (hγ hj) hv (hσ.ends g hg j hj hj') hyv
      have hij : i = j := (List.Nodup.getElem_inj_iff (X.P.Γ.γ_nodup g hg.1)).1 (h₁'.trans h₂'.symm)
      subst hij
      exact hne rfl
    · intro A hA _ _ h
      rw [hηn A hA] at h
      exact h₂.fresh _ ⟨_, hmem A hA, rfl⟩ h
  have hHadj₁ : ∀ f ∈ Y.L.M.edgeSet, ∀ x y, x ∈ tilde f → y ∈ tilde f → x ≠ y → r x y →
      H.Adj x y := by
    intro f hf x y hx hy hne hr
    refine GM04.realizationOf_adj.2 ⟨f, ⟨?_, hcoreF f hf x y hx hy hne hr⟩, ?_⟩
    · rw [h₂.E_eq]
      exact Or.inl hf
    · rw [hδc f hf]
      exact ⟨hx, hy, hne, hr, hrs _ _ hr⟩
  have hHadj₂ : ∀ A' ∈ U, ∀ x y, x ∈ A'.π → y ∈ A'.π → x ≠ y →
      ConnectedIn (A'.real r) x y → H.Adj x y := by
    intro A' hA' x y hx hy hne hc
    refine GM04.realizationOf_adj.2 ⟨new₂ A'.toRootedHypergraph, ⟨?_, hnewF A' hA'⟩, ?_⟩
    · rw [h₂.E_eq]
      exact Or.inr ⟨_, ⟨A', hA'.1, rfl⟩, rfl⟩
    · rw [hδn A' hA'.1]
      exact ⟨hx, hy, hne, hc, hc.symm⟩
  let T : S → S → Prop := fun a b ↦ a = b ∨ r a b
  have hTr : ∀ a, T a a := fun _ ↦ Or.inl rfl
  have hTt : ∀ a b c, T a b → T b c → T a c := by
    rintro a b c (rfl | h₁') h₂'
    · exact h₂'
    · exact Or.inr (h₂'.elim (fun h => h ▸ h₁') (hrt _ _ _ h₁'))
  have hHT : ∀ a b, H.Adj a b → T a b := by
    intro a b hab
    obtain ⟨f, hf, hAdj⟩ := GM04.realizationOf_adj.1 hab
    have hf' : f ∈ Q₂.G.edgeSet := hf.1
    rw [h₂.E_eq] at hf'
    rcases hf' with hc | ⟨_, ⟨A', hA', rfl⟩, rfl⟩
    · rw [hδc f hc] at hAdj
      exact Or.inr hAdj.2.2.2.1
    · rw [hδn A' hA'] at hAdj
      refine connectedIn_induct hTr hTt (fun a b h ↦ ?_) hAdj.2.2.2.1
      obtain ⟨f, -, hg⟩ := (A'.real_adj r).1 h
      exact Or.inr hg.2.2.2.1
  have hup : ∀ A' ∈ U, ∀ z x, z ∈ A'.π → x ∈ A'.π → ConnectedIn (A'.real r) z x →
      ConnectedIn H z x := by
    intro A' hA' z x hz hx hc
    by_cases hzx : z = x
    · subst hzx
      refine GM18.ConnectedIn.refl ?_
      rw [hHverts]
      exact RootedLocation.π_mem_M hA'.1 hz
    · exact connectedIn_of_adj (hHadj₂ A' hA' z x hz hx hzx hc)
  have hfinσ : ∀ v ∈ X.L.M.vertexSet, (σv v).Finite := fun v hv ↦
    Y.P.Γ.finite_V.subset (hσ.vertex_subset v hv)
  have hclaim : ∀ v ∈ X.L.M.vertexSet, ∀ x₀ ∈ σv v, x₀ ∈ Y.L.M.vertexSet →
      ∀ y ∈ σv v, y ∈ Y.L.M.vertexSet → ConnectedIn H x₀ y := by
    intro v hv x₀ hx₀ hx₀M y hy hyM
    let Inv : S → Prop := fun x ↦ (x ∈ Y.L.M.vertexSet ∧ ConnectedIn H x₀ x) ∨
      ∃ A' ∈ U, x ∈ A'.minus.vertexSet ∧ ∃ z ∈ A'.π, ConnectedIn H x₀ z ∧
        ConnectedIn (A'.real r) z x
    have hsimp : ∀ {x}, Inv x → x ∈ Y.L.M.vertexSet → ConnectedIn H x₀ x := by
      rintro x (h | ⟨A', hA', hxA, z, hz, hc₁, hc₂⟩) hxM
      · exact h.2
      · exact hc₁.trans (hup A' hA' z x hz (RootedLocation.mem_π_of_M hA'.1 hxM hxA) hc₂)
    have hstep : ∀ a b, a ∈ σv v → b ∈ σv v → Y.P.Γ.skAdj.Adj a b → Inv a → Inv b := by
      rintro a b ha hb ⟨hne, -, -, e, he, hae, hbe⟩ hInv
      have hrab : r a b := ⟨v, hv, ha, hb⟩
      by_cases heM : e ∈ Y.L.M.edgeSet
      · have haM := RootedLocation.tilde_mem_M heM hae
        have hbM := RootedLocation.tilde_mem_M heM hbe
        exact Or.inl ⟨hbM, (hsimp hInv haM).trans
          (connectedIn_of_adj (hHadj₁ e heM a b hae hbe hne hrab))⟩
      · obtain ⟨A', hA', heA'⟩ := RootedLocation.exists_arm_of_notMem he heM
        have haA := A'.minus_end heA' hae
        have hbA := A'.minus_end heA' hbe
        have hU : A' ∈ U := by
          refine ⟨hA', fun A hA hEq ↦ hne ?_⟩
          subst hEq
          exact (ncard_le_one ((hfinσ v hv).subset inter_subset_left)).1 (hcap A hA v hv)
            a ⟨ha, haA⟩ b ⟨hb, hbA⟩
        have hab : ConnectedIn (A'.real r) a b := connectedIn_of_adj
          ((A'.real_adj r).2 ⟨e, heA', hae, hbe, hne, hrab, hrs _ _ hrab⟩)
        have hleft : a ∈ Y.L.M.vertexSet → ConnectedIn H x₀ a → Inv b := fun haM hc ↦
          Or.inr ⟨A', hU, hbA, a, RootedLocation.mem_π_of_M hA' haM haA, hc, hab⟩
        rcases hInv with ⟨haM, hc⟩ | ⟨A'', hA'', haA'', z, hz, hc₁, hc₂⟩
        · exact hleft haM hc
        · by_cases haπ : a ∈ A''.π
          · have haM := RootedLocation.π_mem_M hA''.1 haπ
            exact hleft haM (hc₁.trans (hup A'' hA'' z a hz haπ hc₂))
          · have heA'' : e ∈ A''.minus.edgeSet := (A''.edge_or he).resolve_right fun hc ↦
              haπ (A''.mem_π.2 ⟨haA'', A''.compl_end hc hae⟩)
            obtain rfl := RootedLocation.eq_of_edge hA' hA''.1 heA' heA''
            exact Or.inr ⟨A', hU, hbA, z, hz, hc₁, hc₂.trans hab⟩
    have hwalk : ∀ (a b : σv v) (w : (Y.P.Γ.skAdj.induce (σv v)).Walk a b), Inv a → Inv b := by
      intro a b w
      induction w with
      | nil => exact id
      | cons hac _ ih => exact fun h ↦ ih (hstep _ _ (Subtype.coe_prop _)
        (Subtype.coe_prop _) hac h)
    obtain ⟨w⟩ := hσ.vertex_connected v hv ⟨x₀, hx₀⟩ ⟨y, hy⟩
    refine hsimp (hwalk _ _ w (Or.inl ⟨hx₀M, GM18.ConnectedIn.refl ?_⟩)) hyM
    rw [hHverts]
    exact hx₀M
  have hcomp : ∀ v ∈ X.L.M.vertexSet, ∃ D, IsComponent H D ∧ D.verts = σv v ∩ Y.L.M.vertexSet := by
    intro v hv
    obtain ⟨x₀, hx, hxM⟩ := hhave v hv
    let x : H.verts := ⟨x₀, by rw [hHverts]; exact hxM⟩
    refine ⟨GM04.component H x, ⟨x, rfl⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hre⟩
      have hyM : y ∈ Y.L.M.vertexSet := hHverts ▸ hy
      refine ⟨?_, hyM⟩
      have hc : ConnectedIn H x₀ y := connectedIn_iff.2 ⟨x.2, hy, hre⟩
      rcases connectedIn_induct hTr hTt hHT hc with rfl | ⟨v', hv', h₁', h₂'⟩
      · exact hx
      · obtain rfl := hdisj hv hv' hx h₁'
        exact h₂'
    · rintro ⟨hy, hyM⟩
      obtain ⟨hx', hy', hre⟩ := connectedIn_iff.1 (hclaim v hv x₀ hx hxM y hy hyM)
      exact ⟨hy', hre⟩
  exact ⟨H, hreal, hcomp⟩

/-- **An outline gives a simulation.** An outline of `X` in `Y` whose arms are matched in colour and
in their patches gives a simulation of a completion of the heart of `X` in one of the heart of
`Y`. -/
theorem simulated_of_outline (hd : χ.IsDisjoint) {X Y : Place χ} {τ : Arm X.P.Γ → Arm Y.P.Γ}
    (hτ : IsOutline X Y τ) {Ω' : Type*} [Preorder Ω'] {ι : ColourScheme.Colour hd ↪o Ω'}
    {new₁ new₂ : RootedHypergraph S (Set S) → Set S} {Q₁ Q₂ : Patchwork Ω' S (Set S)}
    (h₁ : IsCompletedHeart hd X ι new₁ Q₁) (h₂ : IsCompletedHeart hd Y ι new₂ Q₂)
    (hinc : ∀ v ∈ X.P.Γ.V, ∃ c ∈ X.P.Γ.E, v ∈ tilde c)
    (hφ : ∀ A ∈ X.L.arms, Q₁.φ (new₁ A.toRootedHypergraph) ≤ Q₂.φ (new₂ (τ A).toRootedHypergraph))
    (hΔ : ∀ A ∈ X.L.arms, MapsTo (GM04.marchMapSubgraph A.π (τ A).π)
      (Q₁.Δ (new₁ A.toRootedHypergraph)).groupings
      (Q₂.Δ (new₂ (τ A).toRootedHypergraph)).groupings) :
    GM04.Simulated Q₁ Q₂ := by
  classical
  obtain ⟨hmem, hinj, σv, σe, hσ, hEM, hπ, hcap, hcol⟩ := hτ
  let ηe : Set S → Set S := fun f ↦
    if f ∈ X.L.M.edgeSet then σe f else
      if h : ∃ A ∈ X.L.arms, new₁ A.toRootedHypergraph = f then
        new₂ (τ h.choose).toRootedHypergraph else f
  have hηc : ∀ f ∈ X.L.M.edgeSet, ηe f = σe f := fun f hf ↦ ite_eq_left hf
  have hηn : ∀ A ∈ X.L.arms, ηe (new₁ A.toRootedHypergraph) =
      new₂ (τ A).toRootedHypergraph := by
    intro A hA
    have hn := h₁.fresh _ ⟨A, hA, rfl⟩
    have hex : ∃ B ∈ X.L.arms, new₁ B.toRootedHypergraph = new₁ A.toRootedHypergraph :=
      ⟨A, hA, rfl⟩
    have hch := hex.choose_spec
    have hc : hex.choose = A :=
      Arm.toRooted_injective (h₁.inj ⟨_, hch.1, rfl⟩ ⟨_, hA, rfl⟩ hch.2)
    simp only [ηe, ite_eq_right hn, dite_eq_left hex, hc]
  have hE₁ : ∀ {P : Set S → Prop}, (∀ f ∈ X.L.M.edgeSet, P f) →
      (∀ A ∈ X.L.arms, P (new₁ A.toRootedHypergraph)) → ∀ f ∈ Q₁.G.edgeSet, P f := by
    intro P h₁' h₂' f hf
    rw [h₁.E_eq] at hf
    rcases hf with hf | ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · exact h₁' f hf
    · exact h₂' A hA
  have hlen : ∀ g ∈ X.L.M.edgeSet, (X.P.Γ.γ g).length = (Y.P.Γ.γ (σe g)).length := by
    intro g hg
    rw [X.P.Γ.length_γ hg.1, Y.P.Γ.length_γ (hσ.edge_mem g hg), hσ.edge_size g hg]
  have hhave : ∀ v ∈ X.L.M.vertexSet, ∃ x₀, x₀ ∈ σv v ∧ x₀ ∈ Y.L.M.vertexSet := by
    intro v hv
    obtain ⟨c, hc, hvc⟩ := hinc v hv.1
    by_cases hcM : c ∈ X.L.M.edgeSet
    · have hvm : v ∈ X.P.Γ.γ c := by
        have : v ∈ {v | v ∈ X.P.Γ.γ c} := by rw [X.P.Γ.γ_set c hc]; exact hvc
        exact this
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hvm
      have hi' : i < (Y.P.Γ.γ (σe c)).length := by rw [← hlen c hcM]; exact hi
      refine ⟨_, hσ.ends c hcM i hi hi', RootedLocation.tilde_mem_M (hEM c hcM) ?_⟩
      rw [← Y.P.Γ.γ_set _ (hσ.edge_mem c hcM)]
      exact List.getElem_mem hi'
    · obtain ⟨A, hA, hcA⟩ := RootedLocation.exists_arm_of_notMem hc hcM
      have hvπ : v ∈ A.π := RootedLocation.mem_π_of_M hA hv (A.minus_end hcA hvc)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hvπ
      have hi' : i < (τ A).π.length := by rw [(hπ A hA).1]; exact hi
      exact ⟨_, (hπ A hA).2 i hi hi', RootedLocation.π_mem_M (hmem A hA) (List.getElem_mem hi')⟩
  obtain ⟨H, hreal, hcomp⟩ :=
    realization_of_outline h₂ hσ hmem hEM hcap hηc hηn hE₁ hlen hhave
  have hedge : ∀ e ∈ Q₁.G.edgeSet, ηe e ∈ Q₂.G.edgeSet := by
    refine hE₁ (fun f hf ↦ ?_) fun A hA ↦ ?_
    · rw [hηc f hf, h₂.E_eq]
      exact Or.inl (hEM f hf)
    · rw [hηn A hA, h₂.E_eq]
      exact Or.inr ⟨_, ⟨_, hmem A hA, rfl⟩, rfl⟩
  have hexp : GM04.IsExpansion Q₁ Q₂ (fun v ↦ σv v ∩ Y.L.M.vertexSet) ηe := by
    refine ⟨fun v hv ↦ ?_, fun v hv x hx ↦ ?_, hedge, fun v₁ h₁' v₂ h₂' hne ↦ ?_, ?_,
      fun e he ↦ ?_, fun e he hn ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h₁.V_eq] at hv
      exact hhave v hv
    · rw [h₂.V_eq]
      exact hx.2
    · rw [h₁.V_eq] at h₁' h₂'
      exact (hσ.vertex_disjoint v₁ h₁' v₂ h₂' hne).mono inter_subset_left inter_subset_left
    · intro e₁ he₁ e₂ he₂ heq
      have hη : ∀ {f}, f ∈ X.L.M.edgeSet → ∀ {A}, A ∈ X.L.arms →
          ηe f ≠ ηe (new₁ A.toRootedHypergraph) := by
        intro f hf A hA h
        rw [hηc f hf, hηn A hA] at h
        exact h₂.fresh _ ⟨_, hmem A hA, rfl⟩ (h ▸ hEM f hf)
      rw [h₁.E_eq] at he₁ he₂
      rcases he₁ with he₁ | ⟨_, ⟨A₁, hA₁, rfl⟩, rfl⟩ <;>
        rcases he₂ with he₂ | ⟨_, ⟨A₂, hA₂, rfl⟩, rfl⟩
      · rw [hηc _ he₁, hηc _ he₂] at heq
        exact hσ.edge_injOn he₁ he₂ heq
      · exact absurd heq (hη he₁ hA₂)
      · exact absurd heq.symm (hη he₂ hA₁)
      · rw [hηn _ hA₁, hηn _ hA₂] at heq
        have := Arm.toRooted_injective
          (h₂.inj ⟨_, hmem _ hA₁, rfl⟩ ⟨_, hmem _ hA₂, rfl⟩ heq)
        rw [hinj hA₁ hA₂ this]
    · rw [h₁.dom_eq, h₂.dom_eq]
      exact iff_of_true he (hedge e he)
    · exact absurd (h₁.dom_eq ▸ he : e ∈ Q₁.dom) hn
    · rw [h₁.dom_eq]
      refine hE₁ (fun f hf ↦ ?_) fun A hA ↦ ?_
      · rw [hηc f hf, h₁.μ_core f hf, h₂.μ_core _ (hEM f hf)]
        exact hlen f hf
      · rw [hηn A hA, h₁.μ_new _ ⟨A, hA, rfl⟩, h₂.μ_new _ ⟨_, hmem A hA, rfl⟩]
        exact (hπ A hA).1.symm
    · rw [h₁.dom_eq]
      refine hE₁ (fun f hf i hi hi' ↦ ?_) fun A hA i hi hi' ↦ ?_
      · have hμ₁ := h₁.μ_core f hf
        have hμ₂ : Q₂.μ (ηe f) = Y.P.Γ.γ (σe f) := by
          rw [hηc f hf]
          exact h₂.μ_core _ (hEM f hf)
        simp only [hμ₁, hμ₂] at hi hi' ⊢
        refine ⟨hσ.ends f hf i hi hi', RootedLocation.tilde_mem_M (hEM f hf) ?_⟩
        rw [← Y.P.Γ.γ_set _ (hσ.edge_mem f hf)]
        exact List.getElem_mem hi'
      · have hμ₁ : Q₁.μ (new₁ A.toRootedHypergraph) = A.π := h₁.μ_new _ ⟨A, hA, rfl⟩
        have hμ₂ : Q₂.μ (ηe (new₁ A.toRootedHypergraph)) = (τ A).π := by
          rw [hηn A hA]
          exact h₂.μ_new _ ⟨_, hmem A hA, rfl⟩
        simp only [hμ₁, hμ₂] at hi hi' ⊢
        exact ⟨(hπ A hA).2 i hi hi', RootedLocation.π_mem_M (hmem A hA) (List.getElem_mem hi')⟩
    · rw [h₁.roots, h₂.roots]
    · intro i hi
      simp [h₁.roots] at hi
    · rw [h₁.dom_eq]
      refine hE₁ (fun f hf ↦ ?_) fun A hA ↦ ?_
      · rw [hηc f hf, h₁.μ_core f hf, h₂.μ_core _ (hEM f hf), h₁.Δ_core f hf,
          h₂.Δ_core _ (hEM f hf)]
        exact marchMap_free (X.P.Γ.γ_nodup f hf.1) (Y.P.Γ.γ_nodup _ (hσ.edge_mem f hf)) (hlen f hf)
          (X.P.Γ.γ_set f hf.1) (Y.P.Γ.γ_set _ (hσ.edge_mem f hf))
      · rw [hηn A hA, h₁.μ_new _ ⟨A, hA, rfl⟩, h₂.μ_new _ ⟨_, hmem A hA, rfl⟩]
        exact hΔ A hA
    · refine hE₁ (fun f hf ↦ ?_) fun A hA ↦ ?_
      · rw [hηc f hf, h₁.φ_core f hf, h₂.φ_core _ (hEM f hf)]
        refine ι.le_iff_le.2 ?_
        change (χ.unionWQO hd).le (X.P.colour hd f).1 (Y.P.colour hd (σe f)).1
        rw [X.P.colour_val hd hf.1, Y.P.colour_val hd (hσ.edge_mem f hf)]
        exact hcol f hf
      · rw [hηn A hA]
        exact hφ A hA
  exact ⟨fun v ↦ σv v ∩ Y.L.M.vertexSet, ηe, hexp, H, hreal, fun v hv ↦
    hcomp v (h₁.V_eq ▸ hv)⟩

end GraphMinor.GM19
