/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Section7a

/-!
# Graph Minors XIV, Section 7: Proof of (7.8)

This file formalizes (7.8) (`theorem_7_8`, pages 38–39) of Robertson and Seymour,
*Graph Minors. XIV. Extending an embedding*, J. Combin. Theory Ser. B 65 (1995), 23–50.
-/

public section

namespace GraphMinor.GM14

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM09 GM10 GM11

universe u v w

variable {S : Type u} [TopologicalSpace S]

/-! ## Helper Lemmas on Disjoint Families and Subdrawings -/

/-- If two subdrawings `Γ₁, Γ₂` of `H` have disjoint vertex sets, then their point sets `Γ₁.U` and
`Γ₂.U` are disjoint. -/
theorem disjoint_U_of_disjoint_V {H Γ₁ Γ₂ : Drawing S}
    (h₁ : Γ₁.IsSubdrawing H) (h₂ : Γ₂.IsSubdrawing H) (hdis : Disjoint Γ₁.V Γ₂.V) :
    Disjoint Γ₁.U Γ₂.U := by
  refine disjoint_left.mpr fun x hx₁ hx₂ => ?_
  by_cases hxV₁ : x ∈ Γ₁.V
  · by_cases hxV₂ : x ∈ Γ₂.V
    · exact disjoint_left.mp hdis hxV₁ hxV₂
    · obtain ⟨e₂, he₂, hxe₂⟩ := Γ₂.exists_edge_of_mem hx₂ hxV₂
      exact ((h₂.2 he₂).2.1 hxe₂).2 (h₁.1 hxV₁)
  · obtain ⟨e₁, he₁, hxe₁⟩ := Γ₁.exists_edge_of_mem hx₁ hxV₁
    by_cases hxV₂ : x ∈ Γ₂.V
    · exact ((h₁.2 he₁).2.1 hxe₁).2 (h₂.1 hxV₂)
    · obtain ⟨e₂, he₂, hxe₂⟩ := Γ₂.exists_edge_of_mem hx₂ hxV₂
      have he₁H : e₁ ∈ H.E := h₁.2 he₁
      have he₂H : e₂ ∈ H.E := h₂.2 he₂
      have heq : e₁ = e₂ := H.edge_eq_of_mem he₁H he₂H hxe₁ hxe₂
      obtain ⟨a, b, _, haV₁, _, hcap₁⟩ := (Γ₁.toGraph.edge_mem_iff_exists_isLink e₁).mp he₁
      have ha_cl : a ∈ closure e₁ := by
        have : a ∈ closure e₁ ∩ Γ₁.V := hcap₁ ▸ mem_insert a {b}
        exact this.1
      have haV₂ : a ∈ Γ₂.V := by
        have haU₂ : a ∈ Γ₂.U := Γ₂.closure_subset_U (heq ▸ he₂) (heq ▸ ha_cl)
        by_contra haV₂
        obtain ⟨f, hf, haf⟩ := Γ₂.exists_edge_of_mem haU₂ haV₂
        exact ((h₂.2 hf).2.1 haf).2 (h₁.1 haV₁)
      exact disjoint_left.mp hdis haV₁ haV₂

/-- If two subdrawings `Γ₁, Γ₂` of `H` have intersecting point sets `(Γ₁.U ∩ Γ₂.U).Nonempty`, then
their vertex sets intersect `(Γ₁.V ∩ Γ₂.V).Nonempty`. -/
theorem nonempty_inter_V_of_nonempty_inter_U {H Γ₁ Γ₂ : Drawing S}
    (h₁ : Γ₁.IsSubdrawing H) (h₂ : Γ₂.IsSubdrawing H) (hne : (Γ₁.U ∩ Γ₂.U).Nonempty) :
    (Γ₁.V ∩ Γ₂.V).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hempty
  obtain ⟨x, hx₁, hx₂⟩ := hne
  exact disjoint_left.mp (disjoint_U_of_disjoint_V h₁ h₂ hempty) hx₁ hx₂

/-- Pigeonhole principle for pairwise disjoint sets: if `P : Fin m → Set α` is pairwise disjoint
and `X` is a finite set with `X.ncard < m`, then some `P j` is disjoint from `X`. -/
theorem exists_disjoint_of_ncard_lt {α : Type*} {m : ℕ} {P : Fin m → Set α} {X : Set α}
    (hdis : Pairwise (fun j₁ j₂ => Disjoint (P j₁) (P j₂))) (hfin : X.Finite)
    (hlt : X.ncard < m) :
    ∃ j : Fin m, Disjoint (P j) X := by
  by_contra hno
  push Not at hno
  have hex : ∀ j : Fin m, ∃ x, x ∈ P j ∧ x ∈ X := fun j =>
    not_disjoint_iff.mp (hno j)
  choose f hfP hfX using hex
  have hinj : Injective f := by
    intro j₁ j₂ hfj
    by_contra hne
    exact disjoint_left.mp (hdis hne) (hfP j₁) (hfj ▸ hfP j₂)
  have hle : (range f).ncard ≤ X.ncard :=
    ncard_le_ncard (range_subset_iff.mpr hfX) hfin
  rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

/-- Pigeonhole principle for pairs in pairwise disjoint sets: if `C : Fin m → Set α` is pairwise
disjoint and `X` is a finite set with `X.ncard < 2 * m`, then some `C i ∩ X` has cardinality
`≤ 1`. -/
theorem exists_inter_ncard_le_one_of_ncard_lt_two_mul {α : Type*} {m : ℕ}
    {C : Fin m → Set α} {X : Set α}
    (hdis : Pairwise (fun i₁ i₂ => Disjoint (C i₁) (C i₂))) (hfin : X.Finite)
    (hlt : X.ncard < 2 * m) :
    ∃ i : Fin m, (C i ∩ X).ncard ≤ 1 := by
  by_contra hno
  push Not at hno
  have hex : ∀ i : Fin m, ∃ x ∈ C i ∩ X, ∃ y ∈ C i ∩ X, x ≠ y := fun i =>
    (one_lt_ncard (hfin.subset inter_subset_right)).mp (hno i)
  choose f hf g hg hne using hex
  let fg : Fin m ⊕ Fin m → α := Sum.elim f g
  have hinj : Injective fg := by
    rintro (i₁ | i₁) (i₂ | i₂) heq
    · change f i₁ = f i₂ at heq
      congr 1
      by_contra hne_i
      exact Set.disjoint_left.mp (hdis hne_i) (hf i₁).1 (heq ▸ (hf i₂).1)
    · change f i₁ = g i₂ at heq
      exfalso
      have hi : i₁ = i₂ := by
        by_contra hne_i
        exact Set.disjoint_left.mp (hdis hne_i) (hf i₁).1 (heq ▸ (hg i₂).1)
      subst hi
      exact hne i₁ heq
    · change g i₁ = f i₂ at heq
      exfalso
      have hi : i₁ = i₂ := by
        by_contra hne_i
        exact Set.disjoint_left.mp (hdis hne_i) (hg i₁).1 (heq ▸ (hf i₂).1)
      subst hi
      exact hne i₁ heq.symm
    · change g i₁ = g i₂ at heq
      congr 1
      by_contra hne_i
      exact Set.disjoint_left.mp (hdis hne_i) (hg i₁).1 (heq ▸ (hg i₂).1)
  have hsub : range fg ⊆ X := by
    rintro x ⟨i | i, rfl⟩
    · exact (hf i).2
    · exact (hg i).2
  have hle : (range fg).ncard ≤ X.ncard := ncard_le_ncard hsub hfin
  rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_fin] at hle
  omega

/-! ## Helper Lemmas on `clearedSubdrawing` -/

/-- For a `λ`-zone `Λ` around `z`, the vertex set of `H' = H ∩ (Σ - Λ)` is `H.V \ Λ` and its edge
set is `{e ∈ H.E | e ⊆ univ \ Λ}`. -/
theorem clearedSubdrawing_V_and_E [T2Space S] {H : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    (clearedSubdrawing H Λ).V = H.V \ Λ ∧
      (clearedSubdrawing H Λ).E = {e | e ∈ H.E ∧ e ⊆ univ \ Λ} := by
  have hU := clearedSubdrawing_U hZone
  have hSub := clearedSubdrawing_isSubdrawing H Λ
  have hE : (clearedSubdrawing H Λ).E = {e | e ∈ H.E ∧ e ⊆ univ \ Λ} := by
    change (H.span _ _).E = _
    rw [H.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  refine ⟨subset_antisymm ?_ ?_, hE⟩
  · intro v hv
    have hvU : v ∈ H.U \ Λ := hU ▸ (clearedSubdrawing H Λ).V_subset_U hv
    exact ⟨hSub.1 hv, hvU.2⟩
  · rintro v ⟨hvV, hvΛ⟩
    exact Or.inl ⟨⟨hvV, mem_univ _, hvΛ⟩, hvV⟩

/-- If `Γ` is a subdrawing of `H` and `Γ.U` is disjoint from a `λ`-zone `Λ`, then `Γ` is a
subdrawing of `clearedSubdrawing H Λ`. -/
theorem isSubdrawing_clearedSubdrawing [T2Space S] {H Γ : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) (hΓ : Γ.IsSubdrawing H) (hdis : Disjoint Γ.U Λ) :
    Γ.IsSubdrawing (clearedSubdrawing H Λ) := by
  obtain ⟨hV, hE⟩ := clearedSubdrawing_V_and_E hZone
  refine ⟨?_, ?_⟩
  · rw [hV]
    exact fun v hv => ⟨hΓ.1 hv, disjoint_left.mp hdis (Γ.V_subset_U hv)⟩
  · rw [hE]
    exact fun e he => ⟨hΓ.2 he, fun x hx =>
      ⟨mem_univ _, disjoint_left.mp hdis (Γ.closure_subset_U he (subset_closure hx))⟩⟩

/-- For a `λ`-zone `Λ` around `z`, `Λ` is a region of `clearedSubdrawing H Λ`, and every atom
`x' ∈ (clearedSubdrawing H Λ).A` with `x' ≠ Λ` belongs to `H.A`. -/
theorem clearedSubdrawing_mem_R_and_atom [T2Space S] {H : Drawing S}
    {d : Set S → Set S → ℕ} {lam : ℕ} {z Λ : Set S}
    (hZone : IsLambdaZoneAround H d lam z Λ) :
    Λ ∈ (clearedSubdrawing H Λ).R ∧
      ∀ x' ∈ (clearedSubdrawing H Λ).A, x' ≠ Λ → x' ∈ H.A := by
  have hU := clearedSubdrawing_U hZone
  have hSub := clearedSubdrawing_isSubdrawing H Λ
  obtain ⟨hdisL, hclL⟩ := isOpen_disjoint_subBd_and_closure_eq hZone.isOpenDisc.1
  let O₂ : Set S := univ \ (H.U ∪ closure Λ)
  have hO₂ : IsOpen O₂ := isOpen_univ.sdiff (H.isClosed_U.union isClosed_closure)
  have hdisO : Disjoint Λ O₂ :=
    disjoint_left.mpr fun x hx hxO => hxO.2 (Or.inr (subset_closure hx))
  have hcompl : univ \ (clearedSubdrawing H Λ).U = Λ ∪ O₂ := by
    rw [hU]
    ext x
    constructor
    · rintro ⟨_, hx⟩
      by_cases hxΛ : x ∈ Λ
      · exact Or.inl hxΛ
      · refine Or.inr ⟨mem_univ _, ?_⟩
        rintro (hxU | hxcl)
        · exact hx ⟨hxU, hxΛ⟩
        · rw [hclL] at hxcl
          exact hx ⟨hZone.bd_subset_U (hxcl.resolve_left hxΛ), hxΛ⟩
    · rintro (hxΛ | ⟨_, hx⟩)
      · exact ⟨mem_univ _, fun h => h.2 hxΛ⟩
      · exact ⟨mem_univ _, fun h => hx (Or.inl h.1)⟩
  obtain ⟨p, hp⟩ := IsOpenDisc.nonempty hZone.isOpenDisc
  have hpU' : p ∉ (clearedSubdrawing H Λ).U := by
    rw [hU]
    exact fun h => h.2 hp
  have hp_mem : p ∈ univ \ (clearedSubdrawing H Λ).U := ⟨mem_univ _, hpU'⟩
  have hcov' : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) p ⊆ Λ ∪ O₂ := by
    rw [← hcompl]
    exact connectedComponentIn_subset _ _
  have hΛ_eq : connectedComponentIn (univ \ (clearedSubdrawing H Λ).U) p = Λ := by
    refine subset_antisymm ?_ ?_
    · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
        hZone.isOpenDisc.1 hO₂ hdisO hcov' ⟨p, mem_connectedComponentIn hp_mem, hp⟩
    · refine hZone.isOpenDisc.isPathConnected.isConnected.isPreconnected.subset_connectedComponentIn
        hp ?_
      rw [hcompl]
      exact subset_union_left
  have hΛR : Λ ∈ (clearedSubdrawing H Λ).R :=
    (mem_R_iff (clearedSubdrawing H Λ)).mpr ⟨p, hpU', hΛ_eq.symm⟩
  refine ⟨hΛR, ?_⟩
  rintro x' ((⟨v, hv, rfl⟩ | he) | hr) hne
  · exact Or.inl (Or.inl ⟨v, hSub.1 hv, rfl⟩)
  · exact Or.inl (Or.inr (hSub.2 he))
  · exact Or.inr ((clearedSubdrawing_region_eq_or_mem_R hZone hr).resolve_left hne)

/-! ## Helper Lemmas on Separations, Paths, Circuits, and Zones -/

/-- If `P` is a path of `H` between `v` and `u`, then `P.U` is preconnected. -/
theorem isPreconnected_of_isPathBetween [T2Space S] {P : Drawing S} {v u : S}
    (hP : P.IsPathBetween v u) : IsPreconnected P.U := by
  by_cases hvu : v = u
  · subst hvu
    obtain ⟨W, hW, hPV, hPE⟩ := hP
    cases W with
    | nil _ =>
      have hV : P.V = {v} := by
        rw [hPV]
        ext x
        simp [GraphWalk.support_nil]
      have hE : P.E = ∅ := by
        rw [hPE]
        ext e
        simp [GraphWalk.edges]
      have hU : P.U = {v} := by
        rw [P.U_eq, hV, hE]
        simp
      rw [hU]
      exact isPreconnected_singleton
    | cons h r =>
      exact absurd r.end_mem_support (List.nodup_cons.mp hW).1
  · obtain ⟨φ, -⟩ := isLine_of_isPathBetween hP hvu
    have h_eq : P.U = (fun z => (φ z).1) '' univ := by
      ext x
      exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, mem_univ _, by simp⟩,
        fun ⟨z, _, hz⟩ => hz ▸ (φ z).2⟩
    rw [h_eq]
    exact isPreconnected_univ.image _ (continuous_subtype_val.comp φ.continuous).continuousOn

/-- If `(A, B)` is a separation of `H.toHypergraph` and `P` is a path of `H` with initial vertex
`v ∈ A.vertexSet` and `Disjoint P.V (A ∩ B).vertexSet`, then `P.V ⊆ A.vertexSet \ B.vertexSet`. -/
theorem path_vertexSet_subset_diff {H P : Drawing S} {A B : Hypergraph S (Set S)} {v u : S}
    (hsep : H.toHypergraph.IsSeparation A B) (hP : P.IsPathBetween v u) (hPs : P.IsSubdrawing H)
    (hvA : v ∈ A.vertexSet) (hdis : Disjoint P.V (A ∩ B).vertexSet) :
    P.V ⊆ A.vertexSet \ B.vertexSet := by
  obtain ⟨W, _, hPV, _⟩ := hP
  have hwalk : ∀ {x y : S} (W' : GraphWalk P.toGraph x y),
      (∀ z ∈ W'.support, z ∈ P.V) → x ∈ A.vertexSet →
      ∀ z ∈ W'.support, z ∈ A.vertexSet ∧ z ∉ B.vertexSet := by
    intro x y W'
    induction W' with
    | @nil x hx =>
      intro hsup hxA z hz
      rw [GraphWalk.support_nil, List.mem_singleton] at hz
      subst hz
      have hxP : z ∈ P.V := hsup z (by simp)
      refine ⟨hxA, fun hxB => Set.disjoint_left.mp hdis hxP ⟨hxA, hxB⟩⟩
    | @cons x w y e hlink W' ih =>
      intro hsup hxA z hz
      have hxP : x ∈ P.V := hsup x (by simp)
      have hwP : w ∈ P.V := hsup w (List.mem_cons_of_mem x W'.start_mem_support)
      have hxB : x ∉ B.vertexSet := fun hxB => Set.disjoint_left.mp hdis hxP ⟨hxA, hxB⟩
      have heP : e ∈ P.E := hlink.1
      have heH : e ∈ H.E := hPs.2 heP
      have hxe_cl : x ∈ closure e := by
        have : x ∈ closure e ∩ P.V := hlink.2.2.2 ▸ mem_insert x {w}
        exact this.1
      have hwe_cl : w ∈ closure e := by
        have : w ∈ closure e ∩ P.V := hlink.2.2.2 ▸ mem_insert_of_mem x rfl
        exact this.1
      have hinc_x : H.toHypergraph.Inc e x :=
        (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr
          ⟨heH, hPs.1 hxP, hxe_cl⟩
      have hinc_w : H.toHypergraph.Inc e w :=
        (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr
          ⟨heH, hPs.1 hwP, hwe_cl⟩
      have heU : e ∈ A.edgeSet ∪ B.edgeSet := by
        rw [hsep.edgeSet_union]
        exact heH
      have heA : e ∈ A.edgeSet := by
        rcases heU with heA | heB
        · exact heA
        · exfalso
          have hincB : B.Inc e x := (inc_iff_of_le hsep.right_le heB).mpr hinc_x
          exact hxB (B.vertex_mem_of_inc hincB)
      have hwA : w ∈ A.vertexSet :=
        A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le heA).mpr hinc_w)
      rw [GraphWalk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact ⟨hxA, hxB⟩
      · exact ih (fun q hq => hsup q (by simp [hq])) hwA z hz'
  intro z hzP
  have hzW : z ∈ W.support := by rwa [hPV] at hzP
  exact hwalk W (fun q hq => by rw [hPV]; exact hq) hvA z hzW

/-- If `(A, B)` is a separation of `H.toHypergraph` and `C` is a circuit of `H` with
`(C.V ∩ (A ∩ B).vertexSet).ncard ≤ 1`, and either some vertex of `C` is not in `B.vertexSet` or
some edge of `C` is in `A.edgeSet`, then `C.V ⊆ A.vertexSet`, `C.E ⊆ A.edgeSet`, and
`(B.vertexSet ∩ C.V).ncard ≤ 1`. -/
theorem circuit_subset_of_inter_ncard_le_one [T2Space S] {H C : Drawing S}
    {A B : Hypergraph S (Set S)}
    (hsep : H.toHypergraph.IsSeparation A B) (hC : C.IsCircuit) (hCs : C.IsSubdrawing H)
    (hle : (C.V ∩ (A ∩ B).vertexSet).ncard ≤ 1)
    (hside : (∃ w₀ ∈ C.V, w₀ ∉ B.vertexSet) ∨ (∃ e₀ ∈ C.E, e₀ ∈ A.edgeSet)) :
    (C.V ⊆ A.vertexSet ∧ C.E ⊆ A.edgeSet) ∧ (B.vertexSet ∩ C.V).ncard ≤ 1 := by
  have hC' := hC
  obtain ⟨u, W_C, ⟨hnd, hed⟩, hpos, hCV, hCE⟩ := hC
  have hv_inc : ∀ v ∈ C.V, ∃ e ∈ C.E, v ∈ closure e := by
    intro v hv
    rw [hCV] at hv
    cases W_C with
    | nil _ => exact absurd hpos (Nat.lt_irrefl 0)
    | @cons _ w _ e₀ hlink W' =>
      by_cases hvu : v = u
      · subst hvu
        have hue₀ : v ∈ closure e₀ := by
          have : v ∈ closure e₀ ∩ C.V := hlink.2.2.2 ▸ mem_insert v {w}
          exact this.1
        exact ⟨e₀, by rw [hCE]; exact List.mem_cons_self, hue₀⟩
      · have hv_mem : v ∈ (GraphWalk.cons hlink W').support := hv
        have hex_link : ∀ {b y : S} (W₁ : GraphWalk C.toGraph b y) {a : S} {f₀ : Set S}
            (hlink₀ : C.toGraph.IsLink f₀ a b),
            v ≠ a → v ∈ (GraphWalk.cons hlink₀ W₁).support →
            ∃ x e, C.toGraph.IsLink e x v ∧ e ∈ (GraphWalk.cons hlink₀ W₁).edges := by
          intro b y W₁
          induction W₁ with
          | nil hby =>
            intro a f₀ hlink₀ hva hv_m
            rw [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
              List.mem_singleton] at hv_m
            rcases hv_m with rfl | rfl
            · exact absurd rfl hva
            · exact ⟨a, f₀, hlink₀, List.mem_cons_self⟩
          | @cons b y z e₁ hlink₁ W'' ih =>
            intro a f₀ hlink₀ hva hv_m
            rw [GraphWalk.support_cons, List.mem_cons] at hv_m
            rcases hv_m with rfl | hv'
            · exact absurd rfl hva
            · by_cases hvb : v = b
              · subst hvb
                exact ⟨a, f₀, hlink₀, List.mem_cons_self⟩
              · obtain ⟨x, e, hl, hem⟩ := ih hlink₁ hvb hv'
                exact ⟨x, e, hl, List.mem_cons_of_mem f₀ hem⟩
        obtain ⟨x, e, hlink', he_mem⟩ := hex_link W' hlink hvu hv_mem
        have hve : v ∈ closure e := by
          have : v ∈ closure e ∩ C.V := hlink'.2.2.2 ▸ mem_insert_of_mem x rfl
          exact this.1
        exact ⟨e, by rw [hCE]; exact he_mem, hve⟩
  have hCE_sub : C.E ⊆ A.edgeSet := by
    by_contra hnot_sub
    obtain ⟨eB, heBC, heB_notA⟩ := not_subset.mp hnot_sub
    have heBH : eB ∈ H.E := hCs.2 heBC
    have heBU : eB ∈ A.edgeSet ∪ B.edgeSet := by
      rw [hsep.edgeSet_union]
      exact heBH
    have heBB : eB ∈ B.edgeSet := heBU.resolve_left heB_notA
    have hex_eA : ∃ eA ∈ C.E, eA ∈ A.edgeSet := by
      rcases hside with ⟨w₀, hw₀C, hw₀B⟩ | hex
      · obtain ⟨e₀, he₀C, hw₀e₀⟩ := hv_inc w₀ hw₀C
        have he₀H : e₀ ∈ H.E := hCs.2 he₀C
        have hinc₀ : H.toHypergraph.Inc e₀ w₀ :=
          (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr
            ⟨he₀H, hCs.1 hw₀C, hw₀e₀⟩
        have he₀U : e₀ ∈ A.edgeSet ∪ B.edgeSet := by
          rw [hsep.edgeSet_union]
          exact he₀H
        refine ⟨e₀, he₀C, he₀U.resolve_right fun he₀B => ?_⟩
        exact hw₀B (B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le he₀B).mpr hinc₀))
      · exact hex
    obtain ⟨eA, heAC, heAA⟩ := hex_eA
    set S_AB := C.V ∩ (A ∩ B).vertexSet
    have hfin_AB : S_AB.Finite := C.finite_V.subset inter_subset_left
    have hCU_oArc : IsOArc C.U := isOArc_of_isCircuit hC'
    have hconn_Z : IsPreconnected (C.U \ S_AB) := by
      by_cases hne : S_AB.Nonempty
      · obtain ⟨z₀, hz₀⟩ := hne
        have hsing : S_AB = {z₀} :=
          (eq_of_subset_of_ncard_le (singleton_subset_iff.mpr hz₀)
            (by rw [ncard_singleton]; exact hle) hfin_AB).symm
        rw [hsing]
        exact (isPathConnected_oArc_diff hCU_oArc (C.V_subset_U hz₀.1)).isConnected.isPreconnected
      · rw [not_nonempty_iff_eq_empty.mp hne, sdiff_empty]
        exact IsOArc.isPreconnected hCU_oArc
    set U_A := ⋃ e ∈ C.E ∩ A.edgeSet, closure e
    set U_B := ⋃ e ∈ C.E ∩ B.edgeSet, closure e
    have hcl_A : IsClosed U_A :=
      (C.finite_edges.subset inter_subset_left).isClosed_biUnion fun _ _ => isClosed_closure
    have hcl_B : IsClosed U_B :=
      (C.finite_edges.subset inter_subset_left).isClosed_biUnion fun _ _ => isClosed_closure
    have hcov : C.U \ S_AB ⊆ U_A ∪ U_B := by
      rintro x ⟨hxU, -⟩
      by_cases hxV : x ∈ C.V
      · obtain ⟨e, heC, hxe⟩ := hv_inc x hxV
        have heU : e ∈ A.edgeSet ∪ B.edgeSet := by
          rw [hsep.edgeSet_union]
          exact hCs.2 heC
        rcases heU with heA' | heB'
        · exact Or.inl (mem_iUnion₂.mpr ⟨e, ⟨heC, heA'⟩, hxe⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨heC, heB'⟩, hxe⟩)
      · obtain ⟨e, heC, hxe⟩ := C.exists_edge_of_mem hxU hxV
        have heU : e ∈ A.edgeSet ∪ B.edgeSet := by
          rw [hsep.edgeSet_union]
          exact hCs.2 heC
        rcases heU with heA' | heB'
        · exact Or.inl (mem_iUnion₂.mpr ⟨e, ⟨heC, heA'⟩, subset_closure hxe⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨heC, heB'⟩, subset_closure hxe⟩)
    obtain ⟨pA, hpA⟩ := heAC.1
    have hpA_Z : pA ∈ C.U \ S_AB :=
      ⟨(heAC.2.1 hpA).1, fun h => (heAC.2.1 hpA).2 h.1⟩
    have hpA_UA : pA ∈ U_A := mem_iUnion₂.mpr ⟨eA, ⟨heAC, heAA⟩, subset_closure hpA⟩
    obtain ⟨pB, hpB⟩ := heBC.1
    have hpB_Z : pB ∈ C.U \ S_AB :=
      ⟨(heBC.2.1 hpB).1, fun h => (heBC.2.1 hpB).2 h.1⟩
    have hpB_UB : pB ∈ U_B := mem_iUnion₂.mpr ⟨eB, ⟨heBC, heBB⟩, subset_closure hpB⟩
    obtain ⟨z, ⟨hzU, hz_notAB⟩, hzUA, hzUB⟩ :=
      isPreconnected_closed_iff.mp hconn_Z U_A U_B hcl_A hcl_B hcov
        ⟨pA, hpA_Z, hpA_UA⟩ ⟨pB, hpB_Z, hpB_UB⟩
    obtain ⟨fA, ⟨hfAC, hfAA⟩, hzfA⟩ := mem_iUnion₂.mp hzUA
    obtain ⟨fB, ⟨hfBC, hfBB⟩, hzfB⟩ := mem_iUnion₂.mp hzUB
    have hf_ne : fA ≠ fB := by
      intro heq
      subst heq
      have : fA ∈ (A ∩ B).edgeSet := ⟨hfAA, hfBB⟩
      rw [hsep.edgeSet_inter_eq] at this
      exact this
    have hzCV : z ∈ C.V := by
      by_contra hzCV
      have hzfA' : z ∈ fA := by rw [← C.closure_diff_V hfAC]; exact ⟨hzfA, hzCV⟩
      have hzfB' : z ∈ fB := by rw [← C.closure_diff_V hfBC]; exact ⟨hzfB, hzCV⟩
      exact hf_ne (C.edge_eq_of_mem hfAC hfBC hzfA' hzfB')
    have hincA : H.toHypergraph.Inc fA z :=
      (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr
        ⟨hCs.2 hfAC, hCs.1 hzCV, hzfA⟩
    have hincB : H.toHypergraph.Inc fB z :=
      (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr
        ⟨hCs.2 hfBC, hCs.1 hzCV, hzfB⟩
    have hzA : z ∈ A.vertexSet :=
      A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le hfAA).mpr hincA)
    have hzB : z ∈ B.vertexSet :=
      B.vertex_mem_of_inc ((inc_iff_of_le hsep.right_le hfBB).mpr hincB)
    exact hz_notAB ⟨hzCV, hzA, hzB⟩
  have hCV_sub : C.V ⊆ A.vertexSet := by
    intro v hv
    obtain ⟨e, heC, hve⟩ := hv_inc v hv
    have hinc : H.toHypergraph.Inc e v :=
      (PaintingOrDrawing.toHypergraph_inc (Γ := PaintingOrDrawing.drawing H)).mpr
        ⟨hCs.2 heC, hCs.1 hv, hve⟩
    exact A.vertex_mem_of_inc ((inc_iff_of_le hsep.left_le (hCE_sub heC)).mpr hinc)
  refine ⟨⟨hCV_sub, hCE_sub⟩, ?_⟩
  have hsub_inter : B.vertexSet ∩ C.V ⊆ C.V ∩ (A ∩ B).vertexSet :=
    fun x ⟨hxB, hxC⟩ => ⟨hxC, hCV_sub hxC, hxB⟩
  exact (ncard_le_ncard hsub_inter (C.finite_V.subset inter_subset_left)).trans hle

/-- If `C` is a circuit of `H` bounding a closed disc `Δ ⊆ Δ₁` (`subBd Δ = C.U`), and `P` is a path
of `H` between `v ∈ Δ` and `u ∈ subBd Δ₁`, then `(C.V ∩ P.V).Nonempty`. -/
theorem circuit_inter_path_nonempty [T2Space S] (hS : IsClosedSurface S) {H C P : Drawing S}
    {Δ Δ₁ : Set S} {v u : S}
    (hΔ : IsClosedDisc Δ) (_hΔ₁ : IsClosedDisc Δ₁) (hΔ_sub : Δ ⊆ Δ₁)
    (hCs : C.IsSubdrawing H) (hbd : subBd Δ = C.U)
    (hP : P.IsPathBetween v u) (hPs : P.IsSubdrawing H)
    (hv : v ∈ Δ) (hu : u ∈ subBd Δ₁) :
    (C.V ∩ P.V).Nonempty := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  refine nonempty_inter_V_of_nonempty_inter_U hCs hPs ?_
  have hP' := hP
  obtain ⟨W, _, hPV, _⟩ := hP
  have hvP : v ∈ P.U := P.V_subset_U (by rw [hPV]; exact W.start_mem_support)
  have huP : u ∈ P.U := P.V_subset_U (by rw [hPV]; exact W.end_mem_support)
  by_cases huC : u ∈ C.U
  · exact ⟨u, huC, huP⟩
  · have hu_not_Δ : u ∉ Δ := by
      intro huΔ
      have hfrΔ : frontier Δ = C.U := by rw [subBd_eq_frontier', hbd]
      have hclΔ : closure Δ = Δ := hΔ.isClosed.closure_eq
      have hu_int : u ∈ interior Δ := by
        by_contra hu_nint
        have : u ∈ frontier Δ := ⟨hclΔ.symm ▸ huΔ, hu_nint⟩
        exact huC (hfrΔ ▸ this)
      have hu_int₁ : u ∈ interior Δ₁ := interior_mono hΔ_sub hu_int
      have hfr₁ : u ∈ frontier Δ₁ := by rwa [subBd_eq_frontier']
      exact hfr₁.2 hu_int₁
    have hconnP : IsPreconnected P.U := isPreconnected_of_isPathBetween hP'
    have hnot_dis : ¬ Disjoint P.U (frontier Δ) := by
      intro hdis
      exact hu_not_Δ (subset_of_disjoint_frontier hconnP hΔ.isClosed hdis hvP hv huP)
    rw [subBd_eq_frontier', hbd] at hnot_dis
    obtain ⟨x, hxP, hxC⟩ := not_disjoint_iff.mp hnot_dis
    exact ⟨x, hxC, hxP⟩

/-- If `Δ₁ \ subBd Δ₁` is a `λ₁`-zone around `z` in `H`, and `C` is a circuit of `H` bounding a
closed disc `Δ ⊆ Δ₁` with `z ⊆ Δ \ subBd Δ`, then `Δ \ subBd Δ` is a `λ₁`-zone around `z` in `H`. -/
theorem zone_of_closedDisc_subset [T2Space S] (hS : IsClosedSurface S) {H C : Drawing S}
    {d : Set S → Set S → ℕ} {lam₁ : ℕ} {z Δ Δ₁ : Set S}
    (hZone₁ : IsLambdaZoneAround H d lam₁ z (Δ₁ \ subBd Δ₁))
    (hΔ₁ : IsClosedDisc Δ₁) (hΔ : IsClosedDisc Δ) (hΔ_sub : Δ ⊆ Δ₁)
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hbd : subBd Δ = C.U)
    (hz : z ⊆ Δ \ subBd Δ) :
    IsLambdaZoneAround H d lam₁ z (Δ \ subBd Δ) := by
  obtain ⟨hOD, hcl_eq, hbd_eq⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ
  obtain ⟨_, hcl₁_eq, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₁
  refine ⟨hZone₁.z_mem, hOD, hz, ?_, ?_, ?_, ?_, hZone₁.two_le_of_edge⟩
  · rw [hbd_eq, hbd]
    exact isOArc_of_isCircuit hC
  · rw [hcl_eq]
    exact hΔ
  · rw [hbd_eq, hbd]
    exact hCs.U_subset
  · intro x hx hsub
    rw [hcl_eq] at hsub
    exact hZone₁.dist_le x hx (hcl₁_eq.symm ▸ hsub.trans hΔ_sub)

/-- If `Δ \ subBd Δ` is a `λ₁`-zone around `z` in `H` (`IsClosedDisc Δ`), `Λ₂ = Δ₂ \ subBd Δ₂` is a
`λ`-zone around `z` (`IsClosedDisc Δ₂`) with `Δ₂ ⊆ Δ`, and `(T', d')` is obtained by clearing `Λ₂`,
then `Δ \ subBd Δ` is a `λ₁`-zone around `Λ₂` in `clearedSubdrawing H Λ₂`. -/
theorem cleared_zone_of_closedDisc_subset
    [T2Space S] (hS : IsClosedSurface S)
    {H C : Drawing S}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {θ lam lam₁ : ℕ} {z Δ Δ₂ : Set S}
    (hZone : IsLambdaZoneAround H d lam₁ z (Δ \ subBd Δ))
    (hZone₂ : IsLambdaZoneAround H d lam z (Δ₂ \ subBd Δ₂))
    (hCleared : IsClearedTangle H T d θ lam (Δ₂ \ subBd Δ₂) T' d')
    (hΔ : IsClosedDisc Δ) (_hΔ₂ : IsClosedDisc Δ₂) (hΔ₂_sub : Δ₂ ⊆ Δ)
    (_hC : C.IsCircuit) (hCs : C.IsSubdrawing H) (hbd : subBd Δ = C.U) :
    IsLambdaZoneAround (clearedSubdrawing H (Δ₂ \ subBd Δ₂)) d' lam₁
      (Δ₂ \ subBd Δ₂) (Δ \ subBd Δ) := by
  set Λ₂ := Δ₂ \ subBd Δ₂
  set H' := clearedSubdrawing H Λ₂
  obtain ⟨hOD, _, hbd_eq⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ
  obtain ⟨hΛ₂R, hatom'⟩ := clearedSubdrawing_mem_R_and_atom hZone₂
  have hΛ₂A : Λ₂ ∈ H'.A := Or.inr hΛ₂R
  have hΛ₂_sub : Λ₂ ⊆ Δ \ subBd Δ := by
    have h₁ : Λ₂ = interior Δ₂ := by
      change Δ₂ \ subBd Δ₂ = interior Δ₂
      rw [← subBd_eq_frontier']
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    have h₂ : Δ \ subBd Δ = interior Δ := by
      rw [← subBd_eq_frontier']
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    rw [h₁, h₂]
    exact interior_mono hΔ₂_sub
  obtain ⟨_, K', ins', _, _, hd'_eq⟩ := hCleared.hasMetric
  refine ⟨hΛ₂A, hOD, hΛ₂_sub, hZone.isOArc_bd, hZone.isClosedDisc_closure, ?_, ?_, ?_⟩
  · rw [hbd_eq, hbd, clearedSubdrawing_U hZone₂]
    intro x hxC
    refine ⟨hCs.U_subset hxC, fun hxΛ₂ => ?_⟩
    exact (hΛ₂_sub hxΛ₂).2 (hbd ▸ hxC)
  · intro x' hx' hsub
    by_cases hx'Λ₂ : x' = Λ₂
    · subst hx'Λ₂
      rw [hd'_eq Λ₂ hΛ₂A Λ₂ hΛ₂A]
      simp [tangleMetric]
    · have hx'H : x' ∈ H.A := hatom' x' hx' hx'Λ₂
      have hle := (hCleared.dist_bounds z hZone₂.z_mem x' hx'H Λ₂ hΛ₂A x' hx'
        hZone₂.z_subset subset_rfl).2
      exact hle.trans (hZone.dist_le x' hx'H hsub)
  · intro hΛ₂E
    obtain ⟨p, hp⟩ := hΛ₂E.1
    exact absurd (hΛ₂E.2.1 hp).1 (region_subset hΛ₂R hp)

/-! ## Proof of (7.8) -/

/-- If `D` is a circuit of a radial drawing `K` of `H` with `D.length < 2 * θ`, and `x, y ∈ A(H)`
both meet `ins(D)`, then `2 * d(x, y) ≤ D.length` and `d(x, y) ≤ |V(D) ∩ V(H)|`. -/
theorem tangleMetric_le_of_circuit [T2Space S] (hS : IsClosedSurface S) {H K D : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {ins : Drawing S → Set S}
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing H) K θ T ins)
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K) (hlen : D.length < 2 * θ)
    {x y : Set S} (hx : x ∈ H.A) (hy : y ∈ H.A)
    (hxD : (x ∩ ins D).Nonempty) (hyD : (y ∩ ins D).Nonempty) :
    2 * tangleMetric H K ins θ x y ≤ D.length ∧
      tangleMetric H K ins θ x y ≤ (D.V ∩ H.V).ncard := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hD' := hD
  obtain ⟨u, W_D, ⟨_, hed⟩, _, hDV, hDE⟩ := hD
  obtain ⟨W, hs, he⟩ := hDs.exists_walk_up W_D
  have hWD_eq : walkDrawing K W = D := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hs, hDV]
    · rw [walkDrawing_E, he, hDE]
  have hWlen : W.length = D.length := by
    rw [Drawing.length, hDE, ← he]
    have h : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
    rw [h, ncard_coe_finset, List.toFinset_card_of_nodup (he ▸ hed)]
    rfl
  have hWlt : W.length < 2 * θ := hWlen ▸ hlen
  have hinsD_sub : ins D ⊆ insWalk ins K W := by
    intro p hp
    refine Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD', ?_⟩, hp⟩)
    rw [hWD_eq]
    exact ⟨subset_rfl, subset_rfl⟩
  obtain ⟨x', hx', -⟩ := existsUnique_correspondingAtom hK hx
  obtain ⟨y', hy', -⟩ := existsUnique_correspondingAtom hK hy
  have hx'W : x' ⊆ insWalk ins K W :=
    (theorem_3_1_proof hS hK hd hx' W hWlt).mpr (hxD.mono (inter_subset_inter_right x hinsD_sub))
  have hy'W : y' ⊆ insWalk ins K W :=
    (theorem_3_1_proof hS hK hd hy' W hWlt).mpr (hyD.mono (inter_subset_inter_right y hinsD_sub))
  have h2le : 2 * tangleMetric H K ins θ x y ≤ D.length := by
    rw [← hWlen]
    exact two_mul_tangleMetric_le_walk_length hK hx' hy' W hWlt hx'W hy'W
  have hDeq := (circuit_length_eq_two_mul_ncard hK.2.1 hD' hDs).1
  refine ⟨h2le, ?_⟩
  omega

/-- Combined application of (7.4) and (7.6) for a separation `(A₀, B₀) ∈ T₀`, a circuit `C₀`
bounding a closed disc `Δ₀` whose interior `Δ₀ \ subBd Δ₀` is a `lam₀`-zone around `z₀`, and a path
`P₀` starting at `v₀ ∈ Δ₀ ∩ A₀.vertexSet` disjoint from `(A₀ ∩ B₀).vertexSet`. -/
private theorem circuit_of_sep_in_zone
    [T2Space S] (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H₀ K₀ C₀ P₀ : Drawing S} {θ₀ lam₀ : ℕ}
    {T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d₀ : Set S → Set S → ℕ} {ins₀ : Drawing S → Set S}
    {A₀ B₀ : Hypergraph S (Set S)} {z₀ Δ₀ : Set S} {v₀ u₀ : S}
    (hMetric₀ : HasTangleMetric H₀ θ₀ T₀ d₀)
    (hK₀ : (PaintingOrDrawing.drawing H₀).IsRadialDrawing K₀)
    (hd₀ : IsDerivedSlope (PaintingOrDrawing.drawing H₀) K₀ θ₀ T₀ ins₀)
    (hAB₀ : (A₀, B₀) ∈ T₀)
    (hZone₀ : IsLambdaZoneAround H₀ d₀ lam₀ z₀ (Δ₀ \ subBd Δ₀))
    (hΔ₀ : IsClosedDisc Δ₀)
    (hC₀ : C₀.IsCircuit) (hC₀s : C₀.IsSubdrawing H₀) (hbd₀ : subBd Δ₀ = C₀.U)
    (hord₀ : separationOrder A₀ B₀ + lam₀ < θ₀)
    (hP₀ : P₀.IsPathBetween v₀ u₀) (hP₀s : P₀.IsSubdrawing H₀)
    (hv₀_Δ : v₀ ∈ Δ₀) (hv₀_A : v₀ ∈ A₀.vertexSet)
    (hdis_P : Disjoint P₀.V (A₀ ∩ B₀).vertexSet)
    (hne_CP : (C₀.V ∩ P₀.V).Nonempty)
    (hle_C : (C₀.V ∩ (A₀ ∩ B₀).vertexSet).ncard ≤ 1) :
    ∃ D₀ : Drawing S, D₀.IsCircuit ∧ D₀.IsSubdrawing K₀ ∧ D₀.length < 2 * θ₀ ∧
      D₀.V ∩ H₀.V ⊆ (A₀ ∩ B₀).vertexSet ∧ Δ₀ ⊆ ins₀ D₀ ∧ P₀.U ⊆ ins₀ D₀ \ D₀.U := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hsep₀ : H₀.toHypergraph.IsSeparation A₀ B₀ := hMetric₀.1.2.1.isSeparation hAB₀
  have hPV_sub : P₀.V ⊆ A₀.vertexSet \ B₀.vertexSet :=
    path_vertexSet_subset_diff hsep₀ hP₀ hP₀s hv₀_A hdis_P
  obtain ⟨w₀, hw₀C, hw₀P⟩ := hne_CP
  have hw₀B : w₀ ∉ B₀.vertexSet := (hPV_sub hw₀P).2
  obtain ⟨hC₀_A, hBC₀⟩ :=
    circuit_subset_of_inter_ncard_le_one hsep₀ hC₀ hC₀s hle_C (Or.inl ⟨w₀, hw₀C, hw₀B⟩)
  obtain ⟨D₀, hD₀, hD₀s, hD₀len, hD₀V, hCU_sub⟩ :=
    theorem_7_4_proof hS hConn hMetric₀.1 hK₀ hd₀ hAB₀ hC₀ hC₀s hC₀_A hBC₀
  have hDeq := (circuit_length_eq_two_mul_ncard hK₀.2.1 hD₀ hD₀s).1
  have hfin_AB : (A₀ ∩ B₀).vertexSet.Finite :=
    H₀.finite_V.subset hsep₀.left_le.vertexSet_subset |>.subset inter_subset_left
  have hncard_le : (D₀.V ∩ H₀.V).ncard ≤ (A₀ ∩ B₀).vertexSet.ncard :=
    ncard_le_ncard hD₀V hfin_AB
  change (A₀ ∩ B₀).vertexSet.ncard + lam₀ < θ₀ at hord₀
  have hD₀len_lam : D₀.length < 2 * (θ₀ - lam₀) := by omega
  obtain ⟨_, hcl₀_eq, hbd₀_eq⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ₀
  have hbd_sub : subBd (Δ₀ \ subBd Δ₀) ⊆ ins₀ D₀ := by
    rw [hbd₀_eq, hbd₀]
    exact hCU_sub
  have hcl_sub : closure (Δ₀ \ subBd Δ₀) ⊆ ins₀ D₀ :=
    theorem_7_6_proof hS hConn hMetric₀ hK₀ hd₀ hZone₀ hD₀ hD₀s hD₀len_lam hbd_sub
  have hΔ₀_sub : Δ₀ ⊆ ins₀ D₀ := hcl₀_eq ▸ hcl_sub
  obtain ⟨hD₀disc, hD₀bd, -⟩ := hd₀ D₀ hD₀ hD₀s hD₀len
  have hfrD₀ : frontier (ins₀ D₀) = D₀.U := by rw [subBd_eq_frontier', hD₀bd]
  have hUU₀ : H₀.U ∩ K₀.U = H₀.V := hK₀.2.1.1
  have hdis_PU_DU : Disjoint P₀.U D₀.U := by
    refine Set.disjoint_left.mpr fun x hxP hxD => ?_
    have hxHV : x ∈ H₀.V := by
      have : x ∈ H₀.U ∩ K₀.U := ⟨hP₀s.U_subset hxP, hD₀s.U_subset hxD⟩
      rwa [hUU₀] at this
    have hxPV : x ∈ P₀.V := by
      by_contra hxPV
      obtain ⟨e, heP, hxe⟩ := P₀.exists_edge_of_mem hxP hxPV
      exact ((hP₀s.2 heP).2.1 hxe).2 hxHV
    have hxDV : x ∈ D₀.V := by
      by_contra hxDV
      obtain ⟨g, hgD, hxg⟩ := D₀.exists_edge_of_mem hxD hxDV
      exact ((hD₀s.2 hgD).2.1 hxg).2 (hK₀.2.1.2.1 hxHV)
    exact Set.disjoint_left.mp hdis_P hxPV (hD₀V ⟨hxDV, hxHV⟩)
  have hP₀' := hP₀
  obtain ⟨W_P, _, hPV_iff, _⟩ := hP₀
  have hv₀P : v₀ ∈ P₀.U := P₀.V_subset_U (by rw [hPV_iff]; exact W_P.start_mem_support)
  have hPU_sub : P₀.U ⊆ ins₀ D₀ :=
    subset_of_disjoint_frontier (isPreconnected_of_isPathBetween hP₀') hD₀disc.isClosed
      (hfrD₀ ▸ hdis_PU_DU) hv₀P (hΔ₀_sub hv₀_Δ)
  refine ⟨D₀, hD₀, hD₀s, hD₀len, hD₀V, hΔ₀_sub, fun x hxP => ⟨hPU_sub hxP, ?_⟩⟩
  exact Set.disjoint_left.mp hdis_PU_DU hxP

/-- If `D` is a circuit of a radial drawing `K'` of `H' = clearedSubdrawing H Λ₂` with
`|V(D) ∩ V(H')| < θ - 4λ - 2` and `Δ₂ ⊆ ins' D`, then `(H.inter (ins' D), H.interOutside (ins' D)) ∈
T`
and its separator vertex set is `D.V ∩ H'.V`. -/
private theorem inter_ins_mem_of_cleared [T2Space S] (hS : IsClosedSurface S)
  (_hConn : ConnectedSpace S)
    {H K' D : Drawing S} {θ lam : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {ins' : Drawing S → Set S} {z Δ₂ : Set S}
    (hMetric : HasTangleMetric H θ T d)
    (hZone₂ : IsLambdaZoneAround H d lam z (Δ₂ \ subBd Δ₂))
    (hCleared : IsClearedTangle H T d θ lam (Δ₂ \ subBd Δ₂) T' d')
    (_hΔ₂ : IsClosedDisc Δ₂)
    (hK' : (PaintingOrDrawing.drawing (clearedSubdrawing H (Δ₂ \ subBd Δ₂))).IsRadialDrawing K')
    (hd' : IsDerivedSlope (PaintingOrDrawing.drawing (clearedSubdrawing H (Δ₂ \ subBd Δ₂)))
      K' (θ - 4 * lam - 2) T' ins')
    (hD : D.IsCircuit) (hDs : D.IsSubdrawing K')
    (hlen : D.length < 2 * (θ - 4 * lam - 2))
    (hΔ₂_sub : Δ₂ ⊆ ins' D) :
    ((PaintingOrDrawing.drawing H).inter (ins' D),
      (PaintingOrDrawing.drawing H).interOutside (ins' D)) ∈ T ∧
      ((PaintingOrDrawing.drawing H).inter (ins' D) ∩
        (PaintingOrDrawing.drawing H).interOutside (ins' D)).vertexSet ⊆
        D.V ∩ (clearedSubdrawing H (Δ₂ \ subBd Δ₂)).V := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  set Λ₂ := Δ₂ \ subBd Δ₂
  set H' := clearedSubdrawing H Λ₂
  set θ' := θ - 4 * lam - 2
  obtain ⟨hDdisc, hDbd, hDsep'⟩ := hd' D hD hDs hlen
  have hfrD : frontier (ins' D) = D.U := by rw [subBd_eq_frontier', hDbd]
  have hΛ₂_int : Λ₂ ⊆ ins' D \ D.U := by
    have h₁ : Λ₂ = interior Δ₂ := by
      change Δ₂ \ subBd Δ₂ = interior Δ₂
      rw [← subBd_eq_frontier']
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    have h₂ : ins' D \ D.U = interior (ins' D) := by
      rw [← hfrD]
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    rw [h₁, h₂]
    exact interior_mono hΔ₂_sub
  have hdis_DU_Λ₂ : Disjoint D.U Λ₂ :=
    Set.disjoint_left.mpr fun x hxD hxΛ₂ => (hΛ₂_int hxΛ₂).2 hxD
  have hU' := clearedSubdrawing_U hZone₂
  obtain ⟨hV', hE'⟩ := clearedSubdrawing_V_and_E hZone₂
  have hSub' := clearedSubdrawing_isSubdrawing H Λ₂
  have hUU' : H'.U ∩ K'.U = H'.V := hK'.2.1.1
  have hDU_inter_HU : D.U ∩ H.U = D.V ∩ H'.V := by
    ext x
    constructor
    · rintro ⟨hxD, hxH⟩
      have hxH'U : x ∈ H'.U := by
        rw [hU']
        exact ⟨hxH, Set.disjoint_left.mp hdis_DU_Λ₂ hxD⟩
      have hxH'V : x ∈ H'.V := by
        have : x ∈ H'.U ∩ K'.U := ⟨hxH'U, hDs.U_subset hxD⟩
        rwa [hUU'] at this
      have hxDV : x ∈ D.V := by
        by_contra hxDV
        obtain ⟨g, hgD, hxg⟩ := D.exists_edge_of_mem hxD hxDV
        exact ((hDs.2 hgD).2.1 hxg).2 (hK'.2.1.2.1 hxH'V)
      exact ⟨hxDV, hxH'V⟩
    · rintro ⟨hxDV, hxH'V⟩
      exact ⟨D.V_subset_U hxDV, H.V_subset_U (hSub'.1 hxH'V)⟩
  have hDU_inter_HV : D.U ∩ H.V = D.V ∩ H'.V := by
    refine subset_antisymm ?_ ?_
    · intro x ⟨hxD, hxHV⟩
      exact hDU_inter_HU ▸ ⟨hxD, H.V_subset_U hxHV⟩
    · intro x ⟨hxDV, hxH'V⟩
      exact ⟨D.V_subset_U hxDV, hSub'.1 hxH'V⟩
  have hDU_norm : D.U ∩ H.U ⊆ H.V := by
    rw [hDU_inter_HU]
    exact fun x hx => hSub'.1 hx.2
  have hDeq' := (circuit_length_eq_two_mul_ncard hK'.2.1 hD hDs).1
  have hDU_lt : (D.U ∩ H.V).ncard < θ := by
    rw [hDU_inter_HV]
    omega
  have hDU_oArc : IsOArc D.U := isOArc_of_isCircuit hD
  obtain ⟨Δ_H, hΔ_H_disc, hΔ_H_bd, hΔ_H_sep⟩ :=
    hMetric.1.2.2.2 D.U hDU_oArc hDU_norm hDU_lt
  have hAB_V_sub : ((PaintingOrDrawing.drawing H).inter (ins' D) ∩
      (PaintingOrDrawing.drawing H).interOutside (ins' D)).vertexSet ⊆ D.V ∩ H'.V := by
    rintro x ⟨⟨hxHV, hx_in⟩, ⟨_, hx_out⟩⟩
    have hx_fr : x ∈ frontier (ins' D) := by
      rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
      exact ⟨subset_closure hx_in, hx_out⟩
    rw [hfrD] at hx_fr
    exact hDU_inter_HV ▸ ⟨hx_fr, hxHV⟩
  refine ⟨?_, hAB_V_sub⟩
  by_cases h_eq : ins' D = Δ_H
  · exact h_eq ▸ hΔ_H_sep
  · exfalso
    have hbd_eq : discBd (ins' D) = discBd Δ_H := by
      rw [← IsClosedDisc.subBd_eq_discBd hS hDdisc, ← IsClosedDisc.subBd_eq_discBd hS hΔ_H_disc,
        hDbd, hΔ_H_bd]
    have hcov : ins' D ∪ Δ_H = univ :=
      cover_of_discBd_eq hS hDdisc hΔ_H_disc hbd_eq h_eq
    have hfr_H : frontier Δ_H = D.U := by rw [subBd_eq_frontier', hΔ_H_bd]
    have hint_D_dis_H : Disjoint (ins' D \ D.U) Δ_H := by
      obtain ⟨hOD_H, hcl_H, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ_H_disc
      rw [hΔ_H_bd] at hOD_H hcl_H
      have hdis_int : Disjoint (ins' D \ D.U) (Δ_H \ D.U) := by
        by_contra hnot
        obtain ⟨p, hpD, hpH⟩ := not_disjoint_iff.mp hnot
        have hsub : Δ_H \ D.U ⊆ ins' D :=
          subset_of_disjoint_frontier hOD_H.isPathConnected.isConnected.isPreconnected
            hDdisc.isClosed (hfrD ▸ disjoint_sdiff_self_left) hpH hpD.1
        have hΔ_H_sub : Δ_H ⊆ ins' D :=
          hcl_H ▸ hDdisc.isClosed.closure_subset_iff.mpr hsub
        have hins_univ : ins' D = univ := by
          rw [← hcov, union_eq_left.mpr hΔ_H_sub]
        have hbd_empty : D.U = ∅ := by
          rw [← hfrD, hins_univ, frontier_univ]
        obtain ⟨q, hq⟩ := IsOArc.nonempty hDU_oArc
        rw [hbd_empty] at hq
        exact hq
      refine Set.disjoint_left.mpr fun x hxD hxH => ?_
      by_cases hxU : x ∈ D.U
      · exact hxD.2 hxU
      · exact Set.disjoint_left.mp hdis_int hxD ⟨hxH, hxU⟩
    have hcompl_D : univ \ ins' D = Δ_H \ D.U := by
      ext x
      constructor
      · rintro ⟨hx_u, hx_not_D⟩
        rcases hcov.symm ▸ hx_u with hxD | hxH
        · exact absurd hxD hx_not_D
        · exact ⟨hxH, fun hxU => hx_not_D (hDdisc.isClosed.frontier_subset (hfrD.symm ▸ hxU))⟩
      · rintro ⟨hxH, hx_not_U⟩
        refine ⟨mem_univ _, fun hxD => ?_⟩
        exact Set.disjoint_left.mp hint_D_dis_H ⟨hxD, hx_not_U⟩ hxH
    have hcompl_H : univ \ Δ_H = ins' D \ D.U := by
      ext x
      constructor
      · rintro ⟨hx_u, hx_not_H⟩
        rcases hcov.symm ▸ hx_u with hxD | hxH
        · exact ⟨hxD, fun hxU => hx_not_H (hΔ_H_disc.isClosed.frontier_subset (hfr_H.symm ▸ hxU))⟩
        · exact absurd hxH hx_not_H
      · rintro ⟨hxD, hx_not_U⟩
        refine ⟨mem_univ _, fun hxH => ?_⟩
        exact Set.disjoint_left.mp hint_D_dis_H ⟨hxD, hx_not_U⟩ hxH
    obtain ⟨_, hcl_H_eq, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hΔ_H_disc
    obtain ⟨_, hcl_D_eq, _⟩ := IsClosedDisc.isOpenDisc_diff_subBd hS hDdisc
    rw [hΔ_H_bd] at hcl_H_eq
    rw [hDbd] at hcl_D_eq
    have hcl_compl_D : closure (univ \ ins' D) = Δ_H := by
      rw [hcompl_D, hcl_H_eq]
    have hcl_compl_H : closure (univ \ Δ_H) = ins' D := by
      rw [hcompl_H, hcl_D_eq]
    set A₀ := (PaintingOrDrawing.drawing H).inter Δ_H
    set B₀ := (PaintingOrDrawing.drawing H).interOutside Δ_H
    have hB₀_eq : B₀ = (PaintingOrDrawing.drawing H).inter (ins' D) := by
      change (PaintingOrDrawing.drawing H).inter (closure (univ \ Δ_H)) = _
      rw [hcl_compl_H]
    have hA₀_eq : A₀ = (PaintingOrDrawing.drawing H).interOutside (ins' D) := by
      symm
      change (PaintingOrDrawing.drawing H).inter (closure (univ \ ins' D)) = _
      rw [hcl_compl_D]
    have hord₀ : separationOrder A₀ B₀ < θ' := by
      have hsub₀ : (A₀ ∩ B₀).vertexSet ⊆ D.V ∩ H'.V := by
        rw [hA₀_eq, hB₀_eq]
        rintro x ⟨h1, h2⟩
        exact hAB_V_sub ⟨h2, h1⟩
      have hle₀ := ncard_le_ncard hsub₀ (D.finite_V.subset inter_subset_left)
      change (A₀ ∩ B₀).vertexSet.ncard < θ'
      omega
    have hmem' := hCleared.mem_of_order_lt A₀ B₀ hΔ_H_sep hord₀
    have hinter_eq : ∀ X : Set S,
        (PaintingOrDrawing.drawing H).inter X ∩ H'.toHypergraph =
          (PaintingOrDrawing.drawing H').inter X := by
      intro X
      refine Hypergraph.ext ?_ ?_ ?_
      · change (H.V ∩ X) ∩ H'.V = H'.V ∩ X
        ext v
        exact ⟨fun ⟨⟨_, hvX⟩, hv'⟩ => ⟨hv', hvX⟩,
          fun ⟨hv', hvX⟩ => ⟨⟨hSub'.1 hv', hvX⟩, hv'⟩⟩
      · change {e ∈ H.E | e ⊆ X} ∩ H'.E = {e ∈ H'.E | e ⊆ X}
        ext e
        exact ⟨fun ⟨⟨_, heX⟩, he'⟩ => ⟨he', heX⟩,
          fun ⟨he', heX⟩ => ⟨⟨hSub'.2 he', heX⟩, he'⟩⟩
      · funext e v
        apply propext
        change ((H.toHypergraph.Inc e v ∧ e ⊆ X ∧ v ∈ X) ∧ H'.toHypergraph.Inc e v) ↔
          (H'.toHypergraph.Inc e v ∧ e ⊆ X ∧ v ∈ X)
        exact ⟨fun ⟨⟨_, heX, hvX⟩, hinc'⟩ => ⟨hinc', heX, hvX⟩,
          fun ⟨⟨he', hv', hve⟩, heX, hvX⟩ =>
            ⟨⟨⟨hSub'.2 he', hSub'.1 hv', hve⟩, heX, hvX⟩, he', hv', hve⟩⟩
    have hA₀_inter : A₀ ∩ H'.toHypergraph = (PaintingOrDrawing.drawing H').interOutside (ins' D)
      := by
      rw [hA₀_eq]
      exact hinter_eq (closure (univ \ ins' D))
    have hB₀_inter : B₀ ∩ H'.toHypergraph = (PaintingOrDrawing.drawing H').inter (ins' D) := by
      rw [hB₀_eq]
      exact hinter_eq (ins' D)
    rw [hA₀_inter, hB₀_inter] at hmem'
    have hsep_D' := hCleared.hasMetric.1.2.1.isSeparation hDsep'
    refine hCleared.hasMetric.1.2.1.axiom2 hDsep' hmem' hmem' ?_
    rw [GM10.union_assoc, GM10.union_self, hsep_D'.union_eq]

/-- Graph Minors XIV, (7.8) (pages 38–39):
"Let $\beta \ge 4$ be even, let $\lambda \ge 0$, and let $\theta \ge 4\lambda + 2$. Let $H$
be a 2-cell drawing in $\Sigma$, and let $\mathscr{T}$ be a respectful tangle in $H$ of
order $\theta$. Let $z \in A(H)$, let $C_1$, $C_2$ be disjoint circuits of $H$, and let
$U(C_1)$, $U(C_2)$ bound closed discs $\Delta_1$, $\Delta_2 \subseteq \Sigma$ with the
following properties:* (i) $z \subseteq \Delta_2 - bd(\Delta_2)$, and $\Delta_2 \subseteq
\Delta_1 - bd(\Delta_1)$ (ii) $\Delta_1 - bd(\Delta_1)$ is a $(\theta - \beta - 4\lambda -
2)$-zone around $z$ (iii) $\Delta_2 - bd(\Delta_2)$ is a $\lambda$-zone around $z$ (iv) $x
\subseteq \Delta_1 - bd(\Delta_1)$ for every $x \in A(H)$ with $d(z, x) < \beta$, and (v)
*there are circuits $C_3, \dots, C_{\beta/2}$ of $H \cap \Delta_1$ such that $C_1$, $C_2$,
$\dots$, $C_{\beta/2}$ are mutually disjoint and $U(C_3), \dots, U(C_{\beta/2})$ all bound
closed discs in $\Delta_1$ including $\Delta_2$.* ... *Let $P_1, \dots, P_\beta$ be disjoint
paths of $H$ from $V(C_2)$ to $V(C_1)$, such that for $1 \le i \le \beta$, $P_i$ has initial
vertex $v_i \in V(C_2)$ and $U(P_i) \cap (\Delta_2 - bd(\Delta_2)) = \emptyset$. Then
$\{v_1, \dots, v_\beta\}$ is free with respect to the tangle of order $\theta - 4\lambda -
2$ obtained from $\mathscr{T}$ by clearing the $\lambda$-zone $\Delta_2 - bd(\Delta_2)$." -/
theorem theorem_7_8_proof
    [T2Space S] (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H C₁ C₂ : Drawing S} {θ beta lam : ℕ}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {z Δ₁ Δ₂ : Set S}
    {C : Fin (beta / 2) → Drawing S} {Δ : Fin (beta / 2) → Set S}
    {P : Fin beta → Drawing S} {v u : Fin beta → S}
    (_hbeta : 4 ≤ beta) (heven : Even beta) (hθ : beta + 4 * lam + 2 ≤ θ)
    (hMetric : HasTangleMetric H θ T d)
    (hCleared : IsClearedTangle H T d θ lam (Δ₂ \ subBd Δ₂) T' d')
    (_hC₁ : C₁.IsCircuit) (hC₁s : C₁.IsSubdrawing H)
    (hΔ₁ : IsClosedDisc Δ₁) (hbd₁ : subBd Δ₁ = C₁.U)
    (_hC₂ : C₂.IsCircuit) (hC₂s : C₂.IsSubdrawing H)
    (hΔ₂ : IsClosedDisc Δ₂) (hbd₂ : subBd Δ₂ = C₂.U)
    (hi : z ⊆ Δ₂ \ subBd Δ₂ ∧ Δ₂ ⊆ Δ₁ \ subBd Δ₁)
    (hii : IsLambdaZoneAround H d (θ - beta - 4 * lam - 2) z (Δ₁ \ subBd Δ₁))
    (hiii : IsLambdaZoneAround H d lam z (Δ₂ \ subBd Δ₂))
    (hiv : ∀ x ∈ H.A, d z x < beta → x ⊆ Δ₁ \ subBd Δ₁)
    (hv_C : ∀ i : Fin (beta / 2),
      (C i).IsCircuit ∧ (C i).IsSubdrawing H ∧ IsClosedDisc (Δ i) ∧
      subBd (Δ i) = (C i).U ∧ Δ₂ ⊆ Δ i ∧ Δ i ⊆ Δ₁)
    (hv_dis : Pairwise (fun i₁ i₂ : Fin (beta / 2) => Disjoint (C i₁).V (C i₂).V))
    (hP : ∀ j : Fin beta,
      (P j).IsPathBetween (v j) (u j) ∧ (P j).IsSubdrawing H ∧
      v j ∈ C₂.V ∧ u j ∈ C₁.V ∧ Disjoint (P j).U (Δ₂ \ subBd Δ₂))
    (hP_dis : Pairwise (fun j₁ j₂ : Fin beta => Disjoint (P j₁).V (P j₂).V)) :
    IsFreeSet (clearedSubdrawing H (Δ₂ \ subBd Δ₂)).toHypergraph T' (θ - 4 * lam - 2) (range v)
      := by
  set Λ₂ := Δ₂ \ subBd Δ₂
  set H' := clearedSubdrawing H Λ₂
  set θ' := θ - 4 * lam - 2
  obtain ⟨hV', _⟩ := clearedSubdrawing_V_and_E hiii
  have hv_in_P : ∀ j : Fin beta, v j ∈ (P j).V := by
    intro j
    obtain ⟨W, _, hPV, _⟩ := (hP j).1
    rw [hPV]
    exact W.start_mem_support
  have hv_inj : Injective v := by
    intro j₁ j₂ hveq
    by_contra hne
    exact Set.disjoint_left.mp (hP_dis hne) (hv_in_P j₁) (hveq ▸ hv_in_P j₂)
  have hrange_ncard : (range v).ncard = beta := by
    rw [ncard_range_of_injective hv_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hrange_sub : range v ⊆ H'.toHypergraph.vertexSet := by
    rintro x ⟨j, rfl⟩
    change v j ∈ H'.V
    rw [hV']
    refine ⟨hC₂s.1 (hP j).2.2.1, fun hxΛ₂ => ?_⟩
    exact hxΛ₂.2 (hbd₂ ▸ C₂.V_subset_U (hP j).2.2.1)
  refine ⟨hrange_sub, by omega, ?_⟩
  intro A' B' hAB' hrange_A'
  by_contra hlt_ord
  push Not at hlt_ord
  rw [hrange_ncard] at hlt_ord
  change (A' ∩ B').vertexSet.ncard < beta at hlt_ord
  have hsep' : H'.toHypergraph.IsSeparation A' B' := hCleared.hasMetric.1.2.1.isSeparation hAB'
  have hfin_AB' : (A' ∩ B').vertexSet.Finite :=
    H'.finite_V.subset hsep'.left_le.vertexSet_subset |>.subset inter_subset_left
  obtain ⟨j, hdis_Pj⟩ := exists_disjoint_of_ncard_lt hP_dis hfin_AB' hlt_ord
  have h2m : (A' ∩ B').vertexSet.ncard < 2 * (beta / 2) := by
    obtain ⟨k, rfl⟩ := heven
    omega
  obtain ⟨i, hle_Ci⟩ := exists_inter_ncard_le_one_of_ncard_lt_two_mul hv_dis hfin_AB' h2m
  have hPj_sub_H' : (P j).IsSubdrawing H' :=
    isSubdrawing_clearedSubdrawing hiii (hP j).2.1 (hP j).2.2.2.2
  have hΔ₂_int_Δi : Λ₂ ⊆ Δ i \ subBd (Δ i) := by
    have h₁ : Λ₂ = interior Δ₂ := by
      change Δ₂ \ subBd Δ₂ = interior Δ₂
      rw [← subBd_eq_frontier']
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    have h₂ : Δ i \ subBd (Δ i) = interior (Δ i) := by
      rw [← subBd_eq_frontier']
      ext x
      exact ⟨fun ⟨hx, hnf⟩ => by_contra fun hni => hnf ⟨subset_closure hx, hni⟩,
        fun hx => ⟨interior_subset hx, fun hf => hf.2 hx⟩⟩
    rw [h₁, h₂]
    exact interior_mono (hv_C i).2.2.2.2.1
  have hdis_Ci_Λ₂ : Disjoint (C i).U Λ₂ := by
    refine Set.disjoint_left.mpr fun x hxCi hxΛ₂ => ?_
    exact (hΔ₂_int_Δi hxΛ₂).2 ((hv_C i).2.2.2.1 ▸ hxCi)
  have hCi_sub_H' : (C i).IsSubdrawing H' :=
    isSubdrawing_clearedSubdrawing hiii (hv_C i).2.1 hdis_Ci_Λ₂
  have hvj_Δ₂ : v j ∈ Δ₂ := by
    have : v j ∈ subBd Δ₂ := hbd₂ ▸ C₂.V_subset_U (hP j).2.2.1
    rw [← subBd_eq_frontier'] at this
    exact hΔ₂.isClosed.frontier_subset this
  have hvj_Δi : v j ∈ Δ i := (hv_C i).2.2.2.2.1 hvj_Δ₂
  have huj_bd₁ : u j ∈ subBd Δ₁ := hbd₁ ▸ C₁.V_subset_U (hP j).2.2.2.1
  have hne_Ci_Pj : ((C i).V ∩ (P j).V).Nonempty :=
    circuit_inter_path_nonempty hS (hv_C i).2.2.1 hΔ₁ (hv_C i).2.2.2.2.2 (hv_C i).2.1
      (hv_C i).2.2.2.1 (hP j).1 (hP j).2.1 hvj_Δi huj_bd₁
  have hz_Δi : z ⊆ Δ i \ subBd (Δ i) := hi.1.trans hΔ₂_int_Δi
  have hZone_i_H : IsLambdaZoneAround H d (θ - beta - 4 * lam - 2) z (Δ i \ subBd (Δ i)) :=
    zone_of_closedDisc_subset hS hii hΔ₁ (hv_C i).2.2.1 (hv_C i).2.2.2.2.2 (hv_C i).1
      (hv_C i).2.1 (hv_C i).2.2.2.1 hz_Δi
  have hZone_i_H' : IsLambdaZoneAround H' d' (θ - beta - 4 * lam - 2) Λ₂ (Δ i \ subBd (Δ i)) :=
    cleared_zone_of_closedDisc_subset hS hZone_i_H hiii hCleared (hv_C i).2.2.1 hΔ₂
      (hv_C i).2.2.2.2.1 (hv_C i).1 (hv_C i).2.1 (hv_C i).2.2.2.1
  obtain ⟨_, K', ins', hK', hd', _⟩ := hCleared.hasMetric
  have hord'_lam : separationOrder A' B' + (θ - beta - 4 * lam - 2) < θ' := by
    change (A' ∩ B').vertexSet.ncard + (θ - beta - 4 * lam - 2) < θ'
    omega
  obtain ⟨D, hD, hDs, hDlen, hDV, hΔi_sub_D, -⟩ :=
    circuit_of_sep_in_zone hS hConn hCleared.hasMetric hK' hd' hAB' hZone_i_H'
      (hv_C i).2.2.1 (hv_C i).1 hCi_sub_H' (hv_C i).2.2.2.1 hord'_lam (hP j).1 hPj_sub_H'
      hvj_Δi (hrange_A' ⟨j, rfl⟩) hdis_Pj hne_Ci_Pj hle_Ci
  have hΔ₂_sub_D : Δ₂ ⊆ ins' D := (hv_C i).2.2.2.2.1.trans hΔi_sub_D
  obtain ⟨hAB_H, hAB_H_sub⟩ :=
    inter_ins_mem_of_cleared hS hConn hMetric hiii hCleared hΔ₂ hK' hd' hD hDs hDlen hΔ₂_sub_D
  set A_H := (PaintingOrDrawing.drawing H).inter (ins' D)
  set B_H := (PaintingOrDrawing.drawing H).interOutside (ins' D)
  have hAB_H_sub_AB' : (A_H ∩ B_H).vertexSet ⊆ (A' ∩ B').vertexSet := hAB_H_sub.trans hDV
  have hord_H_lt : (A_H ∩ B_H).vertexSet.ncard < beta :=
    (ncard_le_ncard hAB_H_sub_AB' hfin_AB').trans_lt hlt_ord
  have hord_H_lam : separationOrder A_H B_H + (θ - beta - 4 * lam - 2) < θ := by
    change (A_H ∩ B_H).vertexSet.ncard + (θ - beta - 4 * lam - 2) < θ
    omega
  have hvj_AH : v j ∈ A_H.vertexSet := ⟨hC₂s.1 (hP j).2.2.1, hΔ₂_sub_D hvj_Δ₂⟩
  have hdis_Pj_H : Disjoint (P j).V (A_H ∩ B_H).vertexSet :=
    hdis_Pj.mono_right hAB_H_sub_AB'
  have hle_Ci_H : ((C i).V ∩ (A_H ∩ B_H).vertexSet).ncard ≤ 1 := by
    refine (ncard_le_ncard (inter_subset_inter_right (C i).V hAB_H_sub_AB') ?_).trans hle_Ci
    exact (C i).finite_V.subset inter_subset_left
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hMetric' : HasTangleMetric H θ T d := ⟨hResp, K, ins, hK, hd, hd_eq⟩
  obtain ⟨D_star, hD_star, hD_star_s, hD_star_len, hD_star_V, hΔi_sub_star, hPj_sub_star⟩ :=
    circuit_of_sep_in_zone hS hConn hMetric' hK hd hAB_H hZone_i_H
      (hv_C i).2.2.1 (hv_C i).1 (hv_C i).2.1 (hv_C i).2.2.2.1 hord_H_lam (hP j).1 (hP j).2.1
      hvj_Δi hvj_AH hdis_Pj_H hne_Ci_Pj hle_Ci_H
  obtain ⟨p_z, hp_z⟩ := atom_nonempty hiii.z_mem
  have hz_star : (z ∩ ins D_star).Nonempty :=
    ⟨p_z, hp_z, hΔi_sub_star ((hv_C i).2.2.2.2.1 (hi.1 hp_z).1)⟩
  have huj_HV : u j ∈ H.V := hC₁s.1 (hP j).2.2.2.1
  have huj_A : ({u j} : Set S) ∈ H.A := Or.inl (Or.inl ⟨u j, huj_HV, rfl⟩)
  obtain ⟨W_Pj, _, hPV_j, _⟩ := (hP j).1
  have huj_PjU : u j ∈ (P j).U := (P j).V_subset_U (by rw [hPV_j]; exact W_Pj.end_mem_support)
  have huj_star : (({u j} : Set S) ∩ ins D_star).Nonempty :=
    ⟨u j, mem_singleton (u j), (hPj_sub_star huj_PjU).1⟩
  have hd_le : d z {u j} ≤ (D_star.V ∩ H.V).ncard := by
    rw [hd_eq z hiii.z_mem {u j} huj_A]
    exact (tangleMetric_le_of_circuit hS hK hd hD_star hD_star_s hD_star_len hiii.z_mem huj_A
      hz_star huj_star).2
  have hncard_star : (D_star.V ∩ H.V).ncard < beta := by
    refine (ncard_le_ncard (hD_star_V.trans hAB_H_sub_AB') hfin_AB').trans_lt hlt_ord
  have hd_lt : d z {u j} < beta := hd_le.trans_lt hncard_star
  have huj_in_int₁ : u j ∈ Δ₁ \ subBd Δ₁ := hiv {u j} huj_A hd_lt (mem_singleton (u j))
  exact huj_in_int₁.2 huj_bd₁

end GraphMinor.GM14
