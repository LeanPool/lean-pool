/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Contract
public import LeanPool.GraphMinor.GM17.ReplaceDisc

/-!
# Graph Minors XIX, (6.3)

If `G` has an enlargement in `G'` then `G` is isomorphic to a drawing `H` in the same surface with
`rep(H) ≤ rep(G')` (`theorem_6_3`, page 340). The proof is the paper's. We reduce to trees, pass to
the subdrawing `H'` of `G'` made of these trees and the edges `σ(e)`, for which `rep(H') ≤ rep(G')`
(`rep_le_of_isSubdrawing`), and then contract the edges of the trees (`exists_contract_set`). The
paper identifies the points of each tree at once and says that the surface does not change. We
contract one edge at a time by `exists_contract`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- Two points that are ends of one edge of `A`. -/
def EdgeRel (A : Set (Set S)) (x y : S) : Prop := ∃ e ∈ A, x ∈ tilde e ∧ y ∈ tilde e

/-- Two points joined by a path of edges of `A`, or equal. -/
abbrev Conn (A : Set (Set S)) : S → S → Prop := Relation.EqvGen (EdgeRel A)

theorem Conn.map_eq {α : Type*} {A : Set (Set S)} (ρ : S → α)
    (h : ∀ e ∈ A, ∀ x ∈ tilde e, ∀ y ∈ tilde e, ρ x = ρ y) {x y : S} (hc : Conn A x y) : ρ x = ρ y
      := by
  induction hc with
  | rel x y h' => obtain ⟨e, he, h1, h2⟩ := h'; exact h e he x h1 y h2
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ h1 h2 => exact h1.trans h2

theorem Conn.mono {A B : Set (Set S)} (h : ∀ x y, EdgeRel A x y → Conn B x y) {x y : S}
    (hc : Conn A x y) : Conn B x y := by
  induction hc with
  | rel x y h' => exact h x y h'
  | refl x => exact .refl x
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ h1 h2 => exact .trans _ _ _ h1 h2

theorem Conn.of_subset {A B : Set (Set S)} (h : A ⊆ B) {x y : S} (hc : Conn A x y) : Conn B x y :=
  hc.mono fun _ _ ⟨e, he, h1, h2⟩ => .rel _ _ ⟨e, h he, h1, h2⟩

theorem conn_of_reachable {α : Type*} {G : SimpleGraph α} {A : Set (Set S)} (f : α → S)
    (h : ∀ a b, G.Adj a b → Conn A (f a) (f b)) {a b : α} (hr : G.Reachable a b) :
    Conn A (f a) (f b) := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact .refl _
  | cons hadj _ ih => exact .trans _ _ _ (h _ _ hadj) ih

/-- **Contracting a forest.** Let `C` be a finite set of edges of a loop-free drawing `D` such that
no edge of `C` has its ends joined by the other edges of `C`, and no other edge has its ends joined
by `C`. Then we can contract `C`. -/
theorem exists_contract_set (hT : IsClosedSurface S) {D : Drawing S} (hD : LoopFree D)
    {C : Set (Set S)} (hC : C ⊆ D.E)
    (hf : ∀ f ∈ C, ∀ x ∈ tilde f, ∀ y ∈ tilde f, x ≠ y → ¬ Conn (C \ {f}) x y)
    (ho : ∀ e ∈ D.E \ C, ∀ x ∈ tilde e, ∀ y ∈ tilde e, x ≠ y → ¬ Conn C x y) :
    ∃ (H : Drawing S) (π : S → S) (ε : Set S → Set S), LoopFree H ∧ H.V = π '' D.V ∧
      (∀ x ∈ D.V, ∀ y ∈ D.V, π x = π y ↔ Conn C x y) ∧ BijOn ε (D.E \ C) H.E ∧
      (∀ e ∈ D.E \ C, tilde (ε e) = π '' tilde e) ∧ H.rep ≤ D.rep := by
  classical
  have ht2 : T2Space S := hT.2.1
  have hV : ∀ e ∈ D.E, tilde e ⊆ D.V := fun e he x hx => by
    rw [tilde_eq_inter_V D he] at hx
    exact hx.2
  have hCf : C.Finite := D.finite_edges.subset hC
  have key : ∀ C₀ : Set (Set S), C₀.Finite → C₀ ⊆ C → ∃ (H : Drawing S) (π : S → S) (ε : Set S
    → Set S),
      LoopFree H ∧ H.V = π '' D.V ∧ (∀ x ∈ D.V, ∀ y ∈ D.V, π x = π y ↔ Conn C₀ x y) ∧
      BijOn ε (D.E \ C₀) H.E ∧ (∀ e ∈ D.E \ C₀, tilde (ε e) = π '' tilde e) ∧ H.rep ≤ D.rep := by
    intro C₀ hfin
    induction C₀, hfin using Finite.induction_on with
    | empty =>
      intro _
      refine ⟨D, id, id, hD, (image_id _).symm, ?_, ?_, ?_, le_rfl⟩
      · intro x _ y _
        constructor
        · rintro rfl
          exact .refl _
        · intro h
          exact Conn.map_eq id (fun e he => absurd he (notMem_empty e)) h
      · rw [sdiff_empty]
        exact bijOn_id _
      · intro e _
        rw [image_id]
        rfl
    | @insert f C₀ hfC₀ _ ih =>
      intro hsub
      have hfC : f ∈ C := hsub (mem_insert _ _)
      have hC₀ : C₀ ⊆ C := (subset_insert _ _).trans hsub
      have hC₀' : C₀ ⊆ C \ {f} := fun x hx => ⟨hC₀ hx, fun h => hfC₀ (h ▸ hx)⟩
      obtain ⟨H, π, ε, hH, hHV, hπ, hε, hεt, hrep⟩ := ih hC₀
      have hfE : f ∈ D.E \ C₀ := ⟨hC hfC, hfC₀⟩
      have hf' : ε f ∈ H.E := hε.mapsTo hfE
      obtain ⟨u, v, huv, hfe, -⟩ := hD f (hC hfC)
      have huT : u ∈ tilde f := by rw [hfe]; exact .inl rfl
      have hvT : v ∈ tilde f := by rw [hfe]; exact .inr rfl
      have huV := hV f (hC hfC) huT
      have hvV := hV f (hC hfC) hvT
      have hnotconn : ¬ Conn C₀ u v := fun h => hf f hfC u huT v hvT huv (h.of_subset hC₀')
      have hno : ∀ e' ∈ H.E, e' ≠ ε f → tilde e' ≠ tilde (ε f) := by
        intro e' he' hne heq
        obtain ⟨e, he, rfl⟩ := hε.surjOn he'
        have hef : e ≠ f := fun h => hne (h ▸ rfl)
        obtain ⟨p, q, hpq, hte, -⟩ := hD e he.1
        have hpT : p ∈ tilde e := by rw [hte]; exact .inl rfl
        have hqT : q ∈ tilde e := by rw [hte]; exact .inr rfl
        have hpV := hV e he.1 hpT
        have hqV := hV e he.1 hqT
        rw [hεt e he, hεt f hfE] at heq
        -- each of `p, q` is joined to an end of `f`
        have h1 : π p ∈ π '' tilde f := heq ▸ mem_image_of_mem _ hpT
        have h2 : π q ∈ π '' tilde f := heq ▸ mem_image_of_mem _ hqT
        have h3 : π u ∈ π '' tilde e := heq ▸ mem_image_of_mem _ huT
        have h4 : π v ∈ π '' tilde e := heq ▸ mem_image_of_mem _ hvT
        have hcase : (Conn C₀ p u ∧ Conn C₀ q v) ∨ (Conn C₀ p v ∧ Conn C₀ q u) := by
          rw [hfe] at h1 h2
          have hu : ∀ z, z = u ∨ z = v → z ∈ D.V := by
            rintro z (rfl | rfl)
            · exact huV
            · exact hvV
          obtain ⟨z, hz, hzp⟩ := h1
          obtain ⟨z', hz', hzq⟩ := h2
          have c1 := (hπ z (hu z hz) p hpV).mp hzp
          have c2 := (hπ z' (hu z' hz') q hqV).mp hzq
          rcases hz with hz | hz <;> rcases hz' with hz' | hz' <;> rw [hz] at c1 <;> rw [hz'] at c2
          · -- both `p` and `q` go to `u`, so `v` is joined to one of them
            rw [hte] at h4
            obtain ⟨y, hy, hyv⟩ := h4
            have c3 : Conn C₀ y v := (hπ y (by rcases hy with rfl | rfl
              <;> assumption) v hvV).mp hyv
            have c1' : Conn C₀ u y := by
              rcases hy with rfl | rfl
              · exact c1
              · exact c2
            exact absurd (Relation.EqvGen.trans _ _ _ c1' c3) hnotconn
          · exact .inl ⟨.symm _ _ c1, .symm _ _ c2⟩
          · exact .inr ⟨.symm _ _ c1, .symm _ _ c2⟩
          · rw [hte] at h3
            obtain ⟨y, hy, hyu⟩ := h3
            have c3 : Conn C₀ y u := (hπ y (by rcases hy with rfl | rfl
              <;> assumption) u huV).mp hyu
            have c1' : Conn C₀ v y := by
              rcases hy with rfl | rfl
              · exact c1
              · exact c2
            exact absurd (.symm _ _ (Relation.EqvGen.trans _ _ _ c1' c3)) hnotconn
        by_cases heC : e ∈ C
        · have heC' : e ∈ C \ {f} := ⟨heC, hef⟩
          have hrel : Conn (C \ {f}) p q := .rel _ _ ⟨e, heC', hpT, hqT⟩
          rcases hcase with ⟨c1, c2⟩ | ⟨c1, c2⟩
          · have c1' := c1.of_subset hC₀'
            have c2' := c2.of_subset hC₀'
            exact hf f hfC u huT v hvT huv (.trans _ _ _ (.symm _ _ c1') (.trans _ _ _ hrel c2'))
          · have c1' := c1.of_subset hC₀'
            have c2' := c2.of_subset hC₀'
            exact hf f hfC u huT v hvT huv (.trans _ _ _ (.symm _ _ c2') (.symm _ _ (.trans _ _ _
              (.symm _ _ c1') hrel)))
        · have hrel : Conn C u v := .rel _ _ ⟨f, hfC, huT, hvT⟩
          refine ho e ⟨he.1, heC⟩ p hpT q hqT hpq ?_
          rcases hcase with ⟨c1, c2⟩ | ⟨c1, c2⟩
          · exact .trans _ _ _ (c1.of_subset hC₀) (.trans _ _ _ hrel (.symm _ _ (c2.of_subset hC₀)))
          · exact .trans _ _ _ (c1.of_subset hC₀) (.trans _ _ _ (.symm _ _ hrel) (.symm _ _
            (c2.of_subset hC₀)))
      obtain ⟨H', φ, hH', hV', hφ, hb, ht, hr⟩ := exists_contract hT hH hf' hno
      refine ⟨H', φ ∘ π, image φ ∘ ε, hH', by rw [hV', hHV, image_comp], ?_, ?_, ?_, hr.trans hrep⟩
      · intro x hx y hy
        have hπV : ∀ x ∈ D.V, π x ∈ H.V := fun x hx => hHV ▸ mem_image_of_mem _ hx
        have htf := hεt f hfE
        rw [Function.comp_apply, Function.comp_apply, hφ _ (hπV x hx) _ (hπV y hy)]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact ((hπ x hx y hy).mp h).of_subset (subset_insert _ _)
          · rw [htf, hfe] at h1 h2
            have hu : ∀ z, z = u ∨ z = v → z ∈ D.V := by
              rintro z (rfl | rfl)
              · exact huV
              · exact hvV
            obtain ⟨z, hz, hzx⟩ := h1
            obtain ⟨z', hz', hzy⟩ := h2
            have c1 := ((hπ z (hu z hz) x hx).mp hzx).of_subset (subset_insert f C₀)
            have c2 := ((hπ z' (hu z' hz') y hy).mp hzy).of_subset (subset_insert f C₀)
            have hzT : ∀ z, z = u ∨ z = v → z ∈ tilde f := by
              rintro z (rfl | rfl)
              · exact huT
              · exact hvT
            have c3 : Conn (insert f C₀) z z' := .rel _ _ ⟨f, mem_insert _ _, hzT z hz, hzT z' hz'⟩
            exact .trans _ _ _ (.symm _ _ c1) (.trans _ _ _ c3 c2)
        · intro h
          have h1 : (φ ∘ π) x = (φ ∘ π) y := by
            refine Conn.map_eq (φ ∘ π) ?_ h
            intro e he a ha b hb'
            rcases he with rfl | he
            · have ha' : π a ∈ tilde (ε e) := by rw [htf]; exact mem_image_of_mem _ ha
              have hb'' : π b ∈ tilde (ε e) := by rw [htf]; exact mem_image_of_mem _ hb'
              exact (hφ _ (hπV a (hV e (hC hfC) ha)) _ (hπV b (hV e (hC hfC) hb'))).mpr
                (.inr ⟨ha', hb''⟩)
            · have heE := hC (hC₀ he)
              have : π a = π b := (hπ a (hV e heE ha) b (hV e heE hb')).mpr
                (.rel _ _ ⟨e, he, ha, hb'⟩)
              rw [Function.comp_apply, Function.comp_apply, this]
          exact (hφ _ (hπV x hx) _ (hπV y hy)).mp h1
      · have hsd : D.E \ insert f C₀ = (D.E \ C₀) \ {f} := by
          ext e
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
          tauto
        rw [hsd]
        have h1 : BijOn ε ((D.E \ C₀) \ {f}) (H.E \ {ε f}) := by
          refine ⟨fun e he => ⟨hε.mapsTo he.1, fun h => he.2 (hε.injOn he.1 hfE h)⟩,
            hε.injOn.mono sdiff_subset, fun y hy => ?_⟩
          obtain ⟨e, he, rfl⟩ := hε.surjOn hy.1
          exact ⟨e, ⟨he, fun h => hy.2 (h ▸ rfl)⟩, rfl⟩
        exact hb.comp h1
      · intro e he
        have he' : e ∈ D.E \ C₀ := ⟨he.1, fun h => he.2 (mem_insert_of_mem _ h)⟩
        have hne : e ≠ f := fun h => he.2 (h ▸ mem_insert _ _)
        have hne' : ε e ≠ ε f := fun h => hne (hε.injOn he' hfE h)
        rw [Function.comp_apply, ht _ (hε.mapsTo he') hne', hεt e he', image_comp]
  exact key C hCf Subset.rfl

/-- A subdrawing has `rep` at most that of the drawing. -/
theorem rep_le_of_isSubdrawing {H G : Drawing S} (h : H.IsSubdrawing G) : H.rep ≤ G.rep := by
  refine le_sInf ?_
  rintro _ ⟨F, hF, hn, hnull, rfl⟩
  have hnorm : H.IsNormal F := by
    rintro x ⟨hxF, hxU⟩
    by_contra hxV
    obtain ⟨e, he, hxe⟩ := exists_arcComp_superset (isPathConnected_singleton x)
      (singleton_subset_iff.mpr (show x ∈ H.U \ H.V from ⟨hxU, hxV⟩))
    have hxe' : x ∈ e := hxe rfl
    have hG := (h.2 he).2.1 hxe'
    exact hG.2 (hn ⟨hxF, hG.1⟩)
  refine (rep_le_of_arc H hF hnorm hnull).trans ?_
  have h1 : (F ∩ H.V).ncard ≤ (F ∩ G.V).ncard :=
    ncard_le_ncard (inter_subset_inter_right _ h.1) (G.finite_V.subset inter_subset_right)
  exact_mod_cast h1

theorem loopFree_of_gm19 {D : Drawing S} (h : D.IsGM19Drawing) : LoopFree D := by
  intro e he
  obtain ⟨h1, -, ⟨f⟩, h3⟩ := h.no_loops e he
  have hl : IsLineWithEnds (closure e) (f 0).1 (f 1).1 := ⟨f, rfl, rfl⟩
  refine ⟨_, _, GM17.ne_of_isLineWithEnds hl, ?_, hl⟩
  rw [← h3, GM17.lineEnds_eq hl]

theorem gm19_of_loopFree {D : Drawing S} (hb : bd S = ∅) (h : LoopFree D) :
    D.IsGM19Drawing := by
  refine ⟨fun e he => ?_, fun e _ => .inr (by simp [hb])⟩
  obtain ⟨u, v, huv, ht, hl⟩ := h e he
  obtain ⟨f, -⟩ := id hl
  exact ⟨by rw [ht, ncard_pair huv], by rw [ht]; exact (finite_singleton _).insert _, ⟨f⟩,
    by rw [ht, GM17.lineEnds_eq hl]⟩

private theorem minimal_connecting_edges_acyclic
    {S : Type}
    [TopologicalSpace S]
    {G : Drawing S}
    {G' : Drawing S}
    {σv : S → Drawing S}
    (hLG' : LoopFree G')
    (C : Set (Set S))
    (hCg : ∀ v ∈ G.V, ∀ x ∈ (σv v).V, ∀ y ∈ (σv v).V, Conn C x y)
    (hCmin : ∀ C' ⊂ C, ¬(∀ v ∈ G.V, ∀ x ∈ (σv v).V, ∀ y ∈ (σv v).V, Conn C' x y))
    (hCG' : C ⊆ Drawing.E G') :
    ∀ f ∈ C, ∀ x ∈ tilde f, ∀ y ∈ tilde f, x ≠ y → ¬Conn (C \ {f}) x y := by
  intro f hf x hx y hy hxy hconn
  obtain ⟨a, b, -, hfe, -⟩ := hLG' f (hCG' hf)
  have hall : ∀ p ∈ tilde f, ∀ q ∈ tilde f, Conn (C \ {f}) p q := by
    intro p hp q hq
    rw [hfe] at hx hy hp hq
    by_cases hpq : p = q
    · exact hpq ▸ .refl _
    · have hset : ({p, q} : Set S) = {x, y} := by
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hp with rfl | rfl <;>
          rcases hq with rfl | rfl <;>
          first | exact absurd rfl hxy | exact absurd rfl hpq | rfl | exact pair_comm _ _
      have hp' : p ∈ ({x, y} : Set S) := hset ▸ .inl rfl
      have hq' : q ∈ ({x, y} : Set S) := hset ▸ .inr rfl
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact .refl _
      · exact hconn
      · exact .symm _ _ hconn
      · exact .refl _
  have hgood : ∀ v ∈ G.V, ∀ p ∈ (σv v).V, ∀ q ∈ (σv v).V, Conn (C \ {f}) p q := by
    intro v hv p hp q hq
    refine (hCg v hv p hp q hq).mono ?_
    rintro a' b' ⟨e, he, h1, h2⟩
    by_cases hef : e = f
    · subst hef
      exact hall a' h1 b' h2
    · exact .rel _ _ ⟨e, ⟨he, hef⟩, h1, h2⟩
  exact hCmin (C \ {f}) ⟨sdiff_subset, fun h => (h hf).2 rfl⟩ hgood

/-- **Graph Minors XIX, (6.3)** (page 340). If there is an enlargement of `G` in `G'`, for drawings
in a surface with no boundary, then `G` is isomorphic to a drawing `H` in the surface with `rep(H) ≤
rep(G')`. -/
theorem theorem_6_3_proof (hT : IsClosedSurface S) (hb : bd S = ∅) {G G' : Drawing S}
  (hG : G.IsGM19Drawing)
    (hG' : G'.IsGM19Drawing) {σv : S → Drawing S} {σe : Set S → Set S}
      (hσ : IsEnlargement G G' σv σe) :
    ∃ H : Drawing S, H.IsGM19Drawing ∧ G.IsIsomorphic H ∧ H.rep ≤ G'.rep := by
  classical
  have ht2 : T2Space S := hT.2.1
  have hLG := loopFree_of_gm19 hG
  have hLG' := loopFree_of_gm19 hG'
  have hsubV : ∀ v ∈ G.V, (σv v).V ⊆ G'.V := fun v hv => (hσ.vertex_subdrawing v hv).1
  have hsubE : ∀ v ∈ G.V, (σv v).E ⊆ G'.E := fun v hv => (hσ.vertex_subdrawing v hv).2
  -- the label of a vertex of a branch set
  let ρ : S → S := fun x => if h : ∃ v ∈ G.V, x ∈ (σv v).V then h.choose else x
  have hρ : ∀ v ∈ G.V, ∀ x ∈ (σv v).V, ρ x = v := by
    intro v hv x hx
    have h : ∃ v ∈ G.V, x ∈ (σv v).V := ⟨v, hv, hx⟩
    simp only [ρ, dite_eq_left h]
    by_contra hne
    exact (disjoint_left.mp (hσ.vertex_disjoint _ h.choose_spec.1 v hv hne)) h.choose_spec.2 hx
  have hsV : ∀ v ∈ G.V, ∀ e ∈ (σv v).E, tilde e ⊆ (σv v).V := fun v _ e he x hx => by
    rw [tilde_eq_inter_V (σv v) he] at hx
    exact hx.2
  let VV : Set S := ⋃ v ∈ G.V, (σv v).V
  have hUV : ∀ x ∈ VV, ∃ v ∈ G.V, x ∈ (σv v).V := fun x hx => by
    obtain ⟨v, hv, h⟩ := mem_iUnion₂.mp hx
    exact ⟨v, hv, h⟩
  let A : Set (Set S) := ⋃ v ∈ G.V, (σv v).E
  have hAE : A ⊆ G'.E := iUnion₂_subset hsubE
  have hAf : A.Finite := G'.finite_edges.subset hAE
  let Good : Set (Set S) → Prop := fun C => ∀ v ∈ G.V, ∀ x ∈ (σv v).V, ∀ y ∈ (σv v).V, Conn C x y
  have hgoodA : Good A := by
    intro v hv x hx y hy
    have h1 := hσ.vertex_connected v hv (⟨x, hx⟩ : (σv v).V) ⟨y, hy⟩
    refine conn_of_reachable (G := (σv v).adj.induce (σv v).V) (A := A) Subtype.val ?_ h1
    rintro ⟨a, ha⟩ ⟨b, hb'⟩ ⟨-, -, -, e, he, h2, h3⟩
    exact .rel _ _ ⟨e, mem_iUnion₂.mpr ⟨v, hv, he⟩, h2, h3⟩
  -- a minimal set of edges keeping the branch sets connected: a forest
  obtain ⟨C, hCA, hCg, hCmin⟩ : ∃ C ⊆ A, Good C ∧ ∀ C' ⊂ C, ¬ Good C' := by
    have hfin : ({C | C ⊆ A ∧ Good C} : Set (Set (Set S))).Finite :=
      hAf.powerset.subset fun C hC => hC.1
    obtain ⟨C, hC, hmin⟩ := hfin.exists_minimal ⟨A, Subset.rfl, hgoodA⟩
    refine ⟨C, hC.1, hC.2, fun C' hC' hg => ?_⟩
    exact hC'.2 (hmin ⟨hC'.1.trans hC.1, hg⟩ hC'.1)
  have hCE : ∀ e ∈ C, ∃ v ∈ G.V, e ∈ (σv v).E := fun e he => by
    obtain ⟨v, hv, h⟩ := mem_iUnion₂.mp (hCA he)
    exact ⟨v, hv, h⟩
  have hρC : ∀ e ∈ C, ∀ x ∈ tilde e, ∀ y ∈ tilde e, ρ x = ρ y := by
    intro e he x hx y hy
    obtain ⟨v, hv, h⟩ := hCE e he
    rw [hρ v hv x (hsV v hv e h hx), hρ v hv y (hsV v hv e h hy)]
  -- ends of the edges `σ(e)`
  have hends : ∀ e ∈ G.E, ∃ s ∈ G.V, ∃ t ∈ G.V, s ≠ t ∧ tilde e = {s, t} ∧ ∃ p ∈ (σv s).V, ∃ q ∈
    (σv t).V,
      p ≠ q ∧ tilde (σe e) = {p, q} := by
    intro e he
    obtain ⟨s, t, hst, hte, -⟩ := hLG e he
    have hsT : s ∈ tilde e := by rw [hte]; exact .inl rfl
    have htT : t ∈ tilde e := by rw [hte]; exact .inr rfl
    have hVG : tilde e ⊆ G.V := fun x hx => by
      rw [tilde_eq_inter_V G he] at hx
      exact hx.2
    have hsV' := hVG hsT
    have htV' := hVG htT
    obtain ⟨p, hp, hpT⟩ := (hσ.ends_iff e he s hsV').mpr hsT
    obtain ⟨q, hq, hqT⟩ := (hσ.ends_iff e he t htV').mpr htT
    have hpq : p ≠ q := fun h =>
      disjoint_left.mp (hσ.vertex_disjoint s hsV' t htV' hst) hp (h ▸ hq)
    refine ⟨s, hsV', t, htV', hst, hte, p, hp, q, hq, hpq, ?_⟩
    obtain ⟨u, v, huv, ht', -⟩ := hLG' _ (hσ.edge_mem e he)
    rw [ht'] at hpT hqT ⊢
    rcases hpT with rfl | rfl <;> rcases hqT with rfl | rfl
    · exact absurd rfl hpq
    · rfl
    · exact pair_comm _ _
    · exact absurd rfl hpq
  have hECdisj : ∀ e ∈ G.E, σe e ∉ C := by
    intro e he hC
    obtain ⟨s, hs, t, ht', hst, -, p, hp, q, hq, -, h1⟩ := hends e he
    have h2 := hρC _ hC p (by rw [h1]; exact .inl rfl) q (by rw [h1]; exact .inr rfl)
    rw [hρ s hs p hp, hρ t ht' q hq] at h2
    exact hst h2
  let D : Drawing S := G'.span VV (C ∪ σe '' G.E)
  have hCG' : C ⊆ G'.E := hCA.trans hAE
  have hσG' : σe '' G.E ⊆ G'.E := by
    rintro _ ⟨e, he, rfl⟩
    exact hσ.edge_mem e he
  have hDE : D.E = C ∪ σe '' G.E := by
    change (G'.span VV (C ∪ σe '' G.E)).E = _
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (union_subset hCG' hσG')
  have hUG' : VV ⊆ G'.V := iUnion₂_subset hsubV
  have hDV : D.V = VV := by
    apply Subset.antisymm
    · rintro x (⟨hx, -⟩ | hx)
      · exact hx
      · obtain ⟨e, ⟨he, heG⟩, hxe, hxV⟩ := mem_iUnion₂.mp hx
        have hxT : x ∈ tilde e := by
          rw [tilde_eq_inter_V G' heG]
          exact ⟨hxe, hxV⟩
        rcases he with he | ⟨e₀, he₀, rfl⟩
        · obtain ⟨v, hv, h⟩ := hCE e he
          exact mem_iUnion₂.mpr ⟨v, hv, hsV v hv e h hxT⟩
        · obtain ⟨s, hs, t, ht', -, -, p, hp, q, hq, -, h1⟩ := hends e₀ he₀
          rw [h1] at hxT
          rcases hxT with rfl | rfl
          · exact mem_iUnion₂.mpr ⟨s, hs, hp⟩
          · exact mem_iUnion₂.mpr ⟨t, ht', hq⟩
    · exact fun x hx => .inl ⟨hx, hUG' hx⟩
  have hDsub : D.IsSubdrawing G' := Drawing.span_isSubdrawing G' _ _
  have hLD : LoopFree D := fun e he => hLG' e (hDsub.2 he)
  have hCD : C ⊆ D.E := by rw [hDE]; exact subset_union_left
  have hsd : D.E \ C = σe '' G.E := by
    rw [hDE]
    ext e
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
    · rintro ⟨e₀, he₀, rfl⟩
      exact ⟨.inr ⟨e₀, he₀, rfl⟩, hECdisj e₀ he₀⟩
  have hforest : ∀ f ∈ C, ∀ x ∈ tilde f, ∀ y ∈ tilde f, x ≠ y → ¬ Conn (C \ {f}) x y := by
    exact minimal_connecting_edges_acyclic (S := S) (G := G) (G' := G') (σv := σv) hLG' C hCg
      hCmin hCG'
  have hother : ∀ e ∈ D.E \ C, ∀ x ∈ tilde e, ∀ y ∈ tilde e, x ≠ y → ¬ Conn C x y := by
    intro e he x hx y hy hxy hconn
    rw [hsd] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨s, hs, t, ht', hst, -, p, hp, q, hq, hpq, h1⟩ := hends e₀ he₀
    have h2 := Conn.map_eq ρ hρC hconn
    rw [h1] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy rfl
    · rw [hρ s hs _ hp, hρ t ht' _ hq] at h2
      exact hst h2
    · rw [hρ t ht' _ hq, hρ s hs _ hp] at h2
      exact hst h2.symm
    · exact hxy rfl
  obtain ⟨H, π, ε, hH, hHV, hπ, hε, hεt, hrep⟩ := exists_contract_set hT hLD hCD hforest hother
  refine ⟨H, gm19_of_loopFree hb hH, ?_, hrep.trans (rep_le_of_isSubdrawing hDsub)⟩
  -- the isomorphism
  have hx : ∀ v, ∃ x, v ∈ G.V → x ∈ (σv v).V := fun v => by
    by_cases hv : v ∈ G.V
    · obtain ⟨x, hx⟩ := hσ.vertex_nonempty v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨v, fun h => absurd h hv⟩
  choose x hx using hx
  have hxD : ∀ v ∈ G.V, x v ∈ D.V := fun v hv => by
    rw [hDV]
    exact mem_iUnion₂.mpr ⟨v, hv, hx v hv⟩
  have hbranch : ∀ v ∈ G.V, ∀ y ∈ (σv v).V, π y = π (x v) := fun v hv y hy => by
    have hyD : y ∈ D.V := by
      rw [hDV]
      exact mem_iUnion₂.mpr ⟨v, hv, hy⟩
    exact (hπ y hyD _ (hxD v hv)).mpr (hCg v hv y hy _ (hx v hv))
  have hπlabel : ∀ y ∈ D.V, ∀ z ∈ D.V, π y = π z → ρ y = ρ z := fun y hy z hz h =>
    Conn.map_eq ρ hρC ((hπ y hy z hz).mp h)
  have hσE : BijOn σe G.E (σe '' G.E) := ⟨fun e he => ⟨e, he, rfl⟩, hσ.edge_injOn, fun _ h => h⟩
  rw [← hsd] at hσE
  refine ⟨fun v => π (x v), ε ∘ σe, ⟨fun v hv => ?_, fun v hv w hw h => ?_, fun y hy => ?_⟩,
    hε.comp hσE, ?_⟩
  · rw [hHV]
    exact mem_image_of_mem _ (hxD v hv)
  · have := hπlabel _ (hxD v hv) _ (hxD w hw) h
    rwa [hρ v hv _ (hx v hv), hρ w hw _ (hx w hw)] at this
  · rw [hHV, hDV] at hy
    obtain ⟨y, hy, rfl⟩ := hy
    obtain ⟨v, hv, h⟩ := hUV y hy
    exact ⟨v, hv, (hbranch v hv y h).symm⟩
  · intro v hv e he
    have hmem : σe e ∈ D.E \ C := hσE.mapsTo he
    rw [Function.comp_apply, hεt _ hmem]
    constructor
    · intro h
      obtain ⟨y, hy, hyT⟩ := (hσ.ends_iff e he v hv).mpr h
      exact ⟨y, hyT, hbranch v hv y hy⟩
    · rintro ⟨y, hyT, hy⟩
      have hyD : y ∈ D.V := by
        have : y ∈ tilde (σe e) := hyT
        rw [tilde_eq_inter_V D hmem.1] at this
        exact this.2
      have hl := hπlabel y hyD _ (hxD v hv) hy
      rw [hρ v hv _ (hx v hv)] at hl
      rw [hDV] at hyD
      obtain ⟨w, hw, hyw⟩ := hUV y hyD
      rw [hρ w hw y hyw] at hl
      subst hl
      exact (hσ.ends_iff e he w hw).mp ⟨y, hyw, hyT⟩

end GraphMinor.GM19
