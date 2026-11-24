/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Minor.Model
import LeanPool.GraphMinor.Minor.Basic

/-!
# Composing the branch sets of minor models

The omitted proof of XII (4.2), page 249, merges branches along the
contractions of the target minor. This file makes that operation explicit
for models of graph minors. Its branch sets are unions of old branch sets,
which is also the inclusion needed to preserve tangle control.
-/

public section

namespace GraphMinor.GM12

open Set Graph Relation

variable {α β α' β' α'' β'' : Type*}
variable {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}

private noncomputable def chosenK (h : IsMinorModel H G ηv ηe) (v : α') (hv : v ∈ V(H)) :
    Graph α β :=
  (h.connected v hv).choose

private lemma chosenK_le (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    chosenK h v hv ≤ G.deleteEdges (ηe '' E(H)) :=
  (h.connected v hv).choose_spec.1

private lemma chosenK_le_G (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    chosenK h v hv ≤ G :=
  (chosenK_le h hv).trans deleteEdges_le

private lemma chosenK_vertexSet (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    V(chosenK h v hv) = ηv v :=
  (h.connected v hv).choose_spec.2.1

private lemma chosenK_connected (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H)) :
    GraphConnected (chosenK h v hv) :=
  (h.connected v hv).choose_spec.2.2

private lemma chosenK_edge_ends_mem (h : IsMinorModel H G ηv ηe) {v : α'} (hv : v ∈ V(H))
    {e : β} {x y : α} (hl : (chosenK h v hv).IsLink e x y) : x ∈ ηv v ∧ y ∈ ηv v := by
  rw [← chosenK_vertexSet h hv]
  exact ⟨hl.left_mem, hl.right_mem⟩

/-- Compose branch sets and joining edges as in the omitted proof of XII (4.2),
page 249. The new branch is the union of the old branches selected by the
first model, joined by its internal edges. -/
theorem minorModel_comp {H : Graph α'' β''} {K : Graph α' β'} {G : Graph α β}
    {ηv : α'' → Set α'} {ηe : β'' → β'} {ηv' : α' → Set α} {ηe' : β' → β}
    (h₁ : IsMinorModel H K ηv ηe) (h₂ : IsMinorModel K G ηv' ηe') :
    IsMinorModel H G (fun v ↦ ⋃ v' ∈ ηv v, ηv' v') (ηe' ∘ ηe) where
  vertex_nonempty v hv := by
    obtain ⟨v', hv'⟩ := h₁.vertex_nonempty v hv
    obtain ⟨x, hx⟩ := h₂.vertex_nonempty v' (h₁.vertex_subset v hv hv')
    exact ⟨x, mem_biUnion hv' hx⟩
  vertex_subset v hv := by
    rintro x ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩
    exact h₂.vertex_subset v' (h₁.vertex_subset v hv hv') hx
  edge_mem e he := h₂.edge_mem (ηe e) (h₁.edge_mem e he)
  vertex_disjoint v₁ hv₁ v₂ hv₂ hne := by
    rw [disjoint_left]
    rintro x ⟨_, ⟨u₁, rfl⟩, _, ⟨hu₁, rfl⟩, hx₁⟩ ⟨_, ⟨u₂, rfl⟩, _, ⟨hu₂, rfl⟩, hx₂⟩
    have hu₁K := h₁.vertex_subset v₁ hv₁ hu₁
    have hu₂K := h₁.vertex_subset v₂ hv₂ hu₂
    have hu_eq : u₁ = u₂ := by
      by_contra hne'
      exact (h₂.vertex_disjoint u₁ hu₁K u₂ hu₂K hne').notMem_of_mem_left hx₁ hx₂
    exact (h₁.vertex_disjoint v₁ hv₁ v₂ hv₂ hne).notMem_of_mem_left hu₁ (hu_eq ▸ hu₂)
  edge_injOn := h₂.edge_injOn.comp h₁.edge_injOn (mapsTo_iff_subset_preimage.2 h₁.edge_mem)
  inc_iff v hv e he := by
    rw [h₁.inc_iff v hv e he]
    constructor
    · rintro ⟨v', hv', hinc'⟩
      have hv'K := h₁.vertex_subset v hv hv'
      obtain ⟨x, hx, hinc⟩ := (h₂.inc_iff v' hv'K (ηe e) (h₁.edge_mem e he)).1 hinc'
      exact ⟨x, mem_biUnion hv' hx, hinc⟩
    · rintro ⟨x, ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩, hinc⟩
      have hv'K := h₁.vertex_subset v hv hv'
      exact ⟨v', hv', (h₂.inc_iff v' hv'K (ηe e) (h₁.edge_mem e he)).2 ⟨x, hx, hinc⟩⟩
  isLoopAt_iff v hv e he := by
    rw [h₁.isLoopAt_iff v hv e he]
    have heK := h₁.edge_mem e he
    constructor
    · intro hall x hinc
      obtain ⟨a, b, hlK⟩ := exists_isLink_of_mem_edgeSet heK
      have ha_v : a ∈ ηv v := hall a hlK.inc_left
      have hb_v : b ∈ ηv v := hall b hlK.inc_right
      by_cases hloop' : K.IsLoopAt (ηe e) a
      · have hx_a := (h₂.isLoopAt_iff a hlK.left_mem (ηe e) heK).1 hloop' x hinc
        exact mem_biUnion ha_v hx_a
      · have hab_ne : a ≠ b := fun h' ↦ hloop' (h' ▸ hlK)
        obtain ⟨x₁, hx₁, y₁, hlG₁⟩ := (h₂.inc_iff a hlK.left_mem (ηe e) heK).1 hlK.inc_left
        obtain ⟨x₂, hx₂, hinc₂⟩ := (h₂.inc_iff b hlK.right_mem (ηe e) heK).1 hlK.inc_right
        have hx₁x₂ : x₁ ≠ x₂ :=
          (h₂.vertex_disjoint a hlK.left_mem b hlK.right_mem hab_ne).ne_of_mem hx₁ hx₂
        have hx₂y₁ : x₂ = y₁ := hinc₂.eq_of_isLink_of_ne_left hlG₁ hx₁x₂.symm
        obtain rfl | rfl := hinc.eq_or_eq_of_isLink hlG₁
        · exact mem_biUnion ha_v hx₁
        · exact mem_biUnion hb_v (hx₂y₁ ▸ hx₂)
    · intro hall v' hinc'
      have hv'K := hinc'.vertex_mem
      obtain ⟨x, hx, hinc⟩ := (h₂.inc_iff v' hv'K (ηe e) heK).1 hinc'
      obtain ⟨_, ⟨u, rfl⟩, _, ⟨hu, rfl⟩, hxu⟩ := hall x hinc
      have huK := h₁.vertex_subset v hv hu
      have huv' : u = v' := by
        by_contra hne
        exact (h₂.vertex_disjoint u huK v' hv'K hne).notMem_of_mem_left hxu hx
      exact huv' ▸ hu
  connected v hv := by
    obtain ⟨K₁, hK₁_le, hK₁_V, hK₁_conn⟩ := h₁.connected v hv
    let F₂ : Set β := (ηe' '' E(K₁)) ∪
      ⋃ (v' : α') (hv' : v' ∈ ηv v), E(chosenK h₂ v' (h₁.vertex_subset v hv hv'))
    let K₂ : Graph α β := (G.induce (⋃ v' ∈ ηv v, ηv' v')).restrict F₂
    refine ⟨K₂, ?_, rfl, ?_⟩
    · refine ⟨?_, fun e x y ⟨heF₂, hlG, _, _⟩ ↦ ⟨hlG, ?_⟩⟩
      · rintro x ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, hx⟩
        exact h₂.vertex_subset v' (h₁.vertex_subset v hv hv') hx
      · rintro ⟨e₀, he₀, rfl⟩
        rcases heF₂ with ⟨e₁, he₁, heq⟩ | ⟨_, ⟨v', rfl⟩, _, ⟨hv', rfl⟩, heK⟩
        · have he₁_mem : e₁ ∈ E(K) := (hK₁_le.trans deleteEdges_le).edgeSet_mono he₁
          have := h₂.edge_injOn he₁_mem (h₁.edge_mem e₀ he₀) heq
          exact (hK₁_le.edgeSet_mono he₁).2 (this ▸ mem_image_of_mem ηe he₀)
        · have heD := (chosenK_le h₂ (h₁.vertex_subset v hv hv')).edgeSet_mono heK
          exact heD.2 (mem_image_of_mem ηe' (h₁.edge_mem e₀ he₀))
    · have hinner : ∀ {v' : α'} (hv' : v' ∈ ηv v) {x y : α},
          x ∈ ηv' v' → y ∈ ηv' v' → ReflTransGen K₂.Adj x y := by
        intro v' hv' x y hx hy
        have hv'K := h₁.vertex_subset v hv hv'
        have hconn := (chosenK_connected h₂ hv'K).2 x (by rwa [chosenK_vertexSet h₂ hv'K])
          y (by rwa [chosenK_vertexSet h₂ hv'K])
        induction hconn with
        | refl => exact .refl
        | @tail a b _ hab ih =>
          obtain ⟨e, hlK⟩ := hab
          have heF₂ : e ∈ F₂ := Or.inr (mem_iUnion₂_of_mem hv' hlK.edge_mem)
          have hlG : G.IsLink e a b := hlK.mono (chosenK_le_G h₂ hv'K)
          obtain ⟨ha, hb⟩ := chosenK_edge_ends_mem h₂ hv'K hlK
          have haU : a ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hv' ha
          have hbU : b ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hv' hb
          exact (ih ha).tail ⟨e, heF₂, hlG, haU, hbU⟩
      obtain ⟨v₀', hv₀'⟩ := h₁.vertex_nonempty v hv
      obtain ⟨x₀, hx₀⟩ := h₂.vertex_nonempty v₀' (h₁.vertex_subset v hv hv₀')
      refine ⟨⟨x₀, mem_biUnion hv₀' hx₀⟩, ?_⟩
      rintro x ⟨_, ⟨u, rfl⟩, _, ⟨hu, rfl⟩, hxu⟩ y ⟨_, ⟨w, rfl⟩, _, ⟨hw, rfl⟩, hyw⟩
      have hwalk := hK₁_conn.2 u (hK₁_V.symm ▸ hu) w (hK₁_V.symm ▸ hw)
      have hstep : ∀ {p q : α'}, ReflTransGen K₁.Adj p q → p ∈ ηv v → q ∈ ηv v →
          ∀ {a b : α}, a ∈ ηv' p → b ∈ ηv' q → ReflTransGen K₂.Adj a b := by
        intro p q hpq
        induction hpq with
        | refl => exact fun hp _ a b ha hb ↦ hinner hp ha hb
        | @tail c d _ hcd ih =>
          intro hp hd a b ha hb
          obtain ⟨e₁, hlK₁⟩ := hcd
          have hc : c ∈ ηv v := hK₁_V ▸ hlK₁.left_mem
          have hlK : K.IsLink e₁ c d := (hlK₁.mono hK₁_le).1
          obtain ⟨c', hc', hincc'⟩ := (h₂.inc_iff c (h₁.vertex_subset v hv hc) e₁ hlK.edge_mem).1
            hlK.inc_left
          obtain ⟨d', hlG'⟩ := hincc'
          have hd' : d' ∈ ηv' d := by
            by_cases hloop : K.IsLoopAt e₁ c
            · have hcd_eq : c = d := hloop.eq_of_inc hlK.inc_right
              exact hcd_eq ▸
                (h₂.isLoopAt_iff c (h₁.vertex_subset v hv hc) e₁ hlK.edge_mem).1 hloop d'
                  hlG'.inc_right
            · have hcd_ne : c ≠ d := fun h' ↦ hloop (h' ▸ hlK)
              obtain ⟨z, hz, hincz⟩ :=
                (h₂.inc_iff d (h₁.vertex_subset v hv hd) e₁ hlK.edge_mem).1 hlK.inc_right
              have hc'z : c' ≠ z :=
                (h₂.vertex_disjoint c (h₁.vertex_subset v hv hc) d
                  (h₁.vertex_subset v hv hd) hcd_ne).ne_of_mem hc' hz
              have hzd' : z = d' := hincz.eq_of_isLink_of_ne_left hlG' hc'z.symm
              exact hzd' ▸ hz
          have heF₂ : ηe' e₁ ∈ F₂ := Or.inl (mem_image_of_mem ηe' hlK₁.edge_mem)
          have hc'U : c' ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hc hc'
          have hd'U : d' ∈ ⋃ u ∈ ηv v, ηv' u := mem_biUnion hd hd'
          have hadj : K₂.Adj c' d' := ⟨ηe' e₁, heF₂, hlG', hc'U, hd'U⟩
          exact ((ih hp hc ha hc').tail hadj).trans (hinner hd hd' hb)
      exact hstep hwalk hu hw hxu hyw

end GraphMinor.GM12
