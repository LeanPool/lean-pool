/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.WhitneyGraph

/-!
# Recognising a subdivision of a 3-connected graph

To use Whitney's theorem in the proof of (6.4) we must show that a graph is a subdivision of a
simple
3-connected graph. The paper does this by suppressing the vertices of valency 2. Here we record what
we
need in `Good`: a finite graph with no loops, with four vertices of valency other than 2, such that
for
each separation of order at most 2 one side is `Thin`. A thin side is either empty or looks by its
counts like a path that joins the two common vertices through vertices of valency 2.

`good_sub` proves that a good graph is a subdivision of a simple 3-connected graph. We suppress one
vertex of valency 2 at a time (`susp`). The new graph is again good (`Good.susp`), and a subdivision
of
it gives one of the old graph (`sub_step`). When no vertex of valency 2 is left, thin sides are
trivial,
so the graph itself is simple and 3-connected.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Graph GraphMinor.GM06 GraphMinor.GM09 GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-- The number of edges at `v`. For a graph with no loops this is the valency of `v`. -/
noncomputable def deg (G : Graph α β) (v : α) : ℕ := {e | G.Inc e v}.ncard

/-- The side `G₁` of a separation `(G₁, G₂)` of `G` has nothing beyond `G₂`, or it has two common
vertices with `G₂`, its other vertices have valency 2, and it has at most one more edge than it has
other vertices. -/
def Thin (G G₁ G₂ : Graph α β) : Prop :=
  (V(G₁) ⊆ V(G₂) ∧ E(G₁) = ∅) ∨
    ((V(G₁) ∩ V(G₂)).ncard = 2 ∧ (∀ v ∈ V(G₁) \ V(G₂), deg G v = 2) ∧
      E(G₁).ncard ≤ (V(G₁) \ V(G₂)).ncard + 1)

/-- A graph that we can show to be a subdivision of a simple 3-connected graph. -/
structure Good (G : Graph α β) : Prop where
  finV : V(G).Finite
  finE : E(G).Finite
  no_loop : ∀ e v, ¬ G.IsLink e v v
  four : 4 ≤ {v | v ∈ V(G) ∧ deg G v ≠ 2}.ncard
  sep : ∀ G₁ G₂ : Graph α β, IsGraphSeparation G G₁ G₂ → (V(G₁) ∩ V(G₂)).ncard ≤ 2 →
    Thin G G₁ G₂ ∨ Thin G G₂ G₁

/-- The subgraph of `G` with vertices `X` and the ends of `F`, and with edges `F`. -/
def part (G : Graph α β) (X : Set α) (F : Set β) : Graph α β where
  vertexSet := X ∪ {u | ∃ g ∈ F, G.Inc g u}
  IsLink g u v := g ∈ F ∧ G.IsLink g u v
  isLink_symm := fun _ _ => ⟨fun _ _ hxy => ⟨hxy.1, hxy.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := fun _ _ _ _ _ h₁ h₂ => G.eq_or_eq_of_isLink_of_isLink h₁.2 h₂.2
  left_mem_of_isLink := fun _ u v hl => Or.inr ⟨_, hl.1, v, hl.2⟩

theorem part_link {G : Graph α β} {X : Set α} {F : Set β} {g : β} {u v : α} :
    (part G X F).IsLink g u v ↔ g ∈ F ∧ G.IsLink g u v := Iff.rfl

theorem V_part {G : Graph α β} {X : Set α} {F : Set β} (h : ∀ g ∈ F, ∀ u, G.Inc g u → u ∈ X) :
    V(part G X F) = X := by
  apply subset_antisymm
  · rintro u (hu | ⟨g, hg, hi⟩)
    · exact hu
    · exact h g hg u hi
  · exact fun u hu => Or.inl hu

theorem E_part {G : Graph α β} {X : Set α} {F : Set β} (h : F ⊆ E(G)) : E(part G X F) = F := by
  ext g
  rw [(part G X F).edge_mem_iff_exists_isLink]
  constructor
  · rintro ⟨_, _, hl⟩
    exact hl.1
  · intro hg
    obtain ⟨x, y, hl⟩ := (G.edge_mem_iff_exists_isLink g).mp (h hg)
    exact ⟨x, y, hg, hl⟩

theorem part_le {G : Graph α β} {X : Set α} {F : Set β} (hX : X ⊆ V(G)) : part G X F ≤ G := by
  refine ⟨?_, fun _ _ _ hl => hl.2⟩
  rintro u (hu | ⟨g, -, y, hl⟩)
  · exact hX hu
  · exact hl.left_mem

/-- The vertex `w` has exactly the edges `e` and `f`, to different vertices `x` and `y`. -/
structure Susp (G : Graph α β) (w x y : α) (e f : β) : Prop where
  ne : e ≠ f
  le : G.IsLink e w x
  lf : G.IsLink f w y
  only : ∀ g, G.Inc g w → g = e ∨ g = f
  hxw : x ≠ w
  hyw : y ≠ w
  hxy : x ≠ y

variable {G : Graph α β} {w x y : α} {e f : β}

theorem Susp.ne_w (h : Susp G w x y e f) {g : β} {u v : α} (hl : G.IsLink g u v) (hge : g ≠ e)
    (hgf : g ≠ f) : u ≠ w := by
  rintro rfl
  rcases h.only g ⟨v, hl⟩ with rfl | rfl
  · exact hge rfl
  · exact hgf rfl

/-- Suppress the vertex `w`: delete it and `f`, and let `e` join `x` to `y`. -/
def susp (G : Graph α β) (w x y : α) (e f : β) (h : Susp G w x y e f) : Graph α β where
  vertexSet := V(G) \ {w}
  IsLink g u v := (g ≠ e ∧ g ≠ f ∧ G.IsLink g u v) ∨ (g = e ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)))
  isLink_symm := fun _ _ => ⟨fun _ _ hxy => by
    rcases hxy with ⟨a, b, c⟩ | ⟨a, ⟨p, q⟩ | ⟨p, q⟩⟩
    · exact Or.inl ⟨a, b, c.symm⟩
    · exact Or.inr ⟨a, Or.inr ⟨q, p⟩⟩
    · exact Or.inr ⟨a, Or.inl ⟨q, p⟩⟩⟩
  eq_or_eq_of_isLink_of_isLink := fun g a b c d h₁ h₂ => by
    rcases h₁ with ⟨p, q, r⟩ | ⟨p, ha⟩
    · rcases h₂ with ⟨_, _, r'⟩ | ⟨p', -⟩
      · exact G.eq_or_eq_of_isLink_of_isLink r r'
      · exact absurd p' p
    · rcases h₂ with ⟨p', -⟩ | ⟨-, hc⟩
      · exact absurd p p'
      · rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  left_mem_of_isLink := fun g u v hl => by
    rcases hl with ⟨p, q, r⟩ | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact ⟨r.left_mem, h.ne_w r p q⟩
    · exact ⟨h.le.right_mem, h.hxw⟩
    · exact ⟨h.lf.right_mem, h.hyw⟩

theorem susp_link (h : Susp G w x y e f) {g : β} {u v : α} :
    (susp G w x y e f h).IsLink g u v ↔
      (g ≠ e ∧ g ≠ f ∧ G.IsLink g u v) ∨ (g = e ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := Iff.rfl

theorem V_susp (h : Susp G w x y e f) : V(susp G w x y e f h) = V(G) \ {w} := rfl

theorem E_susp (h : Susp G w x y e f) : E(susp G w x y e f h) = E(G) \ {f} := by
  ext g
  rw [(susp G w x y e f h).edge_mem_iff_exists_isLink]
  constructor
  · rintro ⟨u, v, ⟨p, q, r⟩ | ⟨rfl, -⟩⟩
    · exact ⟨r.edge_mem, q⟩
    · exact ⟨h.le.edge_mem, h.ne⟩
  · rintro ⟨hg, hgf⟩
    by_cases hge : g = e
    · exact ⟨x, y, Or.inr ⟨hge, Or.inl ⟨rfl, rfl⟩⟩⟩
    · obtain ⟨u, v, hl⟩ := (G.edge_mem_iff_exists_isLink g).mp hg
      exact ⟨u, v, Or.inl ⟨hge, hgf, hl⟩⟩

theorem susp_inc (h : Susp G w x y e f) {g : β} {v : α} :
    (susp G w x y e f h).Inc g v ↔ (g ≠ e ∧ g ≠ f ∧ G.Inc g v) ∨ (g = e ∧ (v = x ∨ v = y)) := by
  constructor
  · rintro ⟨u, ⟨p, q, r⟩ | ⟨p, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩⟩
    · exact Or.inl ⟨p, q, u, r⟩
    · exact Or.inr ⟨p, Or.inl rfl⟩
    · exact Or.inr ⟨p, Or.inr rfl⟩
  · rintro (⟨p, q, u, r⟩ | ⟨p, rfl | rfl⟩)
    · exact ⟨u, Or.inl ⟨p, q, r⟩⟩
    · exact ⟨y, Or.inr ⟨p, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨x, Or.inr ⟨p, Or.inr ⟨rfl, rfl⟩⟩⟩

theorem inc_of_ne (h : Susp G w x y e f) {g : β} {v : α} (hv : v ≠ w) :
    G.Inc g v ↔ (g ≠ e ∧ g ≠ f ∧ G.Inc g v) ∨ (g = e ∧ v = x) ∨ (g = f ∧ v = y) := by
  constructor
  · intro hi
    by_cases h₁ : g = e
    · subst h₁
      obtain ⟨u, hu⟩ := hi
      rcases G.eq_or_eq_of_isLink_of_isLink hu h.le with rfl | rfl
      · exact absurd rfl hv
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    by_cases h₂ : g = f
    · subst h₂
      obtain ⟨u, hu⟩ := hi
      rcases G.eq_or_eq_of_isLink_of_isLink hu h.lf with rfl | rfl
      · exact absurd rfl hv
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    exact Or.inl ⟨h₁, h₂, hi⟩
  · rintro (⟨-, -, hi⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hi
    · exact ⟨w, h.le.symm⟩
    · exact ⟨w, h.lf.symm⟩

/-- Suppressing `w` does not change the number of edges at another vertex. -/
theorem deg_susp (h : Susp G w x y e f) (hfin : E(G).Finite) {v : α} (hv : v ≠ w) :
    deg (susp G w x y e f h) v = deg G v := by
  classical
  let T : Set β := {g | g ≠ e ∧ g ≠ f ∧ G.Inc g v}
  have hT : T.Finite := hfin.subset fun g hg => hg.2.2.edge_mem
  have heT : e ∉ T := fun hh => hh.1 rfl
  have hfT : f ∉ T := fun hh => hh.2.1 rfl
  by_cases hx : v = x
  · have h₁ : {g | (susp G w x y e f h).Inc g v} = insert e T := by
      ext g
      rw [mem_ofPred_eq, susp_inc]
      simp only [mem_insert_iff, T, mem_ofPred_eq]
      constructor
      · rintro (a | ⟨a, -⟩)
        · exact Or.inr a
        · exact Or.inl a
      · rintro (a | a)
        · exact Or.inr ⟨a, Or.inl hx⟩
        · exact Or.inl a
    have h₂ : {g | G.Inc g v} = insert e T := by
      ext g
      rw [mem_ofPred_eq, inc_of_ne h hv]
      simp only [mem_insert_iff, T, mem_ofPred_eq]
      constructor
      · rintro (a | ⟨a, -⟩ | ⟨-, b⟩)
        · exact Or.inr a
        · exact Or.inl a
        · exact absurd (hx.symm.trans b) h.hxy
      · rintro (a | a)
        · exact Or.inr (Or.inl ⟨a, hx⟩)
        · exact Or.inl a
    simp only [deg, h₁, h₂]
  by_cases hy : v = y
  · have h₁ : {g | (susp G w x y e f h).Inc g v} = insert e T := by
      ext g
      rw [mem_ofPred_eq, susp_inc]
      simp only [mem_insert_iff, T, mem_ofPred_eq]
      constructor
      · rintro (a | ⟨a, -⟩)
        · exact Or.inr a
        · exact Or.inl a
      · rintro (a | a)
        · exact Or.inr ⟨a, Or.inr hy⟩
        · exact Or.inl a
    have h₂ : {g | G.Inc g v} = insert f T := by
      ext g
      rw [mem_ofPred_eq, inc_of_ne h hv]
      simp only [mem_insert_iff, T, mem_ofPred_eq]
      constructor
      · rintro (a | ⟨-, b⟩ | ⟨a, -⟩)
        · exact Or.inr a
        · exact absurd b hx
        · exact Or.inl a
      · rintro (a | a)
        · exact Or.inr (Or.inr ⟨a, hy⟩)
        · exact Or.inl a
    simp only [deg, h₁, h₂]
    rw [ncard_insert_of_notMem heT hT, ncard_insert_of_notMem hfT hT]
  · have h₁ : {g | (susp G w x y e f h).Inc g v} = T := by
      ext g
      rw [mem_ofPred_eq, susp_inc]
      constructor
      · rintro (a | ⟨-, b | b⟩)
        · exact a
        · exact absurd b hx
        · exact absurd b hy
      · exact Or.inl
    have h₂ : {g | G.Inc g v} = T := by
      ext g
      rw [mem_ofPred_eq, inc_of_ne h hv]
      constructor
      · rintro (a | ⟨-, b⟩ | ⟨-, b⟩)
        · exact a
        · exact absurd b hx
        · exact absurd b hy
      · exact Or.inl
    simp only [deg, h₁, h₂]

/-- A separation of the suppressed graph with `e` on the left gives one of `G`, by adding `w` and
`f`
to the left side. -/
theorem thin_of_lift (hG : Good G) (h : Susp G w x y e f) (hw2 : deg G w = 2) {G₁ G₂ : Graph α β}
    (hs : IsGraphSeparation (susp G w x y e f h) G₁ G₂) (hord : (V(G₁) ∩ V(G₂)).ncard ≤ 2)
    (he : e ∈ E(G₁)) :
    Thin (susp G w x y e f h) G₁ G₂ ∨ Thin (susp G w x y e f h) G₂ G₁ := by
  classical
  obtain ⟨hl₁, hl₂, hV, hE, hdis⟩ := hs
  set G' := susp G w x y e f h with hG'
  have hV' : V(G') = V(G) \ {w} := rfl
  have hE' : E(G') = E(G) \ {f} := E_susp h
  have hV₁ : V(G₁) ⊆ V(G') := hl₁.vertexSet_mono
  have hV₂ : V(G₂) ⊆ V(G') := hl₂.vertexSet_mono
  have hE₁ : E(G₁) ⊆ E(G) \ {f} := hE' ▸ hl₁.edgeSet_mono
  have hE₂ : E(G₂) ⊆ E(G) \ {f} := hE' ▸ hl₂.edgeSet_mono
  have hw₁ : w ∉ V(G₁) := fun hh => (hV₁ hh).2 rfl
  have hw₂ : w ∉ V(G₂) := fun hh => (hV₂ hh).2 rfl
  have hf₁ : f ∉ E(G₁) := fun hh => (hE₁ hh).2 rfl
  have hf₂ : f ∉ E(G₂) := fun hh => (hE₂ hh).2 rfl
  have he₂ : e ∉ E(G₂) := fun hh => disjoint_left.mp hdis he hh
  -- The ends of `e` are on the left.
  obtain ⟨a, b, hab⟩ := (G₁.edge_mem_iff_exists_isLink e).mp he
  have hab' := hl₁.isLink_mono hab
  have hxy₁ : x ∈ V(G₁) ∧ y ∈ V(G₁) := by
    rcases hab' with ⟨p, -⟩ | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact absurd rfl p
    · exact ⟨hab.left_mem, hab.right_mem⟩
    · exact ⟨hab.right_mem, hab.left_mem⟩
  have hsub₁ : ∀ g ∈ E(G₁) ∪ {f}, ∀ u, G.Inc g u → u ∈ V(G₁) ∪ {w} := by
    rintro g (hg | rfl) u ⟨v, hl⟩
    · by_cases hge : g = e
      · subst hge
        rcases G.eq_or_eq_of_isLink_of_isLink hl h.le with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl hxy₁.1
      · obtain ⟨c, d, hcd⟩ := (G₁.edge_mem_iff_exists_isLink g).mp hg
        have hgf : g ≠ f := fun hh => hf₁ (hh ▸ hg)
        have : G'.IsLink g c d := hl₁.isLink_mono hcd
        have hcd' : G.IsLink g c d := by
          rcases this with ⟨-, -, r⟩ | ⟨p, -⟩
          · exact r
          · exact absurd p hge
        rcases G.eq_or_eq_of_isLink_of_isLink hl hcd' with rfl | rfl
        · exact Or.inl hcd.left_mem
        · exact Or.inl hcd.right_mem
    · rcases G.eq_or_eq_of_isLink_of_isLink hl h.lf with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl hxy₁.2
  have hsub₂ : ∀ g ∈ E(G₂), ∀ u, G.Inc g u → u ∈ V(G₂) := by
    rintro g hg u ⟨v, hl⟩
    have hge : g ≠ e := fun hh => he₂ (hh ▸ hg)
    have hgf : g ≠ f := fun hh => hf₂ (hh ▸ hg)
    obtain ⟨c, d, hcd⟩ := (G₂.edge_mem_iff_exists_isLink g).mp hg
    have : G'.IsLink g c d := hl₂.isLink_mono hcd
    have hcd' : G.IsLink g c d := by
      rcases this with ⟨-, -, r⟩ | ⟨p, -⟩
      · exact r
      · exact absurd p hge
    rcases G.eq_or_eq_of_isLink_of_isLink hl hcd' with rfl | rfl
    · exact hcd.left_mem
    · exact hcd.right_mem
  have hE₁G : E(G₁) ∪ {f} ⊆ E(G) := by
    rintro g (hg | rfl)
    · exact (hE₁ hg).1
    · exact h.lf.edge_mem
  have hE₂G : E(G₂) ⊆ E(G) := fun g hg => (hE₂ hg).1
  let A := part G (V(G₁) ∪ {w}) (E(G₁) ∪ {f})
  let B := part G V(G₂) E(G₂)
  have hVA : V(A) = V(G₁) ∪ {w} := V_part hsub₁
  have hVB : V(B) = V(G₂) := V_part hsub₂
  have hEA : E(A) = E(G₁) ∪ {f} := E_part hE₁G
  have hEB : E(B) = E(G₂) := E_part hE₂G
  have hcap : V(A) ∩ V(B) = V(G₁) ∩ V(G₂) := by
    rw [hVA, hVB]
    ext z
    constructor
    · rintro ⟨hz | rfl, hz'⟩
      · exact ⟨hz, hz'⟩
      · exact absurd hz' hw₂
    · exact fun hz => ⟨Or.inl hz.1, hz.2⟩
  have hsep : IsGraphSeparation G A B := by
    refine ⟨part_le ?_, part_le fun z hz => (hV₂ hz).1, ?_, ?_, ?_⟩
    · rintro z (hz | rfl)
      · exact (hV₁ hz).1
      · exact h.le.left_mem
    · rw [hVA, hVB]
      ext z
      constructor
      · rintro ((hz | rfl) | hz)
        · exact (hV₁ hz).1
        · exact h.le.left_mem
        · exact (hV₂ hz).1
      · intro hz
        by_cases hzw : z = w
        · exact Or.inl (Or.inr hzw)
        · have : z ∈ V(G₁) ∪ V(G₂) := hV ▸ (⟨hz, hzw⟩ : z ∈ V(G'))
          rcases this with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr h'
    · rw [hEA, hEB]
      ext g
      constructor
      · rintro ((hg | rfl) | hg)
        · exact (hE₁ hg).1
        · exact h.lf.edge_mem
        · exact (hE₂ hg).1
      · intro hg
        by_cases hgf : g = f
        · exact Or.inl (Or.inr hgf)
        · have : g ∈ E(G₁) ∪ E(G₂) := hE ▸ (hE' ▸ ⟨hg, hgf⟩ : g ∈ E(G'))
          rcases this with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr h'
    · rw [hEA, hEB]
      refine disjoint_left.mpr ?_
      rintro g (hg | rfl) hg'
      · exact disjoint_left.mp hdis hg hg'
      · exact hf₂ hg'
  have hdeg : ∀ z, z ≠ w → deg G' z = deg G z := fun z hz => deg_susp h hG.finE hz
  have hdiff₂ : V(B) \ V(A) = V(G₂) \ V(G₁) := by
    rw [hVA, hVB]
    ext z
    constructor
    · exact fun hz => ⟨hz.1, fun hh => hz.2 (Or.inl hh)⟩
    · refine fun hz => ⟨hz.1, ?_⟩
      rintro (hh | rfl)
      · exact hz.2 hh
      · exact hw₂ hz.1
  have hdiff₁ : V(A) \ V(B) = insert w (V(G₁) \ V(G₂)) := by
    rw [hVA, hVB]
    ext z
    constructor
    · rintro ⟨hz | rfl, hz'⟩
      · exact Or.inr ⟨hz, hz'⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hz, hz'⟩)
      · exact ⟨Or.inr rfl, hw₂⟩
      · exact ⟨Or.inl hz, hz'⟩
  have hfinV₁ : (V(G₁) \ V(G₂)).Finite := hG.finV.subset fun z hz => (hV₁ hz.1).1
  have hfinE₁ : E(G₁).Finite := hG.finE.subset fun g hg => (hE₁ hg).1
  have hw_not : w ∉ V(G₁) \ V(G₂) := fun hh => hw₁ hh.1
  rw [← hcap] at hord
  rcases hG.sep A B hsep hord with ht | ht
  · rcases ht with ⟨-, hemp⟩ | ⟨hc, hd, hn⟩
    · have : e ∈ E(A) := hEA ▸ Or.inl he
      rw [hemp] at this
      exact absurd this (notMem_empty _)
    · refine Or.inl (Or.inr ⟨hcap ▸ hc, fun z hz => ?_, ?_⟩)
      · have hzw : z ≠ w := fun hh => hw₁ (hh ▸ hz.1)
        rw [hdeg z hzw]
        exact hd z (hdiff₁ ▸ Or.inr hz)
      · rw [hEA, hdiff₁, union_singleton, ncard_insert_of_notMem hf₁ hfinE₁,
          ncard_insert_of_notMem hw_not hfinV₁] at hn
        omega
  · rcases ht with ⟨hsub, hemp⟩ | ⟨hc, hd, hn⟩
    · refine Or.inr (Or.inl ⟨fun z hz => ?_, by rw [← hEB]; exact hemp⟩)
      have hz' : z ∈ V(B) := hVB ▸ hz
      have := hsub hz'
      rw [hVA] at this
      rcases this with h' | rfl
      · exact h'
      · exact absurd hz hw₂
    · refine Or.inr (Or.inr ⟨by rw [inter_comm, ← hcap, inter_comm]; exact hc, fun z hz => ?_, ?_⟩)
      · have hzw : z ≠ w := fun hh => hw₂ (hh ▸ hz.1)
        rw [hdeg z hzw]
        exact hd z (hdiff₂ ▸ hz)
      · rwa [hEB, hdiff₂] at hn

/-- A good graph stays good when a vertex of valency 2 is suppressed. -/
theorem Good.susp (hG : Good G) (h : Susp G w x y e f) (hw2 : deg G w = 2) :
    Good (susp G w x y e f h) := by
  classical
  have hE' := E_susp h
  have hV' : V(GraphMinor.GM14.Whitney.susp G w x y e f h) = V(G) \ {w} := rfl
  refine ⟨hG.finV.subset sdiff_subset, ?_, ?_, ?_, ?_⟩
  · rw [hE']
    exact hG.finE.subset sdiff_subset
  · rintro g v (⟨-, -, r⟩ | ⟨-, ⟨rfl, b⟩ | ⟨rfl, b⟩⟩)
    · exact hG.no_loop _ _ r
    · exact h.hxy b
    · exact h.hxy b.symm
  · have heq : {v | v ∈ V(GraphMinor.GM14.Whitney.susp G w x y e f h) ∧
        deg (GraphMinor.GM14.Whitney.susp G w x y e f h) v ≠ 2} = {v | v ∈ V(G) ∧ deg G v ≠ 2} := by
      ext z
      simp only [mem_ofPred_eq, hV']
      constructor
      · rintro ⟨⟨hz, hzw⟩, hd⟩
        exact ⟨hz, by rwa [deg_susp h hG.finE hzw] at hd⟩
      · rintro ⟨hz, hd⟩
        have hzw : z ≠ w := fun hh => hd (hh ▸ hw2)
        exact ⟨⟨hz, hzw⟩, by rwa [deg_susp h hG.finE hzw]⟩
    rw [heq]
    exact hG.four
  · intro G₁ G₂ hs hord
    have heE : e ∈ E(G₁) ∪ E(G₂) := by
      rw [hs.2.2.2.1, hE']
      exact ⟨h.le.edge_mem, h.ne⟩
    rcases heE with he | he
    · exact thin_of_lift hG h hw2 hs hord he
    · have hs' : IsGraphSeparation (GraphMinor.GM14.Whitney.susp G w x y e f h) G₂ G₁ :=
        ⟨hs.2.1, hs.1, by rw [union_comm]; exact hs.2.2.1, by rw [union_comm]; exact hs.2.2.2.1,
          hs.2.2.2.2.symm⟩
      rw [inter_comm] at hord
      exact (thin_of_lift hG h hw2 hs' hord he).symm

/-- A walk of the suppressed graph gives a walk of `G`, which goes through `w` in place of `e`. -/
theorem lift_walk (h : Susp G w x y e f) {Q' Q : Graph α β} (hle : Q' ≤ susp G w x y e f h)
    (hV : V(Q') ⊆ V(Q)) (hl : ∀ g u v, Q'.IsLink g u v → g ≠ e → Q.IsLink g u v)
    (he : e ∈ E(Q') → Q.IsLink e w x ∧ Q.IsLink f w y) :
    ∀ {a b : α} (W' : GraphWalk Q' a b), ∃ W : GraphWalk Q a b,
      (∀ z, z ≠ w → (z ∈ W.support ↔ z ∈ W'.support)) ∧ (w ∈ W.support ↔ e ∈ W'.edges) ∧
      (∀ g, g ∈ W.edges ↔ g ∈ W'.edges ∨ (g = f ∧ e ∈ W'.edges)) ∧
      (W'.IsSimple → W.IsSimple) := by
  intro a b W'
  induction W' with
  | nil hv =>
    refine ⟨.nil (hV hv), fun z _ => Iff.rfl, ?_, ?_, ?_⟩
    · have := (hle.vertexSet_mono hv).2
      simp only [GraphWalk.support, GraphWalk.edges, List.mem_singleton, List.not_mem_nil,
        iff_false]
      exact fun hh => this hh.symm
    · simp [GraphWalk.edges]
    · exact fun _ => by simp [GraphWalk.IsSimple, GraphWalk.support]
  | @cons u v t g hlink rest ih =>
    obtain ⟨W₀, h₁, h₂, h₃, h₄⟩ := ih
    have huw : u ≠ w := (hle.vertexSet_mono hlink.left_mem).2
    have hvw : v ≠ w := (hle.vertexSet_mono hlink.right_mem).2
    by_cases hg : g = e
    · subst hg
      have hee := he hlink.edge_mem
      have hlk := hle.isLink_mono hlink
      have hset : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
        rcases hlk with ⟨p, -⟩ | ⟨-, hc⟩
        · exact absurd rfl p
        · exact hc
      have hnotin : ∀ (hs : (GraphWalk.cons hlink rest).IsSimple), g ∉ rest.edges := by
        intro hs hin
        exact (List.nodup_cons.mp hs).1 (inc_mem_support rest hin ⟨v, hlink⟩)
      rcases hset with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨.cons hee.1.symm (.cons hee.2 W₀), fun z hz => ?_, ?_, fun g' => ?_, fun hs => ?_⟩
        · simp only [GraphWalk.support, List.mem_cons, hz, false_or, h₁ z hz]
        · simp [GraphWalk.support, GraphWalk.edges]
        · simp only [GraphWalk.edges, List.mem_cons, h₃ g', true_or, and_true]
          tauto
        · have hrs : rest.IsSimple := (List.nodup_cons.mp hs).2
          have hun : u ∉ rest.support := (List.nodup_cons.mp hs).1
          have hne := hnotin hs
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, h₄ hrs⟩⟩
          · simp only [GraphWalk.support, List.mem_cons, not_or]
            exact ⟨huw, fun hh => hun ((h₁ u huw).mp hh)⟩
          · exact fun hh => hne (h₂.mp hh)
      · refine ⟨.cons hee.2.symm (.cons hee.1 W₀), fun z hz => ?_, ?_, fun g' => ?_, fun hs => ?_⟩
        · simp only [GraphWalk.support, List.mem_cons, hz, false_or, h₁ z hz]
        · simp [GraphWalk.support, GraphWalk.edges]
        · simp only [GraphWalk.edges, List.mem_cons, h₃ g', true_or, and_true]
          tauto
        · have hrs : rest.IsSimple := (List.nodup_cons.mp hs).2
          have hun : u ∉ rest.support := (List.nodup_cons.mp hs).1
          have hne := hnotin hs
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, h₄ hrs⟩⟩
          · simp only [GraphWalk.support, List.mem_cons, not_or]
            exact ⟨huw, fun hh => hun ((h₁ u huw).mp hh)⟩
          · exact fun hh => hne (h₂.mp hh)
    · refine ⟨.cons (hl _ _ _ hlink hg) W₀, fun z hz => ?_, ?_, fun g' => ?_, fun hs => ?_⟩
      · simp only [GraphWalk.support, List.mem_cons, h₁ z hz]
      · simp only [GraphWalk.support, GraphWalk.edges, List.mem_cons, h₂]
        constructor
        · rintro (hh | hh)
          · exact absurd hh.symm huw
          · exact Or.inr hh
        · rintro (hh | hh)
          · exact absurd hh.symm hg
          · exact Or.inr hh
      · have heg : ¬ e = g := fun hh => hg hh.symm
        simp only [GraphWalk.edges, List.mem_cons, h₃ g', heg, false_or, or_assoc]
      · have hrs : rest.IsSimple := (List.nodup_cons.mp hs).2
        have hun : u ∉ rest.support := (List.nodup_cons.mp hs).1
        have hu₀ : u ∉ W₀.support := fun hz => hun ((h₁ u huw).mp hz)
        have hsimple : List.Nodup W₀.support := h₄ hrs
        change List.Nodup (u :: W₀.support)
        exact List.nodup_cons.mpr ⟨hu₀, hsimple⟩

/-- The graph `Q'` with `w` and `f` added if `e` is in `Q'`. -/
def lift (G : Graph α β) (w : α) (e f : β) (Q' : Graph α β) : Graph α β :=
  part G (V(Q') ∪ {z | z = w ∧ e ∈ E(Q')}) (E(Q') ∪ {g | g = f ∧ e ∈ E(Q')})

/-- A subdivision of the suppressed graph gives a subdivision of `G`. -/
theorem sub_step (h : Susp G w x y e f) {G₀ : Graph α β}
    (hs : IsSubdivisionOf (susp G w x y e f h) G₀) : IsSubdivisionOf G G₀ := by
  classical
  obtain ⟨hV₀, P', h₁, h₂, h₃, h₄⟩ := hs
  set G' := susp G w x y e f h with hG'
  have hV' : V(G') = V(G) \ {w} := rfl
  have hE' : E(G') = E(G) \ {f} := E_susp h
  have hlk : ∀ {g u v}, G'.IsLink g u v → g ≠ e → G.IsLink g u v := by
    intro g u v hl hg
    rcases hl with ⟨-, -, r⟩ | ⟨p, -⟩
    · exact r
    · exact absurd p hg
  have hw₀ : w ∉ V(G₀) := fun hh => (hV₀ hh).2 rfl
  -- Facts on the lift of a subgraph.
  have hfacts : ∀ Q' : Graph α β, Q' ≤ G' →
      V(lift G w e f Q') = V(Q') ∪ {z | z = w ∧ e ∈ E(Q')} ∧
      E(lift G w e f Q') = E(Q') ∪ {g | g = f ∧ e ∈ E(Q')} ∧ lift G w e f Q' ≤ G := by
    intro Q' hQ
    have hsub : V(Q') ∪ {z | z = w ∧ e ∈ E(Q')} ⊆ V(G) := by
      rintro z (hz | ⟨rfl, -⟩)
      · exact (hQ.vertexSet_mono hz).1
      · exact h.le.left_mem
    have hinc : ∀ g ∈ E(Q') ∪ {g | g = f ∧ e ∈ E(Q')}, ∀ u, G.Inc g u →
        u ∈ V(Q') ∪ {z | z = w ∧ e ∈ E(Q')} := by
      rintro g (hg | ⟨rfl, hee⟩) u ⟨v, hl⟩
      · by_cases hge : g = e
        · subst hge
          rcases G.eq_or_eq_of_isLink_of_isLink hl h.le with rfl | rfl
          · exact Or.inr ⟨rfl, hg⟩
          · obtain ⟨c, d, hcd⟩ := (Q'.edge_mem_iff_exists_isLink g).mp hg
            rcases hQ.isLink_mono hcd with ⟨p, -⟩ | ⟨-, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩
            · exact absurd rfl p
            · exact Or.inl hcd.left_mem
            · exact Or.inl hcd.right_mem
        · obtain ⟨c, d, hcd⟩ := (Q'.edge_mem_iff_exists_isLink g).mp hg
          rcases G.eq_or_eq_of_isLink_of_isLink hl (hlk (hQ.isLink_mono hcd) hge) with rfl | rfl
          · exact Or.inl hcd.left_mem
          · exact Or.inl hcd.right_mem
      · rcases G.eq_or_eq_of_isLink_of_isLink hl h.lf with rfl | rfl
        · exact Or.inr ⟨rfl, hee⟩
        · obtain ⟨c, d, hcd⟩ := (Q'.edge_mem_iff_exists_isLink e).mp hee
          rcases hQ.isLink_mono hcd with ⟨p, -⟩ | ⟨-, ⟨-, rfl⟩ | ⟨rfl, -⟩⟩
          · exact absurd rfl p
          · exact Or.inl hcd.right_mem
          · exact Or.inl hcd.left_mem
    have hsubE : E(Q') ∪ {g | g = f ∧ e ∈ E(Q')} ⊆ E(G) := by
      rintro g (hg | ⟨rfl, -⟩)
      · exact (hE' ▸ hQ.edgeSet_mono hg : g ∈ E(G) \ {f}).1
      · exact h.lf.edge_mem
    exact ⟨V_part hinc, E_part hsubE, part_le hsub⟩
  refine ⟨fun z hz => (hV₀ hz).1, lift G w e f ∘ P', fun e₀ he₀ => ?_, fun e₁ he₁ e₂ he₂ hne => ?_,
    ?_, ?_⟩
  · obtain ⟨u, v, hl₀, hp, hne, hcap⟩ := h₁ e₀ he₀
    obtain ⟨hle, W', hsimp, hVw, hEw⟩ := hp
    obtain ⟨hVl, hEl, hle'⟩ := hfacts _ hle
    obtain ⟨W, a, b, c, d⟩ := lift_walk (Q := lift G w e f (P' e₀)) h hle
      (fun z hz => hVl ▸ Or.inl hz)
      (fun g p q hl hg => ⟨Or.inl ((P' e₀).edge_mem_iff_exists_isLink g |>.mpr ⟨p, q, hl⟩),
        hlk (hle.isLink_mono hl) hg⟩)
      (fun hee => ⟨⟨Or.inl hee, h.le⟩, ⟨Or.inr ⟨rfl, hee⟩, h.lf⟩⟩) W'
    refine ⟨u, v, hl₀, ⟨hle', W, d hsimp, ?_, ?_⟩, ?_, ?_⟩
    · ext z
      simp only [Function.comp_apply, hVl, mem_union, mem_ofPred_eq, hVw, hEw]
      by_cases hz : z = w
      · subst hz
        have : z ∉ W'.support := fun hh => (hle.vertexSet_mono (hVw ▸ hh)).2 rfl
        simp [this, b]
      · simp [hz, a z hz]
    · ext g
      simp only [Function.comp_apply, hEl, mem_union, mem_ofPred_eq, hEw, c g]
    · exact hne.mono fun g hg => hEl ▸ Or.inl hg
    · simp only [Function.comp_apply, hVl]
      rw [union_inter_distrib_right, ← hcap]
      have : {z | z = w ∧ e ∈ E(P' e₀)} ∩ V(G₀) = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨⟨rfl, -⟩, hz⟩
        exact hw₀ hz
      rw [this, union_empty]
  · obtain ⟨u₁, v₁, -, hp₁, -⟩ := h₁ e₁ he₁
    obtain ⟨u₂, v₂, -, hp₂, -⟩ := h₁ e₂ he₂
    obtain ⟨hV₁, hE₁, -⟩ := hfacts _ hp₁.1
    obtain ⟨hV₂, hE₂, -⟩ := hfacts _ hp₂.1
    obtain ⟨hd, hi⟩ := h₂ e₁ he₁ e₂ he₂ hne
    have hfnot : ∀ {Q'}, Q' ≤ G' → f ∉ E(Q') := fun hQ hh =>
      (hE' ▸ hQ.edgeSet_mono hh : f ∈ E(G) \ {f}).2 rfl
    have hwnot : ∀ {Q'}, Q' ≤ G' → w ∉ V(Q') := fun hQ hh => (hQ.vertexSet_mono hh).2 rfl
    simp only [Function.comp_apply]
    refine ⟨?_, ?_⟩
    · rw [hE₁, hE₂]
      refine disjoint_left.mpr ?_
      rintro g (hg | ⟨hgf, hee⟩) (hg' | ⟨hgf', hee'⟩)
      · exact disjoint_left.mp hd hg hg'
      · exact hfnot hp₁.1 (hgf' ▸ hg)
      · exact hfnot hp₂.1 (hgf ▸ hg')
      · exact disjoint_left.mp hd hee hee'
    · rw [hV₁, hV₂]
      rintro z ⟨hz | ⟨hzw, hee⟩, hz' | ⟨hzw', hee'⟩⟩
      · exact hi ⟨hz, hz'⟩
      · exact absurd (hzw' ▸ hz) (hwnot hp₁.1)
      · exact absurd (hzw ▸ hz') (hwnot hp₂.1)
      · exact absurd hee' (disjoint_left.mp hd hee)
  · ext z
    constructor
    · intro hz
      by_cases hzw : z = w
      · subst hzw
        have heE : e ∈ E(G') := by
          rw [hE']
          exact ⟨h.le.edge_mem, h.ne⟩
        rw [h₄] at heE
        obtain ⟨e₀, he₀, hee⟩ := mem_iUnion₂.mp heE
        obtain ⟨u, v, -, hp, -⟩ := h₁ e₀ he₀
        refine Or.inr (mem_iUnion₂.mpr ⟨e₀, he₀, ?_⟩)
        simp only [Function.comp_apply]
        rw [(hfacts _ hp.1).1]
        exact Or.inr ⟨rfl, hee⟩
      · have : z ∈ V(G') := ⟨hz, hzw⟩
        rw [h₃] at this
        rcases this with hh | hh
        · exact Or.inl hh
        · obtain ⟨e₀, he₀, hzz⟩ := mem_iUnion₂.mp hh
          obtain ⟨u, v, -, hp, -⟩ := h₁ e₀ he₀
          refine Or.inr (mem_iUnion₂.mpr ⟨e₀, he₀, ?_⟩)
          simp only [Function.comp_apply]
          rw [(hfacts _ hp.1).1]
          exact Or.inl hzz
    · rintro (hz | hz)
      · exact (hV₀ hz).1
      · obtain ⟨e₀, he₀, hzz⟩ := mem_iUnion₂.mp hz
        obtain ⟨u, v, -, hp, -⟩ := h₁ e₀ he₀
        exact (hfacts _ hp.1).2.2.vertexSet_mono hzz
  · ext g
    constructor
    · intro hg
      by_cases hgf : g = f
      · subst hgf
        have heE : e ∈ E(G') := by
          rw [hE']
          exact ⟨h.le.edge_mem, h.ne⟩
        rw [h₄] at heE
        obtain ⟨e₀, he₀, hee⟩ := mem_iUnion₂.mp heE
        obtain ⟨u, v, -, hp, -⟩ := h₁ e₀ he₀
        refine mem_iUnion₂.mpr ⟨e₀, he₀, ?_⟩
        simp only [Function.comp_apply]
        rw [(hfacts _ hp.1).2.1]
        exact Or.inr ⟨rfl, hee⟩
      · have : g ∈ E(G') := hE' ▸ ⟨hg, hgf⟩
        rw [h₄] at this
        obtain ⟨e₀, he₀, hzz⟩ := mem_iUnion₂.mp this
        obtain ⟨u, v, -, hp, -⟩ := h₁ e₀ he₀
        refine mem_iUnion₂.mpr ⟨e₀, he₀, ?_⟩
        simp only [Function.comp_apply]
        rw [(hfacts _ hp.1).2.1]
        exact Or.inl hzz
    · intro hg
      obtain ⟨e₀, he₀, hzz⟩ := mem_iUnion₂.mp hg
      obtain ⟨u, v, -, hp, -⟩ := h₁ e₀ he₀
      exact (hfacts _ hp.1).2.2.edgeSet_mono hzz

/-- A good graph with no vertex of valency 2 is simple and 3-connected. -/
theorem simple_of_good (hG : Good G) (h2 : ∀ v ∈ V(G), deg G v ≠ 2) :
    IsSimpleThreeConnectedGraph G := by
  classical
  have hfour : 4 ≤ V(G).ncard :=
    hG.four.trans (ncard_le_ncard (fun _ hv => hv.1) hG.finV)
  have hnot : ∀ {u v : α}, ¬ V(G) ⊆ {u, v} := fun {u v} hsub => by
    have := ncard_le_ncard hsub (toFinite _)
    have h2' := ncard_insert_le u ({v} : Set α)
    rw [ncard_singleton] at h2'
    omega
  refine ⟨⟨fun e _ v => hG.no_loop e v, ?_⟩, hfour, ?_⟩
  · intro e₁ he₁ e₂ he₂ u v hl₁ hl₂
    by_contra hne
    have huv : u ≠ v := fun hh => hG.no_loop e₁ v (hh ▸ hl₁)
    have hu := hl₁.left_mem
    have hv := hl₁.right_mem
    have hinc : ∀ g ∈ ({e₁, e₂} : Set β), ∀ z, G.Inc g z → z ∈ ({u, v} : Set α) := by
      rintro g (rfl | rfl) z ⟨t, ht⟩
      · rcases G.eq_or_eq_of_isLink_of_isLink ht hl₁ with rfl | rfl <;> simp
      · rcases G.eq_or_eq_of_isLink_of_isLink ht hl₂ with rfl | rfl <;> simp
    let A := part G {u, v} {e₁, e₂}
    let B := part G V(G) (E(G) \ {e₁, e₂})
    have hVA : V(A) = {u, v} := V_part hinc
    have hVB : V(B) = V(G) := V_part fun g hg z ⟨t, ht⟩ => ht.left_mem
    have hEA : E(A) = {e₁, e₂} := E_part (by
      rintro g (rfl | rfl)
      · exact he₁
      · exact he₂)
    have hEB : E(B) = E(G) \ {e₁, e₂} := E_part sdiff_subset
    have hsub : ({u, v} : Set α) ⊆ V(G) := by
      rintro z (rfl | rfl)
      · exact hu
      · exact hv
    have hcap : V(A) ∩ V(B) = {u, v} := by
      rw [hVA, hVB]
      exact inter_eq_left.mpr hsub
    have hc2 : ({u, v} : Set α).ncard = 2 := ncard_pair huv
    have hsep : IsGraphSeparation G A B := by
      refine ⟨part_le hsub, part_le subset_rfl, ?_, ?_, ?_⟩
      · rw [hVA, hVB]
        exact union_eq_right.mpr hsub
      · rw [hEA, hEB]
        ext g
        constructor
        · rintro ((rfl | rfl) | hg)
          · exact he₁
          · exact he₂
          · exact hg.1
        · intro hg
          by_cases hh : g ∈ ({e₁, e₂} : Set β)
          · exact Or.inl hh
          · exact Or.inr ⟨hg, hh⟩
      · rw [hEA, hEB]
        exact disjoint_sdiff_right
    rcases hG.sep A B hsep (by rw [hcap, hc2]) with ht | ht
    · rcases ht with ⟨-, hemp⟩ | ⟨-, -, hn⟩
      · have : e₁ ∈ E(A) := hEA ▸ Or.inl rfl
        rw [hemp] at this
        exact absurd this (notMem_empty _)
      · have hd : V(A) \ V(B) = ∅ := by
          rw [hVA, hVB]
          exact eq_empty_of_forall_notMem fun z hz => hz.2 (hsub hz.1)
        rw [hd, ncard_empty, hEA, ncard_pair hne] at hn
        omega
    · have hemp : ∀ z ∈ V(B) \ V(A), False := by
        rcases ht with ⟨hs', -⟩ | ⟨-, hd, -⟩
        · exact fun z hz => hz.2 (hs' hz.1)
        · exact fun z hz => h2 z (hVB ▸ hz.1) (hd z hz)
      refine hnot (u := u) (v := v) fun z hz => ?_
      by_contra hn
      exact hemp z ⟨hVB ▸ hz, hVA ▸ hn⟩
  · intro G₁ G₂ hs hord
    obtain ⟨-, -, hV, -, -⟩ := id hs
    have hkey : ∀ {A B : Graph α β}, V(A) ∪ V(B) = V(G) → Thin G A B → V(B) = V(G) := by
      intro A B hU ht
      have : V(A) ⊆ V(B) := by
        rcases ht with ⟨hs', -⟩ | ⟨-, hd, -⟩
        · exact hs'
        · intro z hz
          by_contra hn
          have hzG : z ∈ V(G) := hU ▸ Or.inl hz
          exact h2 z hzG (hd z ⟨hz, hn⟩)
      rw [← hU]
      exact (union_eq_right.mpr this).symm
    rcases hG.sep G₁ G₂ hs (by omega) with ht | ht
    · exact Or.inr (hkey hV ht)
    · exact Or.inl (hkey (by rw [union_comm]; exact hV) ht)

/-- Each graph is a subdivision of itself, if it has no loops. -/
theorem isSubdivisionOf_self (hl : ∀ e v, ¬ G.IsLink e v v) : IsSubdivisionOf G G := by
  classical
  refine ⟨subset_rfl, fun e => part G {z | G.Inc e z} {e}, fun e he => ?_,
    fun e₁ he₁ e₂ he₂ hne => ?_,
    ?_, ?_⟩
  · obtain ⟨u, v, huv⟩ := (G.edge_mem_iff_exists_isLink e).mp he
    have hne : u ≠ v := fun hh => hl e v (hh ▸ huv)
    have hV : V(part G {z | G.Inc e z} {e}) = {u, v} := by
      rw [V_part (fun g hg z hz => (mem_singleton_iff.mp hg) ▸ hz)]
      ext z
      constructor
      · rintro ⟨t, ht⟩
        rcases G.eq_or_eq_of_isLink_of_isLink ht huv with rfl | rfl <;> simp
      · rintro (rfl | rfl)
        · exact ⟨v, huv⟩
        · exact ⟨u, huv.symm⟩
    have hE : E(part G {z | G.Inc e z} {e}) = {e} := E_part (singleton_subset_iff.mpr he)
    have hlk : (part G {z | G.Inc e z} {e}).IsLink e u v := ⟨rfl, huv⟩
    refine ⟨u, v, huv, ⟨part_le fun z ⟨t, ht⟩ => ht.left_mem, .cons hlk (.nil hlk.right_mem), ?_,
      ?_, ?_⟩,
      ?_, ?_⟩
    · simp [GraphWalk.IsSimple, GraphWalk.support, hne]
    · rw [hV]
      ext z
      simp [GraphWalk.support]
    · rw [hE]
      ext z
      simp [GraphWalk.edges]
    · rw [hE]
      exact singleton_nonempty e
    · rw [hV]
      refine inter_eq_left.mpr ?_
      rintro z (rfl | rfl)
      · exact huv.left_mem
      · exact huv.right_mem
  · refine ⟨?_, fun z hz => ?_⟩
    · rw [E_part (singleton_subset_iff.mpr he₁), E_part (singleton_subset_iff.mpr he₂)]
      exact disjoint_singleton.mpr hne
    · obtain ⟨hz₁, -⟩ := hz
      rcases hz₁ with ⟨t, ht⟩ | ⟨g, -, t, ht⟩ <;> exact ht.left_mem
  · ext z
    constructor
    · exact Or.inl
    · rintro (hz | hz)
      · exact hz
      · obtain ⟨e, -, hz'⟩ := mem_iUnion₂.mp hz
        rcases hz' with ⟨t, ht⟩ | ⟨g, -, t, ht⟩ <;> exact ht.left_mem
  · ext g
    constructor
    · intro hg
      refine mem_iUnion₂.mpr ⟨g, hg, ?_⟩
      rw [E_part (singleton_subset_iff.mpr hg)]
      exact rfl
    · intro hg
      obtain ⟨e, he, hz'⟩ := mem_iUnion₂.mp hg
      rw [E_part (singleton_subset_iff.mpr he)] at hz'
      exact (mem_singleton_iff.mp hz') ▸ he

/-- A vertex of valency 2 in a good graph can be suppressed. -/
theorem exists_susp (hG : Good G) {w : α} (hw : w ∈ V(G)) (h2 : deg G w = 2) :
    ∃ x y e f, Susp G w x y e f := by
  classical
  obtain ⟨e, f, hne, hset⟩ := ncard_eq_two.mp h2
  have hIe : G.Inc e w := by
    have : e ∈ {g | G.Inc g w} := hset ▸ Or.inl rfl
    exact this
  have hIf : G.Inc f w := by
    have : f ∈ {g | G.Inc g w} := hset ▸ Or.inr rfl
    exact this
  obtain ⟨x, hx⟩ := hIe
  obtain ⟨y, hy⟩ := hIf
  have honly : ∀ g, G.Inc g w → g = e ∨ g = f := fun g hg => by
    have : g ∈ ({e, f} : Set β) := hset ▸ hg
    exact this
  have hxw : x ≠ w := fun hh => hG.no_loop e w (hh ▸ hx)
  have hyw : y ≠ w := fun hh => hG.no_loop f w (hh ▸ hy)
  refine ⟨x, y, e, f, hne, hx, hy, honly, hxw, hyw, ?_⟩
  rintro rfl
  have hinc : ∀ g ∈ ({e, f} : Set β), ∀ z, G.Inc g z → z ∈ ({w, x} : Set α) := by
    rintro g (rfl | rfl) z ⟨t, ht⟩
    · rcases G.eq_or_eq_of_isLink_of_isLink ht hx with rfl | rfl <;> simp
    · rcases G.eq_or_eq_of_isLink_of_isLink ht hy with rfl | rfl <;> simp
  have hinc₂ : ∀ g ∈ E(G) \ {e, f}, ∀ z, G.Inc g z → z ∈ V(G) \ {w} := by
    rintro g hg z ⟨t, ht⟩
    refine ⟨ht.left_mem, ?_⟩
    rintro rfl
    exact hg.2 (honly g ⟨t, ht⟩)
  let A := part G {w, x} {e, f}
  let B := part G (V(G) \ {w}) (E(G) \ {e, f})
  have hVA : V(A) = {w, x} := V_part hinc
  have hVB : V(B) = V(G) \ {w} := V_part hinc₂
  have hxV : x ∈ V(G) := hx.right_mem
  have hEA : E(A) = {e, f} := E_part (by
    rintro g (rfl | rfl)
    · exact hx.edge_mem
    · exact hy.edge_mem)
  have hEB : E(B) = E(G) \ {e, f} := E_part sdiff_subset
  have hcap : V(A) ∩ V(B) = {x} := by
    rw [hVA, hVB]
    ext z
    constructor
    · rintro ⟨rfl | rfl, hz⟩
      · exact absurd rfl hz.2
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hxV, hxw⟩
  have hsep : IsGraphSeparation G A B := by
    refine ⟨part_le ?_, part_le sdiff_subset, ?_, ?_, ?_⟩
    · rintro z (rfl | rfl)
      · exact hw
      · exact hxV
    · rw [hVA, hVB]
      ext z
      constructor
      · rintro ((rfl | rfl) | hz)
        · exact hw
        · exact hxV
        · exact hz.1
      · intro hz
        by_cases hzw : z = w
        · exact Or.inl (Or.inl hzw)
        · exact Or.inr ⟨hz, hzw⟩
    · rw [hEA, hEB]
      ext g
      constructor
      · rintro ((rfl | rfl) | hg)
        · exact hx.edge_mem
        · exact hy.edge_mem
        · exact hg.1
      · intro hg
        by_cases hh : g ∈ ({e, f} : Set β)
        · exact Or.inl hh
        · exact Or.inr ⟨hg, hh⟩
    · rw [hEA, hEB]
      exact disjoint_sdiff_right
  have hc1 : (V(A) ∩ V(B)).ncard = 1 := by rw [hcap, ncard_singleton]
  have hc1' : (V(B) ∩ V(A)).ncard = 1 := by rw [inter_comm]; exact hc1
  have hfour : 4 ≤ V(G).ncard := hG.four.trans (ncard_le_ncard (fun _ hv => hv.1) hG.finV)
  rcases hG.sep A B hsep (by omega) with ht | ht
  · rcases ht with ⟨hs', -⟩ | ⟨hc, -, -⟩
    · have : w ∈ V(B) := hs' (hVA ▸ Or.inl rfl)
      exact (hVB ▸ this : w ∈ V(G) \ {w}).2 rfl
    · omega
  · rcases ht with ⟨hs', -⟩ | ⟨hc, -, -⟩
    · have hsub : V(G) ⊆ {w, x} := by
        intro z hz
        by_cases hzw : z = w
        · exact Or.inl hzw
        · exact hVA ▸ hs' (hVB ▸ ⟨hz, hzw⟩)
      have := ncard_le_ncard hsub (toFinite _)
      have h2' := ncard_insert_le w ({x} : Set α)
      rw [ncard_singleton] at h2'
      omega
    · omega

/-- **A good graph is a subdivision of a simple 3-connected graph.** -/
theorem good_sub (hG : Good G) : IsSubdivisionOfSimpleThreeConnected G := by
  classical
  suffices key : ∀ (n : ℕ) (G : Graph α β), Good G → {v | v ∈ V(G) ∧ deg G v = 2}.ncard = n →
      IsSubdivisionOfSimpleThreeConnected G from key _ G hG rfl
  intro n
  induction n with
  | zero =>
    intro G hG hn
    have hfin : {v | v ∈ V(G) ∧ deg G v = 2}.Finite := hG.finV.subset fun _ hv => hv.1
    have hemp := (ncard_eq_zero hfin).mp hn
    have h2 : ∀ v ∈ V(G), deg G v ≠ 2 := fun v hv hd => by
      have : v ∈ {v | v ∈ V(G) ∧ deg G v = 2} := ⟨hv, hd⟩
      rw [hemp] at this
      exact this
    exact ⟨G, simple_of_good hG h2, isSubdivisionOf_self hG.no_loop⟩
  | succ n ih =>
    intro G hG hn
    have hfin : {v | v ∈ V(G) ∧ deg G v = 2}.Finite := hG.finV.subset fun _ hv => hv.1
    obtain ⟨w, hw⟩ := nonempty_of_ncard_ne_zero (s := {v | v ∈ V(G) ∧ deg G v = 2}) (by omega)
    obtain ⟨x, y, e, f, h⟩ := exists_susp hG hw.1 hw.2
    have hset : {v | v ∈ V(susp G w x y e f h) ∧ deg (susp G w x y e f h) v = 2} =
        {v | v ∈ V(G) ∧ deg G v = 2} \ {w} := by
      ext z
      simp only [V_susp]
      constructor
      · rintro ⟨⟨hz, hzw⟩, hd⟩
        exact ⟨⟨hz, by rwa [deg_susp h hG.finE hzw] at hd⟩, hzw⟩
      · rintro ⟨⟨hz, hd⟩, hzw⟩
        exact ⟨⟨hz, hzw⟩, by rwa [deg_susp h hG.finE hzw]⟩
    have hc : {v | v ∈ V(susp G w x y e f h) ∧ deg (susp G w x y e f h) v = 2}.ncard = n := by
      rw [hset, ncard_sdiff_singleton_of_mem hw]
      omega
    obtain ⟨G₀, h₁, h₂⟩ := ih _ (hG.susp h hw.2) hc
    exact ⟨G₀, h₁, sub_step h h₂⟩

end GraphMinor.GM14.Whitney
