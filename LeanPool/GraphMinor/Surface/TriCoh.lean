/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.TriLocal
public import LeanPool.GraphMinor.Surface.TriCount
public import LeanPool.GraphMinor.Surface.LocalCoh
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The cohomology of a triangulation

For a triangulation of a connected closed surface we compare the classes of local cocycles with
values in the field with two elements (`KCl`) to the cocycles of the triangulation modulo
coboundaries. This gives `|V| - |E| + |F| + κ = 2`, where `2 ^ κ` is the number of classes
(`euler_eq`). The classification of surfaces gives the value of `κ` on each surface, so the number
`|V| - |E| + |F|` depends only on the surface. This is the Euler characteristic used in the proof of
Graph Minors XIX, (6.5) (page 341).

A local cocycle has a primitive on each face (`exists_prim_disc`). The primitives on two faces
differ by a constant on a common edge, so the differences of the primitive at the two ends of an
edge define a cocycle of the triangulation. In the other direction, a cocycle `y` of the
triangulation gives a local cocycle through a map `s` from the surface to the vertices with `x` in
the open star of `s x`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter Matrix

local notation "K" => ZMod 2

variable {X : Type} [TopologicalSpace X]

/-- A primitive of `φ` on the set `Φ`. -/
def Prim (φ : X → X → K) (Φ : Set X) (g : X → K) : Prop :=
  ∀ p ∈ Φ, ∃ W ∈ 𝓝 p, ∀ x ∈ W ∩ Φ, ∀ x' ∈ W ∩ Φ, φ x x' = g x + g x'

theorem exists_prim_disc {φ : X → X → K} (hφ : IsCoc φ) {Φ : Set X} (hD : IsClosedDisc Φ) : ∃ g,
  Prim φ Φ g := by
  obtain ⟨k, l, c⟩ := hD.exists_isChart
  obtain ⟨G, ε, hε, hG⟩ := exists_prim hφ c.gc
  refine ⟨G ∘ k, fun p hp => ?_⟩
  have hk : ContinuousWithinAt k Φ p := c.hc p hp
  have h1 : k ⁻¹' ball (k p) (ε / 2) ∈ 𝓝[Φ] p := hk.preimage_mem_nhdsWithin (ball_mem_nhds _
    (by positivity))
  obtain ⟨W, hW, hWs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h1
  refine ⟨W, hW, fun x hx x' hx' => ?_⟩
  have h2 := hG (k x) (c.hm hx.2) (k x') (c.hm hx'.2) (by
    have h3 : k x ∈ ball (k p) (ε / 2) := hWs hx
    have h4 : k x' ∈ ball (k p) (ε / 2) := hWs hx'
    rw [mem_ball, dist_eq_norm] at h3 h4
    have h5 : ‖k x - k x'‖ ≤ ‖k x - k p‖ + ‖k x' - k p‖ := by
      have : k x - k x' = (k x - k p) - (k x' - k p) := by ring
      rw [this]
      exact norm_sub_le _ _
    linarith)
  rw [c.gh hx.2, c.gh hx'.2] at h2
  rw [h2, CharTwo.neg_eq]
  rfl

theorem Prim.mono {φ : X → X → K} {Φ Ψ : Set X} {g : X → K} (h : Prim φ Φ g)
  (hs : Ψ ⊆ Φ) : Prim φ Ψ g := fun p hp => by
  obtain ⟨W, hW, h1⟩ := h p (hs hp)
  exact ⟨W, hW, fun x hx x' hx' => h1 x ⟨hx.1, hs hx.2⟩ x' ⟨hx'.1, hs hx'.2⟩⟩

theorem Prim.add {φ φ' : X → X → K} {Φ : Set X} {g g' : X → K} (h : Prim φ Φ g)
  (h' : Prim φ' Φ g') :
    Prim (fun x y => φ x y + φ' x y) Φ (fun x => g x + g' x) := fun p hp => by
  obtain ⟨W, hW, h1⟩ := h p hp
  obtain ⟨W', hW', h2⟩ := h' p hp
  refine ⟨W ∩ W', inter_mem hW hW', fun x hx x' hx' => ?_⟩
  change φ x x' + φ' x x' = (g x + g' x) + (g x' + g' x')
  rw [h1 x ⟨hx.1.1, hx.2⟩ x' ⟨hx'.1.1, hx'.2⟩, h2 x ⟨hx.1.2, hx.2⟩ x' ⟨hx'.1.2, hx'.2⟩]
  ring

/-- A function that is locally constant on a preconnected set is constant. -/
theorem const_of_locally {C : Set X} (hC : IsPreconnected C) {u : X → K}
  (h : ∀ p ∈ C, ∃ W ∈ 𝓝 p, ∀ x ∈ W ∩ C, u x = u p)
    {a b : X} (ha : a ∈ C) (hb : b ∈ C) : u a = u b := by
  have hp : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  let f : C → K := fun x => u x
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨W, hW, h1⟩ := h x.1 x.2
    have h2 : Subtype.val ⁻¹' W ∈ 𝓝 x := continuous_subtype_val.continuousAt.preimage_mem_nhds hW
    exact Filter.mem_of_superset h2 fun y hy => h1 y.1 ⟨hy, y.2⟩
  exact hf.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩

/-- Two primitives of the same `φ` differ by a constant on a preconnected common subset. -/
theorem Prim.const {φ : X → X → K} {Φ Φ' C : Set X} {g g' : X → K} (h : Prim φ Φ g)
  (h' : Prim φ Φ' g') (hC : IsPreconnected C)
    (hs : C ⊆ Φ) (hs' : C ⊆ Φ') {a b : X} (ha : a ∈ C) (hb : b ∈ C) : g a + g' a = g b + g' b := by
  refine const_of_locally hC (u := fun x => g x + g' x) (fun p hp => ?_) ha hb
  obtain ⟨W, hW, h1⟩ := h p (hs hp)
  obtain ⟨W', hW', h2⟩ := h' p (hs' hp)
  refine ⟨W ∩ W', inter_mem hW hW', fun x hx => ?_⟩
  have h3 := h1 p ⟨mem_of_mem_nhds hW, hs hp⟩ x ⟨hx.1.1, hs hx.2⟩
  have h4 := h2 p ⟨mem_of_mem_nhds hW', hs' hp⟩ x ⟨hx.1.2, hs' hx.2⟩
  have h5 := h3.symm.trans h4
  have h6 : g x + g' x + (g p + g' p) = (g p + g x) + (g' p + g' x) := by ring
  have h7 : g x + g' x + (g p + g' p) = 0 := by
    rw [h6, h5]
    exact CharTwo.add_self_eq_zero _
  exact CharTwo.add_eq_zero.mp h7

variable [T2Space X]

omit [TopologicalSpace X] [T2Space X] in
theorem ncard_val_preimage (V A : Set X) : ({v : V | v.1 ∈ A}).ncard = (A ∩ V).ncard := by
  have h1 : Subtype.val '' {v : V | v.1 ∈ A} = A ∩ V := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, v.2⟩
    · exact fun h => ⟨⟨x, h.2⟩, h.1, rfl⟩
  rw [← h1, ncard_image_of_injective _ Subtype.val_injective]

namespace IsTriang

variable {V : Set X} {E 𝓕 : Set (Set X)}

/-- The combinatorics of a triangulation. -/
noncomputable def cx (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] : TriCx V E 𝓕
  where
  ends e := {v | v.1 ∈ e.1}
  verts Φ := {v | v.1 ∈ Φ.1}
  ends_two e := by
    rw [ncard_val_preimage]
    exact h.ends_ncard e.2
  ends_inj e f hef := by
    have hef' : {v : V | v.1 ∈ e.1} = {v : V | v.1 ∈ f.1} := hef
    refine Subtype.ext (h.simple e.1 e.2 f.1 f.2 ?_)
    ext x
    constructor
    · intro hx
      have : (⟨x, hx.2⟩ : V) ∈ {v : V | v.1 ∈ f.1} := hef' ▸ (hx.1 : (⟨x, hx.2⟩ : V).1 ∈ e.1)
      exact ⟨this, hx.2⟩
    · intro hx
      have : (⟨x, hx.2⟩ : V) ∈ {v : V | v.1 ∈ e.1} := hef' ▸ (hx.1 : (⟨x, hx.2⟩ : V).1 ∈ f.1)
      exact ⟨this, hx.2⟩
  verts_three Φ := by
    rw [ncard_val_preimage]
    exact h.three Φ.1 Φ.2
  pair Φ a ha b hb hab := by
    obtain ⟨e, he, -, hi⟩ := h.face_pair Φ.2 ⟨ha, a.2⟩ ⟨hb, b.2⟩ (fun h' => hab (Subtype.ext h'))
    refine ⟨⟨e, he⟩, ?_⟩
    ext v
    have h1 : v.1 ∈ e ∩ V ↔ v.1 ∈ ({a.1, b.1} : Set X) := by rw [hi]
    constructor
    · intro hv
      rcases h1.mp ⟨hv, v.2⟩ with h2 | h2
      · exact .inl (Subtype.ext h2)
      · exact .inr (Subtype.ext h2)
    · rintro (rfl | rfl)
      · exact (h1.mpr (.inl rfl)).1
      · exact (h1.mpr (.inr rfl)).1
  two e := by
    have h1 := h.two_faces hT e.2
    have h2 : Subtype.val '' {Φ : 𝓕 | ({v : V | v.1 ∈ e.1} : Set V) ⊆ {v | v.1 ∈ Φ.1}}
      = {Φ ∈ 𝓕 | e.1 ⊆ Φ} := by
      ext Φ
      constructor
      · rintro ⟨Φ', hΦ', rfl⟩
        refine ⟨Φ'.2, (h.sub_iff e.2 Φ'.2).mpr fun y hy => ?_⟩
        exact hΦ' (show (⟨y, hy.2⟩ : V).1 ∈ e.1 from hy.1)
      · rintro ⟨hΦ, h3⟩
        exact ⟨⟨Φ, hΦ⟩, fun v hv => h3 hv, rfl⟩
    rw [← h1, ← h2, ncard_image_of_injective _ Subtype.val_injective]
  conn S hS hne := by
    have h1 := h.graph_conn (S := Subtype.val '' S) (fun e he a ha b hb has => by
      obtain ⟨a', ha', rfl⟩ := has
      exact ⟨⟨b, hb.2⟩, hS ⟨e, he⟩ a' ha.1 ⟨b, hb.2⟩ hb.1 ha', rfl⟩) (by
      obtain ⟨v, hv⟩ := hne
      exact ⟨v.1, ⟨v, hv, rfl⟩, v.2⟩)
    rw [eq_univ_iff_forall]
    intro v
    obtain ⟨v', hv', h2⟩ := h1 v.2
    rwa [show v = v' from (Subtype.ext h2).symm]
  dual S hS hne := by
    have h1 := h.dual_conn hT (𝓐 := Subtype.val '' S) (by
      rintro _ ⟨Φ, -, rfl⟩
      exact Φ.2) (fun e he Φ hΦ Φ' hΦ' h2 h3 => by
      obtain ⟨Φ₀, hΦ₀, rfl⟩ := hΦ
      exact ⟨⟨Φ', hΦ'⟩, hS ⟨e, he⟩ Φ₀ hΦ₀ ⟨Φ', hΦ'⟩ (fun v hv => h2 hv) (fun v hv => h3 hv),
        rfl⟩) (hne.image _)
    rw [eq_univ_iff_forall]
    intro Φ
    obtain ⟨Φ', hΦ', h2⟩ : Φ.1 ∈ Subtype.val '' S := by
      rw [h1]
      exact Φ.2
    rwa [show Φ = Φ' from (Subtype.ext h2).symm]
  link w S hS hcl hne Φ' hw := by
    have h1 := h.link_conn hT w.2 (𝓐 := Subtype.val '' S) (by
      rintro _ ⟨Φ, -, rfl⟩
      exact Φ.2) (by
      rintro _ ⟨Φ, hΦ, rfl⟩
      exact hS Φ hΦ) (fun e he hwe Φ hΦ Φ₂ hΦ₂ h2 h3 => by
      obtain ⟨Φ₀, hΦ₀, rfl⟩ := hΦ
      exact ⟨⟨Φ₂, hΦ₂⟩, hcl ⟨e, he⟩ hwe Φ₀ hΦ₀ ⟨Φ₂, hΦ₂⟩ (fun v hv => h2 hv) (fun v hv => h3 hv),
        rfl⟩) (hne.image _) Φ'.2 hw
    obtain ⟨Φ₂, hΦ₂, h2⟩ := h1
    rwa [show Φ' = Φ₂ from (Subtype.ext h2).symm]

theorem cx_I (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] (e : E) (Φ : 𝓕) :
    (h.cx hT).I e Φ ↔ e.1 ⊆ Φ.1 := by
  constructor
  · intro h1
    refine (h.sub_iff e.2 Φ.2).mpr fun y hy => ?_
    exact h1 (show (⟨y, hy.2⟩ : V).1 ∈ e.1 from hy.1)
  · exact fun h1 v hv => h1 hv

variable [Fintype V] [Fintype E] [Fintype 𝓕]

/-- The function `y` on the edges records the primitives of `φ` on the faces. -/
def Rep (V : Set X) (E 𝓕 : Set (Set X)) (φ : X → X → K) (y : E → K) : Prop :=
  ∃ g : Set X → X → K, (∀ Φ ∈ 𝓕, Prim φ Φ (g Φ)) ∧
    ∀ e : E, ∀ Φ ∈ 𝓕, e.1 ⊆ Φ → ∀ a ∈ e.1 ∩ V, ∀ b ∈ e.1 ∩ V, a ≠ b → y e = g Φ a + g Φ b

theorem zero3 (a b c : K) : (a + b) + (b + c) + (a + c) = 0 := by
  revert a b c
  decide

omit [T2Space X] [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
theorem exists_face (h : IsTriang V E 𝓕) (y : X) : ∃ Φ ∈ 𝓕, y ∈ Φ := by
  have : y ∈ ⋃₀ 𝓕 := h.dis.cover ▸ mem_univ y
  exact this

omit [T2Space X] [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
theorem isPreconnected_edge (h : IsTriang V E 𝓕) {e : Set X} (he : e ∈ E) : IsPreconnected e := by
  obtain ⟨u, v, -, hl, -⟩ := h.dis.graph.edge e he
  obtain ⟨a, ha, hr, -, -⟩ := hl.exists_arc
  rw [← hr]
  exact isPreconnected_range ha.1

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
/-- The three edges of a face. -/
theorem exists_three_edges (h : IsTriang V E 𝓕) {Φ : Set X} (hΦ : Φ ∈ 𝓕) {a b c : X}
  (ha : a ∈ Φ ∩ V) (hb : b ∈ Φ ∩ V)
    (hc : c ∈ Φ ∩ V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, ∃ e₃ ∈ E, e₁ ⊆ Φ ∧ e₂ ⊆ Φ ∧ e₃ ⊆ Φ ∧ e₁ ∩ V = {a, b} ∧ e₂ ∩ V = {b, c}
      ∧ e₃ ∩ V = {a, c} ∧
      e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
  obtain ⟨e₁, h1, h1s, h1i⟩ := h.face_pair hΦ ha hb hab
  obtain ⟨e₂, h2, h2s, h2i⟩ := h.face_pair hΦ hb hc hbc
  obtain ⟨e₃, h3, h3s, h3i⟩ := h.face_pair hΦ ha hc hac
  refine ⟨e₁, h1, e₂, h2, e₃, h3, h1s.trans (discBd_subset Φ), h2s.trans (discBd_subset Φ),
    h3s.trans (discBd_subset Φ),
    h1i, h2i, h3i, ?_, ?_, ?_⟩
  · rintro rfl
    have : a ∈ ({b, c} : Set X) := h2i ▸ h1i ▸ (Or.inl rfl : a ∈ ({a, b} : Set X))
    rcases this with h4 | h4
    · exact hab h4
    · exact hac h4
  · rintro rfl
    have : c ∈ ({a, b} : Set X) := h1i ▸ h3i ▸ (Or.inr rfl : c ∈ ({a, c} : Set X))
    rcases this with h4 | h4
    · exact hac h4.symm
    · exact hbc h4.symm
  · rintro rfl
    have : a ∈ ({b, c} : Set X) := h2i ▸ h3i ▸ (Or.inl rfl : a ∈ ({a, c} : Set X))
    rcases this with h4 | h4
    · exact hab h4
    · exact hac h4

omit [T2Space X] [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
/-- Three names for the vertices of a face. -/
theorem exists_verts (h : IsTriang V E 𝓕) {Φ : Set X} (hΦ : Φ ∈ 𝓕) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Φ ∩ V = {a, b, c} := by
  obtain ⟨a, b, c, h1, h2, h3, h4⟩ := ncard_eq_three.mp (h.three Φ hΦ)
  exact ⟨a, b, c, h1, h2, h3, h4⟩

omit [Fintype ↑V] [Fintype ↑𝓕] in
/-- **Each local cocycle gives a cocycle of the triangulation.** -/
theorem exists_rep (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {φ : X → X → K}
  (hφ : IsCoc φ) :
    ∃ y : E → K, (h.cx hT).M.mulVec y = 0 ∧ Rep V E 𝓕 φ y := by
  classical
  have : Finite V := h.dis.graph.fin.to_subtype
  have : Finite 𝓕 := h.dis.fin.to_subtype
  have hch : ∀ Φ : Set X, ∃ g, Φ ∈ 𝓕 → Prim φ Φ g := fun Φ => by
    by_cases hΦ : Φ ∈ 𝓕
    · obtain ⟨g, hg⟩ := exists_prim_disc hφ (h.dis.disc Φ hΦ)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hΦ⟩
  choose g hg using hch
  have agree : ∀ e ∈ E, ∀ Φ ∈ 𝓕, ∀ Φ' ∈ 𝓕, e ⊆ Φ → e ⊆ Φ' → ∀ a ∈ e, ∀ b ∈ e, g Φ a + g Φ b
    = g Φ' a + g Φ' b :=
    fun e he Φ hΦ Φ' hΦ' h1 h2 a ha b hb => by
      have h3 := (hg Φ hΦ).const (hg Φ' hΦ') (h.isPreconnected_edge he) h1 h2 ha hb
      have h4 : g Φ a + g Φ b + (g Φ' a + g Φ' b) = (g Φ a + g Φ' a) + (g Φ b + g Φ' b) := by ring
      refine CharTwo.add_eq_zero.mp ?_
      rw [h4, h3]
      exact CharTwo.add_self_eq_zero _
  have hdata : ∀ e : E, ∃ (Φ : Set X) (u v : X), Φ ∈ 𝓕 ∧ e.1 ⊆ Φ ∧ u ≠ v ∧ e.1 ∩ V = {u, v}
    := fun e => by
    obtain ⟨u, v, huv, -, hi⟩ := h.dis.graph.edge e.1 e.2
    obtain ⟨x, hxe, hxV⟩ := h.exists_inner e.2
    obtain ⟨Φ, hΦ, hx⟩ := h.exists_face x
    exact ⟨Φ, u, v, hΦ, (h.edge_sub e.2 hΦ hxe hxV hx).trans (discBd_subset Φ), huv, hi⟩
  choose Φ₀ u₀ v₀ hΦ₀ hsub₀ hne₀ hi₀ using hdata
  let y : E → K := fun e => g (Φ₀ e) (u₀ e) + g (Φ₀ e) (v₀ e)
  have hrep : ∀ e : E, ∀ Φ ∈ 𝓕, e.1 ⊆ Φ → ∀ a ∈ e.1 ∩ V, ∀ b ∈ e.1 ∩ V, a ≠ b → y e = g Φ a + g Φ b
    := by
    intro e Φ hΦ hs a ha b hb hab
    have hu : u₀ e ∈ e.1 ∩ V := hi₀ e ▸ Or.inl rfl
    have hv : v₀ e ∈ e.1 ∩ V := hi₀ e ▸ Or.inr rfl
    have h1 : y e = g Φ (u₀ e) + g Φ (v₀ e) := agree e.1 e.2 _ (hΦ₀ e) Φ hΦ
      (hsub₀ e) hs _ hu.1 _ hv.1
    rw [h1]
    have ha' : a ∈ ({u₀ e, v₀ e} : Set X) := hi₀ e ▸ ha
    have hb' : b ∈ ({u₀ e, v₀ e} : Set X) := hi₀ e ▸ hb
    rcases ha' with h2 | h2 <;> rcases hb' with h3 | h3
    · exact absurd (h2.trans h3.symm) hab
    · rw [h2, h3]
    · rw [h2, h3, add_comm]
    · exact absurd (h2.trans h3.symm) hab
  refine ⟨y, ?_, g, hg, hrep⟩
  funext Φ
  obtain ⟨a, b, c, hab, hac, hbc, hE⟩ := h.exists_verts Φ.2
  have ha : a ∈ Φ.1 ∩ V := hE ▸ Or.inl rfl
  have hb : b ∈ Φ.1 ∩ V := hE ▸ Or.inr (Or.inl rfl)
  have hc : c ∈ Φ.1 ∩ V := hE ▸ Or.inr (Or.inr rfl)
  obtain ⟨e₁, h1, e₂, h2, e₃, h3, s1, s2, s3, i1, i2, i3, n12, n13, n23⟩
    := h.exists_three_edges Φ.2 ha hb hc hab hac hbc
  have hn : ∀ {e f : Set X} (he : e ∈ E) (hf : f ∈ E), e ≠ f → (⟨e, he⟩ : E) ≠ ⟨f, hf⟩
    := fun _ _ hn h' => hn (congrArg Subtype.val h')
  rw [(h.cx hT).sum_three y Φ ((h.cx_I hT ⟨e₁, h1⟩ Φ).mpr s1) ((h.cx_I hT ⟨e₂, h2⟩ Φ).mpr s2)
    ((h.cx_I hT ⟨e₃, h3⟩ Φ).mpr s3) (hn _ _ n12) (hn _ _ n13) (hn _ _ n23)]
  rw [hrep ⟨e₁, h1⟩ Φ Φ.2 s1 a (i1 ▸ Or.inl rfl) b (i1 ▸ Or.inr rfl) hab,
    hrep ⟨e₂, h2⟩ Φ Φ.2 s2 b (i2 ▸ Or.inl rfl) c (i2 ▸ Or.inr rfl) hbc,
    hrep ⟨e₃, h3⟩ Φ Φ.2 s3 a (i3 ▸ Or.inl rfl) c (i3 ▸ Or.inr rfl) hac]
  exact zero3 _ _ _

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
/-- The ends of an edge in the complex. -/
theorem cx_ends (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] (e : E) {a b : X}
  (ha : a ∈ V) (hb : b ∈ V)
    (hi : e.1 ∩ V = {a, b}) : (h.cx hT).ends e = {⟨a, ha⟩, ⟨b, hb⟩} := by
  ext v
  change v.1 ∈ e.1 ↔ _
  constructor
  · intro hv
    have : v.1 ∈ ({a, b} : Set X) := hi ▸ ⟨hv, v.2⟩
    rcases this with h1 | h1
    · exact .inl (Subtype.ext h1)
    · exact .inr (Subtype.ext h1)
  · rintro (rfl | rfl)
    · exact (hi ▸ (Or.inl rfl) : a ∈ e.1 ∩ V).1
    · exact (hi ▸ (Or.inr rfl) : b ∈ e.1 ∩ V).1

omit [Fintype ↑V] [Fintype ↑E] [Fintype ↑𝓕] in
theorem exists_edge_face (h : IsTriang V E 𝓕) (e : E) : ∃ (Φ : Set X) (u v : X), Φ ∈ 𝓕 ∧ e.1 ⊆ Φ
  ∧ u ≠ v ∧ e.1 ∩ V = {u, v} := by
  obtain ⟨u, v, huv, -, hi⟩ := h.dis.graph.edge e.1 e.2
  obtain ⟨x, hxe, hxV⟩ := h.exists_inner e.2
  obtain ⟨Φ, hΦ, hx⟩ := h.exists_face x
  exact ⟨Φ, u, v, hΦ, (h.edge_sub e.2 hΦ hxe hxV hx).trans (discBd_subset Φ), huv, hi⟩

omit [Fintype ↑E] [Fintype ↑𝓕] in
/-- **Equivalent local cocycles give cocycles that differ by a coboundary.** -/
theorem rep_coboundary (h : IsTriang V E 𝓕) (hT : IsClosedSurface X) [ConnectedSpace X] {φ φ' : X
  → X → K} {y y' : E → K}
    (hy : Rep V E 𝓕 φ y) (hy' : Rep V E 𝓕 φ' y') (hr : CohRel φ φ') :
    ∃ w : V → K, (h.cx hT).N.mulVec w = y + y' := by
  obtain ⟨g, hg, hrep⟩ := hy
  obtain ⟨g', hg', hrep'⟩ := hy'
  obtain ⟨h₀, N, hN, hrel⟩ := hr
  refine ⟨fun v => h₀ v.1, ?_⟩
  funext e
  obtain ⟨Φ, u, v, hΦ, hs, huv, hi⟩ := h.exists_edge_face e
  have hu : u ∈ e.1 ∩ V := hi ▸ Or.inl rfl
  have hv : v ∈ e.1 ∩ V := hi ▸ Or.inr rfl
  have hne : (⟨u, hu.2⟩ : V) ≠ ⟨v, hv.2⟩ := fun h' => huv (congrArg Subtype.val h')
  rw [(h.cx hT).sum_ends e hne (h.cx_ends hT e hu.2 hv.2 hi), Pi.add_apply,
    hrep e Φ hΦ hs u hu v hv huv,
    hrep' e Φ hΦ hs u hu v hv huv]
  have hc := const_of_locally (h.isPreconnected_edge e.2) (u := fun x => g Φ x + g' Φ x + h₀ x)
    (fun p hp => by
    obtain ⟨W, hW, h1⟩ := hg Φ hΦ p (hs hp)
    obtain ⟨W', hW', h2⟩ := hg' Φ hΦ p (hs hp)
    have hNp : (fun x => (p, x)) ⁻¹' N ∈ 𝓝 p :=
      (Continuous.prodMk_right p).continuousAt.preimage_mem_nhds (hN p)
    refine ⟨W ∩ W' ∩ _, inter_mem (inter_mem hW hW') hNp, fun x hx => ?_⟩
    have h3 := h1 p ⟨mem_of_mem_nhds hW, hs hp⟩ x ⟨hx.1.1.1, hs hx.2⟩
    have h4 := h2 p ⟨mem_of_mem_nhds hW', hs hp⟩ x ⟨hx.1.1.2, hs hx.2⟩
    have h5 := hrel p x hx.1.2
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, h3, h4] at h5
    have h6 : (g Φ x + g' Φ x + h₀ x) + (g Φ p + g' Φ p + h₀ p) = (g Φ p + g Φ x +
      (g' Φ p + g' Φ x)) + (h₀ x + h₀ p) := by
      ring
    refine CharTwo.add_eq_zero.mp ?_
    rw [h6, h5]
    exact CharTwo.add_self_eq_zero _) hu.1 hv.1
  have h7 : (g Φ u + g Φ v + (g' Φ u + g' Φ v)) + (h₀ u + h₀ v) =
      (g Φ u + g' Φ u + h₀ u) + (g Φ v + g' Φ v + h₀ v) := by ring
  refine (CharTwo.add_eq_zero.mp ?_).symm
  rw [h7, hc]
  exact CharTwo.add_self_eq_zero _

end IsTriang

end GraphMinor.Surface
