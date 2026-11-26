/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation
public import LeanPool.GraphMinor.GM11.Section5b
import LeanPool.GraphMinor.GM11.LeafNbhd

/-!
# Corners at a vertex, and even valency

The corners of `exists_rotation` lie in regions. This file records which regions, in `IsCorners`
and `exists_corners`, and deduces that "every vertex of $N(Z_1)$ has even valency" (Graph Minors XI,
proof of (5.4), page 83): `even_nHalf`, where a loop counts twice. Going around the vertex, the
colour of the corner, in `Z` or not, changes exactly at the half-edges of `N(Z)`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- `next` is a cyclic order of the half-edges at `v`, and `ρ k` is the region of the corner between
`k` and `next k`. -/
structure IsCorners (Γ : Drawing S) (γ : Set S → I → S) (v : S)
    (next : halfEdges Γ γ v → halfEdges Γ γ v) (ρ : halfEdges Γ γ v → Set S) : Prop where
  inj : Function.Injective next
  reach : ∀ a b, Relation.ReflTransGen (fun x y => y = next x) a b
  region : ∀ k, ρ k ∈ Γ.R
  closure_v : ∀ k, v ∈ closure (ρ k)
  all : ∀ r ∈ Γ.R, v ∈ closure r → ∃ k, r = ρ k
  left : ∀ k, (next k).1.1 ⊆ closure (ρ k)
  right : ∀ k, (next k).1.1 ⊆ closure (ρ (next k))
  sides : ∀ k, ∀ r ∈ Γ.R, (next k).1.1 ⊆ closure r → r = ρ k ∨ r = ρ (next k)

/-- The sectors behind the corners at a vertex `v`: the part `P k` of the corner `k` near `v`,
inside
a closed disc `Q k` with `v` on its boundary. -/
structure IsSectors (Γ : Drawing S) (γ : Set S → I → S) (v : S)
    (next : halfEdges Γ γ v → halfEdges Γ γ v) (ρ P : halfEdges Γ γ v → Set S) (W : Set S)
    (Q : halfEdges Γ γ v → Set S) (τ : halfEdges Γ γ v → I) : Prop where
  corners : IsCorners Γ γ v next ρ
  next_ne : ∀ k, next k ≠ k
  isOpen : IsOpen W
  mem : v ∈ W
  sub : ∀ k, P k ⊆ ρ k
  cover : W \ Γ.U ⊆ ⋃ k, P k
  subQ : ∀ k, P k ⊆ Q k
  disc : ∀ k, IsClosedDisc (Q k)
  bd : ∀ k, v ∈ discBd (Q k)
  inside : ∀ k, (W ∩ Q k) \ discBd (Q k) ⊆ P k
  inter : ∀ k j, k ≠ j → Q k ∩ Q j ⊆ Γ.U
  off : ∀ k (i : halfEdges Γ γ v), i ≠ k → i ≠ next k → ∀ t : I, 0 < t → spoke γ i.1 t ∈ W →
    spoke γ i.1 t ∉ Q k
  bdU : ∀ k, W ∩ discBd (Q k) ⊆ Γ.U
  pos : ∀ k, 0 < τ k
  left : ∀ k t, t ≤ τ k → spoke γ k.1 t ∈ discBd (Q k)
  right : ∀ k t, t ≤ τ (next k) → spoke γ (next k).1 t ∈ discBd (Q k)

/-- The corners at a vertex with at least two half-edges, with their sectors. -/
theorem exists_sectors (hS : IsClosedSurface S)
    (Γ : Drawing S) {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v)) :
    ∃ next ρ P W Q τ, IsSectors Γ γ v next ρ P W Q τ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : T2Space S := hS.2.1
  obtain ⟨next, P, W, Q, hW, hvW, hinj, hne, hreach, hconn, hdis, hcl, hcov, hsid, hQ, hQQ, hoff,
    hbdU, τ, hτ, hτl, hτr⟩ := exists_rotation_sectors hS Γ hγ hv h2
  have hex : ∀ k, ∃ r ∈ Γ.R, P k ⊆ r := by
    intro k
    obtain ⟨x, hx⟩ : (P k).Nonempty := by
      by_contra h
      have h0 := not_nonempty_iff_eq_empty.mp h
      have := hcl k
      rw [h0] at this
      simp at this
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp (hdis k) hx)
    exact ⟨r, hr, subset_region hr (hconn k) (hdis k) hx hxr⟩
  choose ρ hρ hsub using hex
  have hin : ∀ {r x}, r ∈ Γ.R → x ∈ r → ∀ k, x ∈ P k → r = ρ k := fun hr hx k hk =>
    region_eq_of_mem hr (hρ k) hx (hsub k hk)
  refine ⟨next, ρ, P, W, Q, τ, ⟨⟨hinj, hreach, hρ, fun k => closure_mono (hsub k) (hcl k), ?_, ?_,
    ?_, ?_⟩, hne, hW, hvW, hsub, hcov, fun k => (hQ k).2.2.1, fun k => (hQ k).1,
    fun k => (hQ k).2.1, fun k => (hQ k).2.2.2, hQQ, hoff, hbdU, hτ, hτl, hτr⟩⟩
  · intro r hr hvr
    obtain ⟨x, hxW, hxr⟩ := mem_closure_iff.mp hvr W hW hvW
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov ⟨hxW, region_subset hr hxr⟩)
    exact ⟨k, hin hr hxr k hk⟩
  · intro k
    obtain ⟨q, hq, O, -, -, -, h₁, -⟩ := hsid k
    exact edge_subset_closure_of_incident hS (next k).2.1 (hρ k)
      ⟨q, hq, closure_mono (hsub k) h₁⟩
  · intro k
    obtain ⟨q, hq, O, -, -, -, -, h₂⟩ := hsid k
    exact edge_subset_closure_of_incident hS (next k).2.1 (hρ _)
      ⟨q, hq, closure_mono (hsub _) h₂⟩
  · intro k r hr hsubr
    obtain ⟨q, hq, O, hO, hqO, hOs, -, -⟩ := hsid k
    obtain ⟨x, hxO, hxr⟩ := mem_closure_iff.mp (hsubr hq) O hO hqO
    rcases hOs ⟨hxO, region_subset hr hxr⟩ with h | h
    · exact Or.inl (hin hr hxr _ h)
    · exact Or.inr (hin hr hxr _ h)

/-- The corners at a vertex with at least two half-edges. -/
theorem exists_corners (hS : IsClosedSurface S)
    (Γ : Drawing S) {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v)) :
    ∃ next ρ, IsCorners Γ γ v next ρ := by
  obtain ⟨next, ρ, P, W, Q, τ, h⟩ := exists_sectors hS Γ hγ hv h2
  exact ⟨next, ρ, IsSectors.corners h⟩

/-- The half-edges of a subdrawing `N` at `x`. -/
def nHalf (N : Drawing S) (γ : Set S → I → S) (x : S) : Set (Set S × Bool) :=
  {k | k.1 ∈ N.E ∧ γ k.1 (endOf k.2) = x}

/-- Around a cycle, a colouring changes an even number of times. -/
theorem even_card_change {α : Type*} [Finite α] (p : α → α) (hp : Function.Injective p)
    (f : α → Prop) : Even (Nat.card {a // ¬ (f a ↔ f (p a))}) := by
  classical
  let fintypeIndices := Fintype.ofFinite α
  have hbij : Function.Bijective p := Finite.injective_iff_bijective.mp hp
  let e : α ≃ α := Equiv.ofBijective p hbij
  let g : α → ZMod 2 := fun a => if f a then 1 else 0
  have hsum : ∑ a, (g a + g (p a)) = 0 := by
    rw [Finset.sum_add_distrib, show ∑ a, g (p a) = ∑ a, g a from Equiv.sum_comp e g, ← two_mul]
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
  have hpt : ∀ a, g a + g (p a) = if ¬ (f a ↔ f (p a)) then 1 else 0 := by
    intro a
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    by_cases h₁ : f a <;> by_cases h₂ : f (p a) <;> simp [g, h₁, h₂, h11]
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_one] at hsum
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← ZMod.natCast_eq_zero_iff_even]
  exact hsum

/-- The ends of the parametrization of an edge lie in its closure. -/
theorem end_mem_closure {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ) {e : Set S}
    (he : e ∈ Γ.E) (b : Bool) : γ e (endOf b) ∈ closure e := by
  have h : endOf b ∈ closure (Ioo (0 : I) 1) := by
    rw [closure_Ioo (zero_ne_one' I)]
    cases b
    · simp [endOf]
    · simp [endOf]
  exact map_mem_closure (hγ.cont e he) h (t := e) fun t ht => by
    have h' : γ e t ∈ γ e '' Ioo 0 1 := ⟨t, ht, rfl⟩
    rwa [hγ.image e he] at h'

theorem end_mem_V {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ) {e : Set S}
    (he : e ∈ Γ.E) (b : Bool) : γ e (endOf b) ∈ Γ.V := by
  cases b
  · simpa [endOf] using hγ.zero e he
  · simpa [endOf] using hγ.one e he

/-- A vertex in the closure of an edge is an end of its parametrization. -/
theorem exists_end_eq [T2Space S] {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ) {e : Set S}
    (he : e ∈ Γ.E) {v : S} (hv : v ∈ Γ.V) (hve : v ∈ closure e) : ∃ b, γ e (endOf b) = v := by
  have hcl : closure e ⊆ range (γ e) := by
    refine closure_minimal ?_ (isCompact_range (hγ.cont e he)).isClosed
    intro x hx
    have h' : x ∈ γ e '' Ioo 0 1 := by rw [hγ.image e he]; exact hx
    obtain ⟨t, -, rfl⟩ := h'
    exact ⟨t, rfl⟩
  obtain ⟨t, rfl⟩ := hcl hve
  by_cases ht : t ∈ Ioo (0 : I) 1
  · have h' : γ e t ∈ γ e '' Ioo 0 1 := ⟨t, ht, rfl⟩
    rw [hγ.image e he] at h'
    exact absurd hv (he.2.1 h').2
  · by_cases h0 : t = 0
    · exact ⟨false, by simp [endOf, h0]⟩
    · have h1 : t = 1 := by
        by_contra h1
        exact ht ⟨unitInterval.pos_iff_ne_zero.mpr h0, lt_of_le_of_ne le_top h1⟩
      exact ⟨true, by simp [endOf, h1]⟩

variable [T1Space S]

omit [T1Space S] in
/-- Near a vertex with only one half-edge, the points off the drawing are joined off the drawing. -/
theorem exists_single_nbhd (hS : IsClosedSurface S) {Γ : Drawing S} {γ : Set S → I → S}
    (hγ : EdgePar Γ γ) {v : S} (k : halfEdges Γ γ v) (hk : ∀ l : halfEdges Γ γ v, l = k) :
    ∃ Z : Set S, IsOpen Z ∧ v ∈ Z ∧ ∀ x ∈ Z, x ∉ Γ.U → ∀ y ∈ Z, y ∉ Γ.U →
      ∃ A : Set S, IsPreconnected A ∧ Disjoint A Γ.U ∧ x ∈ A ∧ y ∈ A ∧ A ⊆ univ := by
  have : T2Space S := hS.2.1
  obtain ⟨⟨e, b⟩, he, hb⟩ := k
  dsimp only at he hb hk
  have hvV : v ∈ Γ.V := hb ▸ end_mem_V hγ he b
  have hve : v ∈ closure e := hb ▸ end_mem_closure hγ he b
  have hother : γ e (endOf (!b)) ≠ v := by
    intro h
    have := hk ⟨(e, !b), he, h⟩
    have h' := congrArg (fun x => x.1.2) this
    simp at h'
  have hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f := by
    intro f hf hfe hvf
    obtain ⟨c, hc⟩ := exists_end_eq hγ hf hvV hvf
    have := hk ⟨(f, c), hf, hc⟩
    exact hfe (congrArg (fun x => x.1.1) this)
  have hu : γ e (endOf (!b)) ∈ closure e := end_mem_closure hγ he _
  have huV := end_mem_V hγ he (!b)
  set u := γ e (endOf (!b)) with hudef
  have hcase : closure e ∩ Γ.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
    rcases Γ.edge_cond e he with ⟨x, y, hxy, hcap, hL⟩ | ⟨x, hcap, -⟩
    · have hu' : u ∈ ({x, y} : Set S) := hcap ▸ ⟨hu, huV⟩
      have hv' : v ∈ ({x, y} : Set S) := hcap ▸ ⟨hve, hvV⟩
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact absurd rfl hother
      · exact ⟨hcap, hL⟩
      · exact ⟨by rw [hcap, pair_comm], IsLineWithEnds.symm hL⟩
      · exact absurd rfl hother
    · have hu' : u ∈ ({x} : Set S) := hcap ▸ ⟨hu, huV⟩
      have hv' : v ∈ ({x} : Set S) := hcap ▸ ⟨hve, hvV⟩
      exact absurd ((mem_singleton_iff.mp hu').trans (mem_singleton_iff.mp hv').symm) hother
  exact exists_leaf_nbhd hS Γ he hother hcase.1 hcase.2 hleaf isOpen_univ (mem_univ _)

/-- At a vertex with only one half-edge, that edge is not in `N(Z)`: only one region is present. -/
theorem notMem_boundary_of_single (hS : IsClosedSurface S)
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    (k : halfEdges Γ γ v) (hk : ∀ l : halfEdges Γ γ v, l = k) (Z : Set (Set S)) :
    k.1.1 ∉ (boundaryDrawing Γ Z).E := by
  have : T2Space S := hS.2.1
  intro hN
  obtain ⟨Z₀, hZ₀, hvZ, hsame⟩ := exists_single_nbhd hS hγ k hk
  obtain ⟨⟨e, b⟩, he, hb⟩ := k
  dsimp only at he hb hN hk
  have hve : v ∈ closure e := hb ▸ end_mem_closure hγ he b
  obtain ⟨⟨r₁, hr₁, -, hr₁R, hi₁⟩, r₂, ⟨hr₂R, hr₂⟩, -, -, hi₂⟩ := mem_boundaryDrawing_E.mp hN
  have hc₁ := edge_subset_closure_of_incident hS he hr₁R hi₁
  have hc₂ := edge_subset_closure_of_incident hS he hr₂R hi₂
  have hvc₁ : v ∈ closure r₁ := closure_minimal hc₁ isClosed_closure hve
  have hvc₂ : v ∈ closure r₂ := closure_minimal hc₂ isClosed_closure hve
  obtain ⟨x, hxZ, hx⟩ := mem_closure_iff.mp hvc₁ Z₀ hZ₀ hvZ
  obtain ⟨y, hyZ, hy⟩ := mem_closure_iff.mp hvc₂ Z₀ hZ₀ hvZ
  obtain ⟨A, hA, hdis, hxA, hyA⟩ := hsame x hxZ (region_subset hr₁R hx) y hyZ
    (region_subset hr₂R hy)
  have := subset_region hr₁R hA hdis hxA hx hyA.1
  exact hr₂ (region_eq_of_mem hr₂R hr₁R hy this ▸ hr₁)

/-- "every vertex of $N(Z_1)$ has even valency" (Graph Minors XI, proof of (5.4), page 83), for any
set `Z` of regions, where a loop counts twice. -/
theorem even_nHalf (hS : IsClosedSurface S)
    (Γ : Drawing S) {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (Z : Set (Set S)) : Even (nHalf (boundaryDrawing Γ Z) γ v).ncard := by
  classical
  have : T2Space S := hS.2.1
  have hsubE : (boundaryDrawing Γ Z).E ⊆ Γ.E := (boundaryDrawing Γ Z |> fun _ =>
    (Γ.span_isSubdrawing _ _).2)
  have hfin : Finite (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).to_subtype
  have : Fintype (halfEdges Γ γ v) := Fintype.ofFinite _
  -- The set as an image of a subset of the half-edges at `v`.
  have himg : nHalf (boundaryDrawing Γ Z) γ v =
      Subtype.val '' {k : halfEdges Γ γ v | k.1.1 ∈ (boundaryDrawing Γ Z).E} := by
    ext k
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨k, hsubE h₁, h₂⟩, h₁, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨hl, l.2.2⟩
  rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ v)
  · obtain ⟨next, ρ, hC⟩ := exists_corners hS Γ hγ hv h2
    have hbij : Function.Bijective next := Finite.injective_iff_bijective.mp hC.inj
    have hiff : ∀ k, (next k).1.1 ∈ (boundaryDrawing Γ Z).E ↔ ¬ (ρ k ∈ Z ↔ ρ (next k) ∈ Z) := by
      intro k
      have hE := (next k).2.1
      have hinc : ∀ r ∈ Γ.R, Γ.EdgeRegionIncident (next k).1.1 r → r = ρ k ∨ r = ρ (next k) :=
        fun r hr hi => hC.sides k r hr (edge_subset_closure_of_incident hS hE hr hi.2.2)
      have hne : ∀ l, (next k).1.1 ⊆ closure (ρ l) → Γ.EdgeRegionIncident (next k).1.1 (ρ l) := by
        intro l hl
        obtain ⟨p, hp⟩ := (show (next k).1.1 ∈ Γ.E from hE).1
        exact ⟨hE, hC.region l, p, hp, hl hp⟩
      constructor
      · intro h
        obtain ⟨⟨r₁, hr₁, hi₁⟩, r₂, ⟨hr₂R, hr₂⟩, hi₂⟩ := mem_boundaryDrawing_E.mp h
        rcases hinc r₁ hi₁.2.1 hi₁ with rfl | rfl <;> rcases hinc r₂ hr₂R hi₂ with rfl | rfl
        · exact absurd hr₁ hr₂
        · tauto
        · tauto
        · exact absurd hr₁ hr₂
      · intro h
        by_cases h₁ : ρ k ∈ Z
        · have h₂ : ρ (next k) ∉ Z := fun h₂ => h (iff_of_true h₁ h₂)
          exact mem_boundaryDrawing_E.mpr ⟨⟨_, h₁, hne k (hC.left k)⟩, _, ⟨hC.region _, h₂⟩,
            hne _ (hC.right k)⟩
        · have h₂ : ρ (next k) ∈ Z := by
            by_contra h₂
            exact h (iff_of_false h₁ h₂)
          exact mem_boundaryDrawing_E.mpr ⟨⟨_, h₂, hne _ (hC.right k)⟩, _, ⟨hC.region _, h₁⟩,
            hne k (hC.left k)⟩
    have hcard := even_card_change next hC.inj fun k => ρ k ∈ Z
    have heq : ({k : halfEdges Γ γ v | k.1.1 ∈ (boundaryDrawing Γ Z).E}).ncard =
        Nat.card {a // ¬ (ρ a ∈ Z ↔ ρ (next a) ∈ Z)} := by
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective next hbij).symm ?_)
      intro k
      obtain ⟨j, rfl⟩ := hbij.2 k
      have : (Equiv.ofBijective next hbij).symm (next j) = j :=
        (Equiv.ofBijective next hbij).symm_apply_apply j
      rw [this]
      exact hiff j
    rw [heq]
    exact hcard
  · have hle : Nat.card (halfEdges Γ γ v) ≤ 1 := by omega
    have hsub : Subsingleton (halfEdges Γ γ v) := by
      rw [Nat.card_eq_fintype_card] at hle
      exact Fintype.card_le_one_iff_subsingleton.mp hle
    have : {k : halfEdges Γ γ v | k.1.1 ∈ (boundaryDrawing Γ Z).E} = ∅ := by
      ext k
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact notMem_boundary_of_single hS hγ k (fun l => Subsingleton.elim l k) Z
    rw [this]
    simp

end GraphMinor.GM11
