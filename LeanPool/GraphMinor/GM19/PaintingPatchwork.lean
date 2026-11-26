/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section4b
public import LeanPool.GraphMinor.GM19.Section9a
public import LeanPool.GraphMinor.GM18.Section6
public import Mathlib.Data.Nat.Nth

import LeanPool.GraphMinor.GM04.Patchwork.Menger

/-!
# A painting as a patchwork

Graph Minors XIX, Section 9, regards a painting as a patchwork by giving each edge `e` the free
patch on `eTilde`. This file sets that up. A simulation of one such patchwork in another gives an
inflation of paintings.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface
open GraphMinor.GM04 (Patchwork freePatch IsGrouping IsComponent)

universe u w

variable {S : Type u} [TopologicalSpace S] {α : Type w}

namespace QuasiOrder

/-- A sequence with infinitely many terms in a well-quasi-order has two of them in order. -/
theorem IsWQO.exists_pair {Ω : QuasiOrder α} (h : Ω.IsWQO) {f : ℕ → α} {I : Set ℕ}
    (hI : I.Infinite) (hf : ∀ i ∈ I, f i ∈ Ω.E) :
    ∃ i ∈ I, ∃ j ∈ I, i < j ∧ Ω.le (f i) (f j) := by
  classical
  obtain ⟨a, b, hab, hle⟩ := h (fun n ↦ f (Nat.nth (· ∈ I) n))
    fun n ↦ hf _ (Nat.nth_mem_of_infinite hI n)
  exact ⟨_, Nat.nth_mem_of_infinite hI a, _, Nat.nth_mem_of_infinite hI b,
    Nat.nth_strictMono hI hab, hle⟩

end QuasiOrder

namespace ColourScheme

variable {χ : ColourScheme S α}

/-- A finite union of well-quasi-orders with disjoint element sets is a well-quasi-order. -/
theorem isWQO_unionWQO (hd : χ.IsDisjoint) : (χ.unionWQO hd).IsWQO := by
  intro f hf
  let I₂ : Set ℕ := {i | f i ∈ χ.Ω2.E}
  let I₃ : Set ℕ := {i | f i ∈ χ.Ω3.E}
  let IS : Set S → Set ℕ := fun s ↦ {i | f i ∈ (χ.ΩS s).E}
  have hcover : (univ : Set ℕ) = I₂ ∪ I₃ ∪ ⋃ s ∈ χ.Φ.sides, IS s := by
    ext i
    simp only [mem_univ, true_iff]
    rcases hf i with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · refine Or.inr ?_
      obtain ⟨s, hs, his⟩ := mem_iUnion₂.mp h
      exact mem_iUnion₂.mpr ⟨s, hs, his⟩
  have hinf : (I₂ ∪ I₃ ∪ ⋃ s ∈ χ.Φ.sides, IS s).Infinite := hcover ▸ infinite_univ
  rcases infinite_union.mp hinf with h | h
  · rcases infinite_union.mp h with h | h
    · obtain ⟨i, hi, j, hj, hij, hle⟩ := χ.isWQO_2.exists_pair h fun _ hi ↦ hi
      exact ⟨i, j, hij, Or.inl ⟨hi, hj, hle⟩⟩
    · obtain ⟨i, hi, j, hj, hij, hle⟩ := χ.isWQO_3.exists_pair h fun _ hi ↦ hi
      exact ⟨i, j, hij, Or.inr (Or.inl ⟨hi, hj, hle⟩)⟩
  · have hfin : χ.Φ.sides.Finite := χ.Φ.finite_sides
    by_contra hno
    refine h (hfin.biUnion fun s hs ↦ ?_)
    by_contra hs'
    obtain ⟨i, hi, j, hj, hij, hle⟩ := (χ.isWQO_S s hs).exists_pair hs' fun _ hi ↦ hi
    exact hno ⟨i, j, hij, Or.inr (Or.inr ⟨s, hs, hi, hj, hle⟩)⟩

/-- The element set of `Ω_χ`, as a type. -/
def Colour (hd : χ.IsDisjoint) : Type w := {x : α // x ∈ (χ.unionWQO hd).E}

instance (hd : χ.IsDisjoint) : Preorder (Colour hd) where
  le a b := (χ.unionWQO hd).le a.1 b.1
  le_refl a := (χ.unionWQO hd).refl a.1 a.2
  le_trans a b c h₁ h₂ := (χ.unionWQO hd).trans a.1 a.2 b.1 b.2 c.1 c.2 h₁ h₂

instance (hd : χ.IsDisjoint) : WellQuasiOrderedLE (Colour hd) :=
  ⟨fun f ↦ isWQO_unionWQO hd (fun n ↦ (f n).1) fun n ↦ (f n).2⟩

end ColourScheme

open ColourScheme

namespace ColouredPainting

variable {χ : ColourScheme S α}

theorem φ_mem (hd : χ.IsDisjoint) (P : ColouredPainting χ) {e : Set S} (he : e ∈ P.Γ.E) :
    P.φ e ∈ (χ.unionWQO hd).E := by
  rcases P.cases he with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, s, hs, -, h⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (mem_iUnion₂.mpr ⟨s, hs, h⟩)

open Classical in
/-- The colour of an edge, as an element of `Ω_χ`. -/
noncomputable def colour (hd : χ.IsDisjoint) (P : ColouredPainting χ) (e : Set S) : Colour hd :=
  if h : e ∈ P.Γ.E then ⟨P.φ e, P.φ_mem hd h⟩
  else ⟨P.φ P.fits.internally_three_connected.1.some,
    P.φ_mem hd P.fits.internally_three_connected.1.some_mem⟩

theorem colour_val (hd : χ.IsDisjoint) (P : ColouredPainting χ) {e : Set S} (he : e ∈ P.Γ.E) :
    (P.colour hd e).1 = P.φ e := by
  simp [colour, he]

end ColouredPainting

theorem Painting.ends_eq (Γ : Painting S) {e : Set S} (he : e ∈ Γ.E) :
    Γ.toHypergraph.ends e = tilde e := by
  ext v
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨he, Γ.tilde_subset_V he h, h⟩⟩

variable {χ : ColourScheme S α}

/-- A coloured painting as a patchwork: the free patch on `eTilde` for each edge `e`, and the march
`γ(e)` as `μ(e)`. -/
noncomputable def ColouredPainting.toPatchwork (hd : χ.IsDisjoint) (P : ColouredPainting χ) :
    Patchwork (Colour hd) S (Set S) where
  G := P.Γ.toHypergraph.toRooted
  dom := P.Γ.E
  μ := P.Γ.γ
  Δ e := freePatch (P.Γ.toHypergraph.ends e)
  φ := P.colour hd
  dom_subset := Subset.rfl
  μ_nodup e he := P.Γ.γ_nodup e he
  μ_set e he := (P.Γ.γ_set e he).trans (P.Γ.ends_eq he).symm
  Δ_verts _ _ := rfl
  Δ_free _ _ _ := GM04.freePatch_isFree _

omit [TopologicalSpace S] in
/-- The free patch on a finite set is robust. -/
theorem freePatch_isRobust {U : Set S} (hU : U.Finite) : (freePatch U).IsRobust :=
  GM04.Patch.IsFree.isRobust hU (GM04.freePatch_isFree U)

theorem ColouredPainting.toPatchwork_isRobust (hd : χ.IsDisjoint) (P : ColouredPainting χ) :
    (P.toPatchwork hd).IsRobust := fun _e he ↦
  freePatch_isRobust ((P.Γ.ends_eq he) ▸ P.Γ.finite_V.subset (P.Γ.tilde_subset_V he))

omit [TopologicalSpace S] in
/-- A component of a subgraph whose edges all lie in `G` induces a connected subgraph of `G`. -/
theorem preconnected_of_isComponent {H D : (⊤ : SimpleGraph S).Subgraph} {G : SimpleGraph S}
    (hadj : ∀ u v, H.Adj u v → G.Adj u v) (hD : IsComponent H D) :
    (G.induce D.verts).Preconnected := by
  obtain ⟨x, rfl⟩ := hD
  have key : ∀ (a b : H.verts) (w : H.coe.Walk a b)
      (ha : (a : S) ∈ GM04.componentVerts H x) (hb : (b : S) ∈ GM04.componentVerts H x),
      (G.induce (GM04.componentVerts H x)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b w
    induction w with
    | nil => exact fun _ _ ↦ SimpleGraph.Reachable.refl _
    | @cons a c b hac _ ih =>
      intro ha hb
      have hc : (c : S) ∈ GM04.componentVerts H x := by
        obtain ⟨h₁, h₂⟩ := ha
        exact ⟨c.2, h₂.trans (SimpleGraph.Adj.reachable hac)⟩
      have hstep : (G.induce (GM04.componentVerts H x)).Adj ⟨a, ha⟩ ⟨c, hc⟩ :=
        hadj _ _ hac
      exact hstep.reachable.trans (ih hc hb)
  have hx := GM04.self_mem_componentVerts H x
  intro u v
  obtain ⟨hu, hru⟩ := u.2
  obtain ⟨hv, hrv⟩ := v.2
  obtain ⟨wu⟩ := hru
  obtain ⟨wv⟩ := hrv
  exact (key _ _ wu hx u.2).symm.trans (key _ _ wv hx v.2)

/-- A simulation of one painting patchwork in another is an inflation. -/
theorem inflation_of_simulated (hd : χ.IsDisjoint) {P P' : ColouredPainting χ}
    (h : GM04.Simulated (P.toPatchwork hd) (P'.toPatchwork hd)) :
    ∃ σv σe, IsColouredInflation χ P P' σv σe := by
  obtain ⟨ηv, ηe, hexp, H, ⟨δ, hδ, hH⟩, hcomp⟩ := h
  have hadj : ∀ u v, H.Adj u v → P'.Γ.skAdj.Adj u v := by
    intro u v huv
    rw [hH] at huv
    obtain ⟨e, he, hAdj⟩ := GM04.realizationOf_adj.mp huv
    have heE : e ∈ P'.Γ.E := he.1
    have hm := (hδ e he).2
    have hu : u ∈ (δ e).verts := (δ e).edge_vert hAdj
    have hv : v ∈ (δ e).verts := (δ e).edge_vert hAdj.symm
    rw [hm] at hu hv
    have hu' : u ∈ P'.Γ.toHypergraph.ends e := hu
    have hv' : v ∈ P'.Γ.toHypergraph.ends e := hv
    exact ⟨hAdj.ne, hu'.2.1, hv'.2.1, e, heE, hu'.2.2, hv'.2.2⟩
  refine ⟨ηv, ηe, theorem_9_1_proof hd P P' ⟨hexp.edge_mem, fun e he ↦ ?_, hexp.edge_injOn,
    hexp.vertex_nonempty, hexp.vertex_subset, fun v hv ↦ ?_, hexp.vertex_disjoint,
    fun e he i hi hi' ↦ hexp.μ_mem e he i hi hi'⟩ fun e he ↦ ?_⟩
  · rw [← P'.Γ.length_γ (hexp.edge_mem e he), ← P.Γ.length_γ he]
    exact (hexp.μ_length e he).symm
  · obtain ⟨D, hD, hDv⟩ := hcomp v hv
    rw [← hDv]
    exact preconnected_of_isComponent hadj hD
  · have : (χ.unionWQO hd).le (P.colour hd e).1 (P'.colour hd (ηe e)).1 := hexp.φ_le e he
    rwa [P.colour_val hd he, P'.colour_val hd (hexp.edge_mem e he)] at this

end GraphMinor.GM19
