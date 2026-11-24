/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite codes of edges

Several proofs of Graph Minors XX, Section 4 say that some finite set of data is "evidently" a
well-quasi-order: an edge whose ends lie on a march of bounded length has only finitely many shapes.
This file makes that precise. Given a march `r` of length `k`, the data of an edge with ends on `r`,
namely its march `m` and its patch `Δ`, is recorded through positions in `r`, as a member of a
finite
type (`marchCode`, `patchCode`). If two edges have the same code, the bijection `m → m'` maps `Δ` to
`Δ'` (`mapsTo_of_code`).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM04

universe u

variable {α : Type u}

/-- The positions in `r`, below `k`, of members of `X`. -/
def indexSet (k : ℕ) (r : List α) (X : Set α) : Set (Fin k) :=
  {i | ∃ x ∈ X, r[i.1]? = some x}

/-- The pairs `(p, i)` such that the `p`th term of `m` is the `i`th term of `r`. -/
def marchCode (k : ℕ) (r m : List α) : Set (Fin k × Fin k) :=
  {c | ∃ x, m[c.1.1]? = some x ∧ r[c.2.1]? = some x}

/-- The code of a grouping: its vertices and adjacent pairs, as positions in `r`. -/
def groupingCode (k : ℕ) (r : List α) (δ : (⊤ : SimpleGraph α).Subgraph) :
    Set (Fin k) × Set (Fin k × Fin k) :=
  (indexSet k r δ.verts, {c | ∃ x y, r[c.1.1]? = some x ∧ r[c.2.1]? = some y ∧ δ.Adj x y})

/-- The code of a patch: the codes of its groupings. -/
def patchCode (k : ℕ) (r : List α) (Δ : Patch α) : Set (Set (Fin k) × Set (Fin k × Fin k)) :=
  groupingCode k r '' Δ.groupings

/-- The type of codes of edges, which is finite. -/
abbrev EdgeCode (k : ℕ) : Type :=
  Prop × Set (Fin k) × Set (Fin k × Fin k) × Set (Set (Fin k) × Set (Fin k × Fin k))

open Classical in
instance (k : ℕ) : Finite (EdgeCode k) := inferInstance

/-- The code of an edge of a patchwork with respect to a march `r`: whether it lies in `dom(μ)`, and
the positions on `r` of its ends, its march and its patch. -/
def edgeCode {Ω β : Type*} (k : ℕ) (r : List α) (P : Patchwork Ω α β) (e : β) : EdgeCode k :=
  (e ∈ P.dom, indexSet k r (P.G.ends e), marchCode k r (P.μ e), patchCode k r (P.Δ e))

theorem exists_index {r : List α} {k : ℕ} (hk : r.length ≤ k) {x : α} (hx : x ∈ r) :
    ∃ i : Fin k, r[i.1]? = some x := by
  obtain ⟨i, hi, h⟩ := List.getElem_of_mem hx
  exact ⟨⟨i, hi.trans_le hk⟩, List.getElem?_eq_some_iff.mpr ⟨hi, h⟩⟩

theorem marchCorresponds_of_getElem? {m m' : List α} {p : ℕ} {x y : α} (h : m[p]? = some x)
    (h' : m'[p]? = some y) : MarchCorresponds m m' x y := by
  obtain ⟨h₁, h₂⟩ := List.getElem?_eq_some_iff.mp h
  obtain ⟨h₁', h₂'⟩ := List.getElem?_eq_some_iff.mp h'
  exact ⟨p, h₁, h₁', h₂, h₂'⟩

theorem getElem?_of_marchCorresponds {m m' : List α} {x y : α} (h : MarchCorresponds m m' x y) :
    ∃ p : ℕ, m[p]? = some x ∧ m'[p]? = some y := by
  obtain ⟨p, h₁, h₁', h₂, h₂'⟩ := h
  exact ⟨p, List.getElem?_eq_some_iff.mpr ⟨h₁, h₂⟩, List.getElem?_eq_some_iff.mpr ⟨h₁', h₂'⟩⟩

/-- Under equal march codes, a term of `m` at position `p` and of `r` at position `i` gives a common
term of `m'` at `p` and `r'` at `i`. -/
theorem marchCode_forward {k : ℕ} {r r' m m' : List α} (hc : marchCode k r m = marchCode k r' m')
    {x : α} {i : Fin k} {p : ℕ} (hk : m.length ≤ k) (hm : m[p]? = some x)
    (hi : r[i.1]? = some x) : ∃ y, m'[p]? = some y ∧ r'[i.1]? = some y := by
  have hp : p < k := (List.getElem?_eq_some_iff.mp hm).1.trans_le hk
  have : ((⟨p, hp⟩, i) : Fin k × Fin k) ∈ marchCode k r m := ⟨x, hm, hi⟩
  rw [hc] at this
  exact this

/-- A nodup march with all terms in `r` is no longer than `r`. -/
theorem length_le_of_subset {r m : List α} (hm : m.Nodup) (h : ∀ x ∈ m, x ∈ r) :
    m.length ≤ r.length :=
  (hm.subperm h).length_le

/-- Two marches with equal codes, each with terms on its `r`, have the same length. -/
theorem length_eq_of_code {k : ℕ} {r r' m m' : List α} (hr : r.length ≤ k) (hr' : r'.length ≤ k)
    (hm : m.Nodup) (hm' : m'.Nodup) (hs : ∀ x ∈ m, x ∈ r) (hs' : ∀ x ∈ m', x ∈ r')
    (hc : marchCode k r m = marchCode k r' m') : m.length = m'.length := by
  have key : ∀ {r r' m m' : List α}, r.length ≤ k → m.Nodup → (∀ x ∈ m, x ∈ r) →
      marchCode k r m = marchCode k r' m' → m.length ≤ m'.length := by
    intro r r' m m' hr hm hs hc
    by_contra hlt
    push Not at hlt
    have hp : m'.length < m.length := hlt
    have hx := List.getElem_mem hp
    obtain ⟨i, hi⟩ := exists_index hr (hs _ hx)
    have hle : m.length ≤ k := (length_le_of_subset hm hs).trans hr
    obtain ⟨y, hy, -⟩ := marchCode_forward hc hle (List.getElem?_eq_getElem hp) hi
    have := (List.getElem?_eq_some_iff.mp hy).1
    omega
  exact le_antisymm (key hr hm hs hc) (key hr' hm' hs' hc.symm)

/-- If an edge with march `m` and patch `Δ` and an edge with march `m'` and patch `Δ'`, both with
all
ends on marches of length `k`, have the same codes, then `m → m'` maps `Δ` to `Δ'`. -/
theorem mapsTo_of_code {k : ℕ} {r r' m m' : List α} {Δ Δ' : Patch α} (hr : r.length ≤ k)
    (hr' : r'.length ≤ k) (hm : m.Nodup) (hm' : m'.Nodup) (hs : ∀ x ∈ m, x ∈ r)
    (hs' : ∀ x ∈ m', x ∈ r') (hV : Δ.verts = {x | x ∈ m}) (hV' : Δ'.verts = {x | x ∈ m'})
    (hc : marchCode k r m = marchCode k r' m') (hpc : patchCode k r Δ = patchCode k r' Δ') :
    MapsTo (marchMapSubgraph m m') Δ.groupings Δ'.groupings := by
  intro δ hδ
  have hmem : groupingCode k r δ ∈ patchCode k r' Δ' := hpc ▸ mem_image_of_mem _ hδ
  obtain ⟨δ', hδ', hcode⟩ := hmem
  have hle : m.length ≤ k := (length_le_of_subset hm hs).trans hr
  have hle' : m'.length ≤ k := (length_le_of_subset hm' hs').trans hr'
  have hvδ : δ.verts = {x | x ∈ m} := (Δ.verts_eq δ hδ).trans hV
  have hvδ' : δ'.verts = {x | x ∈ m'} := (Δ'.verts_eq δ' hδ').trans hV'
  have hvm : ∀ {x}, x ∈ δ.verts → x ∈ m := fun {x} hx ↦ by
    rw [hvδ] at hx
    exact hx
  have hvm' : ∀ {x}, x ∈ δ'.verts → x ∈ m' := fun {x} hx ↦ by
    rw [hvδ'] at hx
    exact hx
  have hI : indexSet k r' δ'.verts = indexSet k r δ.verts := congrArg Prod.fst hcode
  have hA : ∀ c : Fin k × Fin k, (∃ x y, r'[c.1.1]? = some x ∧ r'[c.2.1]? = some y ∧ δ'.Adj x y) ↔
      ∃ x y, r[c.1.1]? = some x ∧ r[c.2.1]? = some y ∧ δ.Adj x y := fun c ↦
    Set.ext_iff.mp (congrArg Prod.snd hcode) c
  -- A corresponding pair `x, y` sits at a common position of `r` and `r'`.
  have fwd : ∀ {x y}, x ∈ δ.verts → MarchCorresponds m m' x y →
      ∃ i : Fin k, r[i.1]? = some x ∧ r'[i.1]? = some y := by
    intro x y hx hxy
    obtain ⟨p, h₁, h₂⟩ := getElem?_of_marchCorresponds hxy
    obtain ⟨i, hi⟩ := exists_index hr (hs x (hvm hx))
    obtain ⟨y', h₃, h₄⟩ := marchCode_forward hc hle h₁ hi
    have : y' = y := by rw [h₂] at h₃; exact (Option.some.inj h₃).symm
    exact ⟨i, hi, this ▸ h₄⟩
  have bwd : ∀ {y}, y ∈ δ'.verts → ∃ x ∈ δ.verts, MarchCorresponds m m' x y ∧
      ∃ i : Fin k, r[i.1]? = some x ∧ r'[i.1]? = some y := by
    intro y hy
    obtain ⟨i, hi⟩ := exists_index hr' (hs' y (hvm' hy))
    have hmem : i ∈ indexSet k r δ.verts := hI ▸ (⟨y, hy, hi⟩ : i ∈ indexSet k r' δ'.verts)
    obtain ⟨x, hx, hxi⟩ := hmem
    have hxm : x ∈ m := hvm hx
    obtain ⟨p, hp, hpx⟩ := List.getElem_of_mem hxm
    have hpx' : m[p]? = some x := List.getElem?_eq_some_iff.mpr ⟨hp, hpx⟩
    obtain ⟨y', h₃, h₄⟩ := marchCode_forward hc hle hpx' hxi
    have : y' = y := by rw [hi] at h₄; exact (Option.some.inj h₄).symm
    exact ⟨x, hx, marchCorresponds_of_getElem? hpx' (this ▸ h₃), i, hxi, hi⟩
  suffices marchMapSubgraph m m' δ = δ' from this ▸ hδ'
  apply SimpleGraph.Subgraph.ext
  · ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨i, hi, hi'⟩ := fwd hx hxy
      have hmem : i ∈ indexSet k r' δ'.verts := hI ▸ (⟨x, hx, hi⟩ : i ∈ indexSet k r δ.verts)
      obtain ⟨y', hy', hyi⟩ := hmem
      have : y' = y := by rw [hi'] at hyi; exact (Option.some.inj hyi).symm
      exact this ▸ hy'
    · intro hy
      obtain ⟨x, hx, hxy, -⟩ := bwd hy
      exact ⟨x, hx, hxy⟩
  · funext y₁ y₂
    apply propext
    constructor
    · rintro ⟨-, x₁, x₂, h₁, h₂, hadj⟩
      obtain ⟨i₁, hi₁, hi₁'⟩ := fwd (δ.edge_vert hadj) h₁
      obtain ⟨i₂, hi₂, hi₂'⟩ := fwd (δ.edge_vert hadj.symm) h₂
      obtain ⟨u, v, hu, hv, huv⟩ := (hA (i₁, i₂)).mpr ⟨x₁, x₂, hi₁, hi₂, hadj⟩
      have e₁ : u = y₁ := by rw [hi₁'] at hu; exact (Option.some.inj hu).symm
      have e₂ : v = y₂ := by rw [hi₂'] at hv; exact (Option.some.inj hv).symm
      exact e₁ ▸ e₂ ▸ huv
    · intro hadj
      obtain ⟨x₁, -, h₁, i₁, hi₁, hi₁'⟩ := bwd (δ'.edge_vert hadj)
      obtain ⟨x₂, -, h₂, i₂, hi₂, hi₂'⟩ := bwd (δ'.edge_vert hadj.symm)
      obtain ⟨u, v, hu, hv, huv⟩ := (hA (i₁, i₂)).mp ⟨y₁, y₂, hi₁', hi₂', hadj⟩
      have e₁ : u = x₁ := by rw [hi₁] at hu; exact (Option.some.inj hu).symm
      have e₂ : v = x₂ := by rw [hi₂] at hv; exact (Option.some.inj hv).symm
      exact ⟨hadj.ne, x₁, x₂, h₁, h₂, e₁ ▸ e₂ ▸ huv⟩

end GraphMinor.GM20
