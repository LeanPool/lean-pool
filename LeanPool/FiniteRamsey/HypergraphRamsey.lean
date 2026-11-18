/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FinCases

/-!
# Hypergraph Ramsey numbers

This file develops the two-colour Ramsey theory of `k`-uniform hypergraphs (see
`Mathlib.Combinatorics.Hypergraph.Basic`), hypergraphs in which every hyperedge has exactly `k`
vertices, generalising the classical (`k = 2`, ordinary graph) Ramsey arrow relation to hyperedges
of arbitrary fixed size `k`.

Given a `k`-uniform hypergraph `H`, a `Color`-valued colouring of `H`'s hyperedges, and a target
colour, a monochromatic `k`-uniform clique is a vertex subset all of whose `k`-element subsets are
hyperedges of that colour. The two-colour Ramsey arrow `Hypergraph.RamseyProperty n k r s` asserts
that every red/blue colouring of the `k`-element subsets of an `n`-vertex set contains a red
`r`-clique or a blue `s`-clique; `Hypergraph.ramseyNumber` is the least such `n`, given that some
such `n` exists.

## Main declarations

* `Hypergraph.IsKUniform`: every hyperedge of a hypergraph has exactly `k` vertices.
* `Hypergraph.completeKUniform n k`: the complete `k`-uniform hypergraph on `n` vertices, where
  every `k`-element subset of `Fin n` is a hyperedge.
* `Hypergraph.EdgeColoring`: a colouring of a hypergraph's hyperedges by a colour type.
* `Hypergraph.EdgeColoring.MonochromaticClique`, `Hypergraph.EdgeColoring.HasMonochromaticClique`:
  monochromatic `k`-uniform cliques, and their existence at a given size.
* `Hypergraph.EdgeColoring.relabel`, `Hypergraph.EdgeColoring.hasMonochromaticClique_relabel_iff`:
  relabelling a complete `k`-uniform host's vertices along a permutation, and the invariance of
  monochromatic-clique existence under it.
* `Hypergraph.Arrow n k sizes`: every colouring of the `k`-subsets of an `n`-set by a colour type
  `ι` has, for some colour `c`, a `c`-monochromatic clique of size `sizes c`.
* `Hypergraph.ramseyNumber k sizes`: the least such `n` (defined by `sInf`).
* `Hypergraph.RamseyProperty`: the two-colour special case, related to the general one by
  `ramseyProperty_iff_arrow` and `ramseyProperty_iff_arrow_finTwo`.

## Implementation notes

The arrow `Hypergraph.Arrow` and the number `Hypergraph.ramseyNumber` are stated for an arbitrary
colour type with a target size per colour, matching `SimpleGraph.ramseyNumber`; the two-colour
`RamseyProperty` (colours `true`/`false`) is a convenient special case. Existence for general `k`
(the hypergraph Ramsey theorem) is proved by a stepping-up induction not developed in this file,
so `ramseyNumber` is defined with `sInf` and the lemmas that need its true value take an existence
hypothesis. The diagonal case at the end shows existence in the one situation where it is
immediate.

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2) 30 (1930), 264-286.
  (Ramsey's theorem is proved for `k`-element subsets of arbitrary fixed `k`, i.e. for hypergraphs
  of arbitrary fixed uniformity, not just graphs.)

## Tags

ramsey theory, hypergraph, combinatorics
-/

@[expose] public section

namespace Hypergraph

universe u v

open Set

variable {α : Type u}

/-! ### `k`-uniformity and the complete `k`-uniform host -/

/-- A hypergraph `H` is `k`-uniform when every hyperedge has exactly `k` vertices. -/
def IsKUniform (H : Hypergraph α) (k : ℕ) : Prop :=
  ∀ e ∈ E(H), e.ncard = k

/-- The complete `k`-uniform hypergraph on `Fin n`: every `k`-element subset of `Fin n` is a
hyperedge. -/
def completeKUniform (n k : ℕ) : Hypergraph (Fin n) where
  vertexSet := Set.univ
  edgeSet := {e : Set (Fin n) | e.ncard = k}
  subset_vertexSet_of_mem_edgeSet' := fun e _ => Set.subset_univ e

/-- Membership in the complete `k`-uniform hypergraph's edge set is exactly `k`-element-ness. -/
@[simp]
theorem mem_completeKUniform_edgeSet {n k : ℕ} {e : Set (Fin n)} :
    e ∈ E(completeKUniform n k) ↔ e.ncard = k :=
  Iff.rfl

theorem completeKUniform_isKUniform (n k : ℕ) : IsKUniform (completeKUniform n k) k :=
  fun _ he => he

/-! ### Hyperedge colourings and monochromatic cliques -/

/-- A colouring of a hypergraph `H`'s hyperedges by a colour type `Color`. Since a hyperedge is
already `Set α` (no `Sym2` unordered-pair wrapping needed, unlike a graph edge), this is a plain
function on `H`'s edge-membership subtype. -/
def EdgeColoring (H : Hypergraph α) (Color : Type v) : Type (max u v) :=
  {e // e ∈ E(H)} → Color

namespace EdgeColoring

variable {H : Hypergraph α} {Color : Type v}

/-- The sub-collection of `H`'s hyperedges assigned a given colour under `C`. -/
def colorEdges (C : H.EdgeColoring Color) (color : Color) : Set (Set α) :=
  {e | ∃ he : e ∈ E(H), C ⟨e, he⟩ = color}

@[simp]
theorem mem_colorEdges_iff {C : H.EdgeColoring Color} {color : Color} {e : Set α} :
    e ∈ colorEdges C color ↔ ∃ he : e ∈ E(H), C ⟨e, he⟩ = color :=
  Iff.rfl

/-- `S` is a monochromatic `k`-uniform clique of colour `color`: a vertex subset of `H` all of
whose `k`-element subsets are hyperedges of `H` coloured `color`. Vacuously true whenever
`S.card < k`, since there are then no `k`-subsets to check. -/
def MonochromaticClique (C : H.EdgeColoring Color) (color : Color) (k : ℕ) (S : Finset α) : Prop :=
  (↑S : Set α) ⊆ V(H) ∧ ∀ e ∈ S.powersetCard k, (↑e : Set α) ∈ colorEdges C color

/-- Some size-`s` vertex subset is a monochromatic `k`-uniform clique of colour `color`. -/
def HasMonochromaticClique (C : H.EdgeColoring Color) (color : Color) (k s : ℕ) : Prop :=
  ∃ S : Finset α, S.card = s ∧ MonochromaticClique C color k S

/-- A monochromatic clique restricts to one on any subset of its vertices: the subset's
`k`-subsets are among the original clique's `k`-subsets. -/
theorem monochromaticClique_mono_subset {C : H.EdgeColoring Color} {color : Color} {k : ℕ}
    {S S' : Finset α} (hsub : S ⊆ S') (h : MonochromaticClique C color k S') :
    MonochromaticClique C color k S :=
  ⟨(Finset.coe_subset.mpr hsub).trans h.1, fun e he => h.2 e (Finset.powersetCard_mono hsub he)⟩

/-- Antitonicity of `HasMonochromaticClique` in the requested clique size: a colouring that has a
monochromatic clique of some size has one of any smaller size too. -/
theorem hasMonochromaticClique_mono_size {C : H.EdgeColoring Color} {color : Color} {k m n : ℕ}
    (hmn : m ≤ n) (h : HasMonochromaticClique C color k n) :
    HasMonochromaticClique C color k m :=
  let ⟨S, hcard, hmono⟩ := h
  let ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (hcard ▸ hmn : m ≤ S.card)
  ⟨T, hTcard, monochromaticClique_mono_subset hTS hmono⟩

end EdgeColoring

/-! ### Relabelling invariance -/

section Relabel

variable {n k : ℕ} {Color : Type v}

/-- The colouring induced by relabelling vertices of `completeKUniform n k` along a permutation
`σ`: a hyperedge `e` gets the colour `C` assigns to `σ`'s image of `e`. -/
def EdgeColoring.relabel (C : (completeKUniform n k).EdgeColoring Color)
    (σ : Equiv.Perm (Fin n)) : (completeKUniform n k).EdgeColoring Color :=
  fun e => C ⟨σ '' e.1, (Set.ncard_image_of_injective e.1 σ.injective).trans e.2⟩

theorem EdgeColoring.mem_colorEdges_relabel_iff
    {C : (completeKUniform n k).EdgeColoring Color} {color : Color} {σ : Equiv.Perm (Fin n)}
    {e : Set (Fin n)} :
    e ∈ EdgeColoring.colorEdges (C.relabel σ) color ↔ σ '' e ∈ EdgeColoring.colorEdges C color :=
  ⟨fun ⟨he, hc⟩ => ⟨(Set.ncard_image_of_injective e σ.injective).trans he, hc⟩,
    fun ⟨hm, hc⟩ => ⟨(Set.ncard_image_of_injective e σ.injective).symm.trans hm, hc⟩⟩

/-- A relabelled `Finset` is a monochromatic clique for the relabelled colouring iff the original
`Finset` was a monochromatic clique for the original colouring. -/
theorem EdgeColoring.monochromaticClique_relabel_iff
    {C : (completeKUniform n k).EdgeColoring Color} {color : Color} {σ : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} :
    EdgeColoring.MonochromaticClique (C.relabel σ) color k S ↔
      EdgeColoring.MonochromaticClique C color k (S.map σ.toEmbedding) := by
  unfold EdgeColoring.MonochromaticClique
  refine and_congr ⟨fun _ => Set.subset_univ _, fun _ => Set.subset_univ _⟩ ?_
  simp only [Finset.powersetCard_map, Finset.forall_mem_map, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply, Finset.coe_map, Equiv.coe_toEmbedding,
    EdgeColoring.mem_colorEdges_relabel_iff]

/-- Relabelling invariance: the "some monochromatic clique of colour `color` and size `s` exists"
statement does not depend on how the vertices of `completeKUniform n k` are labelled. -/
theorem EdgeColoring.hasMonochromaticClique_relabel_iff
    {C : (completeKUniform n k).EdgeColoring Color} {color : Color} {σ : Equiv.Perm (Fin n)}
    {s : ℕ} :
    EdgeColoring.HasMonochromaticClique (C.relabel σ) color k s ↔
      EdgeColoring.HasMonochromaticClique C color k s :=
  ⟨fun ⟨_, hcard, hmono⟩ =>
    ⟨_, by simpa using hcard, EdgeColoring.monochromaticClique_relabel_iff.mp hmono⟩,
    fun ⟨S, hcard, hmono⟩ => ⟨S.map σ.symm.toEmbedding, by simpa using hcard,
      EdgeColoring.monochromaticClique_relabel_iff.mpr (by simpa [Finset.map_map] using hmono)⟩⟩

end Relabel

/-! ### The two-colour hypergraph Ramsey arrow and least-number API -/

/-- A red/blue colouring of the complete `k`-uniform hypergraph on `n` vertices, using `Bool` as
the two-element colour type (`true` = "red", `false` = "blue"). -/
abbrev TwoColoring (n k : ℕ) : Type :=
  EdgeColoring (completeKUniform n k) Bool

/-- The two-colour `k`-uniform hypergraph Ramsey arrow: every red/blue colouring of the
`k`-element subsets of an `n`-vertex set contains a red `r`-clique or a blue `s`-clique. -/
def RamseyProperty (n k r s : ℕ) : Prop :=
  ∀ C : TwoColoring n k,
    EdgeColoring.HasMonochromaticClique C true k r ∨
      EdgeColoring.HasMonochromaticClique C false k s

/-- Swapping red and blue in a two-colouring. -/
def swapColoring {n k : ℕ} (C : TwoColoring n k) : TwoColoring n k :=
  fun e => !(C e)

theorem hasMonochromaticClique_swapColoring_iff {n k : ℕ} {C : TwoColoring n k} {color : Bool}
    {s : ℕ} :
    EdgeColoring.HasMonochromaticClique (swapColoring C) color k s ↔
      EdgeColoring.HasMonochromaticClique C (!color) k s := by
  have hset : EdgeColoring.colorEdges (swapColoring C) color =
      EdgeColoring.colorEdges C (!color) := by
    ext; simp [swapColoring]
  simp only [EdgeColoring.HasMonochromaticClique, EdgeColoring.MonochromaticClique, hset]

/-- Symmetry: swapping red and blue in the colouring swaps which side the property talks
about. -/
theorem ramseyProperty_swap {n k r s : ℕ} (h : RamseyProperty n k r s) :
    RamseyProperty n k s r := fun C =>
  (h (swapColoring C)).symm.imp hasMonochromaticClique_swapColoring_iff.mp
    hasMonochromaticClique_swapColoring_iff.mp

theorem ramseyProperty_comm (n k r s : ℕ) : RamseyProperty n k r s ↔ RamseyProperty n k s r :=
  ⟨ramseyProperty_swap, ramseyProperty_swap⟩

/-- Monotonicity in the clique-size parameters: asking for smaller monochromatic cliques cannot
make the arrow relation harder to satisfy. -/
theorem ramseyProperty_mono_cliqueSizes {n k r₁ r₂ s₁ s₂ : ℕ} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂)
    (h : RamseyProperty n k r₂ s₂) : RamseyProperty n k r₁ s₁ := fun C =>
  (h C).imp (EdgeColoring.hasMonochromaticClique_mono_size hr)
    (EdgeColoring.hasMonochromaticClique_mono_size hs)

/-! ### The general arrow and the hypergraph Ramsey number -/

section General

variable {ι ι' : Type*}

theorem EdgeColoring.colorEdges_comp_equiv {β : Type*} {H : Hypergraph β} {Color Color' : Type*}
    (C : H.EdgeColoring Color) (e : Color ≃ Color') (c : Color) :
    EdgeColoring.colorEdges (fun x => e (C x)) (e c) = EdgeColoring.colorEdges C c := by
  ext t
  exact exists_congr fun _ => e.apply_eq_iff_eq

theorem EdgeColoring.hasMonochromaticClique_comp_equiv {β : Type*} {H : Hypergraph β}
    {Color Color' : Type*} (C : H.EdgeColoring Color) (e : Color ≃ Color') (c' : Color') (k s : ℕ) :
    EdgeColoring.HasMonochromaticClique (fun x => e (C x)) c' k s ↔
      EdgeColoring.HasMonochromaticClique C (e.symm c') k s := by
  obtain ⟨c, rfl⟩ := e.surjective c'
  unfold EdgeColoring.HasMonochromaticClique EdgeColoring.MonochromaticClique
  rw [EdgeColoring.colorEdges_comp_equiv, Equiv.symm_apply_apply]

/-- **The `k`-uniform hypergraph Ramsey arrow** `n → (sizes c)_c`: every colouring of the
`k`-element subsets of `Fin n` by `ι` has, for some colour `c`, a `c`-monochromatic clique of size
`sizes c`. -/
def Arrow (n k : ℕ) (sizes : ι → ℕ) : Prop :=
  ∀ C : (completeKUniform n k).EdgeColoring ι,
    ∃ c, EdgeColoring.HasMonochromaticClique C c k (sizes c)

/-- Renaming colours does not change the arrow. -/
theorem Arrow.reindex {n k : ℕ} {sizes : ι → ℕ} (e : ι' ≃ ι) :
    Arrow n k (fun c' => sizes (e c')) ↔ Arrow n k sizes := by
  refine ⟨fun h C => ?_, fun h C' => ?_⟩
  · obtain ⟨c', hc'⟩ := h fun x => e.symm (C x)
    exact ⟨e c', by rwa [EdgeColoring.hasMonochromaticClique_comp_equiv, Equiv.symm_symm] at hc'⟩
  · obtain ⟨c, hc⟩ := h fun x => e (C' x)
    exact ⟨e.symm c, by simpa [EdgeColoring.hasMonochromaticClique_comp_equiv] using hc⟩

/-- **The `k`-uniform hypergraph Ramsey number** for target sizes `sizes : ι → ℕ`: the least `n`
with `Arrow n k sizes`. Defined by `sInf`, so it is `0` when no such `n` exists. -/
noncomputable def ramseyNumber (k : ℕ) (sizes : ι → ℕ) : ℕ :=
  sInf {n | Arrow n k sizes}

variable {k n : ℕ} {sizes : ι → ℕ}

theorem ramseyNumber_le_of_arrow (h : Arrow n k sizes) : ramseyNumber k sizes ≤ n :=
  Nat.sInf_le h

theorem arrow_ramseyNumber (hex : ∃ n, Arrow n k sizes) : Arrow (ramseyNumber k sizes) k sizes :=
  Nat.sInf_mem (s := {n | Arrow n k sizes}) hex

theorem not_arrow_of_lt_ramseyNumber (h : n < ramseyNumber k sizes) : ¬ Arrow n k sizes :=
  fun ha => (ramseyNumber_le_of_arrow ha).not_gt h

theorem ramseyNumber_comp_equiv (e : ι' ≃ ι) :
    ramseyNumber k (fun c' => sizes (e c')) = ramseyNumber k sizes :=
  congrArg sInf (Set.ext fun _ => Arrow.reindex e)

end General

/-- `RamseyProperty` is the `Bool`-coloured arrow with sizes `r` (for `true`) and `s` (for
`false`). -/
theorem ramseyProperty_iff_arrow {n k r s : ℕ} :
    RamseyProperty n k r s ↔ Arrow n k (fun b : Bool => if b then r else s) :=
  forall_congr' fun _ => ⟨(·.elim (⟨true, ·⟩) (⟨false, ·⟩)), fun ⟨b, hb⟩ => by
    cases b
    exacts [.inr hb, .inl hb]⟩

/-- The colour renaming `true ↦ 0`, `false ↦ 1`. -/
private def boolEquivFinTwo : Bool ≃ Fin 2 where
  toFun b := if b then 0 else 1
  invFun i := decide (i = 0)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- `RamseyProperty` in the `![r, s]` form used by `ramseyNumber`. -/
theorem ramseyProperty_iff_arrow_finTwo {n k r s : ℕ} :
    RamseyProperty n k r s ↔ Arrow n k ![r, s] := by
  rw [ramseyProperty_iff_arrow, ← Arrow.reindex (sizes := ![r, s]) boolEquivFinTwo]
  simp [boolEquivFinTwo, apply_ite]

/-! ### Worked example: the diagonal `k = r = s` hypergraph Ramsey number

A `k`-uniform hypergraph on exactly `k` vertices has exactly one possible hyperedge, the whole
vertex set, so any 2-colouring puts it in some colour, immediately giving a monochromatic
`k`-clique of that colour. This lands on the classical fact that the diagonal `k`-uniform
hypergraph Ramsey number `R_k(k, k)` is exactly `k`, the smallest case where the question is not
vacuous (below `k` vertices there is no `k`-element subset to colour at all). -/

theorem ramseyProperty_self (k : ℕ) : RamseyProperty k k k k := by
  intro C
  have hedge : ((Finset.univ : Finset (Fin k)) : Set (Fin k)) ∈ E(completeKUniform k k) := by simp
  have key (b : Bool) (hb : C ⟨_, hedge⟩ = b) : EdgeColoring.HasMonochromaticClique C b k k :=
    ⟨Finset.univ, by simp, Set.subset_univ _, fun e he => by
      obtain rfl := Finset.eq_univ_of_card e (by simpa using (Finset.mem_powersetCard.mp he).2)
      exact ⟨hedge, hb⟩⟩
  cases h : C ⟨_, hedge⟩
  exacts [.inr (key _ h), .inl (key _ h)]

/-- Below `k` vertices, no monochromatic `k`-clique can exist at all: there are not even `k`
vertices to form the required `Finset` of size `k`, regardless of colouring. -/
theorem not_ramseyProperty_of_lt_self {n k : ℕ} (hn : n < k) : ¬ RamseyProperty n k k k := by
  have key (b : Bool) : ¬ EdgeColoring.HasMonochromaticClique (fun _ => true : TwoColoring n k)
      b k k := fun ⟨S, hcard, _⟩ => by
    have := S.card_le_univ
    simp only [Fintype.card_fin] at this
    omega
  exact fun h => (h _).elim (key _) (key _)

/-- The headline result: the diagonal `k`-uniform hypergraph Ramsey number `R_k(k, k)` is
exactly `k`. -/
theorem ramseyNumber_self_eq (k : ℕ) : ramseyNumber k ![k, k] = k :=
  have h := ramseyProperty_iff_arrow_finTwo.mp (ramseyProperty_self k)
  le_antisymm (ramseyNumber_le_of_arrow h) <| not_lt.mp fun hlt =>
    not_ramseyProperty_of_lt_self hlt
      (ramseyProperty_iff_arrow_finTwo.mpr (arrow_ramseyNumber ⟨k, h⟩))

end Hypergraph
