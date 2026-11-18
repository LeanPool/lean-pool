/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# The generic Ramsey arrow relation, and its isomorphism/embedding calculus

Every definition and lemma below is built on top of `SimpleGraph.EdgeLabeling`
(`Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling`) and `SimpleGraph.IsContained`
(`Mathlib.Combinatorics.SimpleGraph.Copy`), the two mathlib primitives it is built from, and
nothing else.

## Background

A classical two-colour Ramsey statement `n → (r, s)` says: every red/blue colouring of the edges
of the complete graph on `n` vertices contains a red `K_r` or a blue `K_s`. The natural common
generalisation, to an arbitrary (possibly infinite, possibly non-complete) host graph, an
arbitrary finite-or-otherwise colour palette, and an arbitrary target graph per colour rather than
a single clique size, is:

> Every colouring of the edges of a host graph `G` by colours `ι` contains, for some colour `c`,
> a copy of the colour-`c` target graph `H c`.

This file names that relation `SimpleGraph.Arrow` and proves the first slice of its natural
transport calculus: how the relation behaves under monotonicity and isomorphism of the target
family (`Arrow.mono_target`, `Arrow.iso_target`), of the host graph (`Arrow.mono_host`,
`Arrow.iso_host`, `Arrow.mono_host_le`), and under renaming colours (`Arrow.reindex`). Classical
`R(r, s)`, graph Ramsey numbers `R(G, H)`, multicolour Ramsey numbers `R(n_1, ..., n_k)`, and
size-Ramsey numbers are all instances of this one relation with a suitable choice of `G`, `ι`, and
`H`; this calculus is shared infrastructure for all of them.

Mathlib does not currently have clique/graph Ramsey-number infrastructure: the only "Ramsey" hits
in the library are unrelated uses of the term in `Combinatorics/Hindman.lean` and
`Combinatorics/HalesJewett.lean` (density/arithmetic Ramsey theory, a different subfield). It does
already carry every primitive this file is built from, `SimpleGraph.EdgeLabeling`/`.labelGraph`
(`Coloring/EdgeLabeling.lean`) and `SimpleGraph.IsContained` (`⊑`, `Copy.lean`), so this file is a
from-scratch construction on existing mathlib foundations, not a port of something mathlib
already half-has.

## Design notes

No `EdgeColoring`/`colorGraph` synonym is introduced: `SimpleGraph.EdgeLabeling G ι` and
`C.labelGraph c` are used directly, since any such abbreviation would only rename these two
mathlib names. `Arrow` lives in the `SimpleGraph` namespace, dot-accessible as `G.Arrow H`
alongside mathlib's other host-graph-first API (`G.CliqueFree`, `G.IsNClique`, ...).
`EdgeLabeling.labelGraph_compRight_equiv` is included alongside `Arrow` because every
colour-relabelling argument on a specialisation of `Arrow` needs it; it is otherwise independent
of `Arrow` itself. Induced containment, ordered/tournament variants, and hypergraph variants are
out of scope here: they need different target relations, not a generalisation of `⊑`.

## Tags

ramsey theory, edge coloring, combinatorics
-/

@[expose] public section

namespace SimpleGraph

universe u u' v v' w w'

/-- `G.Arrow H` means: every edge-labelling `C` of the host graph `G` by colours `ι` contains, in
some colour `c`, a copy of the colour-`c` target graph `H c`, i.e. `H c` is a subgraph of the
colour-`c` label graph of `C`, up to embedding (`SimpleGraph.IsContained`, notation `⊑`).

Specialising `G` to the complete graph on `Fin n`, `ι` to a two-element type, and `H` to constant
clique targets recovers the classical `n → (r, s)` Ramsey arrow relation; specialising `ι` to
`Fin k` recovers the multicolour relation `n → (n_1, ..., n_k)`. -/
def Arrow {V : Type u} (G : SimpleGraph V) {ι : Type w} {W : ι → Type v}
    (H : (c : ι) → SimpleGraph (W c)) : Prop :=
  ∀ C : G.EdgeLabeling ι, ∃ c : ι, H c ⊑ C.labelGraph c

variable {V : Type u} {V' : Type u'} {G : SimpleGraph V} {G' : SimpleGraph V'}
  {ι : Type w} {W : ι → Type v} {W' : ι → Type v'}

/-- Pulling an edge-labelling back along a graph embedding: each pulled-back label graph is
contained, via the same embedding, in the corresponding label graph of the original labelling. -/
theorem EdgeLabeling.labelGraph_pullback_isContained {K : Type*} (C : G'.EdgeLabeling K)
    (f : G ↪g G') (k : K) : (C.pullback f.toHom).labelGraph k ⊑ C.labelGraph k :=
  isContained_iff_exists_le_comap.mpr ⟨f.toEmbedding, fun _ _ h =>
    let ⟨hadj, hcol⟩ := (EdgeLabeling.labelGraph_adj _ _).mp h
    (EdgeLabeling.labelGraph_adj _ _).mpr ⟨f.map_adj_iff.mpr hadj, hcol⟩⟩

/-- Pulling an edge-labelling back to a subgraph of its host: each pulled-back label graph is a
subgraph of the corresponding original label graph. -/
theorem EdgeLabeling.labelGraph_pullback_ofLE {G G' : SimpleGraph V} {K : Type*}
    (C : G'.EdgeLabeling K) (hle : G ≤ G') (k : K) :
    (C.pullback (Hom.ofLE hle)).labelGraph k ≤ C.labelGraph k := fun _ _ h =>
  let ⟨hadj, hcol⟩ := (EdgeLabeling.labelGraph_adj _ _).mp h
  (EdgeLabeling.labelGraph_adj _ _).mpr ⟨hle hadj, hcol⟩

/-- Target antitonicity: an arrow relation persists if every colour's target is replaced by one it
already contains, an easier target to find, since any copy of `H c` inside a label graph already
contains a copy of `H' c` whenever `H' c ⊑ H c`. -/
theorem Arrow.mono_target {H : (c : ι) → SimpleGraph (W c)} {H' : (c : ι) → SimpleGraph (W' c)}
    (hsub : ∀ c, H' c ⊑ H c) (h : G.Arrow H) : G.Arrow H' :=
  fun C => (h C).imp fun c => (hsub c).trans

/-- Target isomorphism invariance: the arrow relation is invariant under replacing every colour's
target graph by an isomorphic one, since an isomorphic target is neither harder nor easier to
find. -/
theorem Arrow.iso_target {H : (c : ι) → SimpleGraph (W c)} {H' : (c : ι) → SimpleGraph (W' c)}
    (e : ∀ c, H c ≃g H' c) : G.Arrow H ↔ G.Arrow H' :=
  ⟨Arrow.mono_target fun c => (e c).isContained', Arrow.mono_target fun c => (e c).isContained⟩

/-- Host monotonicity under embeddings: if a host `G` arrows a target family `H`, so does any host
`G'` that `G` embeds into. Pull an `ι`-labelling of `G'` back along the embedding to a labelling of
`G`, find the target there, then push the resulting copy forward along the same embedding. -/
theorem Arrow.mono_host {H : (c : ι) → SimpleGraph (W c)}
    (f : G ↪g G') (h : G.Arrow H) : G'.Arrow H :=
  fun C' => (h (C'.pullback f.toHom)).imp fun c hc =>
    hc.trans (C'.labelGraph_pullback_isContained f c)

/-- Host isomorphism invariance: a direct corollary of `Arrow.mono_host` in both directions,
isomorphic hosts arrow exactly the same target families. -/
theorem Arrow.iso_host {H : (c : ι) → SimpleGraph (W c)} (e : G ≃g G') :
    G.Arrow H ↔ G'.Arrow H :=
  ⟨Arrow.mono_host e.toEmbedding, Arrow.mono_host e.symm.toEmbedding⟩

/-- Host monotonicity under plain subgraph inclusion, on a shared vertex type: adding edges to the
host can only help find the target. Distinct from `Arrow.mono_host`, which needs a full graph
embedding (possibly changing the vertex type); this version compares two hosts on the same vertex
set via `≤`, as needed for e.g. size-Ramsey-style arguments comparing hosts with a fixed vertex
set. -/
theorem Arrow.mono_host_le {G G' : SimpleGraph V} {H : (c : ι) → SimpleGraph (W c)}
    (hle : G ≤ G') (h : G.Arrow H) : G'.Arrow H :=
  fun C' => (h _).imp fun c hc => hc.trans (.of_le (C'.labelGraph_pullback_ofLE hle c))

/-- Recolouring commutes with `labelGraph` via the recolouring equivalence: relabelling an
edge-labelling by an equivalence `f` of colour types and asking for colour `k'` is the same as
asking the original labelling for colour `f.symm k'`. The key computation behind colour-relabelling
invariance of `Arrow` and its specialisations. -/
theorem EdgeLabeling.labelGraph_compRight_equiv {V : Type*} {G : SimpleGraph V} {K K' : Type*}
    (C : G.EdgeLabeling K) (f : K ≃ K') (k' : K') :
    (C.compRight (f : K → K')).labelGraph k' = C.labelGraph (f.symm k') := by
  ext
  simp [EdgeLabeling.labelGraph_adj, Equiv.eq_symm_apply]

variable {ι' : Type w'} in
/-- **Renaming colours.** Arrowing a target family is invariant under a bijection of the colour
type: `G` arrows `H` iff it arrows the family `H ∘ e` indexed by `ι'`. -/
theorem Arrow.reindex {H : (c : ι) → SimpleGraph (W c)} (e : ι' ≃ ι) :
    G.Arrow (fun c' => H (e c')) ↔ G.Arrow H := by
  refine ⟨fun h C => ?_, fun h C' => ?_⟩
  · obtain ⟨c', hc'⟩ := h (C.compRight e.symm)
    exact ⟨e c', by rwa [EdgeLabeling.labelGraph_compRight_equiv, Equiv.symm_symm] at hc'⟩
  · obtain ⟨c, hc⟩ := h (C'.compRight e)
    obtain ⟨c', rfl⟩ := e.surjective c
    exact ⟨c', by rwa [EdgeLabeling.labelGraph_compRight_equiv, Equiv.symm_apply_apply] at hc⟩

/-- A worked instance: with a single colour, every labelling of a host graph arrows the host
itself, since the unique colour's label graph is forced to be the whole host (there is nowhere
else for an edge's colour to go). This checks `Arrow` is usable end to end on a concrete instance,
not only inside further abstraction. -/
example : (⊤ : SimpleGraph (Fin 3)).Arrow (fun _ : Fin 1 => (⊤ : SimpleGraph (Fin 3))) := by
  intro C
  refine ⟨0, ?_⟩
  convert IsContained.refl (⊤ : SimpleGraph (Fin 3))
  ext; simp [Subsingleton.elim _ (0 : Fin 1)]

end SimpleGraph
