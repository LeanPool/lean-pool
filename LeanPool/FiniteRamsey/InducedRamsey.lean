/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.RamseyNumber
import Mathlib.Tactic.FinCases

/-!
# Induced Ramsey numbers

For a family of graphs `H c` indexed by colours `c : ι`, a host graph `G` **induced-arrows** `H`
if every edge-labelling of `G` by `ι` contains, in some colour `c`, an *induced* copy of `H c`
(`SimpleGraph.IsIndContained`, `⊴`) — matching non-edges as well as edges, unlike the ordinary
containment relation `⊑` used by the plain (non-induced) arrow relation. This file gives this
relation (`SimpleGraph.IndArrow`), its monotonicity and isomorphism-invariance lemmas, the
associated least-`n` induced Ramsey number `indRamseyNumber`, and the reduction showing induced
and ordinary containment coincide for complete-graph targets.

The classical induced Ramsey theorem (Deuber; Erdős–Hajnal–Pósa; Rödl) — that induced targets are
always eventually arrowed by some (carefully constructed) host — is a genuinely hard
partite/product construction and is not proved here. `indRamseyNumber` is therefore defined with
`sInf` (junk value `0` when no host works), and the lemmas that need its true value take an
existence hypothesis.

## Main declarations

* `SimpleGraph.IndArrow`: the induced Ramsey arrow relation.
* `SimpleGraph.IndArrow.mono_target`, `SimpleGraph.IndArrow.iso_target`: target
  antitonicity/isomorphism-invariance.
* `SimpleGraph.IndArrow.mono_host`, `SimpleGraph.IndArrow.iso_host`: host
  monotonicity/isomorphism-invariance under graph embeddings.
* `SimpleGraph.indRamseyNumber`: the least `n` such that the complete graph on `n` vertices
  induced-arrows a given target family.
* `SimpleGraph.indArrow_iff_arrow_of_completeGraph_targets`: for complete-graph targets, induced
  and ordinary containment coincide, so `IndArrow` and `Arrow` agree for any host.
* `SimpleGraph.indRamseyNumber_completeGraph_eq_ramseyNumber`: consequently, the induced Ramsey
  number of a complete-graph target family is the ordinary Ramsey number.
-/

@[expose] public section

namespace SimpleGraph

universe u u' v w

/-- **The induced Ramsey arrow relation.** `G.IndArrow H` means: every edge-labelling `C` of the
host graph `G` by colours `ι` contains, in some colour `c`, an *induced* copy of the colour-`c`
target graph `H c` — a vertex subset of `G` on which colour `c`'s label graph is exactly
isomorphic to `H c`, matching non-edges as well as edges (`SimpleGraph.IsIndContained`, notation
`⊴`). The only difference from `SimpleGraph.Arrow` is `⊴` in place of `⊑`. -/
def IndArrow {V : Type u} (G : SimpleGraph V) {ι : Type w} {W : ι → Type v}
    (H : (c : ι) → SimpleGraph (W c)) : Prop :=
  ∀ C : G.EdgeLabeling ι, ∃ c : ι, H c ⊴ C.labelGraph c

variable {V : Type u} {V' : Type u'} {G : SimpleGraph V} {G' : SimpleGraph V'}
  {ι : Type w} {W W' : ι → Type v}

/-- **Target antitonicity.** An induced arrow relation persists if every colour's target is
replaced by one it is already inducingly contained in — an easier target to find an induced copy
of. -/
theorem IndArrow.mono_target {H : (c : ι) → SimpleGraph (W c)} {H' : (c : ι) → SimpleGraph (W' c)}
    (hsub : ∀ c, H' c ⊴ H c) (h : G.IndArrow H) : G.IndArrow H' :=
  fun C => (h C).imp fun c => (hsub c).trans

/-- **Target isomorphism invariance.** The induced arrow relation is invariant under replacing
every colour's target graph by an isomorphic one. -/
theorem IndArrow.iso_target {H : (c : ι) → SimpleGraph (W c)} {H' : (c : ι) → SimpleGraph (W' c)}
    (e : ∀ c, H c ≃g H' c) : G.IndArrow H ↔ G.IndArrow H' :=
  ⟨IndArrow.mono_target fun c => (e c).isIndContained',
    IndArrow.mono_target fun c => (e c).isIndContained⟩

/-- **Host monotonicity under embeddings.** If the smaller host `G` induced-arrows `H`, so does
any host `G'` that `G` embeds into. This builds an actual embedding
`(C'.pullback f.toHom).labelGraph c ↪g C'.labelGraph c` out of `f` itself, because induced
containment needs non-adjacency preserved exactly, not merely edges. This works precisely because
`f : G ↪g G'` is already exact on adjacency (`f.map_adj_iff`): pulling a labelling of `G'` back to
`G` along `f` and then re-pushing a colour class forward along `f` recovers exactly the
corresponding colour class of `G'`, restricted to `f`'s image — matching edges *and* non-edges,
not just edges.

Note that host monotonicity under plain edge-addition (`G ≤ G'` on the *same* vertex set, as
opposed to an embedding into a possibly larger vertex set) genuinely fails for induced
containment, unlike for ordinary containment: `G ≤ G'` can add edges *between vertices of the very
copy just found*, turning what was an induced non-edge in `C.labelGraph c` into an edge of
`C'.labelGraph c`, breaking the exact match. This is not a proof gap — it is the precise reason
the general induced Ramsey theorem needs a carefully *constructed* host (Deuber's or Rödl's
partite/product constructions) rather than "any sufficiently large complete graph": in the induced
setting, more edges on the host do not just make targets easier to find, they can also destroy
induced copies already present. -/
theorem IndArrow.mono_host {H : (c : ι) → SimpleGraph (W c)} (f : G ↪g G') (h : G.IndArrow H) :
    G'.IndArrow H := fun C' =>
  (h (C'.pullback f.toHom)).imp fun _ hc => hc.trans <| Embedding.isIndContained
    ⟨f.toEmbedding, by simp [EdgeLabeling.labelGraph_adj, ← EdgeLabeling.get_eq]⟩

/-- **Host isomorphism invariance.** A direct corollary of `IndArrow.mono_host` in both
directions: isomorphic hosts induced-arrow exactly the same target families. -/
theorem IndArrow.iso_host {H : (c : ι) → SimpleGraph (W c)} (e : G ≃g G') :
    G.IndArrow H ↔ G'.IndArrow H :=
  ⟨IndArrow.mono_host e.toEmbedding, IndArrow.mono_host e.symm.toEmbedding⟩

section CompleteTargetReduction

-- The ordinary (non-induced) Ramsey arrow relation `SimpleGraph.Arrow` used for comparison below
-- is `ArrowSemantics.lean`'s shared definition, imported above rather than restated here.

variable {n : Nat} {r : ι → Nat}

/-- **Reduction for complete-graph targets.** For complete-graph targets, induced and ordinary
containment coincide (a complete graph has no non-edges to mismatch), so `IndArrow` and `Arrow`
agree — for *any* host, not just a complete one. This is
`SimpleGraph.top_isIndContained_iff_top_isContained` (already in mathlib) threaded through the
`∀ C, ∃ c, _` shape of both arrow relations. -/
theorem indArrow_iff_arrow_of_completeGraph_targets {G : SimpleGraph V} :
    G.IndArrow (fun c => completeGraph (Fin (r c))) ↔
      G.Arrow (fun c => completeGraph (Fin (r c))) :=
  forall_congr' fun _ => exists_congr fun _ => top_isIndContained_iff_top_isContained

end CompleteTargetReduction

section IndRamseyNumber

/-- **The induced Ramsey number**: the least `n` such that the complete graph on `Fin n`
induced-arrows `H`. Defined by `sInf`, so it is `0` when no such `n` exists. -/
noncomputable def indRamseyNumber (H : (c : ι) → SimpleGraph (W c)) : ℕ :=
  sInf {n | (⊤ : SimpleGraph (Fin n)).IndArrow H}

variable {H : (c : ι) → SimpleGraph (W c)} {n : ℕ}

/-- Any proved induced arrow gives an upper bound on `indRamseyNumber`. -/
theorem indRamseyNumber_le_of_indArrow (h : (⊤ : SimpleGraph (Fin n)).IndArrow H) :
    indRamseyNumber H ≤ n :=
  Nat.sInf_le h

/-- If some complete host induced-arrows `H`, so does the one of size `indRamseyNumber H`. -/
theorem indArrow_indRamseyNumber (hex : ∃ n, (⊤ : SimpleGraph (Fin n)).IndArrow H) :
    (⊤ : SimpleGraph (Fin (indRamseyNumber H))).IndArrow H :=
  Nat.sInf_mem (s := {n | (⊤ : SimpleGraph (Fin n)).IndArrow H}) hex

/-- **The least-number characterisation**, given existence. Monotone in the host size via
`IndArrow.mono_host` along the complete-graph embedding `Fin n ↪ Fin m`. -/
theorem indArrow_iff_indRamseyNumber_le (hex : ∃ n, (⊤ : SimpleGraph (Fin n)).IndArrow H) :
    (⊤ : SimpleGraph (Fin n)).IndArrow H ↔ indRamseyNumber H ≤ n :=
  ⟨indRamseyNumber_le_of_indArrow, fun hle =>
    (indArrow_indRamseyNumber hex).mono_host (Embedding.completeGraph (Fin.castLEEmb hle))⟩

/-- Below the induced Ramsey number the complete host does not induced-arrow `H`. -/
theorem not_indArrow_of_lt_indRamseyNumber (h : n < indRamseyNumber H) :
    ¬ (⊤ : SimpleGraph (Fin n)).IndArrow H :=
  fun ha => (indRamseyNumber_le_of_indArrow ha).not_gt h

end IndRamseyNumber

section CompleteGraphValidation

variable {r : ι → ℕ}

/-- For complete-graph targets the induced arrow exists unconditionally (when `ι` is finite):
induced-ness is vacuous for complete targets, so Ramsey's theorem applies. -/
theorem exists_indArrow_completeGraph [Finite ι] :
    ∃ n, (⊤ : SimpleGraph (Fin n)).IndArrow (fun c => completeGraph (Fin (r c))) :=
  (exists_arrow _).imp fun _ => indArrow_iff_arrow_of_completeGraph_targets.mpr

/-- **Validation against the ordinary Ramsey number.** For complete-graph targets the induced
Ramsey number is the ordinary Ramsey number. -/
theorem indRamseyNumber_completeGraph_eq_ramseyNumber [Finite ι] :
    indRamseyNumber (fun c => completeGraph (Fin (r c))) = ramseyNumber r :=
  le_antisymm (indRamseyNumber_le_of_indArrow
      (indArrow_iff_arrow_of_completeGraph_targets.mpr (arrow_ramseyNumber r)))
    (ramseyNumber_le_of_arrow (indArrow_iff_arrow_of_completeGraph_targets.mp
      (indArrow_indRamseyNumber exists_indArrow_completeGraph)))

end CompleteGraphValidation

section Example

/-- A concrete, genuinely induced-specific instance: the two-vertex empty graph (no edge) as
*both* colours' target on the complete host `K₂` (`Fin 2`). This target is not complete, so it is
where `⊴` and `⊑` diverge: `(⊥ : SimpleGraph (Fin 2)) ⊑ B` holds for *any* `B` on at least 2
vertices (an empty target's vacuous edge-preservation condition is met by any injective map at
all), so the `Arrow` analogue of this statement would be entirely uninteresting. `⊴`, by
contrast, demands the image be an actual non-adjacent pair — a real combinatorial condition. -/
-- The colour argument is deliberately ignored: both colours get the *same* target graph, which
-- is the point of the instance below (`indArrow_top_fin2_emptyTargets`) — whichever colour is not
-- `K₂`'s single edge has an entirely empty colour class, matching this target either way.
def indArrowEmptyTargets : Bool → SimpleGraph (Fin 2) := Function.const Bool ⊥

/-- **The worked, checked induced-specific instance.** Every red/blue (`Bool`) labelling of `K₂`'s
single edge contains, in some colour, an induced copy of the empty 2-vertex graph. `K₂` has
exactly one possible edge (between `0` and `1`); whichever colour is *not* that edge's colour has
an entirely edge-free colour class, which is then literally equal to `⊥` — the target itself. -/
theorem indArrow_top_fin2_emptyTargets :
    (⊤ : SimpleGraph (Fin 2)).IndArrow indArrowEmptyTargets := by
  intro C
  have hadj : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by decide
  refine ⟨!(C.get 0 1 hadj), ?_⟩
  have hbot : C.labelGraph (!(C.get 0 1 hadj)) = ⊥ := by
    ext x y
    rw [EdgeLabeling.labelGraph_adj]
    fin_cases x <;> fin_cases y <;> simp [Sym2.eq_swap (a := (1 : Fin 2)), EdgeLabeling.get_eq]
  change (⊥ : SimpleGraph (Fin 2)) ⊴ C.labelGraph (!(C.get 0 1 hadj))
  rw [hbot]

end Example

end SimpleGraph
