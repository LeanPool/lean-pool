/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.RamseyNumber
import Mathlib.Tactic.FinCases

/-!
# Induced copies in colour classes

`SimpleGraph.ColorInducedArrow` requires an induced copy of a target inside one label graph of
an edge colouring. Nonedges are tested in that label graph: an edge of the host with a different
colour therefore counts as a nonedge. This is a colour-class property, distinct from the
classical induced Ramsey relation, which requires the copy to be induced in the host itself and
its edges to have one colour.

`colorInducedArrowNumber` is the least complete-host size for this colour-class property, with
value zero if no such size exists. Its specification lemmas retain an explicit existence
hypothesis. For complete targets it agrees with the ordinary Ramsey number. The empty-target
example at the end illustrates the distinction from classical induced Ramsey theory: a complete
two-vertex host has no induced empty pair, but its unused colour class does.

The transport and complete-target lemmas below concern only this colour-class relation. They do
not assert the classical induced Ramsey theorem or provide its least-host number.
-/

@[expose] public section

namespace SimpleGraph

universe u u' v w

/-- Every edge colouring has a target induced in one colour's label graph. Edges of the host
with another colour count as nonedges in that label graph; this is not the classical host-induced
Ramsey relation. -/
def ColorInducedArrow {V : Type u} (G : SimpleGraph V) {ι : Type w} {W : ι → Type v}
    (H : (c : ι) → SimpleGraph (W c)) : Prop :=
  ∀ C : G.EdgeLabeling ι, ∃ c : ι, H c ⊴ C.labelGraph c

variable {V : Type u} {V' : Type u'} {G : SimpleGraph V} {G' : SimpleGraph V'}
  {ι : Type w} {W W' : ι → Type v}

/-- **Target antitonicity.** An induced arrow relation persists if every colour's target is
replaced by one it is already inducingly contained in — an easier target to find an induced copy
of. -/
theorem ColorInducedArrow.mono_target {H : (c : ι) → SimpleGraph (W c)} {H' : (c : ι) →
  SimpleGraph (W' c)}
    (hsub : ∀ c, H' c ⊴ H c) (h : G.ColorInducedArrow H) : G.ColorInducedArrow H' :=
  fun C => (h C).imp fun c => (hsub c).trans

/-- **Target isomorphism invariance.** The induced arrow relation is invariant under replacing
every colour's target graph by an isomorphic one. -/
theorem ColorInducedArrow.iso_target {H : (c : ι) → SimpleGraph (W c)} {H' : (c : ι) → SimpleGraph
  (W' c)}
    (e : ∀ c, H c ≃g H' c) : G.ColorInducedArrow H ↔ G.ColorInducedArrow H' :=
  ⟨ColorInducedArrow.mono_target fun c => (e c).isIndContained',
    ColorInducedArrow.mono_target fun c => (e c).isIndContained⟩

/-- The colour-class induced-copy property passes along graph embeddings: pulling back a
colouring and then mapping the chosen copy forward preserves adjacency in its label graph. -/
theorem ColorInducedArrow.mono_host {H : (c : ι) → SimpleGraph (W c)} (f : G ↪g G') (h :
  G.ColorInducedArrow H) :
    G'.ColorInducedArrow H := fun C' =>
  (h (C'.pullback f.toHom)).imp fun _ hc => hc.trans <| Embedding.isIndContained
    ⟨f.toEmbedding, by simp [EdgeLabeling.labelGraph_adj, ← EdgeLabeling.get_eq]⟩

/-- **Host isomorphism invariance.** A direct corollary of `ColorInducedArrow.mono_host` in both
directions: isomorphic hosts induced-arrow exactly the same target families. -/
theorem ColorInducedArrow.iso_host {H : (c : ι) → SimpleGraph (W c)} (e : G ≃g G') :
    G.ColorInducedArrow H ↔ G'.ColorInducedArrow H :=
  ⟨ColorInducedArrow.mono_host e.toEmbedding, ColorInducedArrow.mono_host e.symm.toEmbedding⟩

section CompleteTargetReduction

-- The ordinary (non-induced) Ramsey arrow relation `SimpleGraph.Arrow` used for comparison below
-- is `ArrowSemantics.lean`'s shared definition, imported above rather than restated here.

variable {n : Nat} {r : ι → Nat}

/-- **Reduction for complete-graph targets.** For complete-graph targets, induced and ordinary
containment coincide (a complete graph has no non-edges to mismatch), so `ColorInducedArrow` and
`Arrow`
agree — for *any* host, not just a complete one. This is
`SimpleGraph.top_isIndContained_iff_top_isContained` (already in mathlib) threaded through the
`∀ C, ∃ c, _` shape of both arrow relations. -/
theorem colorInducedArrow_iff_arrow_of_completeGraph_targets {G : SimpleGraph V} :
    G.ColorInducedArrow (fun c => completeGraph (Fin (r c))) ↔
      G.Arrow (fun c => completeGraph (Fin (r c))) :=
  forall_congr' fun _ => exists_congr fun _ => top_isIndContained_iff_top_isContained

end CompleteTargetReduction

section ColorInducedArrowNumber

/-- **The colour-class induced arrow number**: the least `n` such that the complete graph on `Fin n`
induced-arrows `H`. Defined by `sInf`, so it is `0` when no such `n` exists. -/
noncomputable def colorInducedArrowNumber (H : (c : ι) → SimpleGraph (W c)) : ℕ :=
  sInf {n | (⊤ : SimpleGraph (Fin n)).ColorInducedArrow H}

variable {H : (c : ι) → SimpleGraph (W c)} {n : ℕ}

/-- Any proved induced arrow gives an upper bound on `colorInducedArrowNumber`. -/
theorem colorInducedArrowNumber_le_of_colorInducedArrow (h : (⊤ : SimpleGraph (Fin
  n)).ColorInducedArrow H) :
    colorInducedArrowNumber H ≤ n :=
  Nat.sInf_le h

/-- If some complete host induced-arrows `H`, so does the one of size `colorInducedArrowNumber H`.
-/
theorem colorInducedArrow_colorInducedArrowNumber (hex : ∃ n, (⊤ : SimpleGraph (Fin
  n)).ColorInducedArrow H) :
    (⊤ : SimpleGraph (Fin (colorInducedArrowNumber H))).ColorInducedArrow H :=
  Nat.sInf_mem (s := {n | (⊤ : SimpleGraph (Fin n)).ColorInducedArrow H}) hex

/-- **The least-number characterisation**, given existence. Monotone in the host size via
`ColorInducedArrow.mono_host` along the complete-graph embedding `Fin n ↪ Fin m`. -/
theorem colorInducedArrow_iff_colorInducedArrowNumber_le (hex : ∃ n, (⊤ : SimpleGraph (Fin
  n)).ColorInducedArrow H) :
    (⊤ : SimpleGraph (Fin n)).ColorInducedArrow H ↔ colorInducedArrowNumber H ≤ n :=
  ⟨colorInducedArrowNumber_le_of_colorInducedArrow, fun hle =>
    (colorInducedArrow_colorInducedArrowNumber hex).mono_host (Embedding.completeGraph
      (Fin.castLEEmb hle))⟩

/-- Below the colour-class induced arrow number the complete host does not induced-arrow `H`. -/
theorem not_colorInducedArrow_of_lt_colorInducedArrowNumber (h : n < colorInducedArrowNumber H) :
    ¬ (⊤ : SimpleGraph (Fin n)).ColorInducedArrow H :=
  fun ha => (colorInducedArrowNumber_le_of_colorInducedArrow ha).not_gt h

end ColorInducedArrowNumber

section CompleteGraphValidation

variable {r : ι → ℕ}

/-- For complete-graph targets the colour-class induced arrow exists unconditionally (when `ι` is
finite):
induced-ness is vacuous for complete targets, so Ramsey's theorem applies. -/
theorem exists_colorInducedArrow_completeGraph [Finite ι] :
    ∃ n, (⊤ : SimpleGraph (Fin n)).ColorInducedArrow (fun c => completeGraph (Fin (r c))) :=
  (exists_arrow _).imp fun _ => colorInducedArrow_iff_arrow_of_completeGraph_targets.mpr

/-- **Validation against the ordinary Ramsey number.** For complete-graph targets the colour-class
induced
arrow number is the ordinary Ramsey number. -/
theorem colorInducedArrowNumber_completeGraph_eq_ramseyNumber [Finite ι] :
    colorInducedArrowNumber (fun c => completeGraph (Fin (r c))) = ramseyNumber r :=
  le_antisymm (colorInducedArrowNumber_le_of_colorInducedArrow
      (colorInducedArrow_iff_arrow_of_completeGraph_targets.mpr (arrow_ramseyNumber r)))
    (ramseyNumber_le_of_arrow (colorInducedArrow_iff_arrow_of_completeGraph_targets.mp
      (colorInducedArrow_colorInducedArrowNumber exists_colorInducedArrow_completeGraph)))

end CompleteGraphValidation

section Example

/-- A colour-class induced-copy example: the two-vertex empty graph (no edge) as
*both* colours' target on the complete host `K₂` (`Fin 2`). This target is not complete, so it is
where `⊴` and `⊑` diverge: `(⊥ : SimpleGraph (Fin 2)) ⊑ B` holds for *any* `B` on at least 2
vertices (an empty target's vacuous edge-preservation condition is met by any injective map at
all), so the `Arrow` analogue of this statement would be entirely uninteresting. `⊴`, by
contrast, demands the image be an actual non-adjacent pair — a real combinatorial condition. -/
-- The colour argument is deliberately ignored: both colours get the *same* target graph, which
-- is the point of the instance below (`colorInducedArrow_top_fin2_emptyTargets`) — whichever
-- colour is not
-- `K₂`'s single edge has an entirely empty colour class, matching this target either way.
def colorInducedArrowEmptyTargets : Bool → SimpleGraph (Fin 2) := Function.const Bool ⊥

/-- **A colour-class induced-copy instance, not an induced copy in the host.** Every red/blue
(`Bool`) labelling of `K₂`'s
single edge contains, in some colour, an induced copy of the empty 2-vertex graph. `K₂` has
exactly one possible edge (between `0` and `1`); whichever colour is *not* that edge's colour has
an entirely edge-free colour class, which is then literally equal to `⊥` — the target itself. -/
theorem colorInducedArrow_top_fin2_emptyTargets :
    (⊤ : SimpleGraph (Fin 2)).ColorInducedArrow colorInducedArrowEmptyTargets := by
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
