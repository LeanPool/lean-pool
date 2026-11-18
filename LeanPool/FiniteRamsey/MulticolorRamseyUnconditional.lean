/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.MulticolorRamsey
public import LeanPool.FiniteRamsey.RamseyProperty
import LeanPool.FiniteRamsey.RamseyExistence

/-!
# Closing the multicolour clique arrow's two-colour gap

`exists_multicolorCliqueArrow_of_exists_two` takes the classical two-colour Ramsey arrow's
eventual existence as an explicit hypothesis `h2`, rather than proving it, so that it applies to
any proof of the two-colour case. This file discharges that
hypothesis from `exists_ramseyProperty`, producing the fully unconditional multicolour clique
Ramsey arrow existence theorem.

The only work is bridging vocabulary: `RamseyProperty` is stated via a `Bool`-indexed
`SimpleGraph.TopEdgeLabeling` and the `IsNClique`-based `HasRedClique`/`HasBlueClique` predicates,
whereas `MulticolorCliqueArrow` is stated via a `Fin 2`-indexed `SimpleGraph.EdgeLabeling` and the
`IsContained` relation `⊑`.

## Main declarations

* `SimpleGraph.hasRedClique_iff_top_isContained`, `SimpleGraph.hasBlueClique_iff_top_isContained`:
  the `HasRedClique`/`HasBlueClique`-to-`⊑` bridge, restating `not_cliqueFree_iff_top_isContained`
  for the two-colour vocabulary of `RamseyProperty`.
* `SimpleGraph.ramseyProperty_iff_arrow`: `RamseyProperty n r s` is exactly the generic `Arrow`
  relation (`ArrowSemantics.lean`) at `ι := Bool` and complete-graph targets — making explicit that
  `RamseyProperty` and `MulticolorCliqueArrow` are two colour-index-shaped views of one relation,
  not independently-invented formalisms.
* `SimpleGraph.two_colour_ramsey_gives_multicolorCliqueArrow`: `exists_ramseyProperty` instantiates
  `exists_multicolorCliqueArrow_of_exists_two`'s hypothesis `h2`.
* `SimpleGraph.exists_multicolorCliqueArrow`: the fully unconditional multicolour clique Ramsey
  arrow existence theorem, for every finite colour count and every tuple of clique sizes.

## Proof outline

Given `C : (⊤ : SimpleGraph (Fin n)).EdgeLabeling (Fin 2)`, recolour it to a `Bool`-indexed
two-colouring `Cbool := C.compRight finTwoEquiv : TwoColoring (Fin n)` and apply
`exists_ramseyProperty`'s witness at `Cbool`. This produces a red or blue clique of `Cbool`, which
transports (via `not_cliqueFree_iff_top_isContained`) into the `⊑`-shape `MulticolorCliqueArrow`
demands, at the `Fin 2` colour `finTwoEquiv.symm` sends `true`/`false` to.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- **`HasRedClique` bridges to `IsContained`.** A two-colouring has a red `n`-clique somewhere
iff the complete graph on `n` vertices embeds as a subgraph copy into its red label graph. -/
theorem hasRedClique_iff_top_isContained (C : TwoColoring V) (n : ℕ) :
    HasRedClique C n ↔ completeGraph (Fin n) ⊑ C.labelGraph true := by
  rw [← not_cliqueFree_iff_top_isContained, CliqueFree, not_forall_not]

/-- The blue analogue of `hasRedClique_iff_top_isContained`. -/
theorem hasBlueClique_iff_top_isContained (C : TwoColoring V) (n : ℕ) :
    HasBlueClique C n ↔ completeGraph (Fin n) ⊑ C.labelGraph false := by
  rw [← not_cliqueFree_iff_top_isContained, CliqueFree, not_forall_not]

/-- **`RamseyProperty` is the two-colour case of the generic `Arrow` relation.** Exhibits
`RamseyProperty n r s` directly as `(⊤ : SimpleGraph (Fin n)).Arrow H` for the `Bool`-indexed
target `H b := completeGraph (Fin (if b then r else s))` — the same relation
`MulticolorCliqueArrow` specialises `Arrow` to `Fin k`-indexed colours
(`MulticolorRamsey.lean`),
made explicit here for `RamseyProperty`'s own concrete `Bool`-indexed shape. `RamseyProperty`
itself stays defined directly on `TwoColoring`/`HasRedClique`/`HasBlueClique` rather than as a
literal `Arrow` instance, since its existence proof (`RamseyExistence.lean`, `BinomialBound.lean`)
is a recursive neighbourhood-counting argument genuinely specific to that concrete shape; this
lemma records that the two formulations coincide, rather than requiring every future two-colour
argument to re-derive the connection itself. -/
theorem ramseyProperty_iff_arrow {n r s : ℕ} :
    RamseyProperty n r s ↔
      (⊤ : SimpleGraph (Fin n)).Arrow
        (fun b : Bool => completeGraph (Fin (if b then r else s))) := by
  refine ⟨fun h C => (h C).elim (⟨true, (hasRedClique_iff_top_isContained C r).mp ·⟩)
    (⟨false, (hasBlueClique_iff_top_isContained C s).mp ·⟩), fun h C => ?_⟩
  obtain ⟨_ | _, hb⟩ := h C
  exacts [.inr ((hasBlueClique_iff_top_isContained C s).mpr hb),
    .inl ((hasRedClique_iff_top_isContained C r).mpr hb)]

/-- **Discharging `exists_multicolorCliqueArrow_of_exists_two`'s two-colour hypothesis.**
`exists_ramseyProperty` is precisely the classical two-colour Ramsey arrow's eventual existence,
stated on `Bool`-indexed two-colourings; this instantiates it in the `Fin 2`-indexed
`MulticolorCliqueArrow` shape the induction principle needs, by recolouring through `finTwoEquiv`
and transporting the resulting monochromatic clique with `hasRedClique_iff_top_isContained`/
`hasBlueClique_iff_top_isContained`. -/
theorem two_colour_ramsey_gives_multicolorCliqueArrow (r s : ℕ) :
    ∃ n, MulticolorCliqueArrow n ![r, s] := by
  obtain ⟨n, hn⟩ := exists_ramseyProperty s r
  refine ⟨n, fun C => (hn (C.compRight finTwoEquiv)).elim (fun h => ⟨1, ?_⟩) (fun h => ⟨0, ?_⟩)⟩
  · simpa [finTwoEquiv] using EdgeLabeling.labelGraph_compRight_equiv C finTwoEquiv true ▸
      (hasRedClique_iff_top_isContained _ s).mp h
  · simpa [finTwoEquiv] using EdgeLabeling.labelGraph_compRight_equiv C finTwoEquiv false ▸
      (hasBlueClique_iff_top_isContained _ r).mp h

/-- **The multicolour clique Ramsey arrow: fully unconditional existence.** For every finite
colour count `k` and every tuple of clique sizes `sizes : Fin k → Nat`, some finite host size `n`
makes every `k`-colouring of `K_n`'s edges contain, in some colour, a monochromatic clique of the
requested size for that colour. -/
theorem exists_multicolorCliqueArrow (k : ℕ) (sizes : Fin k → ℕ) :
    ∃ n, MulticolorCliqueArrow n sizes :=
  exists_multicolorCliqueArrow_of_exists_two two_colour_ramsey_gives_multicolorCliqueArrow k sizes

end SimpleGraph
