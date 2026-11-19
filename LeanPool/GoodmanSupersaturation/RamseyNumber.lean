/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.GoodmanSupersaturation.Supersaturation
public import LeanPool.FiniteRamsey.RamseyNumber
import LeanPool.FiniteRamsey.RamseyLowerBoundAsymptotic

/-!
# Supersaturation at the diagonal Ramsey number

`SimpleGraph.choose_le_card_cliqueFinset_add_mul_choose` assumes that every `m`-set of vertices
contains a monochromatic `t`-clique. The pool's `FiniteRamsey` project supplies that hypothesis
for `m = R(t, t)` through `SimpleGraph.exists_isNClique_iff_ramseyNumber_le`, read on the
two-colouring `toTopEdgeLabeling` of an `m`-set (label `1` is `G`, label `0` is `Gᶜ`), and
`t ≤ R(t, t)` is `FiniteRamsey`'s `SimpleGraph.le_ramseyNumber_self`.

## Main statements

* `SimpleGraph.choose_le_card_cliqueFinset_add_mul_choose_ramseyNumber`: if `R(t, t) ≤ n`, then
  `G` and `Gᶜ` together have at least `C(n, t) / C(R(t, t), t)` `t`-cliques.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*}

/-- An embedding of `Fin m` with range inside a finite set `M` of size `m`. -/
private noncomputable def finEmbeddingOfCard {M : Finset V} {m : ℕ} (hM : #M = m) : Fin m ↪ V :=
  (finCongr hM.symm).toEmbedding.trans (M.equivFin.symm.toEmbedding.trans (.subtype _))

private theorem finEmbeddingOfCard_mem {M : Finset V} {m : ℕ} (hM : #M = m) (i : Fin m) :
    finEmbeddingOfCard hM i ∈ M :=
  (M.equivFin.symm (finCongr hM.symm i)).2

/-- **Supersaturation at the diagonal Ramsey number.** If `R(t, t) ≤ n`, the red/blue colouring of
`K_n` given by `G` and `Gᶜ` has at least `C(n, t) / C(R(t, t), t)` monochromatic `t`-cliques. -/
theorem choose_le_card_cliqueFinset_add_mul_choose_ramseyNumber [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ}
    (hR : ramseyNumber ![t, t] ≤ Fintype.card V) :
    (Fintype.card V).choose t ≤
      (#(G.cliqueFinset t) + #(Gᶜ.cliqueFinset t)) * (ramseyNumber ![t, t]).choose t := by
  refine choose_le_card_cliqueFinset_add_mul_choose G (le_ramseyNumber_self t) hR fun M hM => ?_
  set e := finEmbeddingOfCard hM
  obtain ⟨c, s, hs⟩ :=
    exists_isNClique_iff_ramseyNumber_le.mpr le_rfl (G.comap e).toTopEdgeLabeling
  have hsub : s.map e ⊆ M := fun x hx => by
    obtain ⟨i, -, rfl⟩ := mem_map.mp hx
    exact finEmbeddingOfCard_mem hM i
  obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  · rw [toTopEdgeLabeling_labelGraph_compl, Matrix.cons_val_zero] at hs
    refine .inr ⟨s.map e, hsub, (hs.map (f := e)).mono ?_⟩
    rintro _ _ ⟨-, a, b, hab, rfl, rfl⟩
    rw [compl_adj, comap_adj] at hab
    exact (compl_adj G _ _).mpr ⟨e.injective.ne hab.1, hab.2⟩
  · rw [toTopEdgeLabeling_labelGraph, Matrix.cons_val_one, Matrix.cons_val_zero] at hs
    exact .inl ⟨s.map e, hsub, (hs.map (f := e)).mono (map_comap_le e G)⟩

end SimpleGraph
