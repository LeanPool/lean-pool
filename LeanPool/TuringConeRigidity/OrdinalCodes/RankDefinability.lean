/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/RankDefinability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalRankRecursion
public import LeanPool.TuringConeRigidity.SetModels.InternalContainer

/-!
# Rank Definability
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalRank
open TransitiveNameModel BoundedSetTheory
universe u

theorem rankSet_mem_ground (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {x : ZFSet.{u}} (hx : x ∈ M) : rankSet x ∈ M := by
  obtain ⟨d,hd,hdT,hxd⟩ := internal_transitive_container M hM hP hU hS hR hI hx
  exact rankSet_mem_of_container M d hM hP hU hPow hS hR hd hdT hxd

namespace Code

/-- A sigma formula expressing the value of a certified internal rank graph at one argument. -/
def value (x v : ℕ) : SigmaFormula := .existsSet (.existsSet (.existsSet (.bounded
  (.conj (graph 2 1 0) (.conj (.member (x+3) 2) (.pairMem (x+3) (v+3) 0))))))
end Code

theorem realize_rankValue (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (x v : ℕ) :
    (Code.value x v).Realize M e ↔ e v = rankSet (e x) := by
  have matrix (d r f : ZFSet.{u}) (hd : d ∈ M) (hr : r ∈ M) (hf : f ∈ M) :
      (Formula.conj (Code.graph 2 1 0)
        (.conj (.member (x+3) 2) (.pairMem (x+3) (v+3) 0))).Realize M
          (cons f (cons r (cons d e))) ↔
      Graph d r f ∧ e x ∈ d ∧ ZFSet.pair (e x) (e v) ∈ f := by
    rw [Formula.absolute _ M hM _ (by
      intro i
      rcases i with _ | i
      · exact hf
      rcases i with _ | i
      · exact hr
      rcases i with _ | i
      · exact hd
      exact he i)]
    simp only [Formula.Eval,Code.eval_graph,Formula.eval_pairMem,cons_zero,cons_succ]
  change (∃ d ∈ M, ∃ r ∈ M, ∃ f ∈ M, _) ↔ _
  constructor
  · rintro ⟨d,hd,r,hr,f,hf,hφ⟩
    obtain ⟨hg,hxd,hpair⟩ := (matrix d r f hd hr hf).mp hφ
    obtain ⟨a,ha,b,hb,heq⟩ := hg.2.1 _ hpair
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hg.correct _ ha _ hb hpair
  · intro hv
    obtain ⟨d,hd,hdT,hxd⟩ := internal_transitive_container M hM hP hU hS hR hI (he x)
    obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow hd
    obtain ⟨f,hf,hfg⟩ := internal_rankGraph M d q hM hP hU hS hR hd hq hdT hqdef (e x) hxd
    have hh := hull_mem M d q hM hS hd hq (he x)
    have hr := iterUnion_mem M hM hU hf 2
    refine ⟨_,hh,_,hr,f,hf,(matrix _ _ f hh hr hf).mpr
      ⟨hfg,self_mem_hull d q hxd,?_⟩⟩
    exact (hfg.mem_iff _).mpr ⟨e x,self_mem_hull d q hxd,by rw [hv]⟩

end TuringRigidity.InternalRank

end OAI
