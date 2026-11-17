/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/TermEvaluationGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.TermFormula
public import LeanPool.TuringConeRigidity.Syntax.TermCertificate

/-!
# Term Evaluation Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace FiniteTerm

/-- Bounded formula describing an input-output pair in a certified finite-term evaluation
graph. -/
def graphFormula : Formula :=
  .existsMem 6 (.existsMem 8 (.conj (.orderedPair 2 1 0)
    (.existsMem 3 (.conj (certificateFormula 5 6 7 8 9 10 0 11 12 13) (.pairMem 2 1 0)))))

theorem eval_graphFormula (z q A B L O K D : ZFSet.{u}) :
    graphFormula.Eval (cons z (cons q (cons A (cons B (cons L (cons O (cons K (cons D
      (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2))))))))))) ↔
    ∃ c ∈ K, ∃ v ∈ D, z = ZFSet.pair c v ∧ ∃ f ∈ q,
      Certificate A B L O K D f ∧ ZFSet.pair c v ∈ f := by
  simp only [graphFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  apply exists_congr; intro c
  apply and_congr_right; intro _
  apply exists_congr; intro v
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply exists_congr; intro f
  apply and_congr_right; intro _
  apply and_congr_left; intro _
  exact eval_certificateFormula 5 6 7 8 9 10 0 11 12 13
    (cons f (cons v (cons c (cons z (cons q (cons A (cons B (cons L (cons O (cons K (cons D
      (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2)))))))))))))) rfl rfl rfl

theorem internal_evaluation_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hω : ZFSet.omega.{u} ∈ M) {A B L O K D : ZFSet.{u}}
    (hA : A ∈ M) (hB : B ∈ M) (hL : L ∈ M) (hO : O ∈ M) (hK : K ∈ M) (hD : D ∈ M)
    (hcode : ∀ c v, Eval A B L O D c v → c ∈ K) :
    ∃ E ∈ M, E ⊆ ZFSet.prod K D ∧
      ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v := by
  have hprod := product_mem M hM hP hU hPow hS hK hD
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow hprod
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  let e := cons q (cons A (cons B (cons L (cons O (cons K (cons D
      (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2)))))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hq
    rcases i with _ | i
    · exact hA
    rcases i with _ | i
    · exact hB
    rcases i with _ | i
    · exact hL
    rcases i with _ | i
    · exact hO
    rcases i with _ | i
    · exact hK
    rcases i with _ | i
    · exact hD
    rcases i with _ | i
    · exact hn 0
    rcases i with _ | i
    · exact hn 1
    exact hn 2
  let E := ZFSet.sep (fun z => graphFormula.Eval (cons z e)) (ZFSet.prod K D)
  have hE : E ∈ M := sep_mem M hM hS graphFormula e he hprod
  refine ⟨E,hE,fun _ hz => (ZFSet.mem_sep.mp hz).1,?_⟩
  intro c v
  change ZFSet.pair c v ∈ ZFSet.sep _ _ ↔ _
  rw [ZFSet.mem_sep,eval_graphFormula]
  constructor
  · rintro ⟨_,c',_,v',_,hp,f,_,hfc,hcv⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact hfc.sound c v hcv
  · intro hv
    obtain ⟨f,hf,hfc,hcv⟩ := internal_certificate M hM hP hU hK hD hcode hv
    have hfq := (hqdef f).mpr ⟨hf,hfc.subset⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨c,hcode c v hv,v,hv.value_mem,rfl⟩,
      c,hcode c v hv,v,hv.value_mem,rfl,f,hfq,hfc,hcv⟩

theorem uniform_internal_evaluation_graph (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (ht : t ∈ M) (htt : Transitive t) (hnt : ∀ n, natSet.{u} n ∈ t) :
    ∃ K ∈ M, ∀ A ∈ M, A ⊆ t → ∀ B ∈ M, B ⊆ t →
      ∀ L ∈ M, ∀ O ∈ M, ∀ D ∈ M, ∃ E ∈ M, E ⊆ ZFSet.prod K D ∧
        ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v := by
  obtain ⟨K,hK,hbound⟩ := FiniteTuple.internal_finite_code_bound M t hM hP hU hPow hS hR hI ht htt
  refine ⟨K,hK,?_⟩
  intro A hA hAt B hB hBt L hL O hO D hD
  exact internal_evaluation_graph M hM hP hU hPow hS.bounded (omega_mem M hM hS.bounded hI)
    hA hB hL hO hK hD (fun c v hv => hbound c (hv.code_finite hAt hBt hnt))

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
