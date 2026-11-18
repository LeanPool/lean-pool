/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalRegularTree.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularTreeRun

/-!
# Internal Regular Tree
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalRegularTree
open TransitiveNameModel BoundedSetTheory InternalProjectedGeneric RegularBinaryTree RegularTreeRun

theorem graph_domain_unique (a b C f : ZFSet.{0})
    (ha : FunctionGraph a C f) (hb : FunctionGraph b C f) : a = b := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨y,_,hxy,_⟩ := ha.2 x hx
    obtain ⟨x',hx',y',_,he⟩ := hb.1 _ hxy
    exact (ZFSet.pair_inj.mp he).1 ▸ hx'
  · intro hx
    obtain ⟨y,_,hxy,_⟩ := hb.2 x hx
    obtain ⟨x',hx',y',_,he⟩ := ha.1 _ hxy
    exact (ZFSet.pair_inj.mp he).1 ▸ hx'

theorem tree_graph_internal (M c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hBM : B ∈ M) (hTM : T ∈ M)
    (hc : c ∈ positive B)
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hE : ∀ n, E n ∈ B) (hEM : orbitGraph E ∈ M) :
    ∃ A ∈ M, FunctionGraph InternalCohen.conditions (positive B) A ∧
      ∀ (s : List Bool) U,
        ZFSet.pair (InternalCohen.wordCode s) U ∈ A ↔ U = tree c B T E s := by
  let P := positive B
  let X := ZFSet.prod P B
  let Y := ZFSet.prod P P
  have hP := positive_mem M B hM hT hBM
  have hω := sourceT_omega_mem M hM hT
  have hcM := hM _ hP _ hc
  have hX := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hP hBM
  have hY := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hP hP
  have hW := InternalCohen.conditions_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_model_graph_bound M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hω P hP
  let e := cons ZFSet.omega (cons P (cons Q (cons c (cons B (cons X (cons Y
    (cons T (cons (orbitGraph E) (cons (InternalCohen.bitSet true)
      (cons InternalCohen.alphabet (fun _ => InternalCohen.conditions)))))))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|_|_|_|_|_|i
    · exact hω
    · exact hP
    · exact hQM
    · exact hcM
    · exact hBM
    · exact hX
    · exact hY
    · exact hTM
    · exact hEM
    · exact hM _ (InternalCohen.alphabet_mem M hM hT) _ ((InternalCohen.mem_alphabet _).mpr
      ⟨true,rfl⟩)
    · exact InternalCohen.alphabet_mem M hM hT
    exact hW
  let θ := stepFormula 11 8 12 13 14 15 5 16 2 1 0
  let ψ := Formula.modelIteration 4 5 6 0 7 1 θ
  have hψ (s : List Bool) (n : ℕ) (U z : ZFSet.{0}) :
      ψ.Eval (cons (natSet n) (cons U (cons (InternalCohen.wordCode s) (cons z e)))) ↔
        U = run c B T E (InternalCohen.wordCode s) n := by
    apply Formula.modelIteration_spec 4 5 6 0 7 1 θ _ rfl hQ n rfl
      (run c B T E (InternalCohen.wordCode s)) (run_positive c B T E _ hc hf hE) rfl
    intro i V _
    exact stepFormula_spec B T E (InternalCohen.wordCode s) _ V i hf
      (run_positive c B T E _ hc hf hE i) hE
      11 8 12 13 14 15 5 16 2 1 0 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  let φ : Formula := .existsMem 12 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 3 (.conj (.functionGraph 2 0 14) ψ))))
  let A := (ZFSet.prod InternalCohen.conditions P).sep (fun z => φ.Eval (cons z e))
  have hAM : A ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hW hP)
  have hgs (s : List Bool) (U : ZFSet.{0}) :
      ZFSet.pair (InternalCohen.wordCode s) U ∈ A ↔ U = tree c B T E s := by
    simp only [A,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,w,_,V,_,he,n,hn,hfun,hiter⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      have hfg : FunctionGraph n InternalCohen.alphabet (InternalCohen.wordCode s) :=
        (Formula.eval_functionGraph 2 0 14 _).mp hfun
      have hlen := graph_domain_unique n (natSet s.length) _ _ hfg
        (InternalCohen.wordCode_function s)
      subst n
      exact ((hψ s s.length U _).mp hiter).trans (run_word c B T E s)
    · intro heq
      have hUP : U ∈ P := heq ▸ tree_positive c B T E hc hf hE s
      have hsW : InternalCohen.wordCode s ∈ InternalCohen.conditions :=
        (InternalCohen.mem_conditions _).mpr ((InternalCohen.prefix_iff_wordCode _).mpr ⟨s,rfl⟩)
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨hsW,hUP⟩,_,hsW,U,hUP,rfl,natSet s.length,
        (mem_omega _).mpr ⟨s.length,rfl⟩,?_,?_⟩
      · exact (Formula.eval_functionGraph 2 0 14 _).mpr (InternalCohen.wordCode_function s)
      · exact (hψ s s.length U _).mpr (heq.trans (run_word c B T E s).symm)
  refine ⟨A,hAM,⟨?_,?_⟩,hgs⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro w hw
    obtain ⟨s,rfl⟩ := (InternalCohen.prefix_iff_wordCode w).mp ((InternalCohen.mem_conditions
      w).mp hw)
    exact ⟨tree c B T E s,tree_positive c B T E hc hf hE s,(hgs s _).mpr rfl,
      fun U _ hU => (hgs s U).mp hU⟩

end TuringRigidity.InternalRegularTree

end OAI
