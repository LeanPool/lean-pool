/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalCoverInjection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.TermFunctionality
public import LeanPool.TuringConeRigidity.SetModels.InternalUniformization

/-!
# Internal Cover Injection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTerm

noncomputable def inverseCover (h K E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ h, ∃ c ∈ K, z = ZFSet.pair x c ∧ ZFSet.pair c x ∈ E) (ZFSet.prod h K)

theorem inverseCover_pair (h K E x c : ZFSet.{u}) :
    ZFSet.pair x c ∈ inverseCover h K E ↔ x ∈ h ∧ c ∈ K ∧ ZFSet.pair c x ∈ E := by
  rw [inverseCover,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,d,hd,he,hdy⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hy,hd,hdy⟩
  · rintro ⟨hx,hc,hcx⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,c,hc,rfl⟩,x,hx,c,hc,rfl,hcx⟩

theorem inverseCover_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {h K E : ZFSet.{u}} (hh : h ∈ M) (hK : K ∈ M) (hE : E ∈ M) : inverseCover h K E ∈ M := by
  simpa only [inverseCover,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ] using
    sep_mem M hM hS (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.pairMem 0 1 5))))
      (cons h (cons K (fun _ => E))) (by
        intro i
        rcases i with _ | i
        · exact hh
        rcases i with _ | i
        · exact hK
        exact hE) (product_mem M hM hP hU hPow hS hh hK)

theorem internal_injection_of_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hAC : Choice M) {h K E : ZFSet.{u}}
    (hh : h ∈ M) (hK : K ∈ M) (hE : E ∈ M) (hfun : Functional E)
    (hcover : ∀ x ∈ h, ∃ c ∈ K, ZFSet.pair c x ∈ E) :
    ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
      (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ZFSet.pair (j x) x ∈ E) ∧
      (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  classical
  have hr := inverseCover_mem M hM hP hU hPow hS hh hK hE
  obtain ⟨f,hf,hfr,hshape,hsel⟩ := internal_relation_choice M hM hP hU hPow hS hAC hh hK hr (by
    intro x hx
    obtain ⟨c,hc,hcx⟩ := hcover x hx
    exact ⟨c,hc,(inverseCover_pair h K E x c).mpr ⟨hx,hc,hcx⟩⟩)
  let j := fun x => if hx : x ∈ h then (hsel x hx).choose else ∅
  have hj (x : ZFSet.{u}) (hx : x ∈ h) : j x ∈ K ∧ ZFSet.pair x (j x) ∈ f ∧
      ∀ c ∈ K, ZFSet.pair x c ∈ f → c = j x := by
    simp only [j,dite_eq_left hx]
    exact (hsel x hx).choose_spec
  have hEpair (x : ZFSet.{u}) (hx : x ∈ h) : ZFSet.pair (j x) x ∈ E :=
    ((inverseCover_pair h K E x (j x)).mp (hfr (hj x hx).2.1)).2.2
  refine ⟨f,hf,j,?_,fun x hx => (hj x hx).1,hEpair,?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨x,hx,c,hc,rfl⟩ := hshape z hz
      have hcj := (hj x hx).2.2 c hc hz
      exact ⟨x,hx,congrArg (ZFSet.pair x) hcj⟩
    · rintro ⟨x,hx,rfl⟩
      exact (hj x hx).2.1
  · intro x hx y hy he
    have hyE := hEpair y hy
    rw [← he] at hyE
    exact hfun (j x) x y (hEpair x hx) hyE

theorem internal_evaluated_injection (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hAC : Choice M) {A B L O D E K h : ZFSet.{u}}
    (hh : h ∈ M) (hK : K ∈ M) (hE : E ∈ M)
    (hL : Functional L) (hO : Functional O) (hsub : E ⊆ ZFSet.prod K D)
    (hgraph : ∀ c v, ZFSet.pair c v ∈ E ↔ Eval A B L O D c v)
    (hcover : ∀ x ∈ h, ∃ c, Eval A B L O D c x) :
    ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
      (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  have hc : ∀ x ∈ h, ∃ c ∈ K, ZFSet.pair c x ∈ E := by
    intro x hx
    obtain ⟨c,hcx⟩ := hcover x hx
    have hp := (hgraph c x).mpr hcx
    obtain ⟨c',hc',v,_,he⟩ := ZFSet.mem_prod.mp (hsub hp)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨c,hc',hp⟩
  obtain ⟨f,hf,j,hfj,hj,_,hi⟩ := internal_injection_of_cover M hM hP hU hPow hS hAC hh hK hE
    (evaluation_graph_functional hL hO hgraph) hc
  exact ⟨f,hf,j,hfj,hj,hi⟩

end FiniteTerm
end TuringRigidity.BoundedSetTheory

end OAI
