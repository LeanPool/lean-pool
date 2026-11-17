/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/WeakCheckedValue.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCheckedValue
public import LeanPool.TuringConeRigidity.Representation.GroundInclusion

/-!
# Weak Checked Value
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

theorem checkedValue_complete_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
  (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hv : e 0 = checkedCode (e 2) (e 1)) :
    checkedValueFormula.Sat (M : Set ZFSet) e := by
  obtain ⟨d,hd,hdT,hxd⟩ := internal_transitive_container M hM hP hU hS.bounded hR
    hI (he 1)
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow hd
  obtain ⟨f,hf,hg⟩ := internal_checkGraph M d q (e 2) hM hP hU hPow
    hS.bounded hR hd hq (he 2) hdT hqdef (e 1) hxd
  have hh := hull_mem M d q hM hS.bounded hd hq (he 1)
  have hr := iterUnion_mem M hM hU hf 2
  have hx := self_mem_hull d q hxd
  obtain ⟨w,hw,hfw,_⟩ := hg.2.2.1 (e 1) hx
  have hwv : w = e 0 := (hg.correct (e 1) hx w hw hfw).trans hv.symm
  refine ⟨BoundedSetTheory.hull d q (e 1),hh,iterUnion 2 f,hr,f,hf,?_⟩
  have hi : ∀ i, cons f (cons (iterUnion 2 f) (cons (BoundedSetTheory.hull d q (e 1)) e)) i ∈ M :=
    by
    intro i; rcases i with _|_|_|i
    · exact hf
    · exact hr
    · exact hh
    · exact he i
  rw [bounded_sat,Formula.absolute _ M hM _ hi]
  simp only [Formula.Eval,CheckFormula.eval_graph,Formula.eval_pairMem,cons_zero,cons_succ]
  exact ⟨hg,hx,hwv ▸ hw,hwv ▸ hfw⟩

theorem checkedValue_spec_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M) (hU
  : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    checkedValueFormula.Sat (M : Set ZFSet) e ↔ e 0 = checkedCode (e 2) (e 1) :=
  ⟨checkedValue_sound M hM e he,checkedValue_complete_without_choice M hM hP hU hPow hS hR hI e he⟩

end TuringRigidity.ElementaryModel

end OAI
