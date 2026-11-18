/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/EvaluationNameCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.OrderedNameCode
public import LeanPool.TuringConeRigidity.SetModels.InternalCheckRecursion
public import LeanPool.TuringConeRigidity.SetModels.InternalContainer
public import LeanPool.TuringConeRigidity.Syntax.SigmaSyntax

/-!
# Evaluation Name Code
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

/-- A sigma formula selecting a value through a coded name-evaluation relation. -/
def evaluationOutputFormula : SigmaFormula := .existsSet
  (.andBounded (.conj (.member 0 4) (.pairMem 2 0 3))
    (NameCodeFormula.orderedName 5 0 2 1))

theorem internal_evaluation_name_codes (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {V t : ZFSet.{u}} (hV : V ∈ M) (ht : t ∈ M) :
    ∃ B ∈ M, ∀ z, z ∈ B ↔ ∃ x ∈ V,
      orderedNameCode t (checkedCode t x) x = z := by
  obtain ⟨d,hdM,hd,hVd⟩ := internal_transitive_container M hM hP hU hS hR hI hV
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨F,hF,hfg⟩ := internal_checkGraph M d q t hM hP hU hPow hS hR
    hdM hqM ht hd hq V hVd
  let r := iterUnion 2 F
  have hr : r ∈ M := iterUnion_mem M hM hU hF 2
  have hxdom (x : ZFSet.{u}) (hx : x ∈ V) : x ∈ hull d q V :=
    (hull_transitive d q V hd) V (self_mem_hull d q hVd) x hx
  have check (x : ZFSet.{u}) (hx : x ∈ V) :
      checkedCode t x ∈ r ∧ ZFSet.pair x (checkedCode t x) ∈ F := by
    obtain ⟨y,hy,hxy,_⟩ := hfg.2.2.1 x (hxdom x hx)
    have he := hfg.correct x (hxdom x hx) y hy hxy
    exact he ▸ ⟨hy,hxy⟩
  let e := cons F (cons r (fun _ => t))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hF
    rcases i with _ | i
    · exact hr
    exact ht
  apply replacement_image M hM hR evaluationOutputFormula e he hV
    (fun x => orderedNameCode t (checkedCode t x) x)
  · intro x hx
    exact orderedNameCode_mem M hM hP ht (hM r hr _ (check x hx).1) (hM V hV x hx)
  · intro x hx z hz
    have hxM := hM V hV x hx
    have matrix (w : ZFSet.{u}) (hw : w ∈ M) :
        (SigmaFormula.andBounded (.conj (.member 0 4) (.pairMem 2 0 3))
          (NameCodeFormula.orderedName 5 0 2 1)).Realize M (cons w (cons z (cons x e))) ↔
          w ∈ r ∧ ZFSet.pair x w ∈ F ∧ z = orderedNameCode t w x := by
      have he' : ∀ i, cons w (cons z (cons x e)) i ∈ M := by
        intro i
        rcases i with _ | i
        · exact hw
        rcases i with _ | i
        · exact hz
        rcases i with _ | i
        · exact hxM
        exact he i
      rw [SigmaFormula.realize_andBounded,Formula.absolute _ M hM _ he',
        NameCodeFormula.realize_orderedName M hM hP _ _ _ _ _ he']
      simp only [Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
      exact and_assoc
    change (∃ w ∈ M, _) ↔ _
    constructor
    · rintro ⟨w,hw,h⟩
      obtain ⟨hwr,hxw,hz⟩ := (matrix w hw).mp h
      rw [hfg.correct x (hxdom x hx) w hwr hxw] at hz
      exact hz
    · intro hz
      have hwM := hM r hr _ (check x hx).1
      exact ⟨_,hwM,(matrix _ hwM).mpr ⟨(check x hx).1,(check x hx).2,hz⟩⟩

end TuringRigidity.TransitiveNameModel

end OAI
