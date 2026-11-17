/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericTruth.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericFamilySupport
public import LeanPool.TuringConeRigidity.Effective.TupleSystemCertificate

/-!
# Numeric Truth
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem tupleLookup_variable (G t i x : ℕ) :
    Numeric.{u} (fun e => TupleLookup (e G) (e t) (e i) (e x)) :=
  (((defOrderedPair (t+2) 1 0).and (defPairMem (i+2) (x+2) 0)).existsMem (G+1)).existsNat

theorem tuplePrefix_variable (a G t x s : ℕ) :
    Numeric.{u} (fun e => TuplePrefix (e a) (e G) (e t) (e x) (e s)) := by
  let r : ℕ → ℕ := fun i => match i with
    | 0 => 2*a | 1 => 1 | 2 => 2*G | 3 => 2*t | 4 => 2*x | 5 => 2*s | _ => 5
  refine ⟨(tuplePrefixFormula 0 1 2 3 4 5 6).rename r,?_⟩
  intro B _ e
  rw [Formula.eval_rename_comp]
  have he : mix e (params B) ∘ r = cons (e a) (cons ZFSet.omega (cons (e G)
      (cons (e t) (cons (e x) (cons (e s) (fun _ => natSet 0)))))) := by
    funext i
    rcases i with _|_|_|_|_|_|i <;> simp only [r, params, Function.comp_apply, mix_even,
      cons_zero, cons_succ] <;> rfl
  rw [he]
  rfl

theorem setTruthStep_variable (a G T S c t : ℕ) :
    Numeric.{u} (fun e => SetTruthStep (e a) (e G) (e T) (e S) (e c) (e t)) := by
  have ha (tag : ℕ) (hr : Numeric.{u} (fun e => e 1 = e 0)) :=
    (((((binaryGraph_definable _ (atomic_primrec tag) 3 2 (c+4)).and
      ((tupleLookup_variable (G+4) (t+4) 3 1).and
        ((tupleLookup_variable (G+4) (t+4) 2 0).and hr))).existsMem (a+3)).existsMem
          (a+2)).existsNat).existsNat
  have he := ha 0 (equal_definable 1 0)
  have hm := (((((binaryGraph_definable _ (atomic_primrec 1) 3 2 (c+4)).and
    ((tupleLookup_variable (G+4) (t+4) 3 1).and
      ((tupleLookup_variable (G+4) (t+4) 2 0).and (member_definable 1 0)))).existsMem
        (a+3)).existsMem
        (a+2)).existsNat).existsNat
  have hc := (((binaryGraph_definable _ (binary_primrec 2) 1 0 (c+2)).and
    ((defPairMem 1 (t+2) (S+2)).and (defPairMem 0 (t+2) (S+2)))).existsNat).existsNat
  have hn := ((unaryGraph_definable _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem 0 (t+1) (S+1)).neg).existsNat
  have hbody := (((tuplePrefix_variable (a+3) (G+3) (t+3) 1 0).and
    (defPairMem 2 0 (S+3))).existsMem (T+2)).existsMem (a+1)
  have hx := ((unaryGraph_definable _ (unary_primrec 4) 0 (c+1)).and hbody).existsNat
  exact defOr he (defOr hm (defOr hc (defOr hn hx)))

theorem definesSubset_variable (a G T Z c t S : ℕ) :
    Numeric.{u} (fun e => DefinesSubset (e a) (e G) (e T) (e Z) (e c) (e t) (e S)) :=
  (defSubset S a).and (defAllMem (defIff (member_definable 0 (S+1))
    (((tuplePrefix_variable (a+2) (G+2) (t+2) 1 0).and
      (defPairMem (c+2) 0 (Z+2))).existsMem (T+1))) a)

theorem tupleSystem_definable (a G T : ℕ) :
    Numeric.{u} (fun e => TupleSystem (e a) (e G) (e T)) := by
  have hfg (f n a : ℕ) : Numeric.{u} (fun e => FunctionGraph (e n) (e a) (e f)) := by
    refine ⟨.functionGraph (2*f) (2*n) (2*a),?_⟩
    intro B hB e
    simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]
  have hn := defAllMem ((((defOrderedPair 2 1 0).and
    (hfg 0 1 (a+3))).existsMem (G+2)).existsNat) T
  have hz : Numeric.{u} (fun e => ZFSet.pair (natSet 0) (natSet 0) ∈ e T) := (((equalZero 0).and
    (defPairMem 0 0 (T+1))).existsNat).congr (fun e => by
      simp [show natSet.{u} 0 ∈ ZFSet.omega from (mem_omega _).mpr ⟨0, rfl⟩])
  have hc := defAllMem (defAllMem
    ((tuplePrefix_variable (a+3) (G+3) 2 1 0).existsMem (T+2)) (a+1)) T
  exact hn.and (hz.and hc)

end TuringRigidity.NumericSyntax

end OAI
