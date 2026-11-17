/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericFamilySupport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericParameters
public import LeanPool.TuringConeRigidity.Constructibility.UniformSentenceSupport

/-!
# Numeric Family Support
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem setStep_definable (s c : ℕ) :
    Numeric.{u} (fun e => SetStep (e s) (e c)) := by
  have he := ((binaryGraph_definable _ (atomic_primrec 0) 1 0 (c+2)).existsNat).existsNat
  have hm := ((binaryGraph_definable _ (atomic_primrec 1) 1 0 (c+2)).existsNat).existsNat
  have ha := ((binaryGraph_definable _ (binary_primrec 2) 1 0 (c+2)).existsMem (s+1)).existsMem s
  have hn := (unaryGraph_definable _ (unary_primrec 3) 0 (c+1)).existsMem s
  have hx := (unaryGraph_definable _ (unary_primrec 4) 0 (c+1)).existsMem s
  exact defOr he (defOr hm (defOr ha (defOr hn hx)))

theorem setClosed_definable (s : ℕ) :
    Numeric.{u} (fun e => SetClosed (e s)) := by
  have hs := defAllMem (memberNat 0) s
  have hc := defAllMem (setStep_definable (s+1) 0) s
  exact (hs.and hc).congr (fun e => (setClosed_spec (e s)).symm)

theorem leastFamily_definable (q c s : ℕ) :
    Numeric.{u} (fun e => LeastFamily (e q) (e c) (e s)) := by
  have hm := defAllMem (defImp (member_definable (c+1) 0)
    (defImp (setClosed_definable 0) (defSubset (s+1) 0))) q
  exact (member_definable c s).and ((setClosed_definable s).and hm)

theorem setSupportStep_definable (g c b : ℕ) :
    Numeric.{u} (fun e => SetSupportStep (e g) (e c) (e b)) := by
  have hm : Primrec₂ (fun i j : ℕ => max i j + 1) := Primrec.succ.comp Primrec.nat_max
  have ha (t : ℕ) := (((binaryGraph_definable _ (atomic_primrec t) 1 0 (c+2)).and
    (binaryGraph_definable _ hm 1 0 (b+2))).existsNat).existsNat
  have hc := (((((binaryGraph_definable _ (binary_primrec 2) 3 2 (c+4)).and
    ((defPairMem 3 1 (g+4)).and ((defPairMem 2 0 (g+4)).and
      (binaryGraph_definable max Primrec.nat_max 1 0
        (b+4))))).existsNat).existsNat).existsNat).existsNat
  have hn := ((unaryGraph_definable _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem 0 (b+1) (g+1))).existsNat
  have hp : Primrec (fun n : ℕ => n-1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have hx := (((unaryGraph_definable _ (unary_primrec 4) 1 (c+2)).and
    ((defPairMem 1 0 (g+2)).and (unaryGraph_definable _ hp 0 (b+2)))).existsNat).existsNat
  exact defOr (ha 0) (defOr (ha 1) (defOr hc (defOr hn hx)))

theorem setSupportRecursion_definable (f g : ℕ) :
    Numeric.{u} (fun e => SetSupportRecursion (e f) (e g)) := by
  have hn := defAllMem (((defOrderedPair 2 1 0).existsNat).existsMem (f+1)) g
  have hr := defAllMem (defAllNat (defIff (defPairMem 1 0 (g+2))
    (setSupportStep_definable (g+2) 1 0))) f
  exact hn.and hr

end TuringRigidity.NumericSyntax

end OAI
