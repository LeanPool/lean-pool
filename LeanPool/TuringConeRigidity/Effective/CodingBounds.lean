/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingBounds.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticModelDecoding

/-!
# Coding Bounds
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedDecoding
open SetCoding RelationCoding ArithmeticModelDecoding

theorem AntichainBelow.mono {p : AntichainCode} {x y : Degree} (hp : AntichainBelow p x) (h : x ≤
  y) :
    AntichainBelow p y := ⟨hp.1.trans h,hp.2.1.trans h,hp.2.2.trans h⟩

theorem SetBelow.mono {p : SetCode} {x y : Degree} (hp : SetBelow p x) (h : x ≤ y) :
    SetBelow p y := ⟨hp.1.trans h,hp.2.1.mono h,hp.2.2.mono h⟩

theorem RelationBelow.mono {n : ℕ} {p : RelationCode n} {x y : Degree}
    (hp : RelationBelow p x) (h : x ≤ y) : RelationBelow p y :=
  ⟨fun i => (hp.1 i).mono h,hp.2.mono h⟩

/-- Represent a set code as a unary relation code. -/
def unary (p : SetCode) : RelationCode 1 := ⟨fun _ => p,p.tags⟩

theorem unary_below {p : SetCode} {y : Degree} (hp : SetBelow p y) : RelationBelow (unary p) y :=
  ⟨fun _ => hp,hp.2.1⟩

theorem unary_holds (p : SetCode) (x : Degree) : (unary p).Holds (one x) ↔ p.Holds x := by
  constructor
  · rintro ⟨c,hc,_⟩
    exact ⟨c 0,hc 0⟩
  · rintro ⟨c,hc⟩
    refine ⟨fun _ => c,fun i => ?_,?_⟩
    · fin_cases i
      exact hc
    · simpa only [Finset.sup_const,Finset.univ_nonempty,ite_eq_left,unary] using hc.2.1

end TuringRigidity.BoundedDecoding

end OAI
