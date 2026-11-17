/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CategoryMachine.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.CutTranscript
public import LeanPool.TuringConeRigidity.Computability.RationalCut

/-!
# Category Machine
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CategorySearch
open Computable Encodable

/-- The rational-cut bit comparing the rational at index `k` with that at index `i`. -/
def rationalBit (i k : ℕ) : ℕ := if RationalCoding.ltCode k i then 1 else 0

theorem rationalBit_primrec : Primrec₂ rationalBit :=
  Primrec.ite (RationalCoding.ltCode_primrec.comp Primrec.snd Primrec.fst)
    (Primrec.const 1) (Primrec.const 0)

theorem rationalBit_eq (i k : ℕ) :
    Part.some (rationalBit i k) = oracleFunction (cut (rationalEnumeration i : ℝ)) k := by
  simp only [rationalBit,oracleFunction,cut_eq_true,RationalCoding.ltCode_iff]

/-- The real pair given by the two enumerated rational samples. -/
def sample (i j : ℕ) : ℝ × ℝ := (rationalEnumeration i,rationalEnumeration j)

/-- Join a finite partial background table with the total cut oracles of two rational samples. -/
def finiteOracle (L : List ℕ) (i j : ℕ) : ℕ →. ℕ :=
  partialJoin (partialJoin (BranchMachine.lookup L) (fun k => Part.some (rationalBit i k)))
    (fun k => Part.some (rationalBit j k))

theorem partialJoin_oracle (A B : Oracle) :
    partialJoin (oracleFunction A) (oracleFunction B) = oracleFunction (join A B) := by
  funext k
  cases h : k.bodd <;> simp [partialJoin,oracleFunction,join,h]

/-- Read a bit of `A` as the natural number zero or one. -/
noncomputable def Avalue (A : Oracle) (k : ℕ) : ℕ := if A k then 1 else 0

theorem finiteOracle_approximates (A : Oracle) (i j k : ℕ) :
    Approximates (oracleFunction (pairOracle A (sample i j)) k)
      (fun m => finiteOracle (UniformOracle.oraclePrefix (Avalue A) m) i j k) := by
  have hi : (fun k => Part.some (rationalBit i k)) = oracleFunction (cut (rationalEnumeration i :
    ℝ)) :=
    funext (rationalBit_eq i)
  have hj : (fun k => Part.some (rationalBit j k)) = oracleFunction (cut (rationalEnumeration j :
    ℝ)) :=
    funext (rationalBit_eq j)
  have h := BranchMachine.partialJoin_approximates
    (fun k => BranchMachine.partialJoin_approximates
      (UniformOracle.prefix_approximates (Avalue A))
      (fun k => Approximates.const (Part.some (rationalBit i k))) k)
    (fun k => Approximates.const (Part.some (rationalBit j k))) k
  simpa only [finiteOracle,hi,hj,show (fun k => Part.some (Avalue A k)) = oracleFunction A from rfl,
    partialJoin_oracle,pairOracle,sample] using h

/-- Both rational samples lie strictly inside their prescribed rational coordinate intervals. -/
def inside (l r : ℚ × ℚ) (i j : ℕ) : Prop :=
  RationalCoding.ltCode (encode l.1) i ∧ RationalCoding.ltCode i (encode r.1) ∧
  RationalCoding.ltCode (encode l.2) j ∧ RationalCoding.ltCode j (encode r.2)
instance (l r : ℚ × ℚ) (i j : ℕ) : Decidable (inside l r i j) := inferInstanceAs (Decidable (_ ∧ _))

theorem inside_primrec (l r : ℚ × ℚ) : PrimrecRel (inside l r) :=
  (RationalCoding.ltCode_primrec.comp (Primrec.const (encode l.1)) Primrec.fst).and
    ((RationalCoding.ltCode_primrec.comp Primrec.fst (Primrec.const (encode r.1))).and
      ((RationalCoding.ltCode_primrec.comp (Primrec.const (encode l.2)) Primrec.snd).and
        (RationalCoding.ltCode_primrec.comp Primrec.snd (Primrec.const (encode r.2)))))

theorem inside_iff (l r : ℚ × ℚ) (i j : ℕ) :
    inside l r i j ↔ sample i j ∈ rectangle l r := by
  simp [inside,RationalCoding.ltCode_iff,rationalEnumeration,sample,rectangle,and_assoc]

/-- Evaluate the program at a coded rational sample and input when the sample lies inside the
rectangle. -/
def finiteRun (c : OracleCode) (l r : ℚ × ℚ) (L : List ℕ) (w : ℕ) : Part ℕ :=
  let i := (Nat.unpair w).1
  let j := (Nat.unpair (Nat.unpair w).2).1
  let n := (Nat.unpair (Nat.unpair w).2).2
  if inside l r i j then OracleCode.eval (finiteOracle L i j) c n else Part.none

theorem finiteRun_partrec (c : OracleCode) (l r : ℚ × ℚ) : Partrec₂ (finiteRun c l r) := by
  let α := List ℕ × ℕ × ℕ
  have hA : Partrec₂ (fun z : α => BranchMachine.lookup z.1) :=
    BranchMachine.lookup_partrec.comp (fst.comp fst) snd
  have hi : Partrec₂ (fun z : α => fun k => Part.some (rationalBit z.2.1 k)) :=
    (rationalBit_primrec.to_comp.comp (fst.comp (snd.comp fst)) snd)
  have hj : Partrec₂ (fun z : α => fun k => Part.some (rationalBit z.2.2 k)) :=
    (rationalBit_primrec.to_comp.comp (snd.comp (snd.comp fst)) snd)
  have hg : Partrec₂ (fun z : α => finiteOracle z.1 z.2.1 z.2.2) :=
    BranchMachine.partialJoin_partrec (BranchMachine.partialJoin_partrec hA hi) hj
  have he : Partrec₂ (fun z : α => OracleCode.eval (finiteOracle z.1 z.2.1 z.2.2) c) :=
    OracleCode.eval_partrec hg c
  have hi' : Computable (fun z : List ℕ × ℕ => (Nat.unpair z.2).1) :=
    fst.comp (Computable.unpair.comp snd)
  have hj' : Computable (fun z : List ℕ × ℕ => (Nat.unpair (Nat.unpair z.2).2).1) :=
    fst.comp (Computable.unpair.comp (snd.comp (Computable.unpair.comp snd)))
  have hn' : Computable (fun z : List ℕ × ℕ => (Nat.unpair (Nat.unpair z.2).2).2) :=
    snd.comp (Computable.unpair.comp (snd.comp (Computable.unpair.comp snd)))
  have hb : Computable (fun z : List ℕ × ℕ => decide (inside l r (Nat.unpair z.2).1
      (Nat.unpair (Nat.unpair z.2).2).1)) :=
    (inside_primrec l r).decide.to_comp.comp hi' hj'
  have hparam : Computable (fun z : List ℕ × ℕ =>
      (z.1,(Nat.unpair z.2).1,(Nat.unpair (Nat.unpair z.2).2).1)) :=
    fst.pair (hi'.pair hj')
  have hr := he.comp hparam hn'
  exact (partrec_cond hb hr Partrec.none).of_eq (fun z => by simp [finiteRun])

theorem finiteRun_code (c : OracleCode) (l r : ℚ × ℚ) :
    ∃ d : Nat.Partrec.Code, ∀ L w,
      d.eval (Nat.pair (encode L) w) = finiteRun c l r L w := by
  obtain ⟨d,hd⟩ := partrec_code (finiteRun_partrec c l r)
  exact ⟨d,fun L w => hd (L,w)⟩

end TuringRigidity.CategorySearch

end OAI
