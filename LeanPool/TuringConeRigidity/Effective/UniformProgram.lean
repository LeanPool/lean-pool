/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.BranchMachine

/-!
# Uniform Program
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformProgram
open Encodable Computable
abbrev Code := Nat.Partrec.Code
local instance : DecidableEq Code := Encodable.decidableEqOfEncodable Code

def meaning : Code → OracleCode
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair c d => .pair (meaning c) (meaning d)
  | .comp c d => .comp (meaning c) (meaning d)
  | .prec c d => .prec (meaning c) (meaning d)
  | .rfind' c => if c = .zero then .query else .find (meaning c)

def represent : OracleCode → Code
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .query => .rfind' .zero
  | .pair c d => .pair (represent c) (represent d)
  | .comp c d => .comp (represent c) (represent d)
  | .prec c d => .prec (represent c) (represent d)
  | .find c => .rfind' (.comp (represent c) (.pair .left .right))

theorem represent_correct (g : ℕ →. ℕ) (e : OracleCode) :
    OracleCode.eval g (meaning (represent e)) = OracleCode.eval g e := by
  induction e with
  | zero | succ | left | right | query => rfl
  | pair c d hc hd | comp c d hc hd | prec c d hc hd =>
    simp only [represent,meaning,OracleCode.eval,hc,hd]
    rfl
  | find c hc =>
    simp only [represent,meaning,reduceCtorEq,↓reduceIte,OracleCode.eval,hc]
    funext n
    simp only [Nat.unpair_pair, Part.coe_some, Part.map_eq_map, Part.map_some,
      Seq.seq, Part.bind_some]
    apply congrArg Nat.rfind
    funext candidate
    exact congrArg (Part.map (fun value : ℕ => decide (value = 0)))
      (Part.bind_some (Nat.pair n candidate) (OracleCode.eval g c))

def tag : Code → ℕ
  | .zero => 0 | .succ => 1 | .left => 2 | .right => 3
  | .pair _ _ => 4 | .comp _ _ => 5 | .prec _ _ => 6 | .rfind' _ => 7

def first : Code → Code
  | .pair c _ | .comp c _ | .prec c _ | .rfind' c => c
  | _ => .zero

def second : Code → Code
  | .pair _ d | .comp _ d | .prec _ d => d
  | _ => .zero

theorem tag_primrec : Primrec tag := by
  have h := Nat.Partrec.Code.primrec_recOn (α := Code) (σ := ℕ) Primrec.id
    (Primrec.const 0) (Primrec.const 1) (Primrec.const 2) (Primrec.const 3)
    (pr := fun _ _ _ _ _ => 4) (Primrec.const 4)
    (co := fun _ _ _ _ _ => 5) (Primrec.const 5)
    (pc := fun _ _ _ _ _ => 6) (Primrec.const 6)
    (rf := fun _ _ _ => 7) (Primrec.const 7)
  exact h.of_eq (fun e => by cases e <;> rfl)

theorem first_primrec : Primrec first := by
  have h := Nat.Partrec.Code.primrec_recOn (α := Code) (σ := Code) Primrec.id
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (pr := fun _ c _ _ _ => c) (Primrec.fst.comp Primrec.snd)
    (co := fun _ c _ _ _ => c) (Primrec.fst.comp Primrec.snd)
    (pc := fun _ c _ _ _ => c) (Primrec.fst.comp Primrec.snd)
    (rf := fun _ c _ => c) (Primrec.fst.comp Primrec.snd)
  exact h.of_eq (fun e => by cases e <;> rfl)

theorem second_primrec : Primrec second := by
  have h := Nat.Partrec.Code.primrec_recOn (α := Code) (σ := Code) Primrec.id
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (Primrec.const Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
    (pr := fun _ _ d _ _ => d) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (co := fun _ _ d _ _ => d) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (pc := fun _ _ d _ _ => d) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (rf := fun _ _ _ => Nat.Partrec.Code.zero) (Primrec.const Nat.Partrec.Code.zero)
  exact h.of_eq (fun e => by cases e <;> rfl)

variable {α : Type*} [Primcodable α] (g : α → ℕ →. ℕ)

def layer (self : Code) (z : Code × α × ℕ) : Part ℕ :=
  let e := z.1
  let a := z.2.1
  let n := z.2.2
  let c := fun k => self.eval (encode (first e,a,k))
  let d := fun k => self.eval (encode (second e,a,k))
  if tag e = 0 then Part.some 0 else
  if tag e = 1 then Part.some (n+1) else
  if tag e = 2 then Part.some (Nat.unpair n).1 else
  if tag e = 3 then Part.some (Nat.unpair n).2 else
  if tag e = 4 then Nat.pair <$> c n <*> d n else
  if tag e = 5 then d n >>= c else
  if tag e = 6 then
    if (Nat.unpair n).2 = 0 then c (Nat.unpair n).1 else
      self.eval (encode (e,a,Nat.pair (Nat.unpair n).1 ((Nat.unpair n).2-1))) >>= fun b =>
        d (Nat.pair (Nat.unpair n).1 (Nat.pair ((Nat.unpair n).2-1) b)) else
  if first e = .zero then g a n else
    Nat.rfind (fun k => (fun b => b = 0) <$> c (Nat.pair n k))

theorem layer_partrec (hg : Partrec₂ g) : Partrec₂ (layer g) := by
  let e : Computable (fun z : Code × (Code × α × ℕ) => z.2.1) := fst.comp snd
  let a : Computable (fun z : Code × (Code × α × ℕ) => z.2.2.1) := fst.comp (snd.comp snd)
  let n : Computable (fun z : Code × (Code × α × ℕ) => z.2.2.2) := snd.comp (snd.comp snd)
  have hc : Partrec₂ (fun z : Code × (Code × α × ℕ) => fun (k : ℕ) =>
      z.1.eval (encode (first z.2.1,z.2.2.1,k))) :=
    Nat.Partrec.Code.eval_part.comp (fst.comp fst)
      (Computable.encode.comp (((first_primrec.to_comp.comp e).comp fst).pair
        ((a.comp fst).pair snd)))
  have hd : Partrec₂ (fun z : Code × (Code × α × ℕ) => fun (k : ℕ) =>
      z.1.eval (encode (second z.2.1,z.2.2.1,k))) :=
    Nat.Partrec.Code.eval_part.comp (fst.comp fst)
      (Computable.encode.comp (((second_primrec.to_comp.comp e).comp fst).pair
        ((a.comp fst).pair snd)))
  have ht (i : ℕ) : Computable (fun z : Code × (Code × α × ℕ) => tag z.2.1 == i) :=
    (Primrec.beq.comp (tag_primrec.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const i)).to_comp
  have hq : Computable (fun z : Code × (Code × α × ℕ) => first z.2.1 == Nat.Partrec.Code.zero) :=
    (Primrec.beq.comp (first_primrec.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const
      Nat.Partrec.Code.zero)).to_comp
  have hpair : Partrec (fun z : Code × (Code × α × ℕ) =>
      Nat.pair <$> z.1.eval (encode (first z.2.1,z.2.2.1,z.2.2.2)) <*>
        z.1.eval (encode (second z.2.1,z.2.2.1,z.2.2.2))) := by
    change Partrec (fun z : Code × (Code × α × ℕ) =>
      (z.1.eval (encode (first z.2.1,z.2.2.1,z.2.2.2))).bind
        (fun x => (z.1.eval (encode (second z.2.1,z.2.2.1,z.2.2.2))).map (Nat.pair x)))
    apply Partrec.bind (hc.comp Computable.id n)
    apply Partrec.map ((hd.comp Computable.id n).comp fst)
    exact Primrec₂.natPair.to_comp.comp (snd.comp fst) snd
  have hcomp : Partrec (fun z : Code × (Code × α × ℕ) =>
      (z.1.eval (encode (second z.2.1,z.2.2.1,z.2.2.2))).bind
        (fun k => z.1.eval (encode (first z.2.1,z.2.2.1,k)))) := (hd.comp Computable.id n).bind
          (hc.comp fst snd)
  have hprev : Partrec (fun z : Code × (Code × α × ℕ) =>
      z.1.eval (encode (z.2.1,z.2.2.1,Nat.pair (Nat.unpair z.2.2.2).1 ((Nat.unpair
        z.2.2.2).2-1)))) :=
    Nat.Partrec.Code.eval_part.comp fst (Computable.encode.comp (e.pair (a.pair
      (Primrec₂.natPair.to_comp.comp ((fst.comp Computable.unpair).comp n)
        (Computable.pred.comp ((snd.comp Computable.unpair).comp n))))))
  have hnext : Partrec (fun z : (Code × (Code × α × ℕ)) × ℕ =>
      z.1.1.eval (encode (second z.1.2.1,z.1.2.2.1,
        Nat.pair (Nat.unpair z.1.2.2.2).1 (Nat.pair ((Nat.unpair z.1.2.2.2).2-1) z.2)))) :=
    hd.comp fst (Primrec₂.natPair.to_comp.comp (((fst.comp Computable.unpair).comp n).comp fst)
      (Primrec₂.natPair.to_comp.comp ((Computable.pred.comp ((snd.comp Computable.unpair).comp
        n)).comp fst) snd))
  have hzero : Computable (fun z : Code × (Code × α × ℕ) => (Nat.unpair z.2.2.2).2 == 0) :=
    (Primrec.beq.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.snd.comp
      Primrec.snd))))
      (Primrec.const 0)).to_comp
  have hbase : Partrec (fun z : Code × (Code × α × ℕ) =>
      z.1.eval (encode (first z.2.1,z.2.2.1,(Nat.unpair z.2.2.2).1))) :=
    hc.comp Computable.id ((fst.comp Computable.unpair).comp n)
  have hsucc : Partrec (fun z : Code × (Code × α × ℕ) =>
      (z.1.eval (encode (z.2.1,z.2.2.1,Nat.pair (Nat.unpair z.2.2.2).1 ((Nat.unpair
        z.2.2.2).2-1)))).bind
        (fun v => z.1.eval (encode (second z.2.1,z.2.2.1,
          Nat.pair (Nat.unpair z.2.2.2).1 (Nat.pair ((Nat.unpair z.2.2.2).2-1) v))))) :=
            hprev.bind hnext
  have hprec := partrec_cond hzero hbase hsucc
  have hfind : Partrec (fun z : Code × (Code × α × ℕ) =>
      Nat.rfind (fun k => (fun b => b = 0) <$> z.1.eval (encode (first z.2.1,z.2.2.1,Nat.pair
        z.2.2.2 k)))) := Partrec.rfind ((hc.comp fst
    (Primrec₂.natPair.to_comp.comp (n.comp fst) snd)).map
      ((Primrec.beq.comp Primrec.snd (Primrec.const 0)).to_comp))
  have h := partrec_cond (ht 0) (Computable.const 0).partrec
    (partrec_cond (ht 1) (Computable.succ.comp n).partrec
    (partrec_cond (ht 2) ((fst.comp Computable.unpair).comp n).partrec
    (partrec_cond (ht 3) ((snd.comp Computable.unpair).comp n).partrec
    (partrec_cond (ht 4) hpair (partrec_cond (ht 5) hcomp
    (partrec_cond (ht 6) hprec (partrec_cond hq (hg.comp a n) hfind)))))))
  exact h.of_eq (fun z => by simp only [layer,beq_iff_eq]; rfl)

theorem eval_partrec (hg : Partrec₂ g) :
    Partrec (fun z : Code × α × ℕ => OracleCode.eval (g z.2.1) (meaning z.1) z.2.2) := by
  obtain ⟨c,hc⟩ := partrec_fixed_point (layer_partrec g hg)
  have he : ∀ e a n, c.eval (encode (e,a,n)) = OracleCode.eval (g a) (meaning e) n := by
    intro e
    induction e with
    | zero | succ | left | right => intros; rw [hc]; rfl
    | pair e f he hf =>
      intro a n
      rw [hc]
      simp only [layer,tag,first,second,meaning,OracleCode.eval,he,hf]
      simp only [OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.reduceEqDiff,
        Nat.succ_ne_self, Part.map_eq_map]
    | comp e f he hf =>
      intro a n
      rw [hc]
      simp only [layer, tag, first, second, meaning, OracleCode.eval, he, hf]
      simp only [OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.reduceEqDiff,
        Nat.succ_ne_self, Part.bind_eq_bind]
      rfl
    | prec e f he hf =>
      intro a n
      have hn : ∃ u k, n = Nat.pair u k := ⟨_,_,(Nat.pair_unpair n).symm⟩
      obtain ⟨u,k,rfl⟩ := hn
      induction k with
      | zero =>
        rw [hc]
        simp only [layer,tag,first,second,meaning,Nat.unpair_pair]
        simp only [show (6 : ℕ) ≠ 0 from by decide,show (6 : ℕ) ≠ 1 from by decide,
          show (6 : ℕ) ≠ 2 from by decide,show (6 : ℕ) ≠ 3 from by decide,
          show (6 : ℕ) ≠ 4 from by decide,show (6 : ℕ) ≠ 5 from by decide,↓reduceIte]
        rw [he]
        simp only [OracleCode.eval,Nat.unpair_pair,Nat.rec_zero]
      | succ k ih =>
        rw [hc]
        simp only [layer,tag,first,second,meaning,he,hf,Nat.unpair_pair]
        simp only [show (6 : ℕ) ≠ 0 from by decide,show (6 : ℕ) ≠ 1 from by decide,
          show (6 : ℕ) ≠ 2 from by decide,show (6 : ℕ) ≠ 3 from by decide,
          show (6 : ℕ) ≠ 4 from by decide,show (6 : ℕ) ≠ 5 from by decide,
          ↓reduceIte,Nat.add_one_ne_zero,Nat.add_sub_cancel]
        rw [ih]
        simp only [meaning,OracleCode.eval,Nat.unpair_pair]
    | rfind' e he =>
      intro a n
      rw [hc]
      simp only [layer,tag,first,meaning,he]
      simp
      split <;> rfl
  exact (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.encode).of_eq
    (fun z => he z.1 z.2.1 z.2.2)

end TuringRigidity.UniformProgram

end OAI
