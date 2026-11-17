/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/EncodedForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticBounded
public import LeanPool.TuringConeRigidity.Effective.CodingForcing

/-!
# Encoded Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EncodedForcing
open Encodable UniformOracle ArithmeticHierarchy CodingForcing

/-- Decode a finite binary word, using the empty word for an invalid code. -/
def word (e : ℕ) : List Bool := (decode e).getD []
/-- The left word extracted from a condition code. -/
def left (e : ℕ) : List Bool := word (Nat.unpair e).1
/-- The uncorrected right word extracted from a condition code. -/
def rawRight (e : ℕ) : List Bool := word (Nat.unpair (Nat.unpair e).2).1
/-- The right word, replaced by the left word if their lengths differ. -/
def right (e : ℕ) : List Bool := if (rawRight e).length = (left e).length then rawRight e else
  left e
/-- The active index extracted from a condition code. -/
def active (e : ℕ) : ℕ := (Nat.unpair (Nat.unpair e).2).2

/-- Decode a coding condition, repairing unequal word lengths. -/
def condition (e : ℕ) : Condition := ⟨left e, right e, by
  unfold right
  split <;> simp_all, active e⟩

/-- Encode both words and the active index of a coding condition. -/
def code (p : Condition) : ℕ := Nat.pair (encode p.left) (Nat.pair (encode p.right) p.active)

theorem condition_code (p : Condition) : condition (code p) = p := by
  cases p with
  | mk l r h k => simp [condition,code,left,right,rawRight,word,active,h]

theorem word_primrec : Primrec word := Primrec.option_getD.comp Primrec.decode (Primrec.const [])
theorem left_primrec : Primrec left := word_primrec.comp (Primrec.fst.comp Primrec.unpair)
theorem rawRight_primrec : Primrec rawRight := word_primrec.comp
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
theorem right_primrec : Primrec right := Primrec.ite
  (Primrec.eq.comp (Primrec.list_length.comp rawRight_primrec) (Primrec.list_length.comp
    left_primrec))
  rawRight_primrec left_primrec
theorem active_primrec : Primrec active := Primrec.snd.comp
  (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

theorem recursive_primrecPred (Y : Oracle) {P : ℕ → Prop}
    (h : PrimrecPred P) : RecursivePred Y P := by
  classical
  exact (total_primrec (Primrec.ite h (Primrec.const 1) (Primrec.const 0))).of_eq
    (fun x => by by_cases hp : P x <;> simp [hp])

theorem prefix_recursive (Y : Oracle) {l r : ℕ → List Bool} (hl : Primrec l) (hr : Primrec r) :
    RecursivePred Y (fun v => l v <+: r v) := by
  have h : RecursivePred Y (fun v => l v = (r v).take (l v).length) := recursive_primrecPred Y
    (Primrec.eq.comp hl (Primrec.list_take.comp (Primrec.list_length.comp hl) hr))
  exact Form.congr (n := 0) (s := true) h (fun v => List.prefix_iff_eq_take.symm)

/-- View an oracle as a family of columns through natural-number pairing. -/
def columns (B : Oracle) (k n : ℕ) : Bool := B (Nat.pair k n)

private theorem bounded_conjunction_iff {n : ℕ} {P Q R S : ℕ → Prop} :
    (∀ i < n, ¬ P i ∨ ¬ Q i ∨ ¬ R i ∨ S i) ↔
      (∀ i, P i ∧ Q i ∧ R i → i < n → S i) := by
  classical
  constructor
  · intro h i hi hin
    exact (((h i hin).resolve_left (fun hn => hn hi.1)).resolve_left
      (fun hn => hn hi.2.1)).resolve_left (fun hn => hn hi.2.2)
  · intro h i hin
    by_cases hp : P i
    · by_cases hq : Q i
      · by_cases hr : R i
        · exact Or.inr (Or.inr (Or.inr (h i ⟨hp, hq, hr⟩ hin)))
        · exact Or.inr (Or.inr (Or.inl hr))
      · exact Or.inr (Or.inl hq)
    · exact Or.inl hp

theorem extends_recursive (B : Oracle) :
    RecursivePred B (fun v => Extends (columns B) (condition (Nat.unpair v).1) (condition
      (Nat.unpair v).2)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hl := prefix_recursive B (left_primrec.comp f) (left_primrec.comp r)
  have hr := prefix_recursive B (right_primrec.comp f) (right_primrec.comp r)
  have ha := recursive_primrecPred B
    (Primrec.nat_le.comp (active_primrec.comp f) (active_primrec.comp r))
  let p := f.comp f
  let q := r.comp f
  let m := r
  have hlen := recursive_primrecPred B (Primrec.nat_le.comp (Primrec.list_length.comp
    (left_primrec.comp p)) m)
  have hcol := recursive_primrecPred B (Primrec.nat_lt.comp (f.comp m) (active_primrec.comp p))
  have hquery : RecursivePred B (fun v => B (Nat.unpair v).2 = true) := by
    have hq : Nat.RecursiveIn {oracleFunction B} (oracleFunction B) := .oracle _
      (Set.mem_singleton _)
    exact (Nat.RecursiveIn.comp hq (total_primrec m)).of_eq (fun v => by
      change (Part.some (Nat.unpair v).2).bind (fun input => oracleFunction B input) = _
      rw [Part.bind_some]
      cases hb : B (Nat.unpair v).2 <;> simp [oracleFunction,hb])
  have heq := recursive_primrecPred B (Primrec.eq.comp
    ((Primrec.list_getD false).comp (left_primrec.comp q) m)
    ((Primrec.list_getD false).comp (right_primrec.comp q) m))
  have himp := Form.or (n := 0) (s := true) (recursive_not hlen)
    (Form.or (n := 0) (s := true) (recursive_not hcol)
      (Form.or (n := 0) (s := true) (recursive_not hquery) heq))
  have hb := recursive_bounded_all himp (Primrec.list_length.comp (left_primrec.comp r))
  apply Form.congr (n := 0) (s := true) (recursive_and hl (recursive_and hr (recursive_and ha hb)))
  intro v
  simp only [Extends,condition,CodingLocation,columns,Nat.pair_unpair,Nat.unpair_pair]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => bounded_conjunction_iff

end TuringRigidity.EncodedForcing

end OAI
