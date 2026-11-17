/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticHierarchy.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracle

/-!
# Arithmetic Hierarchy
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle

noncomputable def RecursivePred (Y : Oracle) (P : ℕ → Prop) : Prop := by
  classical
  exact Nat.RecursiveIn {oracleFunction Y} (fun x => Part.some (if P x then 1 else 0))

def Quant (s : Bool) (P : ℕ → Prop) : Prop :=
  if s then ∃ a, P a else ∀ a, P a

def Form (Y : Oracle) : ℕ → Bool → (ℕ → Prop) → Prop
  | 0, _, P => RecursivePred Y P
  | n+1, s, P => ∃ Q : ℕ → Prop, Form Y n (!s) Q ∧
      ∀ x, P x ↔ Quant s (fun a => Q (Nat.pair x a))

abbrev Sigma (Y : Oracle) (n : ℕ) (P : ℕ → Prop) := Form Y n true P
abbrev Pi (Y : Oracle) (n : ℕ) (P : ℕ → Prop) := Form Y n false P

theorem Form.congr {Y n s P Q} (h : Form Y n s P) (he : ∀ x, P x ↔ Q x) :
    Form Y n s Q := by
  have : P = Q := funext (fun x => propext (he x))
  exact this ▸ h

theorem recursive_comp {Y P} (h : RecursivePred Y P) {f : ℕ → ℕ} (hf : Primrec f) :
    RecursivePred Y (fun x => P (f x)) := by
  classical
  exact total_comp h (total_primrec hf)

theorem Form.comp {Y n s P} (h : Form Y n s P) {f : ℕ → ℕ} (hf : Primrec f) :
    Form Y n s (fun x => P (f x)) := by
  induction n generalizing s P f with
  | zero => exact recursive_comp h hf
  | succ n ih =>
    obtain ⟨Q, hQ, he⟩ := h
    refine ⟨fun v => Q (Nat.pair (f (Nat.unpair v).1) (Nat.unpair v).2),
      ih hQ (Primrec₂.natPair.comp (hf.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair)), ?_⟩
    intro x
    simpa using he (f x)

theorem recursive_not {Y P} (h : RecursivePred Y P) : RecursivePred Y (fun x => ¬ P x) := by
  classical
  have hf : Primrec (fun v : ℕ => if v = 1 then 0 else 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 0) (Primrec.const 1)
  exact (total_comp (total_primrec hf) h).of_eq (fun x => by by_cases hp : P x <;> simp [hp])

theorem quant_not (s : Bool) (P : ℕ → Prop) :
    (¬ Quant s P) ↔ Quant (!s) (fun x => ¬ P x) := by
  cases s <;> simp [Quant]

theorem Form.neg {Y n s P} (h : Form Y n s P) :
    Form Y n (!s) (fun x => ¬ P x) := by
  induction n generalizing s P with
  | zero => exact recursive_not h
  | succ n ih =>
    obtain ⟨Q, hQ, he⟩ := h
    exact ⟨fun v => ¬ Q v, ih hQ, fun x => (not_congr (he x)).trans (quant_not s _)⟩

theorem recursive_and {Y P Q} (hP : RecursivePred Y P) (hQ : RecursivePred Y Q) :
    RecursivePred Y (fun x => P x ∧ Q x) := by
  classical
  have hf : Primrec (fun v : ℕ => if (Nat.unpair v).1 = 1 ∧ (Nat.unpair v).2 = 1 then 1 else 0) :=
    Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0)
  exact (total_comp (total_primrec hf) (total_pair hP hQ)).of_eq (fun x => by
    by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq])

theorem quant_and (s : Bool) (P Q : ℕ → Prop) :
    (Quant s P ∧ Quant s Q) ↔
      Quant s (fun v => P (Nat.unpair v).1 ∧ Q (Nat.unpair v).2) := by
  cases s
  · simp only [Quant, Bool.false_eq_true, ↓reduceIte]
    exact ⟨fun h v => ⟨h.1 _, h.2 _⟩,
      fun h => ⟨fun a => by simpa using (h (Nat.pair a 0)).1,
        fun b => by simpa using (h (Nat.pair 0 b)).2⟩⟩
  · simp only [Quant, ↓reduceIte]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨Nat.pair a b, by simpa using And.intro ha hb⟩
    · rintro ⟨v, ha, hb⟩
      exact ⟨⟨_, ha⟩, ⟨_, hb⟩⟩

theorem Form.and {Y n s P Q} (hP : Form Y n s P) (hQ : Form Y n s Q) :
    Form Y n s (fun x => P x ∧ Q x) := by
  induction n generalizing s P Q with
  | zero => exact recursive_and hP hQ
  | succ n ih =>
    obtain ⟨A, hA, heA⟩ := hP
    obtain ⟨B, hB, heB⟩ := hQ
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    have h := ih (hA.comp (Primrec₂.natPair.comp f (f.comp r)))
      (hB.comp (Primrec₂.natPair.comp f (r.comp r)))
    refine ⟨_, h, fun x => ?_⟩
    simpa only [Nat.unpair_pair] using
      (and_congr (heA x) (heB x)).trans (quant_and s _ _)

theorem Form.or {Y n s P Q} (hP : Form Y n s P) (hQ : Form Y n s Q) :
    Form Y n s (fun x => P x ∨ Q x) := by
  have h := (hP.neg.and hQ.neg).neg
  simpa only [Bool.not_not, not_and_or, not_not] using h

theorem Form.raise {Y n s P} (h : Form Y n s P) : Form Y (n+1) s P := by
  induction n generalizing s P with
  | zero =>
    refine ⟨fun v => P (Nat.unpair v).1, recursive_comp h (Primrec.fst.comp Primrec.unpair), ?_⟩
    intro x
    cases s <;> simp [Quant]
  | succ n ih =>
    obtain ⟨Q, hQ, he⟩ := h
    exact ⟨Q, ih hQ, he⟩

theorem Form.switch {Y n s P} (h : Form Y n (!s) P) : Form Y (n+1) s P := by
  refine ⟨fun v => P (Nat.unpair v).1, h.comp (Primrec.fst.comp Primrec.unpair), ?_⟩
  intro x
  cases s <;> simp [Quant]

theorem Form.ex {Y n P} (h : Form Y (n + 1) true P) :
    Form Y (n+1) true (fun x => ∃ a, P (Nat.pair x a)) := by
  obtain ⟨Q, hQ, he⟩ := h
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  refine ⟨fun v => Q (Nat.pair (Nat.pair (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1)
    (Nat.unpair (Nat.unpair v).2).2),
    hQ.comp (Primrec₂.natPair.comp (Primrec₂.natPair.comp f (f.comp r)) (r.comp r)), ?_⟩
  intro x
  simp only [Quant, ↓reduceIte, Nat.unpair_pair]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := (he _).mp ha
    exact ⟨Nat.pair a b, by simpa using hb⟩
  · rintro ⟨v, hv⟩
    exact ⟨(Nat.unpair v).1, (he _).mpr ⟨(Nat.unpair v).2, hv⟩⟩

theorem Form.all {Y n P} (h : Form Y (n + 1) false P) :
    Form Y (n+1) false (fun x => ∀ a, P (Nat.pair x a)) := by
  have hh := h.neg.ex.neg
  simpa only [Bool.not_true, Bool.not_false, not_exists, not_not] using hh

end TuringRigidity.ArithmeticHierarchy

end OAI
