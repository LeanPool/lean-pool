/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericParameters.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalPrimitiveRecursion
public import LeanPool.TuringConeRigidity.Syntax.SentenceCodeDefinability

/-!
# Numeric Parameters
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericSyntax
open BoundedSetTheory TransitiveNameModel BoundedDefinability SentenceCoding
universe u

/-- The numerical parameter environment containing omega, the finite-graph bound, and zero. -/
def params (Q : ZFSet.{u}) : ℕ → ZFSet.{u} :=
  cons ZFSet.omega (cons Q (fun _ => natSet 0))

/-- The set contains every finite initial graph of every natural-number function. -/
def Covers (Q : ZFSet.{u}) : Prop := ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ Q

/-- A bounded formula defines the predicate uniformly for every adequate finite-graph bound. -/
def Numeric (P : (ℕ → ZFSet.{u}) → Prop) : Prop :=
  ∃ p : Formula, ∀ Q, Covers Q → ∀ e, p.Eval (mix e (params Q)) ↔ P e

variable {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Numeric.congr (h : Numeric P) (he : ∀ e, P e ↔ Q e) : Numeric Q := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun B hB e => (hp B hB e).trans (he e)⟩

theorem Numeric.subst (h : Numeric P) (r : ℕ → ℕ) : Numeric (fun e => P (e ∘ r)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p.rename (slotMap r id),?_⟩
  intro B hB e
  simpa only [Formula.eval_rename_comp,mix_slotMap,Function.comp_id] using hp B hB (e ∘ r)

theorem Numeric.neg (h : Numeric P) : Numeric (fun e => ¬ P e) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨.neg p,fun B hB e => not_congr (hp B hB e)⟩

theorem Numeric.and (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e ∧ Q e) := by
  obtain ⟨p,hp⟩ := h; obtain ⟨q,hq⟩ := k
  exact ⟨.conj p q,fun B hB e => and_congr (hp B hB e) (hq B hB e)⟩

theorem Numeric.existsMem (h : Numeric P) (i : ℕ) :
    Numeric (fun e => ∃ x ∈ e i, P (cons x e)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨.existsMem (2*i) (p.rename bindSlots),?_⟩
  intro B hB e
  simp only [Formula.Eval,mix_even,Formula.eval_rename_comp,bind_mix,hp B hB]

theorem Numeric.existsNat (h : Numeric P) :
    Numeric (fun e => ∃ x ∈ ZFSet.omega, P (cons x e)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨.existsMem 1 (p.rename bindSlots),?_⟩
  intro B hB e
  simp only [Formula.Eval,Formula.eval_rename_comp,bind_mix,hp B hB]
  rfl

theorem defOr (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e ∨ Q e) :=
  (h.neg.and k.neg).neg.congr (fun _ => by tauto)
theorem defImp (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e → Q e) :=
  (h.and k.neg).neg.congr (fun _ => by tauto)
theorem defIff (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e ↔ Q e) :=
  ((defImp h k).and (defImp k h)).congr (fun _ => iff_def.symm)
theorem defAllMem (h : Numeric P) (i : ℕ) : Numeric (fun e => ∀ x ∈ e i, P (cons x e)) :=
  (h.neg.existsMem i).neg.congr (fun _ => by simp)
theorem defAllNat (h : Numeric P) : Numeric (fun e => ∀ x ∈ ZFSet.omega, P (cons x e)) :=
  h.neg.existsNat.neg.congr (fun _ => by simp)

theorem equal_definable (i j : ℕ) : Numeric (fun e => e i = e j) :=
  ⟨.equal (2*i) (2*j),fun _ _ e => by simp [Formula.Eval]⟩
theorem member_definable (i j : ℕ) : Numeric (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ _ e => by simp [Formula.Eval]⟩
theorem memberNat (i : ℕ) : Numeric (fun e => e i ∈ ZFSet.omega) :=
  ⟨.member (2*i) 1,fun _ _ e => by simp [Formula.Eval,mix,params]⟩
theorem equalZero (i : ℕ) : Numeric (fun e => e i = natSet 0) :=
  ⟨.empty (2*i),fun _ _ e => by simp only [Formula.eval_empty,mix_even]; rfl⟩
theorem defSubset (i j : ℕ) : Numeric (fun e => e i ⊆ e j) :=
  defAllMem (member_definable 0 (j+1)) i
theorem defPairMem (i j g : ℕ) : Numeric (fun e => ZFSet.pair (e i) (e j) ∈ e g) :=
  ⟨.pairMem (2*i) (2*j) (2*g),fun _ _ e => by simp only [Formula.eval_pairMem,mix_even]⟩
theorem defOrderedPair (z i j : ℕ) : Numeric (fun e => e z = ZFSet.pair (e i) (e j)) :=
  ⟨.orderedPair (2*z) (2*i) (2*j),fun _ _ e => by simp only [Formula.eval_orderedPair,mix_even]⟩

theorem unaryGraph_definable (f : ℕ → ℕ) (hf : Primrec f) (i j : ℕ) :
    Numeric (fun e => UnaryGraph f (e i) (e j)) := by
  obtain ⟨p,hp⟩ := primitive_bounded_definition (Primrec.nat_iff.mp hf)
  refine ⟨.conj (.member (2*i) 1) (Formula.unary p 1 3 (2*i) (2*j)),?_⟩
  intro B hB e
  simp only [Formula.Eval,mix_even]
  change (e i ∈ ZFSet.omega ∧ (Formula.unary p 1 3 (2*i) (2*j)).Eval (mix e (params B))) ↔ _
  constructor
  · rintro ⟨hn,h⟩
    obtain ⟨n,hn⟩ := (mem_omega _).mp hn
    refine ⟨n,hn,?_⟩
    simpa only [mix_even] using (Formula.unary_spec hp 1 3 (2*i) (2*j) (mix e (params B)) rfl hB n
      (by simpa only [mix_even] using hn)).mp h
  · rintro ⟨n,hn,hj⟩
    exact ⟨(mem_omega _).mpr ⟨n,hn⟩,(Formula.unary_spec hp 1 3 (2*i) (2*j) (mix e (params B)) rfl
      hB n
      (by simpa only [mix_even] using hn)).mpr (by simpa only [mix_even] using hj)⟩

theorem binaryGraph_definable (f : ℕ → ℕ → ℕ) (hf : Primrec₂ f) (i j k : ℕ) :
    Numeric (fun e => BinaryGraph f (e i) (e j) (e k)) := by
  have hu : Primrec (Nat.unpaired f) := hf.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)
  obtain ⟨p,hp⟩ := primitive_bounded_definition (Primrec.nat_iff.mp hu)
  refine ⟨.conj (.member (2*i) 1) (.conj (.member (2*j) 1)
    (Formula.pairedUnary p 1 3 (2*i) (2*j) (2*k))),?_⟩
  intro B hB e
  simp only [Formula.Eval,mix_even]
  change (e i ∈ ZFSet.omega ∧ e j ∈ ZFSet.omega ∧
    (Formula.pairedUnary p 1 3 (2*i) (2*j) (2*k)).Eval (mix e (params B))) ↔ _
  have hs (a b : ℕ) (ha : e i = natSet a) (hb : e j = natSet b) :=
    Formula.pairedUnary_spec hp 1 3 (2*i) (2*j) (2*k) (mix e (params B)) rfl hB a b
      (by simpa only [mix_even] using ha) (by simpa only [mix_even] using hb)
  simp only [mix_even,Nat.unpaired,Nat.unpair_pair] at hs
  constructor
  · rintro ⟨ha,hb,h⟩
    obtain ⟨a,ha⟩ := (mem_omega _).mp ha
    obtain ⟨b,hb⟩ := (mem_omega _).mp hb
    exact ⟨a,b,ha,hb,(hs a b ha hb).mp h⟩
  · rintro ⟨a,b,ha,hb,hc⟩
    exact ⟨(mem_omega _).mpr ⟨a,ha⟩,(mem_omega _).mpr ⟨b,hb⟩,(hs a b ha hb).mpr hc⟩

end TuringRigidity.NumericSyntax

end OAI
