/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructibleSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.DefinablePower
public import LeanPool.TuringConeRigidity.SetModels.InternalInfinity

/-!
# Constructible Satisfaction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- Code a finite tuple by its length and its natural-number-indexed graph. -/
noncomputable def tupleCode {n : ℕ} (v : Fin n → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natSet n) (ZFSet.range (fun i : Fin n => ZFSet.pair (natSet i.val) (v i)))

theorem tupleCode_length {n m : ℕ} (v : Fin n → ZFSet.{u}) (w : Fin m → ZFSet.{u})
    (h : tupleCode v = tupleCode w) : n = m :=
  natSet_injective (ZFSet.pair_inj.mp h).1

theorem tupleCode_injective (n : ℕ) : Function.Injective (@tupleCode.{u} n) := by
  intro v w h
  have hg := (ZFSet.pair_inj.mp h).2
  funext i
  have hi : ZFSet.pair (natSet i.val) (v i) ∈
      ZFSet.range (fun j : Fin n => ZFSet.pair (natSet j.val) (w j)) := by
    rw [← hg]
    exact ZFSet.mem_range_self (f := fun index : Fin n => ZFSet.pair (natSet index.val) (v index)) i
  obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hi
  obtain ⟨he,hv⟩ := ZFSet.pair_inj.mp hj
  have hji : j = i := Fin.ext (natSet_injective he)
  subst j
  exact hv.symm

/-- The set of coded formula-and-tuple pairs satisfying the full set-theoretic truth relation
over `A`. -/
noncomputable def satisfactionSet (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun t : {t : Σ n : ℕ, SentenceForm × (Fin n → Conditions A) //
      t.2.1.bound ≤ t.1 ∧ t.2.1.Sat (A : Set ZFSet)
        (tupleEnv (fun i => label A (t.2.2 i)))} =>
    ZFSet.pair (natSet (Encodable.encode t.val.2.1))
      (tupleCode (fun i => label A (t.val.2.2 i))))

theorem satisfactionSet_spec (A : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) (hv : ∀ i, v i ∈ A) (hb : p.bound ≤ n) :
    ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v) ∈ satisfactionSet A ↔
      p.Sat (A : Set ZFSet) (tupleEnv v) := by
  rw [satisfactionSet,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨m,q,w⟩,hqm,hq⟩,he⟩
    obtain ⟨hp,ht⟩ := ZFSet.pair_inj.mp he
    have hqp : q = p := Encodable.encode_injective (natSet_injective hp)
    subst q
    have hmn : m = n := tupleCode_length _ _ ht
    subst m
    have hwv := tupleCode_injective n ht
    rwa [hwv] at hq
  · intro hs
    let w : Fin n → Conditions A := fun i => equivShrink A ⟨v i,hv i⟩
    have hw : (fun i => label A (w i)) = v := by
      funext i; simp [w,label]
    refine ⟨⟨⟨n,p,w⟩,hb,?_⟩,?_⟩
    · rwa [hw]
    · exact congrArg (fun v' => ZFSet.pair (natSet (Encodable.encode p)) (tupleCode v')) hw

theorem satisfactionSet_environment (A : ZFSet.{u}) (p : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, i < p.bound → e i ∈ A) :
    ZFSet.pair (natSet (Encodable.encode p))
      (tupleCode (fun i : Fin p.bound => e i)) ∈ satisfactionSet A ↔
      p.Sat (A : Set ZFSet) e := by
  rw [satisfactionSet_spec A p _ (fun i => he i i.isLt) (le_refl _)]
  exact p.finite_support _ _ _ (fun i hi => by simp [tupleEnv,hi])

end TuringRigidity.RelativeConstructible

end OAI
