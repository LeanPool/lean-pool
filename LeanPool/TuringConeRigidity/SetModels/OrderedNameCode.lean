/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/OrderedNameCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExtensionBasicAxioms
public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Ordered Name Code
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

/-- The set code of an unordered-pair name with both children tagged by `t`. -/
noncomputable def pairNameCode (t x y : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair x t, ZFSet.pair y t}

/-- The set code of an ordered-pair name built from nested unordered-pair names. -/
noncomputable def orderedNameCode (t x y : ZFSet.{u}) : ZFSet.{u} :=
  pairNameCode t (pairNameCode t x x) (pairNameCode t x y)

theorem pairNameCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {t x y : ZFSet.{u}} (ht : t ∈ M) (hx : x ∈ M) (hy : y ∈ M) : pairNameCode t x y ∈ M :=
  pair_mem M hM hP (orderedPair_mem M hM hP hx ht) (orderedPair_mem M hM hP hy ht)

theorem orderedNameCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {t x y : ZFSet.{u}} (ht : t ∈ M) (hx : x ∈ M) (hy : y ∈ M) : orderedNameCode t x y ∈ M :=
  pairNameCode_mem M hM hP ht (pairNameCode_mem M hM hP ht hx hx)
    (pairNameCode_mem M hM hP ht hx hy)

namespace NameCodeFormula
open Formula

/-- Bounded formula characterizing the code of an unordered-pair name. -/
def pairName (t x y z : ℕ) : Formula :=
  .conj (allMem z (disj (orderedPair 0 (x+1) (t+1)) (orderedPair 0 (y+1) (t+1))))
    (.conj (.existsMem z (orderedPair 0 (x+1) (t+1)))
      (.existsMem z (orderedPair 0 (y+1) (t+1))))

theorem eval_pairName (t x y z : ℕ) (e : ℕ → ZFSet.{u}) :
    (pairName t x y z).Eval e ↔ e z = pairNameCode (e t) (e x) (e y) := by
  simp only [pairName,Formula.Eval,eval_allMem,eval_disj,eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨h,hx,hy⟩
    apply ZFSet.ext; intro w
    rw [pairNameCode,ZFSet.mem_pair]
    constructor
    · exact h w
    · rintro (rfl|rfl)
      · obtain ⟨v,hv,rfl⟩ := hx; exact hv
      · obtain ⟨v,hv,rfl⟩ := hy; exact hv
  · intro he
    rw [he]
    exact ⟨fun w hw => ZFSet.mem_pair.mp hw,
      ⟨_,ZFSet.mem_pair.mpr (Or.inl rfl),rfl⟩,
      ⟨_,ZFSet.mem_pair.mpr (Or.inr rfl),rfl⟩⟩

/-- A sigma formula characterizing the nested code of an ordered-pair name. -/
def orderedName (t x y z : ℕ) : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (pairName (t+2) (x+2) (x+2) 1)
    (.conj (pairName (t+2) (x+2) (y+2) 0) (pairName (t+2) 1 0 (z+2))))))

theorem realize_orderedName (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (t x y z : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (orderedName t x y z).Realize M e ↔ e z = orderedNameCode (e t) (e x) (e y) := by
  have matrix (a b : ZFSet.{u}) (ha : a ∈ M) (hb : b ∈ M) :
      (Formula.conj (pairName (t+2) (x+2) (x+2) 1)
        (.conj (pairName (t+2) (x+2) (y+2) 0) (pairName (t+2) 1 0 (z+2)))).Realize M
        (cons b (cons a e)) ↔ a = pairNameCode (e t) (e x) (e x) ∧
          b = pairNameCode (e t) (e x) (e y) ∧ e z = pairNameCode (e t) a b := by
    rw [Formula.absolute _ M hM _ (by
      intro i
      rcases i with _ | i
      · exact hb
      rcases i with _ | i
      · exact ha
      exact he i)]
    simp only [Formula.Eval,eval_pairName,cons_zero,cons_succ]
  change (∃ a ∈ M, ∃ b ∈ M, _) ↔ _
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    obtain ⟨rfl,rfl,h⟩ := (matrix a b ha hb).mp h
    exact h
  · intro h
    have ha := pairNameCode_mem M hM hP (he t) (he x) (he x)
    have hb := pairNameCode_mem M hM hP (he t) (he x) (he y)
    exact ⟨_,ha,_,hb,(matrix _ _ ha hb).mpr ⟨rfl,rfl,h⟩⟩
end NameCodeFormula

/-- The forcing name for the Kuratowski ordered pair of two names. -/
noncomputable def orderedPairName {P : Type u} [Top P] (a b : Name P) : Name P :=
  Name.pair (Name.pair a a) (Name.pair a b)

theorem encode_orderedPairName {P : Type u} [Top P] (l : P → ZFSet.{u}) (a b : Name P) :
    (orderedPairName a b).encode l = orderedNameCode (l ⊤) (a.encode l) (b.encode l) := by
  simp only [orderedPairName,encode_pair,orderedNameCode,pairNameCode]

theorem val_orderedPairName {P : Type u} [Top P] (G : Set P) (htop : ⊤ ∈ G) (a b : Name P) :
    (orderedPairName a b).val G = ZFSet.pair (a.val G) (b.val G) := by
  simp [orderedPairName,Name.val_pair G htop,ZFSet.pair]

end TuringRigidity.TransitiveNameModel

end OAI
