/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RelationCoding

/-!
# Bounded Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedDecoding
open AntichainParameters SetCoding RelationCoding

def AntichainBelow (p : AntichainCode) (y : Degree) : Prop :=
  p.bound ≤ y ∧ p.left ≤ y ∧ p.right ≤ y

def LocalNontrivial (y b g₀ g₁ x : Degree) : Prop :=
  x ≤ b ∧ ∃ z : Degree, z ≤ y ∧ z ≤ g₀ ⊔ x ∧ z ≤ g₁ ⊔ x ∧ ¬ z ≤ x

def LocalAntichain (y : Degree) (p : AntichainCode) (x : Degree) : Prop :=
  LocalNontrivial y p.bound p.left p.right x ∧
    ∀ w : Degree, w ≤ y → LocalNontrivial y p.bound p.left p.right w →
      w ≤ x → x ≤ w

theorem local_nontrivial_iff (y b g₀ g₁ x : Degree) (hb : b ≤ y) (hg₀ : g₀ ≤ y) :
    LocalNontrivial y b g₀ g₁ x ↔ NontrivialCommonLower b g₀ g₁ x := by
  constructor
  · rintro ⟨hx, z, _, hz₀, hz₁, hn⟩
    exact ⟨hx, z, hz₀, hz₁, hn⟩
  · rintro ⟨hx, z, hz₀, hz₁, hn⟩
    exact ⟨hx, z, hz₀.trans (sup_le hg₀ (hx.trans hb)), hz₀, hz₁, hn⟩

theorem local_antichain_iff (y : Degree) (p : AntichainCode) (hp : AntichainBelow p y)
    (x : Degree) : LocalAntichain y p x ↔ p.Holds x := by
  unfold LocalAntichain AntichainCode.Holds CodedAntichain
  simp only [local_nontrivial_iff y p.bound p.left p.right _ hp.1 hp.2.1]
  constructor
  · rintro ⟨hx, hmin⟩
    exact ⟨hx, fun w hw hle => hmin w (hw.1.trans hp.1) hw hle⟩
  · rintro ⟨hx, hmin⟩
    exact ⟨hx, fun w _ hw hle => hmin w hw hle⟩

def SetBelow (p : SetCode) (y : Degree) : Prop :=
  p.bound ≤ y ∧ AntichainBelow p.tags y ∧ AntichainBelow p.decorated y

def LocalGraph (y : Degree) (p : SetCode) (x c : Degree) : Prop :=
  x ≤ p.bound ∧ LocalAntichain y p.tags c ∧ LocalAntichain y p.decorated (x ⊔ c)

def LocalSet (y : Degree) (p : SetCode) (x : Degree) : Prop :=
  ∃ c : Degree, c ≤ y ∧ LocalGraph y p x c

theorem local_graph_iff (y : Degree) (p : SetCode) (hp : SetBelow p y) (x c : Degree) :
    LocalGraph y p x c ↔ p.Graph x c := by
  simp only [LocalGraph, SetCode.Graph, local_antichain_iff y p.tags hp.2.1,
    local_antichain_iff y p.decorated hp.2.2]

theorem graph_bounded {y : Degree} {p : SetCode} (hp : SetBelow p y)
    {x c : Degree} (h : p.Graph x c) : x ≤ y ∧ c ≤ y :=
  ⟨h.1.trans hp.1, h.2.1.1.1.trans hp.2.1.1⟩

theorem local_set_iff (y : Degree) (p : SetCode) (hp : SetBelow p y) (x : Degree) :
    LocalSet y p x ↔ p.Holds x := by
  simp only [LocalSet, local_graph_iff y p hp, SetCode.Holds]
  exact ⟨fun ⟨c, _, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨c, (graph_bounded hp hc).2, hc⟩⟩

def RelationBelow {n : ℕ} (p : RelationCode n) (y : Degree) : Prop :=
  (∀ i, SetBelow (p.coordinates i) y) ∧ AntichainBelow p.tuples y

def LocalRelation {n : ℕ} (y : Degree) (p : RelationCode n) (v : Fin n → Degree) : Prop :=
  ∃ c : Fin n → Degree, (∀ i, c i ≤ y ∧ LocalGraph y (p.coordinates i) (v i) (c i)) ∧
    LocalAntichain y p.tuples (Finset.univ.sup c)

theorem local_relation_iff {n : ℕ} (y : Degree) (p : RelationCode n)
    (hp : RelationBelow p y) (v : Fin n → Degree) :
    LocalRelation y p v ↔ p.Holds v := by
  unfold LocalRelation RelationCode.Holds
  simp only [local_antichain_iff y p.tuples hp.2, local_graph_iff y _ (hp.1 _)]
  constructor
  · rintro ⟨c, hc, ht⟩
    exact ⟨c, fun i => (hc i).2, ht⟩
  · rintro ⟨c, hc, ht⟩
    exact ⟨c, fun i => ⟨(graph_bounded (hp.1 i) (hc i)).2, hc i⟩, ht⟩

end TuringRigidity.BoundedDecoding

end OAI
