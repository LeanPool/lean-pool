/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RelationPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.AntichainDecoding
public import LeanPool.TuringConeRigidity.Computability.ArithmeticFinite
public import LeanPool.TuringConeRigidity.OrdinalCodes.IndexTuples

/-!
# Relation Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelationPresentation
open IndexPresentation IndexTuples ArithmeticHierarchy AntichainDecoding
open SetCoding RelationCoding BoundedDecoding

structure ACode where
  bound : ℕ
  left : ℕ
  right : ℕ

def ACode.Good (Y : Oracle) (p : ACode) : Prop :=
  Dom Y p.bound ∧ Dom Y p.left ∧ Dom Y p.right
noncomputable def ACode.decode (Y : Oracle) (p : ACode) : AntichainCode :=
  ⟨value Y p.bound, value Y p.left, value Y p.right⟩
def ACode.Holds (Y : Oracle) (p : ACode) (x : ℕ) : Prop :=
  Antichain Y p.bound p.left p.right x

theorem ACode.holds_iff {Y p x} (hp : ACode.Good Y p) (hx : Dom Y x) :
    p.Holds Y x ↔ (p.decode Y).Holds (value Y x) :=
  antichain_iff hp.1 hp.2.1 hp.2.2 hx

theorem ACode.sigma (Y : Oracle) (p : ACode) {x : ℕ → ℕ} (hx : Primrec x) :
    Sigma Y 5 (fun v => p.Holds Y (x v)) :=
  antichain_sigma Y (Primrec.const _) (Primrec.const _) (Primrec.const _) hx

theorem ACode.exists_code (Y : Oracle) (p : AntichainCode) (hp : AntichainBelow p (degree Y)) :
    ∃ q : ACode, q.Good Y ∧ q.decode Y = p := by
  obtain ⟨b, hb, eb⟩ := value_surjective Y p.bound hp.1
  obtain ⟨l, hl, el⟩ := value_surjective Y p.left hp.2.1
  obtain ⟨r, hr, er⟩ := value_surjective Y p.right hp.2.2
  exact ⟨⟨b,l,r⟩, ⟨hb,hl,hr⟩, by cases p; simp_all [ACode.decode]⟩

structure SCode where
  bound : ℕ
  tags : ACode
  decorated : ACode

def SCode.Good (Y : Oracle) (p : SCode) : Prop :=
  Dom Y p.bound ∧ p.tags.Good Y ∧ p.decorated.Good Y
noncomputable def SCode.decode (Y : Oracle) (p : SCode) : SetCode :=
  ⟨value Y p.bound, p.tags.decode Y, p.decorated.decode Y⟩
def SCode.Graph (Y : Oracle) (p : SCode) (x c : ℕ) : Prop :=
  LE Y x p.bound ∧ p.tags.Holds Y c ∧ p.decorated.Holds Y (joinIndex x c)

theorem SCode.graph_iff {Y p x c} (hp : SCode.Good Y p) (hx : Dom Y x) (hc : Dom Y c) :
    p.Graph Y x c ↔ (p.decode Y).Graph (value Y x) (value Y c) := by
  simp only [SCode.Graph, SetCode.Graph, SCode.decode, le_iff hx hp.1,
    ACode.holds_iff hp.2.1 hc, ACode.holds_iff hp.2.2 (join_dom hx hc), join_value hx hc]

theorem SCode.sigma (Y : Oracle) (p : SCode) {x c : ℕ → ℕ}
    (hx : Primrec x) (hc : Primrec c) : Sigma Y 5 (fun v => p.Graph Y (x v) (c v)) :=
  (le_sigma Y hx (Primrec.const _)).raise.raise.and
    ((p.tags.sigma Y hc).and (p.decorated.sigma Y (joinIndex_primrec.comp hx hc)))

theorem SCode.exists_code (Y : Oracle) (p : SetCode) (hp : SetBelow p (degree Y)) :
    ∃ q : SCode, q.Good Y ∧ q.decode Y = p := by
  obtain ⟨b, hb, eb⟩ := value_surjective Y p.bound hp.1
  obtain ⟨t, ht, et⟩ := ACode.exists_code Y p.tags hp.2.1
  obtain ⟨d, hd, ed⟩ := ACode.exists_code Y p.decorated hp.2.2
  exact ⟨⟨b,t,d⟩, ⟨hb,ht,hd⟩, by cases p; simp_all [SCode.decode]⟩

structure RCode (n : ℕ) where
  coordinates : Fin n → SCode
  tuples : ACode

def RCode.Good {n} (Y : Oracle) (p : RCode n) : Prop :=
  (∀ i, (p.coordinates i).Good Y) ∧ p.tuples.Good Y
noncomputable def RCode.decode {n} (Y : Oracle) (p : RCode n) : RelationCode n :=
  ⟨fun i => (p.coordinates i).decode Y, p.tuples.decode Y⟩

def RCode.Holds {n} (Y : Oracle) (p : RCode n) (v : ℕ) : Prop :=
  (∀ i : Fin n, Dom Y (entry i.val v)) ∧ ∃ t : ℕ,
    (∀ i : Fin n, Dom Y (entry i.val t) ∧
      (p.coordinates i).Graph Y (entry i.val v) (entry i.val t)) ∧
    p.tuples.Holds Y (supIndex n t)

theorem RCode.sigma {n} (Y : Oracle) (p : RCode n) : Sigma Y 5 (p.Holds Y) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hd : Sigma Y 5 (fun v => ∀ i : Fin n, Dom Y (entry i.val v)) :=
    Form.finite_all (fun i => (dom_pi Y (entry_primrec i.val)).switch.raise.raise)
  have hg : Sigma Y 5 (fun v => ∀ i : Fin n, Dom Y (entry i.val (Nat.unpair v).2) ∧
      (p.coordinates i).Graph Y (entry i.val (Nat.unpair v).1) (entry i.val (Nat.unpair v).2)) :=
    Form.finite_all (fun i => ((dom_pi Y ((entry_primrec i.val).comp s)).switch.raise.raise).and
      ((p.coordinates i).sigma Y ((entry_primrec i.val).comp f) ((entry_primrec i.val).comp s)))
  have ht := p.tuples.sigma Y ((supIndex_primrec n).comp s)
  exact (hd.and ((hg.and ht).ex)).congr (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem RCode.holds_iff {n Y} {p : RCode n} (hp : p.Good Y) (v : ℕ) :
    p.Holds Y v ↔ (∀ i : Fin n, Dom Y (entry i.val v)) ∧
      (p.decode Y).Holds (fun i => value Y (entry i.val v)) := by
  unfold RCode.Holds
  apply and_congr_right
  intro hv
  constructor
  · rintro ⟨t, ht, htuple⟩
    refine ⟨fun i => value Y (entry i.val t), fun i => ?_, ?_⟩
    · exact (SCode.graph_iff (hp.1 i) (hv i) (ht i).1).mp (ht i).2
    · have h := (ACode.holds_iff hp.2 (sup_dom (fun i => (ht i).1))).mp htuple
      simpa only [sup_value (fun i => (ht i).1), RCode.decode] using h
  · rintro ⟨c, hc, ht⟩
    have hb : ∀ i, c i ≤ degree Y := by
      intro i
      exact (hc i).2.1.1.1.trans (value_below Y (p.coordinates i).tags.bound)
    choose e he hev using (fun i => value_surjective Y (c i) (hb i))
    obtain ⟨t, het⟩ := tuple_surjective e
    have hdom : ∀ i : Fin n, Dom Y (entry i.val t) := fun i => (het i) ▸ he i
    have hval : (fun i : Fin n => value Y (entry i.val t)) = c := by
      funext i
      rw [het i, hev i]
    refine ⟨t, fun i => ⟨hdom i, ?_⟩, ?_⟩
    · apply (SCode.graph_iff (hp.1 i) (hv i) (hdom i)).mpr
      simpa only [het i, hev i, RCode.decode] using hc i
    · apply (ACode.holds_iff hp.2 (sup_dom hdom)).mpr
      rw [sup_value hdom, hval]
      exact ht

theorem RCode.exists_code {n} (Y : Oracle) (p : RelationCode n)
    (hp : RelationBelow p (degree Y)) : ∃ q : RCode n, q.Good Y ∧ q.decode Y = p := by
  choose c hc ec using (fun i => SCode.exists_code Y (p.coordinates i) (hp.1 i))
  obtain ⟨t, ht, et⟩ := ACode.exists_code Y p.tuples hp.2
  refine ⟨⟨c,t⟩, ⟨hc,ht⟩, ?_⟩
  cases p with
  | mk coords tuples =>
    simp only [RCode.decode]
    congr
    · funext i
      exact ec i

theorem sigma5_decoding {n} (Y : Oracle) (p : RelationCode n)
    (hp : RelationBelow p (degree Y)) :
    Sigma Y 5 (fun v => (∀ i : Fin n, Dom Y (entry i.val v)) ∧
      p.Holds (fun i => value Y (entry i.val v))) := by
  obtain ⟨q, hq, rfl⟩ := RCode.exists_code Y p hp
  exact (q.sigma Y).congr (RCode.holds_iff hq)

end TuringRigidity.RelationPresentation

end OAI
