/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeArithmetic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeCoding

/-!
# Arithmetic presentation of relation codes in a principal cone

The extra lower-bound tests needed to interpret coding in `Ici a` do not
increase the existing Sigma-5 bound. A representative of `a` is assumed
computable in the bounding oracle `Y`; its index is a fixed natural parameter.
All witnesses and all minimality tests are then expressed using program indices.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeArithmetic

open IndexPresentation IndexTuples ArithmeticHierarchy SetCoding RelationCoding
open BoundedDecoding RelationPresentation

/-- Minimality restricted to degrees above the degree with index `k`. -/
def Minimal (Y : Oracle) (k b l r x : ℕ) : Prop :=
  ∀ w, Dom Y w → LE Y k w → AntichainDecoding.Nontrivial Y b l r w →
    LE Y w x → LE Y x w

/-- The represented degree lies above the cone base and is minimal for the cone-relative
nontriviality property. -/
def Antichain (Y : Oracle) (k b l r x : ℕ) : Prop :=
  LE Y k x ∧ AntichainDecoding.Nontrivial Y b l r x ∧ Minimal Y k b l r x

theorem minimal_pi (Y : Oracle) {k b l r x : ℕ → ℕ}
    (hk : Primrec k) (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Pi Y 4 (fun v => Minimal Y (k v) (b v) (l v) (r v) (x v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hd : Pi Y 4 (fun v => ¬ Dom Y (Nat.unpair v).2) := (dom_pi Y s).neg.switch.raise
  have hk' : Pi Y 4 (fun v => ¬ LE Y (k (Nat.unpair v).1) (Nat.unpair v).2) :=
    (le_sigma Y (hk.comp f) s).neg.raise
  have hn := (AntichainDecoding.nontrivial_sigma Y (hb.comp f) (hl.comp f) (hr.comp f) s).neg
  have hw : Pi Y 4 (fun v => ¬ LE Y (Nat.unpair v).2 (x (Nat.unpair v).1)) :=
    (le_sigma Y s (hx.comp f)).neg.raise
  have hxw : Pi Y 4 (fun v => LE Y (x (Nat.unpair v).1) (Nat.unpair v).2) :=
    (le_sigma Y (hx.comp f) s).switch
  exact ((hd.or (hk'.or (hn.or (hw.or hxw)))).all).congr (fun v => by
    simp only [Nat.unpair_pair, Minimal, imp_iff_not_or])

theorem antichain_sigma (Y : Oracle) {k b l r x : ℕ → ℕ}
    (hk : Primrec k) (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Sigma Y 5 (fun v => Antichain Y (k v) (b v) (l v) (r v) (x v)) :=
  (le_sigma Y hk hx).raise.raise.and
    ((AntichainDecoding.nontrivial_sigma Y hb hl hr hx).raise.and
      (minimal_pi Y hk hb hl hr hx).switch)

theorem antichain_iff {Y : Oracle} {k b l r x : ℕ}
    (hk : Dom Y k) (hb : Dom Y b) (hl : Dom Y l) (hr : Dom Y r) (hx : Dom Y x) :
    Antichain Y k b l r x ↔ ConeCoding.Antichain (value Y k)
      ⟨value Y b, value Y l, value Y r⟩ (value Y x) := by
  rw [← ConeCoding.local_antichain_iff (value Y k) (degree Y) _
    ⟨value_below Y b, value_below Y l, value_below Y r⟩]
  unfold Antichain ConeCoding.LocalAntichain
  rw [le_iff hk hx, AntichainDecoding.nontrivial_iff hb hl hr hx]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro hm w haw hw hn hle
    obtain ⟨i, hi, rfl⟩ := value_surjective Y w hw
    exact (le_iff hx hi).mp (hm i hi ((le_iff hk hi).mpr haw)
      ((AntichainDecoding.nontrivial_iff hb hl hr hi).mpr hn) ((le_iff hi hx).mpr hle))
  · intro hm w hw hkw hn hle
    exact (le_iff hx hw).mpr (hm (value Y w) ((le_iff hk hw).mp hkw) (value_below Y w)
      ((AntichainDecoding.nontrivial_iff hb hl hr hw).mp hn) ((le_iff hw hx).mp hle))

/-- The presentation-index antichain code holds above the represented cone base. -/
def ACodeHolds (Y : Oracle) (k : ℕ) (p : ACode) (x : ℕ) : Prop :=
  Antichain Y k p.bound p.left p.right x

theorem acode_iff {Y k p x} (hk : Dom Y k) (hp : ACode.Good Y p) (hx : Dom Y x) :
    ACodeHolds Y k p x ↔ ConeCoding.Antichain (value Y k) (p.decode Y) (value Y x) :=
  antichain_iff hk hp.1 hp.2.1 hp.2.2 hx

theorem acode_sigma (Y : Oracle) (k : ℕ) (p : ACode) {x : ℕ → ℕ} (hx : Primrec x) :
    Sigma Y 5 (fun v => ACodeHolds Y k p (x v)) :=
  antichain_sigma Y (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _) hx

/-- The represented value lies between the cone base and bound, with cone-relative tag and
decoration predicates. -/
def SCodeGraph (Y : Oracle) (k : ℕ) (p : SCode) (x c : ℕ) : Prop :=
  LE Y k x ∧ LE Y x p.bound ∧ ACodeHolds Y k p.tags c ∧
    ACodeHolds Y k p.decorated (joinIndex x c)

theorem scode_iff {Y k p x c} (hk : Dom Y k) (hp : SCode.Good Y p)
    (hx : Dom Y x) (hc : Dom Y c) :
    SCodeGraph Y k p x c ↔ ConeCoding.Graph (value Y k) (p.decode Y) (value Y x) (value Y c) := by
  simp only [SCodeGraph, ConeCoding.Graph, SCode.decode, le_iff hk hx, le_iff hx hp.1,
    acode_iff hk hp.2.1 hc, acode_iff hk hp.2.2 (join_dom hx hc), join_value hx hc]

theorem scode_sigma (Y : Oracle) (k : ℕ) (p : SCode) {x c : ℕ → ℕ}
    (hx : Primrec x) (hc : Primrec c) : Sigma Y 5 (fun v => SCodeGraph Y k p (x v) (c v)) :=
  (le_sigma Y (Primrec.const _) hx).raise.raise.and
    ((le_sigma Y hx (Primrec.const _)).raise.raise.and
      ((acode_sigma Y k p.tags hc).and (acode_sigma Y k p.decorated (joinIndex_primrec.comp hx
        hc))))

/-- The represented tuple has valid indices and cone-relative tags satisfying the tuple
predicate after joining the base. -/
def RCodeHolds {n : ℕ} (Y : Oracle) (k : ℕ) (p : RCode n) (v : ℕ) : Prop :=
  (∀ i : Fin n, Dom Y (entry i.val v)) ∧ ∃ t : ℕ,
    (∀ i : Fin n, Dom Y (entry i.val t) ∧
      SCodeGraph Y k (p.coordinates i) (entry i.val v) (entry i.val t)) ∧
    ACodeHolds Y k p.tuples (joinIndex k (supIndex n t))

theorem rcode_sigma {n : ℕ} (Y : Oracle) (k : ℕ) (p : RCode n) :
    Sigma Y 5 (RCodeHolds Y k p) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hd : Sigma Y 5 (fun v => ∀ i : Fin n, Dom Y (entry i.val v)) :=
    Form.finite_all (fun i => (dom_pi Y (entry_primrec i.val)).switch.raise.raise)
  have hg : Sigma Y 5 (fun v => ∀ i : Fin n, Dom Y (entry i.val (Nat.unpair v).2) ∧
      SCodeGraph Y k (p.coordinates i) (entry i.val (Nat.unpair v).1) (entry i.val (Nat.unpair
        v).2)) :=
    Form.finite_all (fun i => ((dom_pi Y ((entry_primrec i.val).comp s)).switch.raise.raise).and
      (scode_sigma Y k (p.coordinates i) ((entry_primrec i.val).comp f) ((entry_primrec
        i.val).comp s)))
  have ht := acode_sigma Y k p.tuples
    (joinIndex_primrec.comp (Primrec.const k) ((supIndex_primrec n).comp s))
  exact (hd.and ((hg.and ht).ex)).congr (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem rcode_iff {n Y k} {p : RCode n} (hk : Dom Y k) (hp : p.Good Y) (v : ℕ) :
    RCodeHolds Y k p v ↔ (∀ i : Fin n, Dom Y (entry i.val v)) ∧
      ConeCoding.Holds (value Y k) (p.decode Y) (fun i => value Y (entry i.val v)) := by
  unfold RCodeHolds
  apply and_congr_right
  intro hv
  constructor
  · rintro ⟨t, ht, htuple⟩
    refine ⟨fun i => value Y (entry i.val t), fun i => ?_, ?_⟩
    · exact (scode_iff hk (hp.1 i) (hv i) (ht i).1).mp (ht i).2
    · have hh := (acode_iff hk hp.2 (join_dom hk (sup_dom (fun i => (ht i).1)))).mp htuple
      simpa only [join_value hk (sup_dom (fun i => (ht i).1)),
        sup_value (fun i => (ht i).1), RCode.decode] using hh
  · rintro ⟨c, hc, ht⟩
    have hb : ∀ i, c i ≤ degree Y := by
      intro i
      have htag := (hc i).2.2.1
      exact htag.2.1.1.trans (value_below Y (p.coordinates i).tags.bound)
    choose e he hev using (fun i => value_surjective Y (c i) (hb i))
    obtain ⟨t, het⟩ := tuple_surjective e
    have hdom : ∀ i : Fin n, Dom Y (entry i.val t) := fun i => (het i) ▸ he i
    have hval : (fun i : Fin n => value Y (entry i.val t)) = c := by
      funext i
      rw [het i, hev i]
    refine ⟨t, fun i => ⟨hdom i, ?_⟩, ?_⟩
    · apply (scode_iff hk (hp.1 i) (hv i) (hdom i)).mpr
      simpa only [het i, hev i, RCode.decode] using hc i
    · apply (acode_iff hk hp.2 (join_dom hk (sup_dom hdom))).mpr
      rw [join_value hk (sup_dom hdom), sup_value hdom, hval]
      exact ht

/-- A Sigma-5 presentation of a bounded relation interpreted in the cone. -/
theorem sigma5_decoding {n : ℕ} (a : Degree) (Y : Oracle) (ha : a ≤ degree Y)
    (p : RelationCode n) (hp : RelationBelow p (degree Y)) :
    Sigma Y 5 (fun v => (∀ i : Fin n, Dom Y (entry i.val v)) ∧
      ConeCoding.Holds a p (fun i => value Y (entry i.val v))) := by
  obtain ⟨k, hk, he⟩ := value_surjective Y a ha
  obtain ⟨q, hq, rfl⟩ := RCode.exists_code Y p hp
  have hh := (rcode_sigma Y k q).congr (rcode_iff hk hq)
  simpa only [he] using hh

end OAI.TuringRigidity.ConeArithmetic
