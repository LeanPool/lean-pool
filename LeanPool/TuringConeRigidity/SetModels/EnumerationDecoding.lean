/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/EnumerationDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalColumnIndices
public import LeanPool.TuringConeRigidity.Computability.ArithmeticModelDecoding

/-!
# Enumeration Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EnumerationDecoding
open IndexPresentation IndexTuples ArithmeticHierarchy DecodingTheorem
open SetCoding RelationCoding BoundedDecoding OracleJump ArithmeticModelDecoding

/-- A degree-coded successor chain together with a degree payload at every node. -/
structure Enumeration where
  /-- The injective sequence of degree nodes indexing the enumeration. -/
  node : ℕ → Degree
  injective : Function.Injective node
  /-- The degree value attached to each enumeration node. -/
  output : ℕ → Degree
  /-- The binary relation code for successor on the node sequence. -/
  successor : RelationCode 2
  /-- The binary relation code pairing each node with its enumerated degree value. -/
  payload : RelationCode 2
  successor_spec : ∀ a b, successor.Holds (two a b) ↔ ∃ k, a = node k ∧ b = node (k+1)
  payload_spec : ∀ a b, payload.Holds (two a b) ↔ ∃ k, a = node k ∧ b = output k

theorem path_node {Y} (c : Enumeration) {z : ℕ} (hz : Dom Y z) (he : value Y z = c.node 0)
    {n t : ℕ} (hpath : Path Y c.successor z n t) :
    ∀ i, i ≤ n → Dom Y (item t i) ∧ value Y (item t i) = c.node i := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨hpath.1, (le_antisymm ((le_iff hpath.1 hz).mp hpath.2.1)
      ((le_iff hz hpath.1).mp hpath.2.2.1)).trans he⟩
  | succ i ih =>
    have hprev := ih (by omega)
    have hs := hpath.2.2.2 i (by omega)
    have hnext : Dom Y (item t (i+1)) := by
      simpa [twoIndex,entry] using hs.1 (1 : Fin 2)
    obtain ⟨k,hk,hkn⟩ := (c.successor_spec _ _).mp ((presented_two hprev.1 hnext).mp hs)
    have hki : k = i := c.injective (hk.symm.trans hprev.2)
    exact ⟨hnext, by simpa [hki] using hkn⟩

theorem node_below (Y : Oracle) (c : Enumeration)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) : c.node n ≤ degree Y := by
  have hs := (c.successor_spec (c.node n) (c.node (n+1))).mpr ⟨n,rfl,rfl⟩
  obtain ⟨d,hd,_⟩ := hs
  exact (graph_bounded (hS.1 0) (hd 0)).1

theorem path_sigma (Y : Oracle) (S : RelationCode 2) (z : ℕ)
    (hS : RelationBelow S (degree Y)) : Sigma Y 5 (fun v => Path Y S z (Nat.unpair v).1
      (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let start := item_primrec.comp r (Primrec.const 0)
  have hd : Sigma Y 5 (fun v => Dom Y (item (Nat.unpair v).2 0)) :=
    (dom_pi Y start).switch.raise.raise
  have hl := (le_sigma Y start (Primrec.const z)).raise.raise
  have hr := (le_sigma Y (Primrec.const z) start).raise.raise
  have hs := ((RelationPresentation.sigma5_decoding Y S hS).comp
    (twoIndex_primrec.comp (item_primrec.comp (r.comp f) r)
      (item_primrec.comp (r.comp f) (Primrec.succ.comp r)))).bounded_all f
  exact (hd.and (hl.and (hr.and hs))).congr (fun v => by
    simp only [ArithmeticModelDecoding.Path,Presented,Nat.unpair_pair])

/-- A successor path from `z` ends at a node whose payload is the degree represented by `j`. -/
def Defined (Y : Oracle) (S P : RelationCode 2) (z n j : ℕ) : Prop :=
  ∃ t, Path Y S z n t ∧ Presented Y P (twoIndex (item t n) j)

theorem defined_sigma (Y : Oracle) (S P : RelationCode 2) (z : ℕ)
    (hS : RelationBelow S (degree Y)) (hP : RelationBelow P (degree Y)) :
    Sigma Y 5 (fun v => Defined Y S P z (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hs := (path_sigma Y S z hS).comp (Primrec₂.natPair.comp (f.comp f) r)
  have hp := (RelationPresentation.sigma5_decoding Y P hP).comp
    (twoIndex_primrec.comp (item_primrec.comp r (f.comp f)) (r.comp f))
  exact ((hs.and hp).ex).congr (fun v => by simp only [Defined,Presented,Nat.unpair_pair])

theorem defined_iff {Y} (c : Enumeration) {z j : ℕ} (hz : Dom Y z) (hj : Dom Y j)
    (he : value Y z = c.node 0) (hS : RelationBelow c.successor (degree Y)) (n : ℕ) :
    Defined Y c.successor c.payload z n j ↔ c.output n = value Y j := by
  constructor
  · rintro ⟨t,hpath,hp⟩
    have hn := path_node c hz he hpath n le_rfl
    obtain ⟨k,hk,hval⟩ := (c.payload_spec _ _).mp ((presented_two hn.1 hj).mp hp)
    have hkn := c.injective (hk.symm.trans hn.2)
    exact hkn ▸ hval.symm
  · intro hU
    choose e hd hev using (fun i => value_surjective Y (c.node i) (node_below Y c hS i))
    obtain ⟨t,ht⟩ := (exists_items (n+1) (fun i a => a = e i)).mp
      (fun i _ => ⟨e i,rfl⟩)
    have hdom (i : ℕ) (hi : i ≤ n) : Dom Y (item t i) := by rw [ht i (by omega)]; exact hd i
    have hval (i : ℕ) (hi : i ≤ n) : value Y (item t i) = c.node i := by
      rw [ht i (by omega),hev i]
    refine ⟨t,⟨hdom 0 (by omega),?_,?_,?_⟩,?_⟩
    · apply (le_iff (hdom 0 (by omega)) hz).mpr
      rw [hval 0 (by omega),he]
    · apply (le_iff hz (hdom 0 (by omega))).mpr
      rw [hval 0 (by omega),he]
    · intro i hi
      apply (presented_two (hdom i (by omega)) (hdom (i+1) (by omega))).mpr
      exact (c.successor_spec _ _).mpr ⟨i,hval i (by omega),hval (i+1) (by omega)⟩
    · apply (presented_two (hdom n le_rfl) hj).mpr
      exact (c.payload_spec _ _).mpr ⟨n,hval n le_rfl,hU.symm⟩

theorem graph_sigma {H Y : Oracle} (hHY : Reduces H Y) (c : Enumeration)
    (hS : RelationBelow c.successor (degree Y)) (hP : RelationBelow c.payload (degree Y)) :
    Sigma Y 5 (fun v => c.output (Nat.unpair v).1 = degree (EncodedForcing.columns H (Nat.unpair
      v).2)) := by
  obtain ⟨z,hz,he⟩ := value_surjective Y (c.node 0) (node_below Y c hS 0)
  obtain ⟨idx,hidx,hrep⟩ := LocalColumnIndices.uniform_indices hHY
  have hi := (defined_sigma Y c.successor c.payload z hS hP).comp
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (hidx.comp (Primrec.snd.comp Primrec.unpair)))
  apply hi.congr
  intro v
  simp only [Nat.unpair_pair]
  rw [defined_iff c hz ((TableIndices.valid_iff_represents _ _).mpr ⟨_,hrep _⟩) he hS]
  rw [value_eq (hrep _)]

end TuringRigidity.EnumerationDecoding

end OAI
