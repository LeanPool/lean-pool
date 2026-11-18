/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticModelDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.DecodingTheorem
public import LeanPool.TuringConeRigidity.Computability.ArithmeticBounded

/-!
# Arithmetic Model Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticModelDecoding
open IndexPresentation IndexTuples ArithmeticHierarchy DecodingTheorem
open SetCoding RelationCoding BoundedDecoding OracleJump

/-- The singleton degree tuple used to query a unary relation code. -/
def one (a : Degree) : Fin 1 → Degree := ![a]
/-- The ordered degree pair used to query a binary relation code. -/
def two (a b : Degree) : Fin 2 → Degree := ![a,b]
/-- Natural-number code of a singleton index tuple. -/
def oneIndex (a : ℕ) : ℕ := Nat.pair a 0
/-- Natural-number code of a pair of indices. -/
def twoIndex (a b : ℕ) : ℕ := Nat.pair a (Nat.pair b 0)

theorem oneIndex_primrec : Primrec oneIndex := Primrec₂.natPair.comp Primrec.id (Primrec.const 0)
theorem twoIndex_primrec : Primrec₂ twoIndex :=
  Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))

theorem presented_one {Y p a} (ha : Dom Y a) :
    Presented Y p (oneIndex a) ↔ p.Holds (one (value Y a)) := by
  have ht : (fun i : Fin 1 => value Y (entry i.val (oneIndex a))) = one (value Y a) := by
    funext i
    fin_cases i
    simp [entry,oneIndex,one]
  have hd : ∀ i : Fin 1, Dom Y (entry i.val (oneIndex a)) := by
    intro i
    fin_cases i
    simpa [entry,oneIndex] using ha
  simp only [Presented,hd,forall_const,true_and,ht]

theorem presented_two {Y p a b} (ha : Dom Y a) (hb : Dom Y b) :
    Presented Y p (twoIndex a b) ↔ p.Holds (two (value Y a) (value Y b)) := by
  have ht : (fun i : Fin 2 => value Y (entry i.val (twoIndex a b))) = two (value Y a) (value Y b)
    := by
    funext i
    fin_cases i <;> simp [entry,twoIndex,two]
  have hd : ∀ i : Fin 2, Dom Y (entry i.val (twoIndex a b)) := by
    intro i
    fin_cases i
    · simpa [entry,twoIndex] using ha
    · simpa [entry,twoIndex] using hb
  simp only [Presented,hd,forall_const,true_and,ht]

/-- A copy of a natural-number successor structure with a distinguished predicate in the
degrees. -/
structure Copy (U : ℕ → Prop) where
  /-- The degree representing each natural number in the copy. -/
  node : ℕ → Degree
  injective : Function.Injective node
  /-- The binary relation code representing successor on the copy. -/
  successor : RelationCode 2
  /-- The unary relation code representing the distinguished predicate on the copy. -/
  predicate : RelationCode 1
  successor_spec : ∀ a b, successor.Holds (two a b) ↔ ∃ k, a = node k ∧ b = node (k+1)
  predicate_spec : ∀ a, predicate.Holds (one a) ↔ ∃ k, U k ∧ a = node k

/-- A coded successor path starting at an index equivalent to `z` in the presentation. -/
def Path (Y : Oracle) (S : RelationCode 2) (z n t : ℕ) : Prop :=
  Dom Y (item t 0) ∧ LE Y (item t 0) z ∧ LE Y z (item t 0) ∧
    ∀ i < n, Presented Y S (twoIndex (item t i) (item t (i+1)))

/-- The predicate holds at the endpoint of a coded successor path of length `n`. -/
def Defined (Y : Oracle) (S : RelationCode 2) (P : RelationCode 1) (z n : ℕ) : Prop :=
  ∃ t, Path Y S z n t ∧ Presented Y P (oneIndex (item t n))

theorem defined_sigma (Y : Oracle) (S : RelationCode 2) (P : RelationCode 1) (z : ℕ)
    (hS : RelationBelow S (degree Y)) (hP : RelationBelow P (degree Y)) :
    Sigma Y 5 (Defined Y S P z) := by
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
  have hp := (RelationPresentation.sigma5_decoding Y P hP).comp
    (oneIndex_primrec.comp (item_primrec.comp r f))
  exact (((hd.and (hl.and (hr.and hs))).and hp).ex).congr (fun v => by
    simp only [Nat.unpair_pair,Defined,Path,Presented])

theorem path_node {U Y} (c : Copy U) {z : ℕ} (hz : Dom Y z) (he : value Y z = c.node 0)
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

theorem node_below {U} (Y : Oracle) (c : Copy U)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) : c.node n ≤ degree Y := by
  have hs := (c.successor_spec (c.node n) (c.node (n+1))).mpr ⟨n,rfl,rfl⟩
  obtain ⟨d,hd,_⟩ := hs
  exact (graph_bounded (hS.1 0) (hd 0)).1

theorem defined_iff {U Y} (c : Copy U) {z : ℕ} (hz : Dom Y z) (he : value Y z = c.node 0)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) :
    Defined Y c.successor c.predicate z n ↔ U n := by
  constructor
  · rintro ⟨t,hpath,hp⟩
    have hn := path_node c hz he hpath n le_rfl
    obtain ⟨k,hUk,hk⟩ := (c.predicate_spec _).mp ((presented_one hn.1).mp hp)
    have hkn := c.injective (hk.symm.trans hn.2)
    exact hkn ▸ hUk
  · intro hU
    choose e hd hev using (fun i => value_surjective Y (c.node i) (node_below Y c hS i))
    obtain ⟨t,ht⟩ := (exists_items (n+1) (fun i a => a = e i)).mp
      (fun i _ => ⟨e i,rfl⟩)
    have hdom (i : ℕ) (hi : i ≤ n) : Dom Y (item t i) := by rw [ht i (by omega)]; exact hd i
    have hval (i : ℕ) (hi : i ≤ n) : value Y (item t i) = c.node i := by
      rw [ht i (by omega), hev i]
    refine ⟨t, ⟨hdom 0 (by omega), ?_, ?_, ?_⟩, ?_⟩
    · apply (le_iff (hdom 0 (by omega)) hz).mpr
      rw [hval 0 (by omega),he]
    · apply (le_iff hz (hdom 0 (by omega))).mpr
      rw [hval 0 (by omega),he]
    · intro i hi
      apply (presented_two (hdom i (by omega)) (hdom (i+1) (by omega))).mpr
      apply (c.successor_spec _ _).mpr
      exact ⟨i,hval i (by omega),hval (i+1) (by omega)⟩
    · apply (presented_one (hdom n le_rfl)).mpr
      exact (c.predicate_spec _).mpr ⟨n,hU,hval n le_rfl⟩

theorem unary_decoding {U} (Y : Oracle) (c : Copy U)
    (hS : RelationBelow c.successor (degree Y)) (hP : RelationBelow c.predicate (degree Y)) :
    Sigma Y 5 U ∧ RecursivePred (iterate Y 5) U := by
  obtain ⟨z,hz,he⟩ := value_surjective Y (c.node 0) (node_below Y c hS 0)
  have h := (defined_sigma Y c.successor c.predicate z hS hP).congr (defined_iff c hz he hS)
  exact ⟨h,form_recursive h⟩

end TuringRigidity.ArithmeticModelDecoding

end OAI
