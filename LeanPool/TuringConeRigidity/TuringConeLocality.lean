/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeArithmetic
public import LeanPool.TuringConeRigidity.Effective.LocalUnary

/-!
# A one-sided arithmetic bound for a global cone isomorphism

This file decodes the copies transported in `TuringConeCoding`. If `B` represents
`e(0')`, and `X` represents `g(deg Y) = e^{-1}(a ⊔ deg Y)`, then

    X ≤T (Y ⊕ B)^(5).

This requires neither a regular representative of `e` nor one of `g`, and does
not assume that `e` preserves the jump. It is an arithmetic bound on individual
values, not a uniform or Borel selection of those values. The latter is still
needed for the unconditional cone-rigidity theorem.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeLocality

open IndexPresentation IndexTuples ArithmeticHierarchy ArithmeticModelDecoding
open SetCoding RelationCoding BoundedDecoding OracleJump
open ConeRigidity

/-- A program-index presentation of a relation interpreted above `a`. -/
def Presented {n : ℕ} (a : Degree) (Y : Oracle) (p : RelationCode n) (t : ℕ) : Prop :=
  (∀ i : Fin n, Dom Y (entry i.val t)) ∧
    ConeCoding.Holds a p (fun i => value Y (entry i.val t))

theorem presented_one {a Y p x} (hx : Dom Y x) :
    Presented a Y p (oneIndex x) ↔ ConeCoding.Holds a p (one (value Y x)) := by
  have ht : (fun i : Fin 1 => value Y (entry i.val (oneIndex x))) = one (value Y x) := by
    funext i
    fin_cases i
    simp [entry, oneIndex, one]
  have hd : ∀ i : Fin 1, Dom Y (entry i.val (oneIndex x)) := by
    intro i
    fin_cases i
    simpa [entry, oneIndex] using hx
  simp only [Presented, hd, forall_const, true_and, ht]

theorem presented_two {a Y p x z} (hx : Dom Y x) (hz : Dom Y z) :
    Presented a Y p (twoIndex x z) ↔
      ConeCoding.Holds a p (two (value Y x) (value Y z)) := by
  have ht : (fun i : Fin 2 => value Y (entry i.val (twoIndex x z))) =
      two (value Y x) (value Y z) := by
    funext i
    fin_cases i <;> simp [entry, twoIndex, two]
  have hd : ∀ i : Fin 2, Dom Y (entry i.val (twoIndex x z)) := by
    intro i
    fin_cases i
    · simpa [entry, twoIndex] using hx
    · simpa [entry, twoIndex] using hz
  simp only [Presented, hd, forall_const, true_and, ht]

def Path (a : Degree) (Y : Oracle) (S : RelationCode 2) (z n t : ℕ) : Prop :=
  Dom Y (item t 0) ∧ LE Y (item t 0) z ∧ LE Y z (item t 0) ∧
    ∀ i < n, Presented a Y S (twoIndex (item t i) (item t (i + 1)))

def Defined (a : Degree) (Y : Oracle) (S : RelationCode 2) (P : RelationCode 1)
    (z n : ℕ) : Prop :=
  ∃ t, Path a Y S z n t ∧ Presented a Y P (oneIndex (item t n))

theorem defined_sigma (a : Degree) (Y : Oracle) (ha : a ≤ degree Y)
    (S : RelationCode 2) (P : RelationCode 1) (z : ℕ)
    (hS : RelationBelow S (degree Y)) (hP : RelationBelow P (degree Y)) :
    Sigma Y 5 (Defined a Y S P z) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let start := item_primrec.comp r (Primrec.const 0)
  have hd : Sigma Y 5 (fun v => Dom Y (item (Nat.unpair v).2 0)) :=
    (dom_pi Y start).switch.raise.raise
  have hl := (le_sigma Y start (Primrec.const z)).raise.raise
  have hr := (le_sigma Y (Primrec.const z) start).raise.raise
  have hs := ((ConeArithmetic.sigma5_decoding a Y ha S hS).comp
    (twoIndex_primrec.comp (item_primrec.comp (r.comp f) r)
      (item_primrec.comp (r.comp f) (Primrec.succ.comp r)))).bounded_all f
  have hp := (ConeArithmetic.sigma5_decoding a Y ha P hP).comp
    (oneIndex_primrec.comp (item_primrec.comp r f))
  exact (((hd.and (hl.and (hr.and hs))).and hp).ex).congr (fun v => by
    simp only [Nat.unpair_pair, Defined, Path, Presented])

theorem path_node {a U Y} (c : ConeCoding.Copy a U) {z : ℕ}
    (hz : Dom Y z) (he : value Y z = (c.node 0).val)
    {n t : ℕ} (hpath : Path a Y c.successor z n t) :
    ∀ i, i ≤ n → Dom Y (item t i) ∧ value Y (item t i) = (c.node i).val := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨hpath.1, (le_antisymm ((le_iff hpath.1 hz).mp hpath.2.1)
      ((le_iff hz hpath.1).mp hpath.2.2.1)).trans he⟩
  | succ i ih =>
    have hprev := ih (by omega)
    have hs := hpath.2.2.2 i (by omega)
    have hnext : Dom Y (item t (i + 1)) := by
      simpa [twoIndex, entry] using hs.1 (1 : Fin 2)
    have hs' := (presented_two hprev.1 hnext).mp hs
    have hbase : a ≤ value Y (item t (i + 1)) := by
      obtain ⟨d, hd, _⟩ := hs'
      exact (hd 1).1
    let next : Set.Ici a := ⟨value Y (item t (i + 1)), Set.mem_Ici.mpr hbase⟩
    have hh : ConeCoding.Holds a c.successor (two (c.node i).val next.val) := by
      simpa only [hprev.2] using hs'
    obtain ⟨k, hk, hkn⟩ := (c.successor_spec _ _).mp hh
    have hki : k = i := (c.injective hk).symm
    refine ⟨hnext, ?_⟩
    simpa only [hki] using congrArg Subtype.val hkn

theorem node_below {a U} (Y : Oracle) (c : ConeCoding.Copy a U)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) : (c.node n).val ≤ degree Y := by
  have hs := (c.successor_spec (c.node n) (c.node (n + 1))).mpr ⟨n, rfl, rfl⟩
  obtain ⟨d, hd, _⟩ := hs
  exact (hd 0).2.1.trans (hS.1 0).1

theorem defined_iff {a U Y} (c : ConeCoding.Copy a U) {z : ℕ}
    (hz : Dom Y z) (he : value Y z = (c.node 0).val)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) :
    Defined a Y c.successor c.predicate z n ↔ U n := by
  constructor
  · rintro ⟨t, hpath, hp⟩
    have hn := path_node c hz he hpath n le_rfl
    have hp' : ConeCoding.Holds a c.predicate (one (c.node n).val) := by
      simpa only [hn.2] using (presented_one hn.1).mp hp
    obtain ⟨k, hUk, hk⟩ := (c.predicate_spec _).mp hp'
    have hkn : k = n := (c.injective hk).symm
    exact hkn ▸ hUk
  · intro hU
    choose e hd hev using (fun i => value_surjective Y (c.node i).val (node_below Y c hS i))
    obtain ⟨t, ht⟩ := (exists_items (n + 1) (fun i j => j = e i)).mp
      (fun i _ => ⟨e i, rfl⟩)
    have hdom (i : ℕ) (hi : i ≤ n) : Dom Y (item t i) := by
      rw [ht i (by omega)]
      exact hd i
    have hval (i : ℕ) (hi : i ≤ n) : value Y (item t i) = (c.node i).val := by
      rw [ht i (by omega), hev i]
    refine ⟨t, ⟨hdom 0 (by omega), ?_, ?_, ?_⟩, ?_⟩
    · apply (le_iff (hdom 0 (by omega)) hz).mpr
      rw [hval 0 (by omega), he]
    · apply (le_iff hz (hdom 0 (by omega))).mpr
      rw [hval 0 (by omega), he]
    · intro i hi
      apply (presented_two (hdom i (by omega)) (hdom (i + 1) (by omega))).mpr
      rw [hval i (by omega), hval (i + 1) (by omega)]
      exact (c.successor_spec _ _).mpr ⟨i, rfl, rfl⟩
    · apply (presented_one (hdom n le_rfl)).mpr
      rw [hval n le_rfl]
      exact (c.predicate_spec _).mpr ⟨n, hU, rfl⟩

/-- The transported unary predicate is recursive in the fifth jump of a bound
for its coding parameters. -/
theorem unary_decoding {U : ℕ → Prop} (a : Degree) (Y : Oracle) (ha : a ≤ degree Y)
    (c : ConeCoding.Copy a U) (hS : RelationBelow c.successor (degree Y))
    (hP : RelationBelow c.predicate (degree Y)) :
    Sigma Y 5 U ∧ RecursivePred (iterate Y 5) U := by
  obtain ⟨z, hz, he⟩ := value_surjective Y (c.node 0).val (node_below Y c hS 0)
  have h := (defined_sigma a Y ha c.successor c.predicate z hS hP).congr
    (defined_iff c hz he hS)
  exact ⟨h, form_recursive h⟩

/-- Pointwise inverse arithmetic control, with the single anchor `e(0')`.
No measurability, genericity, or jump-preservation hypothesis occurs. -/
theorem pullback_reduces_fifth_jump {a : Degree} (e : Degree ≃o Set.Ici a)
    (B : Oracle) (hB : degree B = (e (degree (jump FixedArithmetic.zero))).val)
    (X Y : Oracle) (hX : degree X = pullback e (degree Y)) :
    Reduces X (iterate (join Y B) 5) := by
  obtain ⟨c, hS, hP⟩ := LocalUnary.localized_copy X
  have hab : a ≤ degree B := hB.symm ▸ ConeCoding.base_le_image e _
  have hb : ConeCoding.image e (degree (join X (jump FixedArithmetic.zero))) =
      degree (join Y B) := by
    change ConeCoding.image e (degree X ⊔ degree (jump FixedArithmetic.zero)) = degree Y ⊔ degree B
    rw [ConeCoding.image_sup, hX]
    change (e (pullback e (degree Y))).val ⊔ (e (degree (jump FixedArithmetic.zero))).val = _
    rw [apply_pullback_val, ← hB]
    exact le_antisymm
      (sup_le (sup_le (hab.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hS' := ConeCoding.map_relation_below e c.successor _ hS
  have hP' := ConeCoding.map_relation_below e c.predicate _ hP
  rw [hb] at hS' hP'
  have ha : a ≤ degree (join Y B) := hab.trans (reduces_join_right Y B)
  have hrec := (unary_decoding a (join Y B) ha (ConeCoding.transportCopy e c) hS' hP').2
  apply RecursiveIn.iff_nat.mpr
  exact hrec.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction, hx])

/-- Degree-level packaging of the pointwise bound. It does not select the
witness `X` as a Borel function of `Y`. -/
theorem inverse_arithmetic_bound {a : Degree} (e : Degree ≃o Set.Ici a) (x : Degree) :
    ∃ X Y : Oracle, degree X = pullback e x ∧
      degree Y = x ⊔ (e (degree (jump FixedArithmetic.zero))).val ∧
      Reduces X (iterate Y 5) := by
  obtain ⟨Z, hZ⟩ := degree_surjective x
  obtain ⟨B, hB⟩ := degree_surjective (e (degree (jump FixedArithmetic.zero))).val
  obtain ⟨X, hX⟩ := degree_surjective (pullback e x)
  refine ⟨X, join Z B, hX, ?_, ?_⟩
  · change degree Z ⊔ degree B = _
    rw [hZ, hB]
  · apply pullback_reduces_fifth_jump e B hB X Z
    simpa only [hZ] using hX

end OAI.TuringRigidity.ConeLocality
