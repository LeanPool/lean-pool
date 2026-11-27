/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseListSearch

/-!
# Computability of the sparse-list verifier

Every loop in the finite checker has an explicit total computability proof.
List multiplicities are computed by a bounded counter. Rational comparisons
use the canonical rational arithmetic already implemented in the project.
-/

@[expose] public section

namespace Klr.SparseListSearch

open AffineCode SparseSearch RationalComputability

/-- Count the true values of a Boolean predicate on an initial segment of the naturals. -/
def boundedCount (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => boundedCount p n + if p n then 1 else 0

theorem boundedCount_succ_shift (p : ℕ → Bool) (n : ℕ) :
    boundedCount p (n + 1) = (if p 0 then 1 else 0) +
      boundedCount (fun i => p (i + 1)) n := by
  induction n with
  | zero => simp [boundedCount]
  | succ n ih =>
    rw [boundedCount, ih, boundedCount, Nat.add_assoc]

theorem boundedCount_getD {β : Type*} (p : β → Bool) (l : List β) (d : β) :
    boundedCount (fun i => p (l.getD i d)) l.length = l.countP p := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.length_cons, boundedCount_succ_shift, List.countP_cons]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, Nat.add_comm]

theorem computable_boundedCount {α : Type*} [Primcodable α] {p : α → ℕ → Bool}
    (hp : Computable₂ p) : Computable (fun a : α × ℕ => boundedCount (p a.1) a.2) := by
  have ha : Computable (fun a : (α × ℕ) × (ℕ × ℕ) => a.1.1) :=
    Computable.fst.comp Computable.fst
  have hi : Computable (fun a : (α × ℕ) × (ℕ × ℕ) => a.2.1) :=
    Computable.fst.comp Computable.snd
  have hn : Computable (fun a : (α × ℕ) × (ℕ × ℕ) => a.2.2) :=
    Computable.snd.comp Computable.snd
  have hbit := (hp.comp ha hi).cond (Computable.const 1) (Computable.const 0)
  have hs := Primrec.nat_add.to_comp.comp hn hbit
  apply (Computable.nat_rec Computable.snd (Computable.const 0) hs.to₂).of_eq
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih =>
    simpa only [boundedCount, Nat.rec_add_one, Bool.cond_eq_ite] using
      congrArg (fun k => k + if p a.1 n then 1 else 0) ih

/-- Counting a computable Boolean predicate along a computable finite list is computable. -/
theorem computable_list_countP {α β : Type*} [Primcodable α] [Primcodable β]
    [Inhabited β] {f : α → List β} {p : α → β → Bool}
    (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).countP (p a)) := by
  have hg : Computable (fun a : α × ℕ => (f a.1).getD a.2 default) :=
    (Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst) Computable.snd
  have hc := (computable_boundedCount
    (p := fun a i => p a ((f a).getD i default)) (hp.comp Computable.fst hg)).comp
      (Computable.id.pair (Computable.list_length.comp hf))
  exact hc.of_eq fun a => boundedCount_getD (p a) (f a) default

theorem computable_countTrue : Computable (fun s : List Bool => s.countP id) :=
  computable_list_countP (p := fun _ b => b) Computable.id Computable.snd

theorem computable_universeSize : Computable universeSize := Computable.fst
theorem computable_supportSize : Computable supportSize := Computable.fst.comp Computable.snd
theorem computable_rowRank : Computable rowRank :=
  Computable.fst.comp (Computable.snd.comp Computable.snd)
theorem computable_listLength : Computable listLength :=
  Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
theorem computable_density : Computable density :=
  Computable.fst.comp
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
theorem computable_badFraction : Computable badFraction :=
  Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))

theorem computable_offSupportCheck : Computable₂ offSupportCheck := by
  have ha : Computable (fun p : ((Parameters × Entry) × ℕ) × ℕ => p.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun p : ((Parameters × Entry) × ℕ) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hj : Computable (fun p : ((Parameters × Entry) × ℕ) × ℕ => p.2) := Computable.snd
  have hm := (Primrec.list_getD false).to_comp.comp (Computable.fst.comp ha) hj
  have he := computable_entry.comp
    ((computable_rows.comp (Computable.snd.comp ha)).pair (hi.pair hj))
  have hb := Primrec.or.to_comp.comp hm (Primrec.not.to_comp.comp he)
  have hM : Computable (fun p : (Parameters × Entry) × ℕ => universeSize p.1.1) :=
    computable_universeSize.comp (Computable.fst.comp Computable.fst)
  have hrow := (EffectiveScan.computable_boundedAll
    (p := fun p : (Parameters × Entry) × ℕ => fun j =>
      p.1.2.1.getD j false || !entry (rows p.1.2.2) p.2 j) hb).comp
        (Computable.id.pair hM)
  have hr : Computable (fun p : Parameters × Entry => rowRank p.1) :=
    computable_rowRank.comp Computable.fst
  have hall := (EffectiveScan.computable_boundedAll
    (p := fun p : Parameters × Entry => fun i => EffectiveScan.boundedAll
      (fun j => p.2.1.getD j false || !entry (rows p.2.2) i j) (universeSize p.1))
      hrow).comp (Computable.id.pair hr)
  exact hall.of_eq fun _ => rfl

theorem computable_entryCheck : Computable₂ entryCheck := by
  have hp : Computable (fun p : Parameters × Entry => p.1) := Computable.fst
  have hm : Computable (fun p : Parameters × Entry => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hc : Computable (fun p : Parameters × Entry => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hlen := Primrec.eq.decide.to_comp.comp
    (Computable.list_length.comp hm) (computable_universeSize.comp hp)
  have hcard := Primrec.eq.decide.to_comp.comp
    (computable_countTrue.comp hm) (computable_supportSize.comp hp)
  have hw := Primrec.eq.decide.to_comp.comp
    (computable_width.comp hc) (computable_universeSize.comp hp)
  have hr := Primrec.eq.decide.to_comp.comp
    (computable_rank.comp hc) (computable_rowRank.comp hp)
  have hfinal := Primrec.and.to_comp.comp (computable_fullRank.comp hc) computable_offSupportCheck
  have h := Primrec.and.to_comp.comp hlen (Primrec.and.to_comp.comp hcard
    (Primrec.and.to_comp.comp hw (Primrec.and.to_comp.comp hr hfinal)))
  exact h.of_eq fun _ => rfl

theorem computable_incidenceCount :
    Computable (fun p : CodeList × ℕ => p.1.countP (fun a => a.1.getD p.2 false)) := by
  have hm : Computable (fun p : (CodeList × ℕ) × Entry => p.2.1) :=
    Computable.fst.comp Computable.snd
  have hi : Computable (fun p : (CodeList × ℕ) × Entry => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hb := (Primrec.list_getD false).to_comp.comp hm hi
  exact computable_list_countP (p := fun p : CodeList × ℕ => fun a : Entry =>
    a.1.getD p.2 false) Computable.fst hb.to₂

theorem computable_incidenceCheck : Computable₂ incidenceCheck := by
  have hp : Computable (fun p : (Parameters × CodeList) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hL : Computable (fun p : (Parameters × CodeList) × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hi : Computable (fun p : (Parameters × CodeList) × ℕ => p.2) := Computable.snd
  have hleft := Primrec.nat_mul.to_comp.comp (computable_universeSize.comp hp)
    (computable_incidenceCount.comp (hL.pair hi))
  have hright := Primrec.nat_mul.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (computable_supportSize.comp hp))
    (computable_listLength.comp hp)
  have hb := Primrec.nat_le.decide.to_comp.comp hleft hright
  have hM : Computable (fun p : Parameters × CodeList => universeSize p.1) :=
    computable_universeSize.comp Computable.fst
  have hall := (EffectiveScan.computable_boundedAll
    (p := fun p : Parameters × CodeList => fun i => decide
      (universeSize p.1 * p.2.countP (fun a => a.1.getD i false) ≤
        2 * supportSize p.1 * listLength p.1)) hb).comp (Computable.id.pair hM)
  exact hall.of_eq fun _ => rfl

theorem computable_failureCount : Computable (fun p : CodeList × List Bool =>
    p.1.countP (fun a => !maskedFullRank a.2 p.2)) := by
  have hc : Computable (fun p : (CodeList × List Bool) × Entry => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hd : Computable (fun p : (CodeList × List Bool) × Entry => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hb := Primrec.not.to_comp.comp (computable_maskedFullRank.comp hc hd)
  exact computable_list_countP (p := fun p : CodeList × List Bool => fun a : Entry =>
    !maskedFullRank a.2 p.2) Computable.fst hb.to₂

theorem computable_restrictionCheck : Computable (fun p : (Parameters × CodeList) × List Bool =>
    restrictionCheck p.1.1 p.1.2 p.2) := by
  have hp : Computable (fun p : (Parameters × CodeList) × List Bool => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hL : Computable (fun p : (Parameters × CodeList) × List Bool => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hd : Computable (fun p : (Parameters × CodeList) × List Bool => p.2) := Computable.snd
  have hbound := primrec_rat_mul.to_comp.comp (computable_density.comp hp)
    (primrec_rat_natCast.to_comp.comp (computable_universeSize.comp hp))
  have hcount := primrec_rat_natCast.to_comp.comp (computable_countTrue.comp hd)
  have hdense := primrec_rat_le.decide.to_comp.comp hbound hcount
  have hbad := primrec_rat_natCast.to_comp.comp (computable_failureCount.comp (hL.pair hd))
  have hbudget := primrec_rat_mul.to_comp.comp (computable_badFraction.comp hp)
    (primrec_rat_natCast.to_comp.comp (computable_listLength.comp hp))
  have hsmall := primrec_rat_le.decide.to_comp.comp hbad hbudget
  have hc := Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hdense) hsmall
  exact hc.of_eq fun _ => rfl

/-- The complete candidate-list checker is a proved total computable function. -/
theorem computable_check : Computable₂ check := by
  have hp : Computable (fun p : Parameters × CodeList => p.1) := Computable.fst
  have hL : Computable (fun p : Parameters × CodeList => p.2) := Computable.snd
  have hlength := Primrec.eq.decide.to_comp.comp
    (Computable.list_length.comp hL) (computable_listLength.comp hp)
  have hep : Computable (fun p : (Parameters × CodeList) × Entry => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hea : Computable (fun p : (Parameters × CodeList) × Entry => p.2) := Computable.snd
  have hentries := computable_list_all (p := fun p : Parameters × CodeList => entryCheck p.1)
    hL (computable_entryCheck.comp hep hea)
  have hwords := computable_words.comp (computable_universeSize.comp hp)
  have hrestrictions := computable_list_all
    (p := fun p : Parameters × CodeList => restrictionCheck p.1 p.2)
    hwords computable_restrictionCheck
  have hc := Primrec.and.to_comp.comp hlength (Primrec.and.to_comp.comp hentries
    (Primrec.and.to_comp.comp computable_incidenceCheck hrestrictions))
  exact hc.of_eq fun _ => rfl

theorem computablePred_good : ComputablePred (fun p : Parameters × CodeList =>
    Good (universeSize p.1) (supportSize p.1) (rowRank p.1) (listLength p.1)
      (density p.1) (badFraction p.1) p.2) := by
  have h : ComputablePred (fun p : Parameters × CodeList => check p.1 p.2 = true) :=
    ComputablePred.computable_iff.mpr ⟨_, computable_check, rfl⟩
  exact h.of_eq fun p => check_eq_true p.1 p.2

end Klr.SparseListSearch
