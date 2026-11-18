/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Extracted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StageLimits.lean.
The density and common-column proofs separate the column family from its background oracle.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.StageEngine
public import LeanPool.TuringConeRigidity.CohenForcing.CohenCompleteness
public import LeanPool.TuringConeRigidity.Effective.CodingDiagonal

/-!
# Shared finite-injury limit arguments
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StageEngineLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open StageEngine
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Type} (I : StateInterface S) (procedures : Procedures) {F : ℕ → Oracle}
  (hpair : ∀ t p, Extends F (atLevel p t) (candidate procedures t p))
  (hopen : ∀ e p, Extends F p (condition (procedures.openProcedure (Nat.pair e (code p)))))
  {B : Oracle}
  (hdecision : ∀ e p, OracleJump.Halts B e (procedures.openProcedure (Nat.pair e (code p))) ∨
    ∀ r, Extends F (condition (procedures.openProcedure (Nat.pair e (code p)))) (condition r) →
      ¬ OracleJump.Halts B e r)
  (hcolumns : ∀ k, Reduces (F k) B)

/-- The left limit oracle of the supplied condition construction. -/
def G₀ : Oracle := leftLimit (conditions I procedures)
/-- The right limit oracle of the supplied condition construction. -/
def G₁ : Oracle := rightLimit (conditions I procedures)

include hpair in
theorem generic_prefix_next (s : ℕ) :
    (generic I procedures (construction I procedures s)).left <+: (conditions I procedures
      (s+1)).left ∧
    (generic I procedures (construction I procedures s)).right <+: (conditions I procedures
      (s+1)).right := by
  have h : (generic I procedures (construction I procedures s)).left <+: (stageWord I
    procedures s (construction I procedures s)).left ∧
      (generic I procedures (construction I procedures s)).right <+: (stageWord I procedures s
        (construction I procedures s)).right := by
    cases ha : stageAction I procedures s (construction I procedures s) with
    | none => simp [stageWord,ha]
    | some t =>
      have hc := hpair t (generic I procedures (construction I procedures s))
      exact ⟨by simpa [stageWord, ha, atLevel] using hc.1,
        by simpa [stageWord, ha, atLevel] using hc.2.1⟩
  rw [conditions_succ]
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

include hpair hopen in
theorem limits_extend_generic (s : ℕ) :
    CommonIdeal.Extends (G₀ I procedures) (generic I procedures (construction I procedures
      s)).left ∧
    CommonIdeal.Extends (G₁ I procedures) (generic I procedures (construction I procedures
      s)).right := by
  have hp := generic_prefix_next I procedures hpair s
  constructor
  · intro m hm
    have hh := (limits_extend (word_growth I procedures hpair hopen) (length_bound I procedures
      hpair hopen) (s+1) m
      (hm.trans_le hp.1.length_le)).1
    exact hh.trans (getD_of_prefix hp.1 hm)
  · intro m hm
    have hn : m < (conditions I procedures (s+1)).left.length := by
      rw [(conditions I procedures (s+1)).sameLength]
      exact hm.trans_le hp.2.length_le
    have hh := (limits_extend (word_growth I procedures hpair hopen) (length_bound I procedures
      hpair hopen)
      (s+1) m hn).2
    exact hh.trans (getD_of_prefix hp.2 hm)


include hpair hopen in
theorem limits_extend_action {s t : ℕ}
    (ha : stageAction I procedures s (construction I procedures s) = some t) :
    CommonIdeal.Extends (G₀ I procedures) (candidate procedures t (generic I procedures
      (construction I procedures s))).left ∧
    CommonIdeal.Extends (G₁ I procedures) (candidate procedures t (generic I procedures
      (construction I procedures s))).right :=
      by
  have hl : (candidate procedures t (generic I procedures (construction I procedures s))).left
    <+: (conditions I procedures
    (s+1)).left := by
    rw [conditions_succ]
    change _ <+: (stageWord I procedures s (construction I procedures s)).left ++ [false]
    simp only [stageWord,ha]
    exact List.prefix_append _ _
  have hr : (candidate procedures t (generic I procedures (construction I procedures s))).right
    <+: (conditions I procedures
    (s+1)).right :=
    by
    rw [conditions_succ]
    change _ <+: (stageWord I procedures s (construction I procedures s)).right ++ [false]
    simp only [stageWord,ha]
    exact List.prefix_append _ _
  constructor
  · intro m hm
    exact ((limits_extend (word_growth I procedures hpair hopen) (length_bound I procedures
      hpair hopen) (s+1) m
      (hm.trans_le
      hl.length_le)).1).trans
      (getD_of_prefix hl hm)
  · intro m hm
    have hn : m < (conditions I procedures (s+1)).left.length := by
      rw [(conditions I procedures (s+1)).sameLength]
      exact hm.trans_le hr.length_le
    exact ((limits_extend (word_growth I procedures hpair hopen) (length_bound I procedures
      hpair hopen) (s+1) m
      hn).2).trans (getD_of_prefix hr
      hm)

include hpair hopen hdecision in
theorem meets_dense {P : ℕ → Prop} (hP : Sigma B 1 P)
    (hdense : ∀ p : Condition, ∃ q : ℕ, Extends F p (condition q) ∧ P q) :
    ∃ q : ℕ, P q ∧ CommonIdeal.Extends (G₀ I procedures) (condition q).left ∧
      CommonIdeal.Extends (G₁ I procedures) (condition q).right := by
  obtain ⟨e,he⟩ := EffectiveCohen.sigma1_enumeration hP
  obtain ⟨s,hs,_⟩ := surviving_generic_visit I procedures e
  let p := construction I procedures s
  let q := procedures.openProcedure (Nat.pair e (code (I.condition p)))
  have hdec := hdecision e (I.condition p)
  have hq : P q := by
    rcases hdec with h | h
    · exact (he q).mpr h
    · obtain ⟨r,hr,hR⟩ := hdense (condition q)
      exact False.elim (h r hr ((he r).mp hR))
  refine ⟨q,hq,?_⟩
  have hh := limits_extend_generic I procedures hpair hopen s
  simpa only [generic,hs,p,q] using hh

theorem disagreement_recursive (A X : Oracle) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)))
    (hX : Reduces X A) : RecursivePred A (fun v =>
      loc (Nat.unpair v).2 < (left (Nat.unpair v).1).length ∧
      (left (Nat.unpair v).1).getD (loc (Nat.unpair v).2) false ≠ X (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hm := total_comp hloc (total_primrec r)
  have hx := total_comp (RecursiveIn.iff_nat.mp hX) (total_primrec r)
  have hp : Primrec (fun v : ℕ =>
      if (Nat.unpair (Nat.unpair v).2).1 < (left (Nat.unpair v).1).length ∧
        CommonIdeal.bit ((left (Nat.unpair v).1).getD (Nat.unpair (Nat.unpair v).2).1 false) ≠
          (Nat.unpair (Nat.unpair v).2).2 then 1 else 0) :=
    Primrec.ite ((Primrec.nat_lt.comp (f.comp r) (Primrec.list_length.comp (left_primrec.comp
      f))).and
      ((Primrec.eq.comp (CommonIdeal.bit_primrec.comp ((Primrec.list_getD false).comp
        (left_primrec.comp f) (f.comp r))) (r.comp r)).not)) (Primrec.const 1) (Primrec.const 0)
  have hh := total_comp (total_primrec hp) (total_pair (total_primrec f) (total_pair hm hx))
  have hbits (b c : Bool) : (CommonIdeal.bit b ≠ (if c then 1 else 0)) ↔ b ≠ c := by
    cases b <;> cases c <;> decide
  exact hh.of_eq (fun v => by
    simp only [Nat.unpair_pair,hbits]
    by_cases ht : loc (Nat.unpair v).2 < (left (Nat.unpair v).1).length ∧
        (left (Nat.unpair v).1).getD (loc (Nat.unpair v).2) false ≠ X (Nat.unpair v).2
    · simp only [ite_eq_left ht]
    · simp only [ite_eq_right ht])

include hpair hopen hdecision in
theorem reads_not_reduces (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction B} (fun n => Part.some (loc n)))
    (hunbounded : ∀ N, ∃ n, N ≤ loc n) : ¬ Reduces (fun n => G₀ I procedures (loc n)) B := by
  intro hX
  let X : Oracle := fun n => G₀ I procedures (loc n)
  have hP : Sigma B 1 (fun p => ∃ n, loc n < (left p).length ∧ (left p).getD (loc n) false ≠ X n)
    := by
    simpa only [Nat.unpair_pair] using
      (Form.raise (n := 0) (s := true) (disagreement_recursive B X loc hloc hX)).ex
  have hdense : ∀ p : Condition, ∃ q : ℕ, Extends F p (condition q) ∧
      ∃ n, loc n < (left q).length ∧ (left q).getD (loc n) false ≠ X n := by
    intro p
    obtain ⟨n,hn⟩ := hunbounded p.left.length
    obtain ⟨q,hpq,hql,hqb⟩ := CodingDiagonal.prescribe F p (loc n) hn (!(X n))
    refine ⟨code q,by simpa [condition_code] using hpq,n,?_,?_⟩
    · simpa only [show left (code q) = q.left from congrArg Condition.left (condition_code q)]
      using hql
    · rw [show left (code q) = q.left from congrArg Condition.left (condition_code q),hqb]
      cases X n <;> decide
  obtain ⟨q,⟨n,hn,hne⟩,hl,_⟩ := meets_dense I procedures hpair hopen hdecision hP hdense
  exact hne (hl (loc n) hn).symm

include hpair hopen hdecision hcolumns in
theorem common_noncomputable_columns
    (hA : ∀ k, {a | F k a = true}.Infinite) :
    ∀ k, ∃ Z : Oracle, Reduces Z (join (G₀ I procedures) (F k)) ∧
      Reduces Z (join (G₁ I procedures) (F k)) ∧ ¬ Reduces Z (F k) := by
  intro k
  obtain ⟨S,hS⟩ := surviving_columns I procedures hpair hopen (k+1)
  let cutoff := (conditions I procedures S).left.length
  let loc := CodingColumns.location (F k) (hA k) k cutoff
  have hcol : Reduces (F k) B := hcolumns k
  have hloc : Nat.RecursiveIn {oracleFunction B} (fun n => Part.some (loc n)) :=
    (CodingColumns.location_recursive (F k) (hA k) k cutoff).subst (fun f hf => by
      have he : f = oracleFunction (F k) := Set.mem_singleton_iff.mp hf
      subst f
      exact RecursiveIn.iff_nat.mp hcol)
  have hn := reads_not_reduces I procedures hpair hopen hdecision loc hloc
    (fun N => ⟨N,CodingColumns.le_location _ _ _ _ _⟩)
  let Z := CodingColumns.readColumn (F k) (hA k) k cutoff (G₀ I procedures)
  have heq : Z = CodingColumns.readColumn (F k) (hA k) k cutoff (G₁ I procedures) := by
    funext n
    have hm := CodingColumns.location_mem (F k) (hA k) k cutoff n
    simp only [CodingColumns.column] at hm
    split at hm
    next h =>
      apply hS _ h.1
      · rw [h.2]; omega
      · simpa only [h.2] using hm
    next h => simp at hm
  exact ⟨Z,CodingColumns.readColumn_reduces _ _ _ _ _,
    heq.symm ▸ CodingColumns.readColumn_reduces _ _ _ _ _,fun h => hn (reduces_trans h hcol)⟩


end
end TuringRigidity.StageEngineLimits

end OAI
