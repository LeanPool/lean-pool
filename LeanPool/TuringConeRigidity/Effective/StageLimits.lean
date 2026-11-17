/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StageLimits.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.StageComputability
public import LeanPool.TuringConeRigidity.CohenForcing.CohenCompleteness
public import LeanPool.TuringConeRigidity.Effective.CodingDiagonal
public import LeanPool.TuringConeRigidity.Effective.CodingExtraction

/-!
# Stage Limits
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StageLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open PriorityStage
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The left limit oracle of the priority condition construction. -/
def G₀ (A : Oracle) : Oracle := leftLimit (conditions A)
/-- The right limit oracle of the priority condition construction. -/
def G₁ (A : Oracle) : Oracle := rightLimit (conditions A)

theorem generic_prefix_next (A : Oracle) (s : ℕ) :
    (generic A (construction A s)).left <+: (conditions A (s+1)).left ∧
    (generic A (construction A s)).right <+: (conditions A (s+1)).right := by
  have h : (generic A (construction A s)).left <+: (stageWord A s (construction A s)).left ∧
      (generic A (construction A s)).right <+: (stageWord A s (construction A s)).right := by
    cases ha : stageAction A s (construction A s) with
    | none => simp [stageWord,ha]
    | some t =>
      have hc := candidate_extends A t (generic A (construction A s))
      exact ⟨by simpa [stageWord, ha, atLevel] using hc.1,
        by simpa [stageWord, ha, atLevel] using hc.2.1⟩
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

theorem limits_extend_generic (A : Oracle) (s : ℕ) :
    CommonIdeal.Extends (G₀ A) (generic A (construction A s)).left ∧
    CommonIdeal.Extends (G₁ A) (generic A (construction A s)).right := by
  have hp := generic_prefix_next A s
  constructor
  · intro m hm
    have hh := (limits_extend (word_growth A) (length_bound A) (s+1) m (hm.trans_le
      hp.1.length_le)).1
    exact hh.trans (getD_of_prefix hp.1 hm)
  · intro m hm
    have hn : m < (conditions A (s+1)).left.length := by
      rw [(conditions A (s+1)).sameLength]
      exact hm.trans_le hp.2.length_le
    have hh := (limits_extend (word_growth A) (length_bound A) (s+1) m hn).2
    exact hh.trans (getD_of_prefix hp.2 hm)

theorem meets_dense (A : Oracle) {P : ℕ → Prop} (hP : Sigma A 1 P)
    (hdense : ∀ p : Condition, ∃ q : ℕ, Extends (columns A) p (condition q) ∧ P q) :
    ∃ q : ℕ, P q ∧ CommonIdeal.Extends (G₀ A) (condition q).left ∧
      CommonIdeal.Extends (G₁ A) (condition q).right := by
  obtain ⟨e,he⟩ := EffectiveCohen.sigma1_enumeration hP
  obtain ⟨s,hs,_⟩ := surviving_generic_visit A e
  let p := construction A s
  let q := openProcedure A (Nat.pair e (code p.condition))
  have hdec := ((Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl
    A))).2
    e (code p.condition)).2
  change OracleJump.Halts A e q ∨
    (∀ r, Extends (columns A) (condition q) (condition r) → ¬ OracleJump.Halts A e r) at hdec
  have hq : P q := by
    rcases hdec with h | h
    · exact (he q).mpr h
    · obtain ⟨r,hr,hR⟩ := hdense (condition q)
      exact False.elim (h r hr ((he r).mp hR))
  refine ⟨q,hq,?_⟩
  have hh := limits_extend_generic A s
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

theorem reads_not_reduces (A : Oracle) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)))
    (hunbounded : ∀ N, ∃ n, N ≤ loc n) : ¬ Reduces (fun n => G₀ A (loc n)) A := by
  intro hX
  let X : Oracle := fun n => G₀ A (loc n)
  have hP : Sigma A 1 (fun p => ∃ n, loc n < (left p).length ∧ (left p).getD (loc n) false ≠ X n)
    := by
    simpa only [Nat.unpair_pair] using
      (Form.raise (n := 0) (s := true) (disagreement_recursive A X loc hloc hX)).ex
  have hdense : ∀ p : Condition, ∃ q : ℕ, Extends (columns A) p (condition q) ∧
      ∃ n, loc n < (left q).length ∧ (left q).getD (loc n) false ≠ X n := by
    intro p
    obtain ⟨n,hn⟩ := hunbounded p.left.length
    obtain ⟨q,hpq,hql,hqb⟩ := CodingDiagonal.prescribe (columns A) p (loc n) hn (!(X n))
    refine ⟨code q,by simpa [condition_code] using hpq,n,?_,?_⟩
    · simpa only [show left (code q) = q.left from congrArg Condition.left (condition_code q)]
      using hql
    · rw [show left (code q) = q.left from congrArg Condition.left (condition_code q),hqb]
      cases X n <;> decide
  obtain ⟨q,⟨n,hn,hne⟩,hl,_⟩ := meets_dense A hP hdense
  exact hne (hl (loc n) hn).symm

theorem common_noncomputable_columns (A : Oracle)
    (hA : ∀ k, {a | columns A k a = true}.Infinite) :
    ∀ k, ∃ C : Oracle, Reduces C (join (G₀ A) (columns A k)) ∧
      Reduces C (join (G₁ A) (columns A k)) ∧ ¬ Reduces C (columns A k) := by
  intro k
  obtain ⟨S,hS⟩ := surviving_columns A (k+1)
  let cutoff := (conditions A S).left.length
  let loc := CodingColumns.location (columns A k) (hA k) k cutoff
  have hcol : Reduces (columns A k) A := CodingExtraction.column_projection_reduces A k
  have hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)) :=
    (CodingColumns.location_recursive (columns A k) (hA k) k cutoff).subst (fun f hf => by
      have he : f = oracleFunction (columns A k) := Set.mem_singleton_iff.mp hf
      subst f
      exact RecursiveIn.iff_nat.mp hcol)
  have hn := reads_not_reduces A loc hloc (fun N => ⟨N,CodingColumns.le_location _ _ _ _ _⟩)
  let C := CodingColumns.readColumn (columns A k) (hA k) k cutoff (G₀ A)
  have heq : C = CodingColumns.readColumn (columns A k) (hA k) k cutoff (G₁ A) := by
    funext n
    have hm := CodingColumns.location_mem (columns A k) (hA k) k cutoff n
    simp only [CodingColumns.column] at hm
    split at hm
    next h =>
      apply hS _ h.1
      · rw [h.2]; omega
      · simpa only [h.2] using hm
    next h => simp at hm
  exact ⟨C,CodingColumns.readColumn_reduces _ _ _ _ _,
    heq ▸ CodingColumns.readColumn_reduces _ _ _ _ _,fun h => hn (reduces_trans h hcol)⟩

theorem effective_first_clause (A : Oracle)
    (hA : ∀ k, {a | columns A k a = true}.Infinite) :
    Reduces (join (G₀ A) (G₁ A)) (OracleJump.jump A) ∧
      ∀ k, ∃ C : Oracle, Reduces C (join (G₀ A) (columns A k)) ∧
        Reduces C (join (G₁ A) (columns A k)) ∧ ¬ Reduces C (columns A k) :=
  ⟨StageComputability.limits_recursive A,common_noncomputable_columns A hA⟩

end
end TuringRigidity.StageLimits

end OAI
