/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalLimits.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalComputability
public import LeanPool.TuringConeRigidity.CohenForcing.CohenCompleteness
public import LeanPool.TuringConeRigidity.Effective.CodingDiagonal
public import LeanPool.TuringConeRigidity.Effective.CodingExtraction

/-!
# Local Limits
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open LocalStage
noncomputable section
attribute [local instance] Classical.propDecidable

def G₀ (D : LocalInputs.Data) : Oracle := leftLimit (conditions D)
def G₁ (D : LocalInputs.Data) : Oracle := rightLimit (conditions D)

theorem generic_prefix_next (D : LocalInputs.Data) (s : ℕ) :
    (generic D (construction D s)).left <+: (conditions D (s+1)).left ∧
    (generic D (construction D s)).right <+: (conditions D (s+1)).right := by
  have h : (generic D (construction D s)).left <+: (stageWord D s (construction D s)).left ∧
      (generic D (construction D s)).right <+: (stageWord D s (construction D s)).right := by
    cases ha : stageAction D s (construction D s) with
    | none => simp [stageWord,ha]
    | some t =>
      have hc := candidate_extends D t (generic D (construction D s))
      exact ⟨by simpa [stageWord, ha, atLevel] using hc.1, by simpa [stageWord, ha, atLevel] using
        hc.2.1⟩
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

theorem limits_extend_generic (D : LocalInputs.Data) (s : ℕ) :
    CommonIdeal.Extends (G₀ D) (generic D (construction D s)).left ∧
    CommonIdeal.Extends (G₁ D) (generic D (construction D s)).right := by
  have hp := generic_prefix_next D s
  constructor
  · intro m hm
    have hh := (limits_extend (word_growth D) (length_bound D) (s+1) m (hm.trans_le
      hp.1.length_le)).1
    exact hh.trans (getD_of_prefix hp.1 hm)
  · intro m hm
    have hn : m < (conditions D (s+1)).left.length := by
      rw [(conditions D (s+1)).sameLength]
      exact hm.trans_le hp.2.length_le
    have hh := (limits_extend (word_growth D) (length_bound D) (s+1) m hn).2
    exact hh.trans (getD_of_prefix hp.2 hm)

theorem meets_dense (D : LocalInputs.Data) {P : ℕ → Prop} (hP : Sigma D.B 1 P)
    (hdense : ∀ p : Condition, ∃ q : ℕ, Extends D.F p (condition q) ∧ P q) :
    ∃ q : ℕ, P q ∧ CommonIdeal.Extends (G₀ D) (condition q).left ∧
      CommonIdeal.Extends (G₁ D) (condition q).right := by
  obtain ⟨e,he⟩ := EffectiveCohen.sigma1_enumeration hP
  obtain ⟨s,hs,_⟩ := surviving_generic_visit D e
  let p := construction D s
  let q := openProcedure D (Nat.pair e (code p.condition))
  have hdec := (D.open_spec e (code p.condition)).2
  change OracleJump.Halts D.B e q ∨
    (q = code p.condition ∧
      ∀ r, Extends D.F (condition (code p.condition)) (condition r) → ¬ OracleJump.Halts D.B e r)
        at hdec
  have hq : P q := by
    rcases hdec with h | ⟨_,h⟩
    · exact (he q).mpr h
    · obtain ⟨r,hr,hR⟩ := hdense (condition (code p.condition))
      exact False.elim (h r hr ((he r).mp hR))
  refine ⟨q,hq,?_⟩
  have hh := limits_extend_generic D s
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

theorem reads_not_reduces (D : LocalInputs.Data) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction D.B} (fun n => Part.some (loc n)))
    (hunbounded : ∀ N, ∃ n, N ≤ loc n) : ¬ Reduces (fun n => G₀ D (loc n)) D.B := by
  intro hX
  let X : Oracle := fun n => G₀ D (loc n)
  have hP : Sigma D.B 1 (fun p => ∃ n, loc n < (left p).length ∧ (left p).getD (loc n) false ≠ X
    n) := by
    simpa only [Nat.unpair_pair] using
      (Form.raise (n := 0) (s := true) (disagreement_recursive D.B X loc hloc hX)).ex
  have hdense : ∀ p : Condition, ∃ q : ℕ, Extends D.F p (condition q) ∧
      ∃ n, loc n < (left q).length ∧ (left q).getD (loc n) false ≠ X n := by
    intro p
    obtain ⟨n,hn⟩ := hunbounded p.left.length
    obtain ⟨q,hpq,hql,hqb⟩ := CodingDiagonal.prescribe D.F p (loc n) hn (!(X n))
    refine ⟨code q,by simpa [condition_code] using hpq,n,?_,?_⟩
    · simpa only [show left (code q) = q.left from congrArg Condition.left (condition_code q)]
      using hql
    · rw [show left (code q) = q.left from congrArg Condition.left (condition_code q),hqb]
      cases X n <;> decide
  obtain ⟨q,⟨n,hn,hne⟩,hl,_⟩ := meets_dense D hP hdense
  exact hne (hl (loc n) hn).symm

theorem common_noncomputable_columns (D : LocalInputs.Data)
    (hA : ∀ k, {a | D.F k a = true}.Infinite) :
    ∀ k, ∃ C : Oracle, Reduces C (join (G₀ D) (D.F k)) ∧
      Reduces C (join (G₁ D) (D.F k)) ∧ ¬ Reduces C (D.F k) := by
  intro k
  obtain ⟨S,hS⟩ := surviving_columns D (k+1)
  let cutoff := (conditions D S).left.length
  let loc := CodingColumns.location (D.F k) (hA k) k cutoff
  have hcol : Reduces (D.F k) D.B := TableIndices.represents_reduces
    (D.codes_valid (k+1) k (Nat.lt_succ_self k))
  have hloc : Nat.RecursiveIn {oracleFunction D.B} (fun n => Part.some (loc n)) :=
    (CodingColumns.location_recursive (D.F k) (hA k) k cutoff).subst (fun f hf => by
      have he : f = oracleFunction (D.F k) := Set.mem_singleton_iff.mp hf
      subst f
      exact RecursiveIn.iff_nat.mp hcol)
  have hn := reads_not_reduces D loc hloc (fun N => ⟨N,CodingColumns.le_location _ _ _ _ _⟩)
  let C := CodingColumns.readColumn (D.F k) (hA k) k cutoff (G₀ D)
  have heq : C = CodingColumns.readColumn (D.F k) (hA k) k cutoff (G₁ D) := by
    funext n
    have hm := CodingColumns.location_mem (D.F k) (hA k) k cutoff n
    simp only [CodingColumns.column] at hm
    split at hm
    next h =>
      apply hS _ h.1
      · rw [h.2]; omega
      · simpa only [h.2] using hm
    next h => simp at hm
  exact ⟨C,CodingColumns.readColumn_reduces _ _ _ _ _,
    heq.symm ▸ CodingColumns.readColumn_reduces _ _ _ _ _,fun h => hn (reduces_trans h hcol)⟩

theorem effective_first_clause (D : LocalInputs.Data)
    (hA : ∀ k, {a | D.F k a = true}.Infinite) :
    Reduces (join (G₀ D) (G₁ D)) (D.bound) ∧
      ∀ k, ∃ C : Oracle, Reduces C (join (G₀ D) (D.F k)) ∧
        Reduces C (join (G₁ D) (D.F k)) ∧ ¬ Reduces C (D.F k) :=
  ⟨LocalComputability.limits_recursive D,common_noncomputable_columns D hA⟩

end
end TuringRigidity.LocalLimits

end OAI
