/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalUnary.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalCoding
public import LeanPool.TuringConeRigidity.SetModels.FixedArithmetic

/-!
# Local Unary
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalUnary
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding
noncomputable section
attribute [local instance] Classical.propDecidable

theorem predicate_code (C A : Oracle)
    (hind : ∀ a₀ a₁ : Degree, a₀ ≤ degree C → a₁ ≤ degree C → ∀ i (F : Finset ℕ),
      a₀ ⊔ degree (columns A i) ≤ a₁ ⊔ F.sup (fun j => degree (columns A j)) ↔
        a₀ ≤ a₁ ∧ i ∈ F)
    (hlow : Reduces (jump (join C A)) (jump FixedArithmetic.zero)) (X : Oracle) :
    ∃ p : RelationCode 1, RelationBelow p (degree (join X (jump FixedArithmetic.zero))) ∧
      ∀ x, p.Holds (one x) ↔ ∃ k, X k = true ∧ x = degree (columns C k) := by
  by_cases hne : ∃ k, X k = true
  · obtain ⟨k₀,hk₀⟩ := hne
    let P := fun k => X k = true
    let select := EffectivePresentation.pick P k₀
    have hP : RecursivePred X P := by
      have hq : Nat.RecursiveIn {oracleFunction X} (oracleFunction X) := .oracle _
        (Set.mem_singleton _)
      exact hq.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction,P,hx])
    have hs := EffectivePresentation.pick_recursive hP k₀
    have hsel (k : ℕ) : X (select k) = true := by
      by_cases hk : X k = true
      · simpa only [select,EffectivePresentation.pick,P,ite_eq_left hk] using hk
      · simpa only [select,EffectivePresentation.pick,P,ite_eq_right hk] using hk₀
    have hfix (k : ℕ) (hk : X k = true) : select k = k := by
      simp only [select,EffectivePresentation.pick,P,ite_eq_left hk]
    let B := join C A
    let F := EffectiveFamilies.mix C A
    have hF : Reduces F B := EffectiveFamilies.mix_reduces C A
    have hcol (k : ℕ) : degree (columns C k) ≤ degree C :=
      CodingExtraction.column_projection_reduces C k
    have htag (x y : Degree) (hx : x ≤ degree C) (hy : y ≤ degree C) (i j : ℕ) :
        x ⊔ degree (columns A i) ≤ y ⊔ degree (columns A j) ↔ x ≤ y ∧ i = j := by
      simpa only [Finset.sup_singleton,Finset.mem_singleton] using hind x y hx hy i {j}
    have hAntiA : ∀ i j, degree (columns A i) ≤ degree (columns A j) →
        degree (columns A i) = degree (columns A j) := by
      intro i j h
      have hij := (htag ⊥ ⊥ bot_le bot_le i j).mp (by simpa only [bot_sup_eq] using h)
      exact congrArg (fun k => degree (columns A k)) hij.2
    have hAntiF : ∀ i j, degree (columns F (select i)) ≤ degree (columns F (select j)) →
        degree (columns F (select i)) = degree (columns F (select j)) := by
      intro i j h
      have hh : degree (columns C (select i)) ⊔ degree (columns A (select i)) ≤
          degree (columns C (select j)) ⊔ degree (columns A (select j)) := by
        rw [show F = EffectiveFamilies.mix C A from
          rfl,EffectiveFamilies.mix_column,EffectiveFamilies.mix_column] at h
        exact h
      have hij := (htag _ _ (hcol _) (hcol _) _ _).mp hh
      exact congrArg (fun k => degree (columns F k)) hij.2
    obtain ⟨pc,hpc,hpcspec⟩ := EffectiveFamilies.antichainCode_below (reduces_join_right C A) hAntiA
    obtain ⟨g₀,g₁,hg,hgspec⟩ := LocalCoding.selected_antichain hF select hs hAntiF
    let pt : AntichainCode := ⟨degree B,g₀,g₁⟩
    let ps : SetCode := ⟨degree C,pc,pt⟩
    have hB : degree B ≤ degree (join X (jump FixedArithmetic.zero)) :=
      (show degree B ≤ degree (jump B) from reduces_jump B).trans (hlow.trans (reduces_join_right
        _ _))
    have hj : degree (join X (jump B)) ≤ degree (join X (jump FixedArithmetic.zero)) :=
      join_mono (reduces_refl X) hlow
    have hps : SetBelow ps (degree (join X (jump FixedArithmetic.zero))) :=
      ⟨(show degree C ≤ degree B from reduces_join_left C A).trans hB,
        hpc.mono (hlow.trans (reduces_join_right _ _)),
        ⟨hB,(le_sup_left.trans hg).trans hj,(le_sup_right.trans hg).trans hj⟩⟩
    refine ⟨unary ps,unary_below hps,fun x => ?_⟩
    rw [unary_holds]
    constructor
    · rintro ⟨a,hx,ha,ht⟩
      obtain ⟨i,rfl⟩ := (hpcspec a).mp ha
      obtain ⟨j,hj⟩ := (hgspec (x ⊔ degree (columns A i))).mp ht
      have he : degree (columns C (select j)) ⊔ degree (columns A (select j)) =
          x ⊔ degree (columns A i) := by
        rw [show F = EffectiveFamilies.mix C A from rfl,EffectiveFamilies.mix_column] at hj
        exact hj
      have h₀ := (htag _ _ (hcol _) hx _ _).mp he.le
      have h₁ := (htag _ _ hx (hcol _) _ _).mp he.ge
      exact ⟨select j,hsel j,le_antisymm h₁.1 h₀.1⟩
    · rintro ⟨k,hk,rfl⟩
      refine ⟨degree (columns A k),hcol k,(hpcspec _).mpr ⟨k,rfl⟩,?_⟩
      apply (hgspec _).mpr
      refine ⟨k,?_⟩
      rw [hfix k hk,show F = EffectiveFamilies.mix C A from rfl,EffectiveFamilies.mix_column]
      rfl
  · refine ⟨EffectivePresentation.emptyRelation 1,EffectivePresentation.emptyRelation_below _
    _,fun x => ?_⟩
    constructor
    · intro h
      exact False.elim (EffectivePresentation.emptyRelation_holds 1 _ h)
    · rintro ⟨k,hk,_⟩
      exact False.elim (hne ⟨k,hk⟩)

theorem localized_copy (X : Oracle) : ∃ c : Copy (fun n => X n = true),
    RelationBelow c.successor (degree (join X (jump FixedArithmetic.zero))) ∧
      RelationBelow c.predicate (degree (join X (jump FixedArithmetic.zero))) := by
  obtain ⟨K⟩ := FixedArithmetic.frame_exists
  obtain ⟨A,_,hlow,hind⟩ := CohenColumns.uniform_low_independent K.C
  have hlow' : Reduces (jump (join K.C A)) (jump FixedArithmetic.zero) := by
    change degree (jump (join K.C A)) ≤ degree (jump FixedArithmetic.zero)
    rw [hlow]
    exact K.low
  obtain ⟨P,hP,hpspec⟩ := predicate_code K.C A hind hlow' X
  let c : Copy (fun n => X n = true) := ⟨fun k => degree (columns K.C k),K.injective,
    K.successor,P,K.spec,hpspec⟩
  exact ⟨c,K.below.mono (reduces_join_right _ _),hP⟩

end
end TuringRigidity.LocalUnary

end OAI
