/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EffectivePresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.EffectiveRelations

/-!
# Effective Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectivePresentation
open EncodedForcing UniformOracle ArithmeticHierarchy EffectiveFamilies EffectiveRelations
open SetCoding RelationCoding BoundedDecoding AntichainParameters
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Keep an index satisfying `P`, and otherwise replace it by the fixed fallback index. -/
def pick (P : ℕ → Prop) (j₀ j : ℕ) : ℕ := if P j then j else j₀

theorem pick_recursive {A : Oracle} {P : ℕ → Prop} (hP : RecursivePred A P) (j₀ : ℕ) :
    Nat.RecursiveIn {oracleFunction A} (fun j => Part.some (pick P j₀ j)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := Primrec.ite (Primrec.eq.comp r (Primrec.const 1)) f (Primrec.const j₀)
  exact (total_comp (total_primrec hp) (total_pair (total_primrec Primrec.id) hP)).of_eq
    (fun j => by by_cases h : P j <;> simp [pick,h])

/-- Select presentation entries through `P`, replacing rejected indices by the chosen
fallback. -/
def selected (A : Oracle) (P : ℕ → Prop) (j₀ : ℕ) : Oracle := fun v =>
  A (Nat.pair (Nat.pair (Nat.unpair (Nat.unpair v).1).1
    (pick P j₀ (Nat.unpair (Nat.unpair v).1).2)) (Nat.unpair v).2)

theorem selected_reduces {A : Oracle} {P : ℕ → Prop} (hP : RecursivePred A P) (j₀ : ℕ) :
    Reduces (selected A P j₀) A := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := total_comp (pick_recursive hP j₀) (total_primrec (r.comp f))
  have hidx := total_pair (total_pair (total_primrec (f.comp f)) hp) (total_primrec r)
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  exact RecursiveIn.iff_nat.mpr (total_comp hq hidx)

@[simp] theorem selected_column (A : Oracle) (P : ℕ → Prop) (j₀ i j : ℕ) :
    columns (selected A P j₀) (Nat.pair i j) = columns A (Nat.pair i (pick P j₀ j)) := by
  funext n
  simp [selected,columns]

/-- The bottom-valued antichain code representing an empty coding family. -/
def emptyAntichain : AntichainCode := ⟨⊥,⊥,⊥⟩

theorem emptyAntichain_holds (x : Degree) : ¬ emptyAntichain.Holds x := by
  simp [emptyAntichain,AntichainCode.Holds,CodedAntichain,NontrivialCommonLower]

/-- The bottom-valued relation code of the specified arity. -/
def emptyRelation (n : ℕ) : RelationCode n :=
  ⟨fun _ => ⟨⊥,emptyAntichain,emptyAntichain⟩,emptyAntichain⟩

theorem emptyRelation_below (n : ℕ) (y : Degree) : RelationBelow (emptyRelation n) y := by
  exact ⟨fun _ => ⟨bot_le,⟨bot_le,bot_le,bot_le⟩,⟨bot_le,bot_le,bot_le⟩⟩,⟨bot_le,bot_le,bot_le⟩⟩

theorem emptyRelation_holds (n : ℕ) (v : Fin n → Degree) : ¬ (emptyRelation n).Holds v := by
  rintro ⟨c,_,hc⟩
  exact emptyAntichain_holds _ hc

theorem effective_coding (A : Oracle) (P : ℕ → Prop) (hP : RecursivePred A P) (n : ℕ) :
    ∃ p : RelationCode n, RelationBelow p (degree (OracleJump.jump A)) ∧
      ∀ v, p.Holds v ↔ ∃ j, P j ∧ ∀ i : Fin n, degree (columns A (Nat.pair i.val j)) = v i := by
  by_cases hne : ∃ j, P j
  · obtain ⟨j₀,hj₀⟩ := hne
    let F := selected A P j₀
    obtain ⟨p,hp,hcode⟩ := effective_relation_sequence F n
    have hbound := OracleJump.jump_mono (selected_reduces hP j₀)
    have hp' : RelationBelow p (degree (OracleJump.jump A)) := by
      refine ⟨fun i => ?_,?_⟩
      · exact ⟨(hp.1 i).1.trans hbound,
          ⟨(hp.1 i).2.1.1.trans hbound,(hp.1 i).2.1.2.1.trans hbound,(hp.1 i).2.1.2.2.trans hbound⟩,
          ⟨(hp.1 i).2.2.1.trans hbound,(hp.1 i).2.2.2.1.trans hbound,(hp.1 i).2.2.2.2.trans hbound⟩⟩
      · exact ⟨hp.2.1.trans hbound,hp.2.2.1.trans hbound,hp.2.2.2.trans hbound⟩
    refine ⟨p,hp',fun v => ?_⟩
    rw [hcode]
    constructor
    · rintro ⟨j,hj⟩
      have hvalid : P (pick P j₀ j) := by by_cases h : P j <;> simp [pick,h,hj₀]
      exact ⟨pick P j₀ j,hvalid,fun i => by simpa only [F,selected_column] using hj i⟩
    · rintro ⟨j,hj,hv⟩
      exact ⟨j,fun i => by simpa only [F,selected_column,pick,ite_eq_left hj] using hv i⟩
  · refine ⟨emptyRelation n,emptyRelation_below _ _,fun v => ?_⟩
    constructor
    · intro h
      exact False.elim (emptyRelation_holds n v h)
    · rintro ⟨j,hj,_⟩
      exact False.elim (hne ⟨j,hj⟩)

end
end TuringRigidity.EffectivePresentation

end OAI
