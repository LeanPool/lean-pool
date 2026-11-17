/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/ConstructionStageBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.SingleRealConstruction

/-!
# Construction Stage Bound
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

/-- An ordinal bound exceeding all stages used by the construction and its sub-constructions. -/
noncomputable def Construction.stageBound : Construction.{u} → Ordinal.{u}
  | .reals => 0
  | .parameter => 0
  | .define o _ _ c => max o (Finset.univ.sup (fun i => (c i).stageBound)) + 1

theorem internal_ordinal_finite_sup (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {α : Type*} (s : Finset α) (v : α → Ordinal.{u})
    (h : ∀ i ∈ s, (v i).toZFSet ∈ M) : (s.sup v).toZFSet ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using internal_ordinal_zero M hM hT
  | @insert a s ha ih =>
    rw [Finset.sup_insert]
    exact internal_ordinal_max M (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem Construction.stageBound_mem (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hi : t.Indexed M) : t.stageBound.toZFSet ∈ M := by
  induction t with
  | reals => exact internal_ordinal_zero M hM hT
  | parameter => exact internal_ordinal_zero M hM hT
  | define o n p c ih =>
    exact internal_ordinal_succ M hM hT _ (internal_ordinal_max M hi.1
      (internal_ordinal_finite_sup M hM hT Finset.univ _ (fun i _ => ih i (hi.2 i))))

theorem Construction.stageInputs_bounded (t : Construction.{u}) (R : ZFSet.{u}) :
    ∀ k, t.stageInputs R k ∈ level R t.stageBound := by
  have hR (o : Ordinal.{u}) : R ∈ level R o := seed_subset_stage R o.toZFSet (parameter_mem_seed R)
  induction t with
  | reals => exact fun _ => hR 0
  | parameter => exact fun _ => hR 0
  | define o n p c ih =>
    intro k
    have hupper (i : Fin n) : (c i).stageBound ≤ (Construction.define o n p c).stageBound :=
      (Finset.le_sup (Finset.mem_univ i)).trans
        ((le_max_right o _).trans (le_of_lt (lt_add_one _)))
    cases k with
    | zero =>
      exact level_mem_level R ((le_max_left o _).trans_lt (lt_add_one _))
    | succ k =>
      unfold Construction.stageInputs
      simp only [Construction.inputData]
      by_cases h : (Nat.unpair k).1 < n
      · rw [dite_eq_left h]
        have hchild := level_mono R (hupper ⟨(Nat.unpair k).1,h⟩)
          (ih ⟨(Nat.unpair k).1,h⟩ (Nat.unpair k).2)
        unfold Construction.stageInputs at hchild
        cases hd : (c ⟨(Nat.unpair k).1,h⟩).inputData (Nat.unpair k).2 <;>
          simpa only [hd,ConstructionInput.prefix] using hchild
      · rw [dite_eq_right h]
        exact hR _

end TuringRigidity.RelativeConstructible

end OAI
