/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/JumpIdeal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentLocality
public import LeanPool.TuringConeRigidity.Representation.GlobalLocality

/-!
# Jump Ideal
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.JumpIdeal
open OracleJump IdealInterpretation IdealLocality PersistentRestrictions PersistentLocality
  GlobalLocality
noncomputable section

theorem iterate_monotone (x : Degree) : Monotone (degreeIterate x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact degree_le_jump _

/-- The countable ideal of degrees below some finite jump iterate of `x`. -/
def generated (x : Degree) : CountableIdeal where
  carrier := {y | ∃ n, y ≤ degreeIterate x n}
  nonempty := ⟨x,0,le_rfl⟩
  countable := by
    have he : {y | ∃ n, y ≤ degreeIterate x n} = ⋃ n, Set.Iic (degreeIterate x n) := by
      ext y
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_Iic]
    rw [he]
    exact Set.countable_iUnion (fun n => countable_principal_lower _)
  lower := by
    intro a b hab hb
    obtain ⟨n,hn⟩ := hb
    exact ⟨n,hab.trans hn⟩
  join_mem := by
    intro a b ha hb
    obtain ⟨m,hm⟩ := ha
    obtain ⟨n,hn⟩ := hb
    exact ⟨max m n,sup_le (hm.trans (iterate_monotone x (le_max_left m n)))
      (hn.trans (iterate_monotone x (le_max_right m n)))⟩

theorem includes (x : Degree) : x ∈ (generated x).carrier := ⟨0,le_rfl⟩

theorem closed (x : Degree) : JumpClosed (ideal (generated x)) := by
  intro y hy
  obtain ⟨n,hn⟩ := hy
  exact ⟨n+1,degreeJump_mono hn⟩

theorem least (x : Degree) (J : DegreeIdeal) (hx : x ∈ J.carrier)
    (hj : JumpClosed J) : (generated x).carrier ⊆ J.carrier := by
  have hi (n : ℕ) : degreeIterate x n ∈ J.carrier := by
    induction n with
    | zero => exact hx
    | succ n ih => exact hj _ ih
  intro y hy
  obtain ⟨n,hn⟩ := hy
  exact J.lower hn (hi n)

end
end TuringRigidity.JumpIdeal

end OAI
