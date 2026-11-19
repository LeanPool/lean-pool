/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GlobalLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.IdealLocality

/-!
# Global Locality
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GlobalLocality
open OracleJump IdealInterpretation IdealLocality
noncomputable section

/-- The degree ideal whose carrier is the entire degree order. -/
def fullIdeal : DegreeIdeal :=
  ⟨Set.univ,⟨⊥,Set.mem_univ _⟩,fun {_ _} _ _ => Set.mem_univ _,fun {_ _} _ _ => Set.mem_univ _⟩

/-- Lift a global degree automorphism to an automorphism of the full ideal. -/
def lift (π : Degree ≃o Degree) : fullIdeal ≃o fullIdeal :=
  { toEquiv :=
      { toFun := fun x => ⟨π x.val,Set.mem_univ _⟩
        invFun := fun x => ⟨π.symm x.val,Set.mem_univ _⟩
        left_inv := fun x => Element.ext _ _ (π.symm_apply_apply x.val)
        right_inv := fun x => Element.ext _ _ (π.apply_symm_apply x.val) }
    map_rel_iff' := by intro a b; exact π.le_iff_le }

/-- The finite iterates of the Turing jump on degrees. -/
def degreeIterate (x : Degree) : ℕ → Degree
  | 0 => x
  | n+1 => degreeJump (degreeIterate x n)

@[simp] theorem degreeIterate_degree (X : Oracle) (n : ℕ) :
    degreeIterate (degree X) n = degree (iterate X n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [degreeIterate,ih,degreeJump_degree]; rfl

theorem arithmetic_bound (π : Degree ≃o Degree) (x : Degree) :
    π x ≤ degreeIterate (x ⊔ π.symm (degree (jump FixedArithmetic.zero))) 5 := by
  let z : fullIdeal := ⟨degree (jump FixedArithmetic.zero),Set.mem_univ _⟩
  let y : fullIdeal := ⟨x,Set.mem_univ _⟩
  obtain ⟨X,Y,hX,hY,hXY⟩ := image_arithmetic (lift π) z rfl y
  change degree X = π x at hX
  change degree Y = x ⊔ π.symm (degree (jump FixedArithmetic.zero)) at hY
  rw [← hX,← hY,degreeIterate_degree]
  exact hXY

theorem source_3_3_1 (π : Degree ≃o Degree) (x : Degree)
    (hx : π.symm (degree (jump FixedArithmetic.zero)) ≤ x) : π x ≤ degreeIterate x 5 := by
  simpa only [sup_eq_left.mpr hx] using arithmetic_bound π x

end
end TuringRigidity.GlobalLocality

end OAI
