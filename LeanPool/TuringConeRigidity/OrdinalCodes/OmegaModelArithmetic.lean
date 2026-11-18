/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaModelArithmetic.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaModelAxiomTransport
public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticClosure

/-!
# Omega Model Arithmetic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OmegaModelCore.OmegaData
open BoundedSetTheory SetModelReals SetModelSyntax
universe u
noncomputable section
variable {α : Type u} (S : OmegaData α)

/-- An element of the internal power of omega whose numeral membership agrees with the oracle
`A`. -/
def RealCode (a : α) (A : Oracle) : Prop :=
  S.mem a (S.power S.omega) ∧ ∀ n, S.mem (S.num n) a ↔ A n = true

theorem realCode_collapse {a : α} {A : Oracle} (ha : S.RealCode a A) :
    S.collapse (⟨a,1,ha.1⟩ : S.Core) = realSet A := by
  obtain ⟨B,hB,hBc⟩ := S.collapse_real a ha.1
  have he : B=A := by
    funext n
    have hn := (hBc n).trans (ha.2 n)
    cases hb : B n <;> cases ha : A n <;> simp_all
  exact hB.trans (congrArg realSet he)

theorem represented_real_iff (A : Oracle) :
    (∃ a : α, S.RealCode a A) ↔ A ∈ reals S.collapsedModel := by
  constructor
  · rintro ⟨a,ha⟩
    exact (S.mem_collapsedModel _).mpr ⟨⟨a,1,ha.1⟩,(S.realCode_collapse ha).symm⟩
  · intro hA
    change realSet A ∈ S.collapsedModel at hA
    obtain ⟨a,ha⟩ := (S.mem_collapsedModel _).mp hA
    have hsub : S.collapse a ⊆ S.collapse S.omegaNode := by
      rw [S.collapse_omega,←ha]
      exact realSet_subset A
    refine ⟨a.val,(S.mem_power _ _).mpr ((S.collapse_subset_iff a S.omegaNode).mp hsub),?_⟩
    intro n
    change S.Rel (S.numNode n) a ↔ A n = true
    rw [←S.collapse_mem_iff,S.collapse_num,←ha,nat_mem_realSet]

theorem omega_arithmetic_comprehension (hP : S.PairingAxiom) (hU : S.UnionAxiom)
    (hS : S.SeparationAxiom) {P : UniformArithmetic.Predicate} (hp : UniformArithmetic.Arith P)
    (O : UniformArithmetic.Oracles) (hO : ∀ i, ∃ a, S.RealCode a (O i))
    (A : Oracle) (hA : ∀ n, P O n ↔ A n = true) : ∃ a, S.RealCode a A := by
  apply (S.represented_real_iff A).mpr
  exact arithmetic_comprehension (S.collapsed_context hP hU hS) hp O
    (fun i => (S.represented_real_iff _).mp (hO i)) A hA

theorem omega_lower (hP : S.PairingAxiom) (hU : S.UnionAxiom) (hS : S.SeparationAxiom)
    {A B : Oracle} (hB : ∃ b, S.RealCode b B) (hAB : Reduces A B) : ∃ a, S.RealCode a A :=
  (S.represented_real_iff _).mpr (lower_mem (S.collapsed_context hP hU hS)
    ((S.represented_real_iff _).mp hB) hAB)

theorem omega_jump (hP : S.PairingAxiom) (hU : S.UnionAxiom) (hS : S.SeparationAxiom)
    {A : Oracle} (hA : ∃ a, S.RealCode a A) : ∃ b, S.RealCode b (OracleJump.jump A) :=
  (S.represented_real_iff _).mpr (jump_mem (S.collapsed_context hP hU hS)
    ((S.represented_real_iff _).mp hA))

end
end TuringRigidity.OmegaModelCore.OmegaData

end OAI
