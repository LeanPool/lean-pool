/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistentLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.IdealLocality
public import LeanPool.TuringConeRigidity.Constructibility.PersistentRestrictions
public import LeanPool.TuringConeRigidity.SetModels.CountableBound

/-!
# Persistent Locality
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PersistentLocality
open IdealInterpretation IdealLocality PersistentRestrictions OracleJump
noncomputable section

def ideal (I : CountableIdeal) : DegreeIdeal :=
  ⟨I.carrier,I.nonempty,fun {_ _} h hmem => I.lower h hmem,
    fun {_ _} h₁ h₂ => I.join_mem h₁ h₂⟩

def bridge (I : CountableIdeal) : I ≃o ideal I where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def lift {I : CountableIdeal} (ρ : I ≃o I) : ideal I ≃o ideal I :=
  (bridge I).symm.trans (ρ.trans (bridge I))

def unlift {I : CountableIdeal} (ρ : ideal I ≃o ideal I) : I ≃o I :=
  (bridge I).trans (ρ.trans (bridge I).symm)

theorem extends_symm {I K : CountableIdeal} {hIK : I.carrier ⊆ K.carrier}
    {ρ : I ≃o I} {σ : K ≃o K} (he : Extends hIK ρ σ) :
    Extends hIK ρ.symm σ.symm := by
  intro x
  have h : σ ⟨(ρ.symm x).val,hIK (ρ.symm x).property⟩ = ⟨x.val,hIK x.property⟩ := by
    apply Subtype.ext
    exact (he (ρ.symm x)).trans (congrArg Subtype.val (ρ.apply_symm_apply x))
  have hh := congrArg (fun y => (σ.symm y).val) h
  simpa only [σ.symm_apply_apply] using hh.symm

theorem source_4_1_5 (I J : CountableIdeal) (ρ : I ≃o I)
    (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hjump : JumpClosed (ideal J)) :
    ∃ σ : J ≃o J, Extends hIJ ρ σ := by
  obtain ⟨b,hb⟩ := CountableBound.countable_bounded J.carrier J.countable
  obtain ⟨K,hIK,τ,hbK,he⟩ := hp b
  have hJK : J.carrier ⊆ K.carrier := fun x hx => K.lower (hb x hx) hbK
  let z : I := ⟨degree (jump FixedArithmetic.zero),hz⟩
  let zK : ideal K := ⟨z.val,hIK z.property⟩
  have hforward : ((lift τ) zK).val ∈ J.carrier := by
    change (τ ⟨z.val,hIK z.property⟩).val ∈ J.carrier
    rw [he z]
    exact hIJ (ρ z).property
  have hback : ((lift τ).symm zK).val ∈ J.carrier := by
    change (τ.symm ⟨z.val,hIK z.property⟩).val ∈ J.carrier
    rw [extends_symm he z]
    exact hIJ (ρ.symm z).property
  obtain ⟨σ,hσ⟩ := source_4_1_4 (lift τ) zK rfl hJK hjump (J.join_mem hforward hback)
  refine ⟨unlift σ,fun x => ?_⟩
  exact (hσ ⟨x.val,hIJ x.property⟩).trans (he x)

end
end TuringRigidity.PersistentLocality

end OAI
