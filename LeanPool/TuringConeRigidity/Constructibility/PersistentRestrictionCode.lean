/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistentRestrictionCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentPresentation

/-!
# Persistent Restriction Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PersistentRestrictionCode
open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation IdealLocality
open PersistentRestrictions PersistentLocality PersistentPresentation
noncomputable section

theorem restriction {I J K : CountableIdeal} (ρ : I ≃o I) (τ : K ≃o K)
    (hIK : I.carrier ⊆ K.carrier) (he : Extends hIK ρ τ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hJK : J.carrier ⊆ K.carrier)
    (hj : JumpClosed (ideal J)) {H : Oracle} (hpres : Presented J H)
    (hLK : (JumpIdeal.generated (degree H)).carrier ⊆ K.carrier) :
    ∃ σ : J ≃o J, Extends hIJ ρ σ ∧ Extends hJK σ τ ∧
      RecursivePred (iterate H 11) (Graph σ hpres) := by
  let L := JumpIdeal.generated (degree H)
  have hH : degree H ∈ L.carrier := JumpIdeal.includes _
  have hJL : J.carrier ⊆ L.carrier := by
    intro x hx
    obtain ⟨n,rfl⟩ := (hpres x).mp hx
    exact L.lower (CodingExtraction.column_projection_reduces H n) hH
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
  have himages := J.join_mem hforward hback
  obtain ⟨σJ,hσJ⟩ := source_4_1_4 (lift τ) zK rfl hJK hj himages
  obtain ⟨σL,hσL⟩ := source_4_1_4 (lift τ) zK rfl hLK (JumpIdeal.closed _) (hJL himages)
  let σ := unlift σJ
  have hτ : Extends hJK σ τ := fun x => (hσJ ((bridge J) x)).symm
  have hρ : Extends hIJ ρ σ := by
    intro x
    exact (hσJ ⟨x.val,hIJ x.property⟩).trans (he x)
  have hinv : ∀ x : ideal L, (σL x).val ∈ J.carrier ↔ x.val ∈ J.carrier := by
    intro x
    rw [hσL x]
    exact invariant (lift τ) zK rfl hj himages ⟨x.val,hLK x.property⟩
  have hg := (IdealPresentation.source_4_1_7 (ideal J) (ideal L) H σL hpres
    (hIJ hz) hH (JumpIdeal.closed _) hinv).1
  have hh : Sigma (iterate H 6) 5 (Graph σ hpres) := hg.congr (fun v => by
    have ha := hσL (IdealPresentation.entry H hH (Nat.unpair v).1)
    have hb := hτ (entry hpres (Nat.unpair v).1)
    exact Iff.of_eq (congrArg (fun x : Degree => x = degree (columns H (Nat.unpair v).2))
      (ha.trans hb)))
  have hr := form_recursive hh
  exact ⟨σ,hρ,hτ,hr⟩

end
end TuringRigidity.PersistentRestrictionCode

end OAI
