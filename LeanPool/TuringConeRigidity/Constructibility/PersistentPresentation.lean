/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistentPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.JumpIdeal
public import LeanPool.TuringConeRigidity.SetModels.IdealPresentation

/-!
# Persistent Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PersistentPresentation
open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation IdealLocality
  PersistentRestrictions PersistentLocality
noncomputable section

/-- The oracle's columns enumerate exactly the carrier of the countable ideal. -/
def Presented (I : CountableIdeal) (H : Oracle) : Prop :=
  ∀ x, x ∈ I.carrier ↔ ∃ k, degree (columns H k) = x

/-- The ideal element represented by the `n`th oracle column. -/
def entry {I : CountableIdeal} {H : Oracle} (hpres : Presented I H) (n : ℕ) : I :=
  ⟨degree (columns H n),(hpres _).mpr ⟨n,rfl⟩⟩

/-- The graph of the ideal automorphism, expressed through pairs of presentation indices. -/
def Graph {I : CountableIdeal} (ρ : I ≃o I) {H : Oracle} (hpres : Presented I H) (v : ℕ) : Prop :=
  (ρ (entry hpres (Nat.unpair v).1)).val = degree (columns H (Nat.unpair v).2)

theorem source_4_1_8 {I : CountableIdeal} (ρ : I ≃o I) (hp : Persistent I ρ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    {H : Oracle} (hpres : Presented I H) :
    Sigma (iterate H 6) 5 (Graph ρ hpres) ∧ RecursivePred (iterate H 11) (Graph ρ hpres) := by
  let J := JumpIdeal.generated (degree H)
  have hH : degree H ∈ J.carrier := JumpIdeal.includes _
  have hIJ : I.carrier ⊆ J.carrier := by
    intro x hx
    obtain ⟨k,rfl⟩ := (hpres x).mp hx
    exact J.lower (CodingExtraction.column_projection_reduces H k) hH
  obtain ⟨σ,he⟩ := source_4_1_5 I J ρ hp hz hIJ (JumpIdeal.closed _)
  have hinv : ∀ x : ideal J, ((lift σ) x).val ∈ I.carrier ↔ x.val ∈ I.carrier := by
    intro x
    constructor
    · intro hx
      let y : I := ⟨((lift σ) x).val,hx⟩
      have hh := extends_symm he y
      have hh' : (σ.symm (σ ((bridge J).symm x))).val = (ρ.symm y).val := hh
      rw [σ.symm_apply_apply] at hh'
      change x.val = (ρ.symm y).val at hh'
      rw [hh']
      exact (ρ.symm y).property
    · intro hx
      have hh := he ⟨x.val,hx⟩
      change ((lift σ) x).val = (ρ ⟨x.val,hx⟩).val at hh
      rw [hh]
      exact (ρ ⟨x.val,hx⟩).property
  have hg := (IdealPresentation.source_4_1_7 (ideal I) (ideal J) H (lift σ)
    hpres hz hH (JumpIdeal.closed _) hinv).1
  have hh : Sigma (iterate H 6) 5 (Graph ρ hpres) := hg.congr (fun v => by
    change (σ ⟨degree (columns H (Nat.unpair v).1),_⟩).val = _ ↔ _
    exact Iff.of_eq (congrArg (fun x : Degree => x = degree (columns H (Nat.unpair v).2))
      (he (entry hpres (Nat.unpair v).1))))
  have hr := form_recursive hh
  exact ⟨hh,hr⟩

end
end TuringRigidity.PersistentPresentation

end OAI
