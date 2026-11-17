/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/IdealPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticPresentation
public import LeanPool.TuringConeRigidity.SetModels.IdealEnumeration

/-!
# Ideal Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IdealPresentation
open OracleJump ArithmeticHierarchy EncodedForcing BoundedDecoding IdealInterpretation IdealLocality
open EnumerationDecoding EnumerationConstruction
noncomputable section

def entry {J : DegreeIdeal} (H : Oracle) (hH : degree H ∈ J.carrier) (n : ℕ) : J :=
  ⟨degree (columns H n),J.lower (CodingExtraction.column_projection_reduces H n) hH⟩

def Graph {J : DegreeIdeal} (ρ : J ≃o J) (H : Oracle) (hH : degree H ∈ J.carrier) (v : ℕ) : Prop :=
  (ρ (entry H hH (Nat.unpair v).1)).val = degree (columns H (Nat.unpair v).2)

theorem source_4_1_7 (I J : DegreeIdeal) (H : Oracle) (ρ : J ≃o J)
    (hpres : ∀ x, x ∈ I.carrier ↔ ∃ k, degree (columns H k) = x)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hH : degree H ∈ J.carrier) (hjump : JumpClosed J)
    (hinv : ∀ x : J, (ρ x).val ∈ I.carrier ↔ x.val ∈ I.carrier) :
    Sigma (iterate H 6) 5 (Graph ρ H hH) ∧ RecursivePred (iterate H 11) (Graph ρ H hH) := by
  have hbound (x : Degree) (hx : x ∈ I.carrier) : x ≤ degree H := by
    obtain ⟨k,rfl⟩ := (hpres x).mp hx
    exact CodingExtraction.column_projection_reduces H k
  have hzero : Reduces (jump FixedArithmetic.zero) H := hbound _ hz
  let z : J := ⟨degree (jump FixedArithmetic.zero),J.lower hzero hH⟩
  have hpre : (ρ.symm z).val ≤ degree H := by
    apply hbound
    apply (hinv (ρ.symm z)).mp
    simpa only [ρ.apply_symm_apply,z] using hz
  let b : J := ⟨degree (jump H),hjump _ hH⟩
  obtain ⟨c,hout,hS,hP⟩ := enumeration_exists H hzero
  obtain ⟨d,hdout,hdS,hdP⟩ := transport_enumeration ρ c b hS hP (entry H hH)
    (fun n => by simp only [entry,hout])
  have hb : (ρ b).val ≤ degree (iterate H 6) := by
    obtain ⟨X,Y,hX,hY,hXY⟩ := image_arithmetic ρ z rfl b
    have hYH : Reduces Y (jump H) := by
      change degree Y ≤ degree (jump H)
      rw [hY]
      exact sup_le le_rfl (hpre.trans (reduces_jump H))
    rw [← hX]
    exact reduces_trans hXY (iterate_mono hYH 5)
  have hg := graph_sigma (ArithmeticPresentation.reduces_iterate H 6) d (hdS.mono hb) (hdP.mono hb)
  have h : Sigma (iterate H 6) 5 (Graph ρ H hH) := hg.congr (fun v => by
    simp only [hdout,Graph])
  have hr := form_recursive h
  exact ⟨h,hr⟩

end
end TuringRigidity.IdealPresentation

end OAI
