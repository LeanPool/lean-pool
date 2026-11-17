/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.EnumerationTransport
public import LeanPool.TuringConeRigidity.SetModels.EnumerationConstruction

/-!
# Arithmetic Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticPresentation
open OracleJump ArithmeticHierarchy EncodedForcing BoundedDecoding IdealInterpretation
open EnumerationDecoding EnumerationConstruction EnumerationTransport GlobalLocality
noncomputable section

theorem reduces_iterate (H : Oracle) (n : ℕ) : Reduces H (iterate H n) := by
  induction n with
  | zero => exact reduces_refl H
  | succ n ih => exact reduces_trans ih (reduces_jump _)

/-- The automorphism sends the degree of the first indexed column to that of the second. -/
def Graph (π : Degree ≃o Degree) (H : Oracle) (v : ℕ) : Prop :=
  π (degree (columns H (Nat.unpair v).1)) = degree (columns H (Nat.unpair v).2)

theorem graph_arithmetic (π : Degree ≃o Degree) (H : Oracle)
    (hz : Reduces (jump FixedArithmetic.zero) H)
    (hpre : π.symm (degree (jump FixedArithmetic.zero)) ≤ degree H) :
    Sigma (iterate H 6) 5 (Graph π H) ∧ RecursivePred (iterate H 11) (Graph π H) := by
  obtain ⟨c,hout,hS,hP⟩ := enumeration_exists H hz
  let d := mapEnumeration π c
  obtain ⟨hdS,hdP⟩ := mapEnumeration_below π c (degree (jump H)) hS hP
  have hb : π (degree (jump H)) ≤ degree (iterate H 6) := by
    have hh := source_3_3_1 π (degree (jump H)) (hpre.trans (reduces_jump H))
    rw [degreeIterate_degree] at hh
    exact hh
  have hg := graph_sigma (reduces_iterate H 6) d (hdS.mono hb) (hdP.mono hb)
  have h : Sigma (iterate H 6) 5 (Graph π H) := hg.congr (fun v => by
    simp only [d,mapEnumeration,hout,Graph])
  have hr := form_recursive h
  exact ⟨h,hr⟩

theorem source_3_3_5 (π : Degree ≃o Degree) (I : DegreeIdeal) (H : Oracle)
    (hpres : ∀ x, x ∈ I.carrier ↔ ∃ k, degree (columns H k) = x)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hinv : ∀ x, π x ∈ I.carrier ↔ x ∈ I.carrier) :
    Sigma (iterate H 6) 5 (Graph π H) ∧ RecursivePred (iterate H 11) (Graph π H) := by
  have hbound (x : Degree) (hx : x ∈ I.carrier) : x ≤ degree H := by
    obtain ⟨k,rfl⟩ := (hpres x).mp hx
    exact CodingExtraction.column_projection_reduces H k
  have hp : π.symm (degree (jump FixedArithmetic.zero)) ∈ I.carrier :=
    (hinv _).mp (by simpa only [π.apply_symm_apply] using hz)
  exact graph_arithmetic π H (hbound _ hz) (hbound _ hp)

end
end TuringRigidity.ArithmeticPresentation

end OAI
