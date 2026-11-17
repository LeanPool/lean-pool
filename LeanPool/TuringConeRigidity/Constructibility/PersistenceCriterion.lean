/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistenceCriterion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalExtension
public import LeanPool.TuringConeRigidity.Constructibility.PersistentExtension
public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalAutomorphism
public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalIdeal

/-!
# Persistence Criterion
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PersistenceCriterion
open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions PersistentLocality
open PersistentPresentation PersistentCountability NumericalAutomorphism NumericalIdeal
  NumericalExtension
noncomputable section

/-- The Boolean-one acceptance graph of an oracle program. -/
def ProgramGraph (Y : Oracle) (p : OracleCode) (v : ℕ) : Prop :=
  1 ∈ OracleCode.eval (oracleFunction Y) p v

/-- Every suitable coded ideal extension admits a program-coded action compatible with `R`. -/
def Criterion (A : Oracle) (R : ℕ → Prop) : Prop :=
  ∀ H : Oracle, JumpCode H → Includes A H →
    ∃ p : OracleCode, Action H (ProgramGraph (iterate H 11) p) ∧
      Compatible A H R (ProgramGraph (iterate H 11) p)

theorem action_congr {H : Oracle} {P Q : ℕ → Prop} (h : ∀ v, P v ↔ Q v) :
    Action H P ↔ Action H Q := by
  have he : P = Q := funext (fun v => propext (h v))
  rw [he]

theorem program_graph {I : CountableIdeal} {H Y : Oracle} (hpres : Presented I H)
    (ρ : I ≃o I) (hr : RecursivePred Y (PersistentPresentation.Graph ρ hpres)) :
    ∃ p : OracleCode, ∀ v, ProgramGraph Y p v ↔ PersistentPresentation.Graph ρ hpres v := by
  obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp
    (graphOracle_reduces hpres ρ hr)
  refine ⟨p,fun v => ?_⟩
  simp only [ProgramGraph,hp,oracleFunction,graphOracle]
  by_cases hg : PersistentPresentation.Graph ρ hpres v <;> simp [hg]

theorem persistent_iff {I : CountableIdeal} {A : Oracle} (hA : Presented I A)
    (ρ : I ≃o I) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier) :
    Persistent I ρ ↔ Criterion A (PersistentPresentation.Graph ρ hA) := by
  constructor
  · intro hp H hc hi
    let J := decode H hc
    have hH : Presented J H := decoded_presentation H hc
    have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hH).mp hi
    obtain ⟨σ,he,hpσ⟩ := PersistentExtension.source_4_1_10 I J ρ hp hz hIJ (decoded_closed H hc)
    obtain ⟨p,hpgraph⟩ := program_graph hH σ (source_4_1_8 σ hpσ (hIJ hz) hH).2
    refine ⟨p,(action_congr hpgraph).mpr (action_of_automorphism hH σ),?_⟩
    exact (compatible_congr hpgraph).mpr ((compatible_iff hA hH hIJ ρ σ).mpr he)
  · intro hc x
    let J := JumpIdeal.generated (degree A ⊔ x)
    have hIJ : I.carrier ⊆ J.carrier := by
      intro y hy
      obtain ⟨n,rfl⟩ := (hA y).mp hy
      exact J.lower (le_trans (show degree (columns A n) ≤ degree A from
        CodingExtraction.column_projection_reduces A n) le_sup_left)
        (JumpIdeal.includes _)
    have hx : x ∈ J.carrier := J.lower le_sup_right (JumpIdeal.includes _)
    obtain ⟨H,hH⟩ := presentation_exists J
    have hjcode : JumpCode H := code_of_ideal hH (JumpIdeal.closed _)
    have hi : Includes A H := (includes_iff hA hH).mpr hIJ
    obtain ⟨p,ha,hcompat⟩ := hc H hjcode hi
    let K := decode H hjcode
    have hK : Presented K H := decoded_presentation H hjcode
    have hIK : I.carrier ⊆ K.carrier := (includes_iff hA hK).mp hi
    obtain ⟨σ,hσ⟩ := reconstruct hK ha
    refine ⟨K,hIK,σ,(hK x).mpr ((hH x).mp hx),?_⟩
    exact (compatible_iff hA hK hIK ρ σ).mp ((compatible_congr hσ).mp hcompat)

end
end TuringRigidity.PersistenceCriterion

end OAI
