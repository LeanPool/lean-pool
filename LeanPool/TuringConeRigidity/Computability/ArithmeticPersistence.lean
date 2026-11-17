/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticPersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticActions
public import LeanPool.TuringConeRigidity.Constructibility.PersistenceCriterion

/-!
# Arithmetic Persistence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticPersistence
open Encodable EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic
open PersistentRestrictions PersistentLocality PersistentPresentation PersistentCountability
open NumericalAutomorphism NumericalIdeal NumericalExtension
noncomputable section

def Criterion (A R : Oracle) : Prop :=
  ∀ H : Oracle, JumpCode H → Includes A H →
    ∃ e : ℕ, Action H (fun v => tableOracle (iterate H 11) e v = true) ∧
      Compatible A H (fun v => R v = true) (fun v => tableOracle (iterate H 11) e v = true)

theorem graph_program {I : CountableIdeal} {H Y : Oracle} (hH : Presented I H)
    (ρ : I ≃o I) (hr : RecursivePred Y (Graph ρ hH)) :
    ∃ e : ℕ, ∀ v, tableOracle Y e v = true ↔ Graph ρ hH v := by
  obtain ⟨d,hd⟩ := TableIndices.reduces_represents (graphOracle_reduces hH ρ hr)
  have hd' : TableIndices.Represents Y (IndexMatrix.machine (encode d)) (graphOracle hH ρ) := by
    simpa only [IndexMatrix.machine_encode] using hd
  refine ⟨encode d,fun v => ?_⟩
  rw [tableOracle_eq hd']
  simp [graphOracle]

theorem persistent_iff {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (ρ : I ≃o I) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ Graph ρ hA v) :
    Persistent I ρ ↔ Criterion A R := by
  constructor
  · intro hp H hc hi
    let J := decode H hc
    have hH : Presented J H := decoded_presentation H hc
    have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hH).mp hi
    obtain ⟨σ,he,hpσ⟩ := PersistentExtension.source_4_1_10 I J ρ hp hz hIJ (decoded_closed H hc)
    obtain ⟨e,hg⟩ := graph_program hH σ (source_4_1_8 σ hpσ (hIJ hz) hH).2
    refine ⟨e,(PersistenceCriterion.action_congr hg).mpr (action_of_automorphism hH σ),?_⟩
    intro i j n m hr hp hin
    exact ((compatible_iff hA hH hIJ ρ σ).mpr he) i j n m
      ((hR _).mp hr) ((hg _).mp hp) hin
  · intro hc x
    let J := JumpIdeal.generated (degree A ⊔ x)
    have hIJ : I.carrier ⊆ J.carrier := by
      intro y hy
      obtain ⟨n,rfl⟩ := (hA y).mp hy
      exact J.lower (le_trans (show degree (columns A n) ≤ degree A from
        CodingExtraction.column_projection_reduces A n) le_sup_left) (JumpIdeal.includes _)
    have hx : x ∈ J.carrier := J.lower le_sup_right (JumpIdeal.includes _)
    obtain ⟨H,hH⟩ := presentation_exists J
    have hj : JumpCode H := code_of_ideal hH (JumpIdeal.closed _)
    have hi : Includes A H := (includes_iff hA hH).mpr hIJ
    obtain ⟨e,ha,hcompat⟩ := hc H hj hi
    obtain ⟨σ,hσ⟩ := reconstruct hH ha
    refine ⟨J,hIJ,σ,hx,(compatible_iff hA hH hIJ ρ σ).mp ?_⟩
    intro i j n m hr hp hin
    exact hcompat i j n m ((hR _).mpr hr) ((hσ _).mpr hp) hin

def Matrix (O : Oracles) (_ : ℕ) : Prop :=
  JumpCode (O 2) → Includes (O 0) (O 2) →
    ∃ e : ℕ, Action (O 2) (fun v => tableOracle (iterate (O 2) 11) e v = true) ∧
      Compatible (O 0) (O 2) (fun v => O 1 v = true)
        (fun v => tableOracle (iterate (O 2) 11) e v = true)

theorem matrix_arith : Arith Matrix := by
  have hA := parameter_arith 0
  have hR := parameter_arith 1
  have hH := parameter_arith 2
  have hP := tableOracle_arith (iterate_arith hH 11) UniformArithmetic.right_primrec
  have he := ((action_arith hH hP).and (compatible_arith hA hH hR hP)).ex
  exact ((jumpCode_arith hH).imp ((includes_arith hA hH).imp he)).congr
    (fun _ _ => by simp only [Matrix,UniformArithmetic.right,Nat.unpair_pair])

end
end TuringRigidity.ArithmeticPersistence

end OAI
