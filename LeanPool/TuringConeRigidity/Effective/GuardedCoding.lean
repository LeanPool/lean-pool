/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedExtraction
public import LeanPool.TuringConeRigidity.Computability.NormalizedRecovery
public import LeanPool.TuringConeRigidity.Effective.AntichainParameters

/-!
# Guarded Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedCoding
open EncodedForcing StageNormalization AntichainParameters

theorem effective_coding (A : Oracle) : ∃ G₀ G₁ : Oracle,
    Reduces (join G₀ G₁) (OracleJump.jump A) ∧
    (∀ k, ∃ C : Oracle, Reduces C (join G₀ (columns A k)) ∧
      Reduces C (join G₁ (columns A k)) ∧ ¬ Reduces C (columns A k)) ∧
    ∀ Y Z : Oracle, Reduces Y A → Reduces Z (join G₀ Y) →
      Reduces Z (join G₁ Y) → ¬ Reduces Z Y → ∃ k, Reduces (columns A k) Y := by
  let B := normalized A
  obtain ⟨hbound,hfirst⟩ := GuardedLimits.effective_first_clause B
    (fun k => (normalized_spec A k).2.1)
  refine ⟨GuardedLimits.G₀ B,GuardedLimits.G₁ B,
    reduces_trans hbound (OracleJump.jump_mono (normalized_reduces A)),?_,?_⟩
  · intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    obtain ⟨hBA,hAB⟩ := (degree_eq_iff _ _).mp (normalized_spec A k).1
    exact ⟨C,reduces_trans h₀ (join_mono (reduces_refl _) hBA),
      reduces_trans h₁ (join_mono (reduces_refl _) hBA),fun h => hn (reduces_trans h hAB)⟩
  · intro Y Z hY h₀ h₁ hn
    obtain ⟨k,hk⟩ := GuardedExtraction.common_lower_computes_column
      (fun k => (normalized_spec A k).2.2)
      (reduces_trans hY (NormalizedRecovery.normalized_inverse A))
      (reduces_trans h₀ (AntichainCoding.swap_join_reduces _ _))
      (reduces_trans h₁ (AntichainCoding.swap_join_reduces _ _)) hn
    exact ⟨k,reduces_trans (((degree_eq_iff _ _).mp (normalized_spec A k).1).2) hk⟩

theorem effective_antichain_parameters (A : Oracle)
    (hAnti : ∀ i j, degree (columns A i) ≤ degree (columns A j) →
      degree (columns A i) = degree (columns A j)) :
    ∃ g₀ g₁ : Degree, g₀ ⊔ g₁ ≤ OracleJump.degreeJump (degree A) ∧
      ∀ x : Degree, CodedAntichain (degree A) g₀ g₁ x ↔ ∃ k, degree (columns A k) = x := by
  obtain ⟨G₀,G₁,hbound,hfirst,hsecond⟩ := effective_coding A
  have hm : ∀ k, NontrivialCommonLower (degree A) (degree G₀) (degree G₁) (degree (columns A k))
    := by
    intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    exact ⟨CodingExtraction.column_projection_reduces A k,degree C,h₀,h₁,hn⟩
  have hc : ∀ x, NontrivialCommonLower (degree A) (degree G₀) (degree G₁) x →
      ∃ k, degree (columns A k) ≤ x := by
    intro x hx
    obtain ⟨Y,rfl⟩ := degree_surjective x
    obtain ⟨z,h₀,h₁,hn⟩ := hx.2
    obtain ⟨Z,rfl⟩ := degree_surjective z
    exact hsecond Y Z hx.1 h₀ h₁ hn
  refine ⟨degree G₀,degree G₁,hbound,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := hc x hx.1
    exact ⟨k,le_antisymm hk (hx.2 _ (hm k) hk)⟩
  · rintro ⟨k,rfl⟩
    refine ⟨hm k,fun y hy hyk => ?_⟩
    obtain ⟨j,hj⟩ := hc y hy
    exact hAnti j k (hj.trans hyk) ▸ hj

end TuringRigidity.GuardedCoding

end OAI
