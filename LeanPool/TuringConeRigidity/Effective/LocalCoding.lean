/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalExtraction
public import LeanPool.TuringConeRigidity.Effective.StageNormalization
public import LeanPool.TuringConeRigidity.Effective.AntichainParameters

/-!
# Local Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalCoding
open EncodedForcing StageNormalization AntichainParameters

theorem selected_coding {A B X : Oracle} (hAB : Reduces A B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n))) :
    ∃ G₀ G₁ : Oracle, Reduces (join G₀ G₁) (join X (OracleJump.jump B)) ∧
      (∀ k, ∃ C : Oracle, Reduces C (join G₀ (columns A (select k))) ∧
        Reduces C (join G₁ (columns A (select k))) ∧ ¬ Reduces C (columns A (select k))) ∧
      ∀ Y Z : Oracle, Reduces Y B → Reduces Z (join G₀ Y) →
        Reduces Z (join G₁ Y) → ¬ Reduces Z Y → ∃ k, Reduces (columns A (select k)) Y := by
  obtain ⟨codes,hcodes,hvalid⟩ := LocalColumnIndices.selected_prefixes
    (reduces_trans (normalized_reduces A) hAB) select hs
  let D : LocalInputs.Data := ⟨B,X,fun k => columns (normalized A) (select k),codes,hcodes,hvalid⟩
  obtain ⟨hbound,hfirst⟩ := LocalLimits.effective_first_clause D
    (fun k => (normalized_spec A (select k)).2.1)
  refine ⟨LocalLimits.G₀ D,LocalLimits.G₁ D,hbound,?_,?_⟩
  · intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    obtain ⟨hBA,hAB'⟩ := (degree_eq_iff _ _).mp (normalized_spec A (select k)).1
    exact ⟨C,reduces_trans h₀ (join_mono (reduces_refl _) hBA),
      reduces_trans h₁ (join_mono (reduces_refl _) hBA),fun h => hn (reduces_trans h hAB')⟩
  · intro Y Z hY h₀ h₁ hn
    obtain ⟨k,hk⟩ := LocalExtraction.common_lower_computes_column (D := D)
      (fun k => (normalized_spec A (select k)).2.2) hY
      (reduces_trans h₀ (AntichainCoding.swap_join_reduces _ _))
      (reduces_trans h₁ (AntichainCoding.swap_join_reduces _ _)) hn
    exact ⟨k,reduces_trans (((degree_eq_iff _ _).mp (normalized_spec A (select k)).1).2) hk⟩

theorem selected_antichain {A B X : Oracle} (hAB : Reduces A B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n)))
    (hAnti : ∀ i j, degree (columns A (select i)) ≤ degree (columns A (select j)) →
      degree (columns A (select i)) = degree (columns A (select j))) :
    ∃ g₀ g₁ : Degree, g₀ ⊔ g₁ ≤ degree (join X (OracleJump.jump B)) ∧
      ∀ x : Degree, CodedAntichain (degree B) g₀ g₁ x ↔ ∃ k, degree (columns A (select k)) = x := by
  obtain ⟨G₀,G₁,hbound,hfirst,hsecond⟩ := selected_coding hAB select hs
  have hm : ∀ k, NontrivialCommonLower (degree B) (degree G₀) (degree G₁) (degree (columns A
    (select k))) := by
    intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    exact ⟨reduces_trans (CodingExtraction.column_projection_reduces A (select k)) hAB,degree
      C,h₀,h₁,hn⟩
  have hc : ∀ x, NontrivialCommonLower (degree B) (degree G₀) (degree G₁) x →
      ∃ k, degree (columns A (select k)) ≤ x := by
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

end TuringRigidity.LocalCoding

end OAI
