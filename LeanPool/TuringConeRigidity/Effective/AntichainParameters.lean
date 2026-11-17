/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/AntichainParameters.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.AntichainCoding

/-!
# Antichain Parameters
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AntichainParameters

def NontrivialCommonLower (b g₀ g₁ x : Degree) : Prop :=
  x ≤ b ∧ ∃ z : Degree, z ≤ g₀ ⊔ x ∧ z ≤ g₁ ⊔ x ∧ ¬ z ≤ x

def CodedAntichain (b g₀ g₁ x : Degree) : Prop :=
  NontrivialCommonLower b g₀ g₁ x ∧
    ∀ y : Degree, NontrivialCommonLower b g₀ g₁ y → y ≤ x → x ≤ y

theorem coding_degree_properties (A : ℕ → Oracle) (B : Oracle)
    (hB : ∀ k, Reduces (A k) B) :
    ∃ g₀ g₁ : Degree,
      (∀ k, NontrivialCommonLower (degree B) g₀ g₁ (degree (A k))) ∧
      ∀ x : Degree, NontrivialCommonLower (degree B) g₀ g₁ x → ∃ k, degree (A k) ≤ x := by
  obtain ⟨G₀, G₁, hfirst, hsecond⟩ := AntichainCoding.antichain_coding A B
  refine ⟨degree G₀, degree G₁, ?_, ?_⟩
  · intro k
    obtain ⟨C, h₀, h₁, hn⟩ := hfirst k
    exact ⟨hB k, degree C, h₀, h₁, hn⟩
  · intro x hx
    obtain ⟨Y, rfl⟩ := degree_surjective x
    obtain ⟨z, h₀, h₁, hn⟩ := hx.2
    obtain ⟨Z, rfl⟩ := degree_surjective z
    rcases hsecond Y hx.1 with h | hk
    · exact False.elim (hn (h Z h₀ h₁))
    · exact hk

theorem antichain_parameters (A : ℕ → Oracle) (B : Oracle)
    (hB : ∀ k, Reduces (A k) B)
    (hAnti : ∀ i j, degree (A i) ≤ degree (A j) → degree (A i) = degree (A j)) :
    ∃ g₀ g₁ : Degree, ∀ x : Degree,
      CodedAntichain (degree B) g₀ g₁ x ↔ ∃ k, degree (A k) = x := by
  obtain ⟨g₀, g₁, hmember, hcover⟩ := coding_degree_properties A B hB
  refine ⟨g₀, g₁, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hcover x hx.1
    exact ⟨k, le_antisymm hk (hx.2 _ (hmember k) hk)⟩
  · rintro ⟨k, rfl⟩
    refine ⟨hmember k, ?_⟩
    intro y hy hyk
    obtain ⟨j, hj⟩ := hcover y hy
    have he := hAnti j k (hj.trans hyk)
    exact he ▸ hj

theorem countable_antichain_parameters (S : Set Degree) (b : Degree)
    (hS : S.Countable) (hB : ∀ x ∈ S, x ≤ b)
    (hAnti : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → x = y) :
    ∃ g₀ g₁ : Degree, ∀ x : Degree, CodedAntichain b g₀ g₁ x ↔ x ∈ S := by
  by_cases hne : S.Nonempty
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    choose A hA using (fun k => degree_surjective (f k))
    obtain ⟨B, rfl⟩ := degree_surjective b
    have hbound : ∀ k, Reduces (A k) B := by
      intro k
      change degree (A k) ≤ degree B
      rw [hA k]
      exact hB (f k) (by rw [hf]; exact Set.mem_range_self k)
    have hanti : ∀ i j, degree (A i) ≤ degree (A j) → degree (A i) = degree (A j) := by
      intro i j hij
      rw [hA i, hA j] at hij ⊢
      exact hAnti (f i) (by rw [hf]; exact Set.mem_range_self i)
        (f j) (by rw [hf]; exact Set.mem_range_self j) hij
    obtain ⟨g₀, g₁, hg⟩ := antichain_parameters A B hbound hanti
    refine ⟨g₀, g₁, ?_⟩
    intro x
    rw [hg x, hf]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, (hA k).symm.trans hk⟩,
      fun ⟨k, hk⟩ => ⟨k, (hA k).trans hk⟩⟩
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨⊥, ⊥, ?_⟩
    intro x
    simp [CodedAntichain, NontrivialCommonLower, he]

end TuringRigidity.AntichainParameters

end OAI
