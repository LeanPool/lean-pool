/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeRelativeAntichain.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeCoding
public import LeanPool.TuringConeRigidity.Effective.LocalCoding
public import LeanPool.TuringConeRigidity.Effective.EffectiveFamilies

/-!
# Effective antichain coding above a fixed base

The ordinary coding construction has a coverage clause, not just a description
of its minimal elements. That clause lets us restrict minimality to a cone.
Joining the base to the two coding parameters does not change nontriviality at
any point of the cone. Every resulting parameter is itself in the cone, which
is necessary when pulling a code back through a partial cone isomorphism.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeRelativeCoding

open EncodedForcing OracleJump ArithmeticHierarchy UniformOracle
open SetCoding RelationCoding AntichainParameters BoundedDecoding

noncomputable section

/-- Lower bounds on every parameter, complementary to `AntichainBelow`. -/
def AntichainAbove (p : AntichainCode) (a : Degree) : Prop :=
  a ≤ p.bound ∧ a ≤ p.left ∧ a ≤ p.right

/-- Every degree parameter of the set code lies above the cone base. -/
def SetAbove (p : SetCode) (a : Degree) : Prop :=
  a ≤ p.bound ∧ AntichainAbove p.tags a ∧ AntichainAbove p.decorated a

/-- Every coordinate-set and tuple-antichain parameter lies above the cone base. -/
def RelationAbove {n : ℕ} (p : RelationCode n) (a : Degree) : Prop :=
  (∀ i, SetAbove (p.coordinates i) a) ∧ AntichainAbove p.tuples a

theorem nontrivial_join_base (a b g₀ g₁ x : Degree) (hax : a ≤ x) :
    NontrivialCommonLower b (a ⊔ g₀) (a ⊔ g₁) x ↔
      NontrivialCommonLower b g₀ g₁ x := by
  have h₀ : (a ⊔ g₀) ⊔ x = g₀ ⊔ x := by
    calc
      _ = g₀ ⊔ (a ⊔ x) := by ac_rfl
      _ = _ := by rw [sup_eq_right.mpr hax]
  have h₁ : (a ⊔ g₁) ⊔ x = g₁ ⊔ x := by
    calc
      _ = g₁ ⊔ (a ⊔ x) := by ac_rfl
      _ = _ := by rw [sup_eq_right.mpr hax]
  simp only [NontrivialCommonLower, h₀, h₁]

/-- The selected-family construction is localized at `X ⊕ B'`, rather than
at `(X ⊕ B)'`. This distinction is essential for the locality argument. -/
theorem selected_antichain_code {F B X : Oracle} (a : Degree)
    (hFB : Reduces F B) (haB : a ≤ degree B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n)))
    (hbase : ∀ k, a ≤ degree (columns F (select k)))
    (hAnti : ∀ i j, degree (columns F (select i)) ≤ degree (columns F (select j)) →
      degree (columns F (select i)) = degree (columns F (select j))) :
    ∃ p : AntichainCode, AntichainAbove p a ∧
      AntichainBelow p (degree (join X (jump B))) ∧
      ∀ x, ConeCoding.Antichain a p x ↔ ∃ k, degree (columns F (select k)) = x := by
  obtain ⟨G₀, G₁, hbound, hfirst, hsecond⟩ := LocalCoding.selected_coding hFB select hs
  have hm (k : ℕ) : NontrivialCommonLower (degree B) (degree G₀) (degree G₁)
      (degree (columns F (select k))) := by
    obtain ⟨C, h₀, h₁, hn⟩ := hfirst k
    exact ⟨reduces_trans (CodingExtraction.column_projection_reduces F _) hFB,
      degree C, h₀, h₁, hn⟩
  have hc (x : Degree) (hx : NontrivialCommonLower (degree B) (degree G₀) (degree G₁) x) :
      ∃ k, degree (columns F (select k)) ≤ x := by
    obtain ⟨Y, rfl⟩ := degree_surjective x
    obtain ⟨z, h₀, h₁, hn⟩ := hx.2
    obtain ⟨Z, rfl⟩ := degree_surjective z
    exact hsecond Y Z hx.1 h₀ h₁ hn
  let p : AntichainCode := ⟨degree B, a ⊔ degree G₀, a ⊔ degree G₁⟩
  have hB : degree B ≤ degree (join X (jump B)) :=
    (reduces_jump B).trans (reduces_join_right X (jump B))
  refine ⟨p, ⟨haB, le_sup_left, le_sup_left⟩,
    ⟨hB, sup_le (haB.trans hB) (reduces_trans (reduces_join_left G₀ G₁) hbound),
      sup_le (haB.trans hB) (reduces_trans (reduces_join_right G₀ G₁) hbound)⟩, ?_⟩
  intro x
  constructor
  · rintro ⟨hax, hx, hmin⟩
    obtain ⟨k, hk⟩ := hc x ((nontrivial_join_base _ _ _ _ _ hax).mp hx)
    exact ⟨k, le_antisymm hk (hmin _ (hbase k)
      ((nontrivial_join_base _ _ _ _ _ (hbase k)).mpr (hm k)) hk)⟩
  · rintro ⟨k, rfl⟩
    refine ⟨hbase k, (nontrivial_join_base _ _ _ _ _ (hbase k)).mpr (hm k), ?_⟩
    intro y hay hy hyk
    obtain ⟨j, hj⟩ := hc y ((nontrivial_join_base _ _ _ _ _ hay).mp hy)
    exact hAnti j k (hj.trans hyk) ▸ hj

/-- A whole uniformly presented antichain can be coded below the jump of its
bound, with all parameters above the base. -/
theorem antichain_code {F B : Oracle} (a : Degree) (hFB : Reduces F B)
    (haB : a ≤ degree B) (hbase : ∀ k, a ≤ degree (columns F k))
    (hAnti : ∀ i j, degree (columns F i) ≤ degree (columns F j) →
      degree (columns F i) = degree (columns F j)) :
    ∃ p : AntichainCode, AntichainAbove p a ∧ AntichainBelow p (degree (jump B)) ∧
      ∀ x, ConeCoding.Antichain a p x ↔ ∃ k, degree (columns F k) = x := by
  obtain ⟨p, ha, hp, hs⟩ := selected_antichain_code (X := B) a hFB haB
    id (total_primrec Primrec.id) hbase hAnti
  have he : degree (join B (jump B)) = degree (jump B) := by
    change degree B ⊔ degree (jump B) = degree (jump B)
    exact sup_eq_right.mpr (reduces_jump B)
  exact ⟨p, ha, he ▸ hp, hs⟩

/-- Repeat `A` in every column of a paired oracle. -/
def repeatOracle (A : Oracle) : Oracle := fun n => A (Nat.unpair n).2

@[simp] theorem repeat_column (A : Oracle) (k : ℕ) : columns (repeatOracle A) k = A := by
  funext n
  simp only [columns, repeatOracle, Nat.unpair_pair]

theorem repeat_reduces (A : Oracle) : Reduces (repeatOracle A) A :=
  EffectiveFamilies.reindex_reduces A (Primrec.snd.comp Primrec.unpair)

/-- Adjoin the same base oracle to every column of a uniform sequence. -/
def pad (A C : Oracle) : Oracle := EffectiveFamilies.mix (repeatOracle A) C

@[simp] theorem pad_column (A C : Oracle) (k : ℕ) :
    columns (pad A C) k = join A (columns C k) := by
  simp only [pad, EffectiveFamilies.mix_column, repeat_column]

theorem pad_reduces (A C : Oracle) : Reduces (pad A C) (join A C) :=
  reduces_trans (EffectiveFamilies.mix_reduces _ _) (join_mono (repeat_reduces A) (reduces_refl C))

theorem base_le_pad_column (A C : Oracle) (k : ℕ) :
    degree A ≤ degree (columns (pad A C) k) := by
  rw [pad_column]
  exact reduces_join_left _ _

end
end OAI.TuringRigidity.ConeRelativeCoding
