/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/AntichainCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingGeneric
public import LeanPool.TuringConeRigidity.Effective.CodingRequirements

/-!
# Antichain Coding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AntichainCoding
open CodingForcing CodingColumns CodingDiagonal CodingGeneric CodingRequirements

/-- Indices for the diagonal and common-computation requirements in antichain coding. -/
abbrev Index := (ℕ × ℕ × OracleCode) ⊕ (OracleCode × OracleCode × OracleCode)

/-- Decode an antichain-coding requirement, treating invalid codes as vacuous requirements. -/
def requirements (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (B : Oracle) (n : ℕ) (p : Condition) : Prop :=
  match Encodable.decode (α := Index) n with
  | none => True
  | some (.inl (k, cutoff, e)) => Diagonal A hA k cutoff e p
  | some (.inr (c, e₀, e₁)) => GoodForCode A B c e₀ e₁ p

theorem requirements_dense (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (hIntro : ∀ k Z, (∀ a, Z a = true → A k a = true) →
      {a | Z a = true}.Infinite → Reduces (A k) Z) (B : Oracle) (n : ℕ) :
    Dense A (requirements A hA B n) := by
  intro p
  unfold requirements
  cases hd : Encodable.decode (α := Index) n with
  | none => exact ⟨p, extends_refl A p, trivial⟩
  | some x =>
    cases x with
    | inl v => exact diagonal_dense A hA v.1 v.2.1 v.2.2 p
    | inr v => exact goodForCode_dense A hIntro B v.1 v.2.1 v.2.2 p

theorem swap_join_reduces (G Y : Oracle) : Reduces (join G Y) (join Y G) :=
  join_reduces (reduces_join_right Y G) (reduces_join_left Y G)

theorem normalized_coding (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (hIntro : ∀ k Z, (∀ a, Z a = true → A k a = true) →
      {a | Z a = true}.Infinite → Reduces (A k) Z) (B : Oracle) :
    ∃ G₀ G₁ : Oracle,
      (∀ k, ∃ C : Oracle, Reduces C (join G₀ (A k)) ∧ Reduces C (join G₁ (A k)) ∧ ¬ Reduces C (A
        k)) ∧
      ∀ Y : Oracle, Reduces Y B →
        (∀ Z : Oracle, Reduces Z (join G₀ Y) → Reduces Z (join G₁ Y) → Reduces Z Y) ∨
        ∃ k, Reduces (A k) Y := by
  let R := requirements A hA B
  let hR := requirements_dense A hA hIntro B
  let G₀ := leftReal A R hR
  let G₁ := rightReal A R hR
  have hnot : ∀ k cutoff, ¬ Reduces (readColumn (A k) (hA k) k cutoff G₀) (A k) := by
    intro k cutoff h
    obtain ⟨e, he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
    let i := Encodable.encode (Sum.inl (k, cutoff, e) : Index)
    have hd : Diagonal A hA k cutoff e (stage A R hR (i+1)) := by
      simpa only [R, requirements, i, Encodable.encodek] using (stage_spec A R hR i).2.1
    obtain ⟨n, hn, hne⟩ := hd
    apply hne
    rw [he]
    change Part.some (if G₀ (location (A k) (hA k) k cutoff n) then 1 else 0) = _
    rw [show G₀ (location (A k) (hA k) k cutoff n) =
        (stage A R hR (i+1)).left.getD (location (A k) (hA k) k cutoff n) false from
      leftReal_extends A R hR (i+1) _ hn]
  refine ⟨G₀, G₁, ?_, ?_⟩
  · intro k
    let cutoff := (stage A R hR (k+1)).left.length
    let C := readColumn (A k) (hA k) k cutoff G₀
    have heq : C = readColumn (A k) (hA k) k cutoff G₁ := by
      funext n
      apply coding_agreement A R hR (k+1)
      have hm := location_mem (A k) (hA k) k cutoff n
      simp only [column] at hm
      split at hm
      next h =>
        refine ⟨h.1, ?_, ?_⟩
        · rw [h.2]; exact (stage_spec A R hR k).2.2.1
        · simpa only [h.2] using hm
      next h => simp at hm
    exact ⟨C, readColumn_reduces _ _ _ _ _, heq ▸ readColumn_reduces _ _ _ _ _, hnot k cutoff⟩
  · intro Y hY
    by_cases hk : ∃ k, Reduces (A k) Y
    · exact Or.inr hk
    · left
      intro Z h₀ h₁
      obtain ⟨c, hc⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hY
      obtain ⟨e₀, he₀⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp
        (reduces_trans h₀ (swap_join_reduces G₀ Y))
      obtain ⟨e₁, he₁⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp
        (reduces_trans h₁ (swap_join_reduces G₁ Y))
      let i := Encodable.encode (Sum.inr (c, e₀, e₁) : Index)
      have hg : GoodForCode A B c e₀ e₁ (stage A R hR (i+1)) := by
        simpa only [R, requirements, i, Encodable.encodek] using (stage_spec A R hR i).2.1
      have hleft : CommonIdeal.Extends G₀ (stage A R hR (i+1)).left :=
        fun n hn => leftReal_extends A R hR (i+1) n hn
      have hright : CommonIdeal.Extends G₁ (stage A R hR (i+1)).right := by
        intro n hn
        exact rightReal_extends A R hR (i+1) n (by simpa [← Condition.sameLength] using hn)
      exact (good_common_output hleft hright he₀ he₁ (hg Y hc)).resolve_right hk

theorem antichain_coding (A : ℕ → Oracle) (B : Oracle) :
    ∃ G₀ G₁ : Oracle,
      (∀ k, ∃ C : Oracle, Reduces C (join G₀ (A k)) ∧ Reduces C (join G₁ (A k)) ∧ ¬ Reduces C (A
        k)) ∧
      ∀ Y : Oracle, Reduces Y B →
        (∀ Z : Oracle, Reduces Z (join G₀ Y) → Reduces Z (join G₁ Y) → Reduces Z Y) ∨
        ∃ k, Reduces (A k) Y := by
  let F := fun k => Introreducible.prefixSet (A k)
  have hF : ∀ k, {a | F k a = true}.Infinite := fun k => Introreducible.prefixSet_infinite (A k)
  have hIntro : ∀ k Z, (∀ a, Z a = true → F k a = true) →
      {a | Z a = true}.Infinite → Reduces (F k) Z := by
    intro k Z hsub hinf
    exact reduces_trans (Introreducible.prefixSet_reduces (A k))
      (Introreducible.reduces_of_infinite_subset hsub hinf)
  obtain ⟨G₀, G₁, hfirst, hsecond⟩ := normalized_coding F hF hIntro B
  refine ⟨G₀, G₁, ?_, ?_⟩
  · intro k
    obtain ⟨C, h₀, h₁, hn⟩ := hfirst k
    have hFA := Introreducible.prefixSet_reduces (A k)
    have hAF := ((degree_eq_iff _ _).mp (Introreducible.prefixSet_degree (A k))).2
    exact ⟨C, reduces_trans h₀ (join_mono (reduces_refl G₀) hFA),
      reduces_trans h₁ (join_mono (reduces_refl G₁) hFA), fun hCA => hn (reduces_trans hCA hAF)⟩
  · intro Y hY
    rcases hsecond Y hY with h | ⟨k, hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, reduces_trans
        (((degree_eq_iff _ _).mp (Introreducible.prefixSet_degree (A k))).2) hk⟩

end TuringRigidity.AntichainCoding

end OAI
