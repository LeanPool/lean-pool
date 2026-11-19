/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ConservativeExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.CommonIdealSearch

/-!
# Conservative Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ConservativeExtension
open CommonIdeal

/-- The finite word either gives a wrong computed bit or makes every successful future output
agree with `Y`. -/
def Decide (A Y : Oracle) (e : OracleCode) (s : List Bool) : Prop :=
  (∃ n a, a ∈ run A e s n ∧ a ≠ bit (Y n)) ∨
  ∀ t, s <+: t → ∀ n a, a ∈ run A e t n → a = bit (Y n)

theorem decide_dense (A Y : Oracle) (e : OracleCode) (s : List Bool) :
    ∃ t, s <+: t ∧ Decide A Y e t := by
  by_cases h : ∃ t, s <+: t ∧ ∃ n a, a ∈ run A e t n ∧ a ≠ bit (Y n)
  · obtain ⟨t, ht, h⟩ := h
    exact ⟨t, ht, Or.inl h⟩
  · refine ⟨s, List.prefix_rfl, Or.inr ?_⟩
    intro t ht n a ha
    by_contra hn
    exact h ⟨t, ht, n, a, ha, hn⟩

theorem removes_oracle {A Y G : Oracle} {e : OracleCode} {s : List Bool}
    (hG : Extends G s) (hD : Decide A Y e s)
    (he : OracleCode.eval (oracleFunction (join A G)) e = oracleFunction Y) :
    Reduces Y A := by
  have hu : ∀ t, s <+: t → ∀ n a, a ∈ run A e t n → a = bit (Y n) := by
    rcases hD with ⟨n, a, ha, hn⟩ | hD
    · have hh := run_total hG n a ha
      rw [he] at hh
      exact False.elim (hn (Part.mem_some_iff.mp hh))
    · exact hD
  apply common_output_reduces (G := G) (H := G) (p := e) (q := e)
    (s := s) (t := s) hG hG (Or.inr ?_) he he
  intro u v n a b hu' hv' ha hb
  exact (hu u hu' n a ha).trans (hu v hv' n b hb).symm

/-- A finite word disagrees with the designated computation from `B`, including when that
computation is undefined. -/
def Diagonal (B : Oracle) (e : OracleCode) (s : List Bool) : Prop :=
  ∃ n, n < s.length ∧
    OracleCode.eval (oracleFunction B) e n ≠ Part.some (bit (s.getD n false))

theorem diagonal_dense (B : Oracle) (e : OracleCode) (s : List Bool) :
    ∃ t, s <+: t ∧ Diagonal B e t := by
  have hex : ∃ b : Bool, OracleCode.eval (oracleFunction B) e s.length ≠ Part.some (bit b) := by
    by_cases h : OracleCode.eval (oracleFunction B) e s.length = Part.some (bit false)
    · exact ⟨true, by rw [h]; simp [bit]⟩
    · exact ⟨false, h⟩
  obtain ⟨b, hb⟩ := hex
  refine ⟨s ++ [b], List.prefix_append _ _, s.length, by simp, ?_⟩
  simpa [List.getD_eq_getElem?_getD, List.getElem?_append] using hb

theorem meets_countable {ι : Type*} [Countable ι] (R : ι → List Bool → Prop)
    (hR : ∀ i s, ∃ t, s <+: t ∧ R i t) :
    ∃ G : Oracle, ∀ i, ∃ s, Extends G s ∧ R i s := by
  classical
  let := Encodable.ofCountable ι
  let Q : Unit → ℕ → ℕ → Prop := fun _ n c =>
    ∀ i, Encodable.decode n = some i → R i (BorelGeneric.word c)
  have hd : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ Q x n t := by
    intro x n s
    let u := BorelGeneric.word s ++ [false]
    have hs : BorelGeneric.word s <+: u := List.prefix_append _ _
    have hl : (BorelGeneric.word s).length < u.length := by simp [u]
    cases hh : Encodable.decode (α := ι) n with
    | none =>
      obtain ⟨t, ht⟩ := BorelGeneric.word_surjective u
      refine ⟨t, ⟨ht ▸ hs, ht ▸ hl⟩, ?_⟩
      intro i hi
      simp [hh] at hi
    | some i =>
      obtain ⟨v, huv, hv⟩ := hR i u
      obtain ⟨t, ht⟩ := BorelGeneric.word_surjective v
      refine ⟨t, ⟨ht ▸ hs.trans huv, ht ▸ hl.trans_le huv.length_le⟩, ?_⟩
      intro j hj
      have he : i = j := Option.some.inj (hh.symm.trans hj)
      subst j
      simpa [ht] using hv
  refine ⟨BorelGeneric.generic Q hd (), ?_⟩
  intro i
  let n := Encodable.encode i
  let t := BorelGeneric.stage Q hd (n+1) ()
  refine ⟨BorelGeneric.word t, BorelGeneric.meets_stage Q hd () (n+1), ?_⟩
  exact (BorelGeneric.next_spec Q hd n () (BorelGeneric.stage Q hd n ())).2 i
    (by simp [n])

theorem exists_conservative_extension (B : Oracle) :
    ∃ C : Oracle, ¬ Reduces C B ∧
      ∀ A Y : Oracle, Reduces A B → Reduces Y B →
        Reduces Y (join A C) → Reduces Y A := by
  let L := {A : Oracle // Reduces A B}
  have : Countable L := (countable_reduces B).to_subtype
  let I := Sum OracleCode (L × L × OracleCode)
  let R : I → List Bool → Prop := fun i s => match i with
    | .inl e => Diagonal B e s
    | .inr (A, Y, e) => Decide A.val Y.val e s
  have hR : ∀ i s, ∃ t, s <+: t ∧ R i t := by
    intro i s
    cases i with
    | inl e => exact diagonal_dense B e s
    | inr v => exact decide_dense v.1.val v.2.1.val v.2.2 s
  obtain ⟨C, hC⟩ := meets_countable R hR
  refine ⟨C, ?_, ?_⟩
  · intro h
    obtain ⟨e, he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
    obtain ⟨s, hs, n, hn, hne⟩ := hC (.inl e)
    apply hne
    rw [he]
    change Part.some (bit (C n)) = _
    rw [hs n hn]
  · intro A Y hA hY h
    obtain ⟨e, he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
    obtain ⟨s, hs, hd⟩ := hC (.inr (⟨A, hA⟩, ⟨Y, hY⟩, e))
    exact removes_oracle hs hd he

theorem exists_conservative_degree (b : Degree) :
    ∃ c : Degree, ¬ c ≤ b ∧
      ∀ a y : Degree, a ≤ b → y ≤ b → y ≤ a ⊔ c → y ≤ a := by
  obtain ⟨B, rfl⟩ := degree_surjective b
  obtain ⟨C, hC, h⟩ := exists_conservative_extension B
  refine ⟨degree C, hC, ?_⟩
  intro a y ha hy hr
  obtain ⟨A, rfl⟩ := degree_surjective a
  obtain ⟨Y, rfl⟩ := degree_surjective y
  exact h A Y ha hy hr

end TuringRigidity.ConservativeExtension

end OAI
