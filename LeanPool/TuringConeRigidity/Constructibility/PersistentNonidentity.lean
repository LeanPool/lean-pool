/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistentNonidentity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticCoanalytic

/-!
# Persistent Nonidentity
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticPersistence
open EncodedForcing OracleJump UniformArithmetic PersistentRestrictions
open PersistentPresentation PersistentCountability NumericalAutomorphism
noncomputable section

/-- The coded action relates two columns with different Turing degrees. -/
def Moved (A R : Oracle) : Prop :=
  ∃ n m, R (Nat.pair n m) = true ∧ degree (columns A n) ≠ degree (columns A m)

theorem moved_iff {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (ρ : I ≃o I) (hR : ∀ v, R v = true ↔ Graph ρ hA v) :
    Moved A R ↔ ∃ x : I, ρ x ≠ x := by
  constructor
  · rintro ⟨n,m,hr,hne⟩
    refine ⟨entry hA n,fun he => ?_⟩
    have hg := (hR (Nat.pair n m)).mp hr
    simp only [PersistentPresentation.Graph,Nat.unpair_pair] at hg
    exact hne ((congrArg Subtype.val he).symm.trans hg)
  · rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := (hA x.val).mp x.property
    obtain ⟨m,hm⟩ := (hA (ρ x).val).mp (ρ x).property
    have he : entry hA n = x := Subtype.ext hn
    refine ⟨n,m,(hR _).mpr ?_,?_⟩
    · simp only [PersistentPresentation.Graph,Nat.unpair_pair]
      rw [he,hm]
    · intro hh
      apply hx
      apply Subtype.ext
      exact hm.symm.trans (hh.symm.trans hn)

theorem moved_arith : Arith (fun O (_ : ℕ) => Moved (O 0) (O 1)) := by
  have hp := query_at (parameter_arith 1) (Primrec.const 0)
    (Primrec₂.natPair.comp (UniformArithmetic.right_primrec.comp UniformArithmetic.left_primrec)
      UniformArithmetic.right_primrec)
  have he := degree_equal_arith
    (column_arith (parameter_arith 0) (UniformArithmetic.right_primrec.comp
      UniformArithmetic.left_primrec))
    (column_arith (parameter_arith 0) UniformArithmetic.right_primrec)
  exact (hp.and he.neg).ex.ex.congr
    (fun _ _ => by simp only [Moved,UniformArithmetic.left,UniformArithmetic.right,Nat.unpair_pair])

theorem nonidentity_piOneOne : PiOneOne (fun A R => Property A R ∧ Moved A R) := by
  obtain ⟨Q,hQ,hiff⟩ := source_4_2_1
  refine ⟨fun O v => Q O v ∧ Moved (O 0) (O 1),hQ.and moved_arith,fun A R => ?_⟩
  dsimp only
  rw [hiff]
  change ((∀ H, Q (parameters A R H) 0) ∧ Moved A R) ↔
    ∀ H, Q (parameters A R H) 0 ∧ Moved A R
  exact ⟨fun h H => ⟨h.1 H,h.2⟩,fun h => ⟨fun H => (h H).1,(h FixedArithmetic.zero).2⟩⟩

theorem nonidentity_coanalytic : MeasureTheory.AnalyticSet
    ({x : Oracle × Oracle | Property x.1 x.2 ∧ Moved x.1 x.2}ᶜ) :=
  nonidentity_piOneOne.coanalytic

theorem nonrigidity_witness (h : ¬ MainTheorem) :
    ∃ A R : Oracle, Property A R ∧ Moved A R := by
  classical
  simp only [MainTheorem,not_forall] at h
  obtain ⟨π,x,hx⟩ := h
  let z := degree (jump FixedArithmetic.zero)
  obtain ⟨I,hi,hf,hb⟩ := countable_invariant_hull π {x,z} (Set.toFinite _).countable
  let ρ := restrict π I hf hb
  have hρ : RestrictsTo π I ρ := fun _ => rfl
  have hp : Persistent I ρ := persistent_of_global_restriction π I ρ hρ
  have hz : z ∈ I.carrier := hi (by simp)
  have hxi : x ∈ I.carrier := hi (by simp)
  have hn : ∃ a : I, ρ a ≠ a := by
    refine ⟨⟨x,hxi⟩,fun he => ?_⟩
    exact hx (congrArg Subtype.val he)
  obtain ⟨A,hA⟩ := presentation_exists I
  let R := graphOracle hA ρ
  have hR : ∀ v, R v = true ↔ Graph ρ hA v := fun v => by simp [R,graphOracle]
  exact ⟨A,R,⟨I,hA,hz,ρ,hR,hp⟩,(moved_iff hA ρ hR).mpr hn⟩

end
end TuringRigidity.ArithmeticPersistence

end OAI
