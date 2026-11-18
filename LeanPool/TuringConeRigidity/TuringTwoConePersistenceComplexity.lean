/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePersistenceComplexity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeArithmeticCriterion
public import LeanPool.TuringConeRigidity.Computability.ArithmeticPresentationProperty

/-!
# A uniform Pi-1-1 definition of persistent two-cone maps

A presents an ordinary ideal, R its conventional partial graph, and k pairs
the two base-column indices. Valid graph codes reconstruct actual maps. The
only real quantifier in the resulting normal form is universal over larger
presentations H; their extension graphs are supplied by natural program indices.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePersistenceComplexity

open EncodedForcing OracleJump UniformArithmetic PersistentRestrictions
open ConePersistence (Cone)
open ConePresentation (Presented)
open TwoConePresentation (RawGraph)

noncomputable section

/-- A coded ideal containing both base jumps and a coded action between its two principal
cones. -/
def Base (A R : Oracle) (k : ℕ) : Prop :=
  ArithmeticPersistence.IdealCode A ∧
    (∃ n, degreeJump (degree (columns A (Nat.unpair k).1)) = degree (columns A n)) ∧
    (∃ n, degreeJump (degree (columns A (Nat.unpair k).2)) = degree (columns A n)) ∧
    TwoConeNumerical.Action (columns A (Nat.unpair k).1) (columns A (Nat.unpair k).2)
      A (fun v => R v = true)

/-- A semantic property of an actual map, not a complexity assumption. -/
def Property (A R : Oracle) (k : ℕ) : Prop :=
  ∃ I : CountableIdeal, ∃ _hA : Presented I A,
    degreeJump (degree (columns A (Nat.unpair k).1)) ∈ I.carrier ∧
    degreeJump (degree (columns A (Nat.unpair k).2)) ∈ I.carrier ∧
      ∃ ρ : Cone I (degree (columns A (Nat.unpair k).1)) ≃o
          Cone I (degree (columns A (Nat.unpair k).2)),
        (∀ v, R v = true ↔ RawGraph ρ A v) ∧ TwoConePersistence.Persistent I ρ

theorem property_iff (A R : Oracle) (k : ℕ) :
    Property A R k ↔ Base A R k ∧ TwoConeArithmeticCriterion.Criterion A R k := by
  constructor
  · rintro ⟨I, hA, hza, hzb, ρ, hR, hp⟩
    have ha := (TwoConeNumerical.action_congr hR).mpr (TwoConeNumerical.action_of_iso hA ρ)
    obtain ⟨n, hn⟩ := (hA _).mp hza
    obtain ⟨m, hm⟩ := (hA _).mp hzb
    exact ⟨⟨ArithmeticPersistence.ideal_code hA, ⟨n, hn.symm⟩, ⟨m, hm.symm⟩, ha⟩,
      (TwoConeArithmeticCriterion.persistent_iff hA k ρ hza hzb hR).mp hp⟩
  · rintro ⟨⟨hi, ⟨n, hn⟩, ⟨m, hm⟩, ha⟩, hc⟩
    let I := ArithmeticPersistence.idealOfCode A hi
    have hA : Presented I A := fun _ => Iff.rfl
    have hza : degreeJump (degree (columns A (Nat.unpair k).1)) ∈ I.carrier :=
      (hA _).mpr ⟨n, hn.symm⟩
    have hzb : degreeJump (degree (columns A (Nat.unpair k).2)) ∈ I.carrier :=
      (hA _).mpr ⟨m, hm.symm⟩
    obtain ⟨ρ, hR⟩ := TwoConeNumerical.reconstruct hA ha
    exact ⟨I, hA, hza, hzb, ρ, hR,
      (TwoConeArithmeticCriterion.persistent_iff hA k ρ hza hzb hR).mpr hc⟩

theorem base_arith : Arith (fun O k => Base (O 0) (O 1) k) := by
  have hA := parameter_arith 0
  have hR := parameter_arith 1
  have hB := column_arith hA (Primrec.fst.comp Primrec.unpair)
  have hC := column_arith hA (Primrec.snd.comp Primrec.unpair)
  have hzB := (degree_equal_arith (jump_arith (hB.comp UniformArithmetic.left_primrec))
    (columns_at hA UniformArithmetic.left_primrec UniformArithmetic.right_primrec)).ex
  have hzC := (degree_equal_arith (jump_arith (hC.comp UniformArithmetic.left_primrec))
    (columns_at hA UniformArithmetic.left_primrec UniformArithmetic.right_primrec)).ex
  have hi := (lower_arith hA).and (join_closed_arith hA)
  exact (hi.and (hzB.and (hzC.and (TwoConeArithmeticCriterion.action_arith hB hC hA hR)))).congr
    (fun _ _ => by simp only [Base, ArithmeticPersistence.IdealCode,
      UniformArithmetic.left, UniformArithmetic.right, Nat.unpair_pair, degreeJump_degree])

/-- Combine the two-cone presentation's base conditions with its arithmetic persistence
matrix. -/
def PresentationMatrix (O : Oracles) (k : ℕ) : Prop :=
  Base (O 0) (O 1) k ∧ TwoConeArithmeticCriterion.Matrix O k

theorem presentationMatrix_arith : Arith PresentationMatrix :=
  base_arith.and TwoConeArithmeticCriterion.matrix_arith

theorem presentationMatrix_iff (A R : Oracle) (k : ℕ) :
    (∀ H : Oracle, PresentationMatrix (ArithmeticPersistence.parameters A R H) k) ↔
      Property A R k := by
  rw [property_iff]
  change (∀ H, Base A R k ∧ TwoConeArithmeticCriterion.Matrix
    (ArithmeticPersistence.parameters A R H) k) ↔
      Base A R k ∧ TwoConeArithmeticCriterion.Criterion A R k
  exact ⟨fun h => ⟨(h FixedArithmetic.zero).1, fun H => (h H).2⟩,
    fun h H => ⟨h.1, h.2 H⟩⟩

/-- One arithmetic matrix, uniform in the two reals and both base indices. -/
theorem piOneOne_uniform :
    ∃ Q : Predicate, Arith Q ∧ ∀ (A R : Oracle) (k : ℕ),
      Property A R k ↔ ∀ H : Oracle, Q (ArithmeticPersistence.parameters A R H) k :=
  ⟨PresentationMatrix, presentationMatrix_arith,
    fun A R k => (presentationMatrix_iff A R k).symm⟩

theorem piOneOne (k : ℕ) :
    ArithmeticPersistence.PiOneOne (fun A R => Property A R k) := by
  refine ⟨fun O _ => PresentationMatrix O k,
    Arith.comp (fun _ => k) presentationMatrix_arith (Primrec.const k), ?_⟩
  exact fun A R => (presentationMatrix_iff A R k).symm

end
end OAI.TuringRigidity.TwoConePersistenceComplexity
