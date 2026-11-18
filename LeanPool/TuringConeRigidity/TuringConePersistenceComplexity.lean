/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePersistenceComplexity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeArithmeticCriterion
public import LeanPool.TuringConeRigidity.Computability.ArithmeticPresentationProperty

/-!
# A uniform Pi-1-1 definition of persistent cone maps

A real A presents an ordinary ideal; R codes the indexed graph; k selects a
column of A representing the base degree. The property below is semantic, and
the theorems identify it with a genuinely arithmetic matrix preceded by a
single universal real quantifier. The matrix uses only numerical indices for
extension maps. No projective-complexity claim is assumed.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePersistenceComplexity

open EncodedForcing OracleJump UniformArithmetic PersistentRestrictions
open ConePersistence ConePresentation

noncomputable section

/-- A coded ideal containing the base jump and carrying a coded action onto its principal
cone. -/
def Base (A R : Oracle) (k : ℕ) : Prop :=
  ArithmeticPersistence.IdealCode A ∧
    (∃ n, degreeJump (degree (columns A k)) = degree (columns A n)) ∧
    ConeNumerical.Action (columns A k) A (fun v => R v = true)

/-- Codes an actual persistent partial cone isomorphism. The base is the
k-th column, and its jump must belong to the presented ideal. -/
def Property (A R : Oracle) (k : ℕ) : Prop :=
  ∃ I : CountableIdeal, ∃ hA : Presented I A,
    degreeJump (degree (columns A k)) ∈ I.carrier ∧
      ∃ ρ : I ≃o Cone I (degree (columns A k)),
        (∀ v, R v = true ↔ ConePresentation.Graph ρ hA v) ∧ ConePersistence.Persistent I ρ

theorem property_iff (A R : Oracle) (k : ℕ) :
    Property A R k ↔ Base A R k ∧ ConeArithmeticCriterion.Criterion A R k := by
  constructor
  · rintro ⟨I, hA, hza, ρ, hR, hp⟩
    have ha := (ConeNumerical.action_congr hR).mpr (ConeNumerical.action_of_iso hA ρ)
    obtain ⟨n, hn⟩ := (hA _).mp hza
    exact ⟨⟨ArithmeticPersistence.ideal_code hA, ⟨n, hn.symm⟩, ha⟩,
      (ConeArithmeticCriterion.persistent_iff hA k ρ hza hR).mp hp⟩
  · rintro ⟨⟨hi, ⟨n, hn⟩, ha⟩, hc⟩
    let I := ArithmeticPersistence.idealOfCode A hi
    have hA : Presented I A := fun _ => Iff.rfl
    have hza : degreeJump (degree (columns A k)) ∈ I.carrier := (hA _).mpr ⟨n, hn.symm⟩
    obtain ⟨ρ, hR⟩ := ConeNumerical.reconstruct hA ha
    exact ⟨I, hA, hza, ρ, hR,
      (ConeArithmeticCriterion.persistent_iff hA k ρ hza hR).mpr hc⟩

theorem base_arith : Arith (fun O k => Base (O 0) (O 1) k) := by
  have hA := parameter_arith 0
  have hR := parameter_arith 1
  have hB := column_arith hA Primrec.id
  have hz := (degree_equal_arith (jump_arith (hB.comp UniformArithmetic.left_primrec))
    (columns_at hA UniformArithmetic.left_primrec UniformArithmetic.right_primrec)).ex
  have hi := (lower_arith hA).and (join_closed_arith hA)
  exact (hi.and (hz.and (ConeArithmeticCriterion.action_arith hB hA hR))).congr
    (fun _ _ => by simp only [Base, ArithmeticPersistence.IdealCode,
      UniformArithmetic.left, UniformArithmetic.right, Nat.unpair_pair, degreeJump_degree, id_eq])

/-- Combine the cone presentation's base conditions with its arithmetic persistence matrix. -/
def PresentationMatrix (O : Oracles) (k : ℕ) : Prop :=
  Base (O 0) (O 1) k ∧ ConeArithmeticCriterion.Matrix O k

theorem presentationMatrix_arith : Arith PresentationMatrix :=
  base_arith.and ConeArithmeticCriterion.matrix_arith

theorem presentationMatrix_iff (A R : Oracle) (k : ℕ) :
    (∀ H : Oracle, PresentationMatrix (ArithmeticPersistence.parameters A R H) k) ↔
      Property A R k := by
  rw [property_iff]
  change (∀ H, Base A R k ∧ ConeArithmeticCriterion.Matrix
    (ArithmeticPersistence.parameters A R H) k) ↔
      Base A R k ∧ ConeArithmeticCriterion.Criterion A R k
  exact ⟨fun h => ⟨(h FixedArithmetic.zero).1, fun H => (h H).2⟩,
    fun h H => ⟨h.1, h.2 H⟩⟩

/-- One arithmetic matrix works uniformly for all two real parameters and
all base-column indices. This is the claimed Pi-1-1 normal form. -/
theorem piOneOne_uniform :
    ∃ Q : Predicate, Arith Q ∧ ∀ (A R : Oracle) (k : ℕ),
      Property A R k ↔ ∀ H : Oracle, Q (ArithmeticPersistence.parameters A R H) k :=
  ⟨PresentationMatrix, presentationMatrix_arith,
    fun A R k => (presentationMatrix_iff A R k).symm⟩

/-- Also express each section using the original development's PiOneOne
predicate, rather than introducing a new complexity convention. -/
theorem piOneOne (k : ℕ) :
    ArithmeticPersistence.PiOneOne (fun A R => Property A R k) := by
  refine ⟨fun O _ => PresentationMatrix O k,
    Arith.comp (fun _ => k) presentationMatrix_arith (Primrec.const k), ?_⟩
  exact fun A R => (presentationMatrix_iff A R k).symm

end
end OAI.TuringRigidity.ConePersistenceComplexity
