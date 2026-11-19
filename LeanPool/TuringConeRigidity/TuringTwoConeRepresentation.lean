/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeRepresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeRigidity
public import LeanPool.TuringConeRigidity.Representation.GenericRepresentation

/-!
# Generic representatives for maps between two cones

The generic-to-Borel upgrade uses a minimal pair over the TARGET base joined
with the input. Common lower bounds outside the source cone are handled by
joining with the source base before applying the isomorphism.

The existence of the generic representative for an arbitrary two-cone map
remains an explicit hypothesis throughout this file.
-/


@[expose] public section


namespace OAI.TuringRigidity.TwoConeRigidity

open FiniteShuffle ShuffleRequirements PairGenericSelection

/-- The pullback has a continuous oracle lift on a countable dense-open generic domain. -/
def InverseGenericContinuousLift {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) : Prop :=
  ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
    ∃ F : Oracle → Oracle, ContinuousOn F {X | GenericFor D X} ∧
      ∀ X, GenericFor D X → degree (F X) = pullback e (degree X)

/-- One program with a fixed oracle parameter computes the pullback on a countable dense-open
generic domain. -/
def InverseGenericProgramLift {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) : Prop :=
  ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
    ∃ P : Oracle, ∃ p : OracleCode, ∀ X, GenericFor D X →
      ∃ Y, OracleCode.eval (oracleFunction (join X P)) p = oracleFunction Y ∧
        degree Y = pullback e (degree X)

theorem inverse_generic_program_of_continuous {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (h : InverseGenericContinuousLift e) :
    InverseGenericProgramLift e := by
  obtain ⟨D, hD, F, hF, hrep⟩ := h
  obtain ⟨P, p, hp⟩ := ContinuousCode.continuous_uniform_program
    {X | GenericFor D X} F hF
  exact ⟨D, hD, P, p, fun X hX => ⟨F X, hp X hX, hrep X hX⟩⟩

/-- Minimal pairs are chosen over `B ⊕ X`, with `degree B = b`. -/
theorem inverse_borel_lift_of_generic_program {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (h : InverseGenericProgramLift e) :
    InverseBorelLift e := by
  obtain ⟨B, hB⟩ := degree_surjective b
  obtain ⟨D, hD, P, p, hp⟩ := h
  obtain ⟨K, L, hL, hdegree, hideal⟩ :=
    joined_generic_program_pair (pullback e) (pullback_sup e) B D hD P p hp
  apply borel_of_ideal_intersection (L false) (L true) (hL false) (hL true)
    (fun X => pullback e (degree X))
  intro X z
  rw [hdegree X false, hdegree X true]
  simp only [le_pullback_iff]
  have hbase := hideal X (imageJoin e z)
  change (imageJoin e z ≤ degree B ⊔ degree X ↔
    imageJoin e z ≤ (degree B ⊔ degree X) ⊔ degree (K false X) ∧
    imageJoin e z ≤ (degree B ⊔ degree X) ⊔ degree (K true X)) at hbase
  change imageJoin e z ≤ b ⊔ degree X ↔
    imageJoin e z ≤ b ⊔ (degree X ⊔ degree (K false X)) ∧
    imageJoin e z ≤ b ⊔ (degree X ⊔ degree (K true X))
  simpa only [hB, sup_assoc] using hbase

theorem inverse_borel_lift_of_generic_continuous {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (h : InverseGenericContinuousLift e) :
    InverseBorelLift e :=
  inverse_borel_lift_of_generic_program e (inverse_generic_program_of_continuous e h)

theorem target_le_source_of_inverse_generic_program {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (h : InverseGenericProgramLift e) : b ≤ a :=
  target_le_source_of_inverse_borel_lift e (inverse_borel_lift_of_generic_program e h)

theorem bases_eq_of_inverse_generic_programs {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (hinv : InverseGenericProgramLift e)
    (hfwd : InverseGenericProgramLift e.symm) : a = b :=
  bases_eq_of_inverse_borel_lifts e (inverse_borel_lift_of_generic_program e hinv)
    (inverse_borel_lift_of_generic_program e.symm hfwd)

theorem apply_val_eq_of_inverse_generic_programs {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (hinv : InverseGenericProgramLift e)
    (hfwd : InverseGenericProgramLift e.symm) (x : Set.Ici a) : (e x).val = x.val :=
  apply_val_eq_of_inverse_borel_lifts e (inverse_borel_lift_of_generic_program e hinv)
    (inverse_borel_lift_of_generic_program e.symm hfwd) x

theorem bases_eq_of_inverse_generic_continuous_lifts {a b : Degree}
    (e : Set.Ici a ≃o Set.Ici b) (hinv : InverseGenericContinuousLift e)
    (hfwd : InverseGenericContinuousLift e.symm) : a = b :=
  bases_eq_of_inverse_borel_lifts e (inverse_borel_lift_of_generic_continuous e hinv)
    (inverse_borel_lift_of_generic_continuous e.symm hfwd)

/-- The remaining representation theorem is explicitly assumed, not asserted. -/
theorem cones_orderIso_iff_of_generic_representation
    (hrep : ∀ (a b : Degree) (e : Set.Ici a ≃o Set.Ici b),
      InverseGenericProgramLift e) (a b : Degree) :
    Nonempty (Set.Ici a ≃o Set.Ici b) ↔ a = b := by
  constructor
  · rintro ⟨e⟩
    exact bases_eq_of_inverse_generic_programs e (hrep a b e) (hrep b a e.symm)
  · intro h
    subst b
    exact ⟨OrderIso.refl _⟩

/-- The same explicit representation hypothesis gives rigidity of each cone. -/
theorem apply_val_eq_of_generic_representation
    (hrep : ∀ (a b : Degree) (e : Set.Ici a ≃o Set.Ici b),
      InverseGenericProgramLift e) {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (x : Set.Ici a) : (e x).val = x.val :=
  apply_val_eq_of_inverse_generic_programs e (hrep a b e) (hrep b a e.symm) x

end OAI.TuringRigidity.TwoConeRigidity
