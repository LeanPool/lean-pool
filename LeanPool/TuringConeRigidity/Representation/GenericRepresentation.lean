/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericRepresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.PairGenericSelection
public import LeanPool.TuringConeRigidity.Representation.CommonIdealSelection
public import LeanPool.TuringConeRigidity.SetModels.ContinuousCode
public import LeanPool.TuringConeRigidity.Representation.RepresentationEndgame
public import LeanPool.TuringConeRigidity.Representation.CoverageMain

/-!
# Generic Representation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
open FiniteShuffle ShuffleRequirements PairGenericSelection

theorem selected_generic_ideal (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n)) :
    ∃ G : Bool → Oracle → Oracle, (∀ b, Measurable (G b)) ∧
      (∀ A b, GenericFor D (G b A) ∧ GenericCoding.InfiniteOdd (G b A) ∧
        ∀ Y, GenericFor D (GenericCoding.code Y (G b A))) ∧
      ∀ A a, a ≤ degree A ↔ a ≤ degree (join A (G false A)) ∧ a ≤ degree (join A (G true A)) := by
  obtain ⟨Z,hZ,hgeneric,hfamily⟩ := borel_pair_selection D hd CommonIdeal.family
    CommonIdeal.family_dense CommonIdeal.family_measurable
  refine ⟨fun b A => column b (Z A),fun b => (column_measurable b).comp hZ,hgeneric,?_⟩
  intro A a
  exact CommonIdeal.ideal_of_family A (Z A) (hfamily A) a

/-- The automorphism has a continuous oracle lift on a set meeting a countable dense-open
family. -/
def GenericContinuousRepresentation (π : Degree ≃o Degree) : Prop :=
  ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
    ∃ f : Oracle → Oracle, ContinuousOn f {A | GenericFor D A} ∧
      ∀ A, GenericFor D A → degree (f A) = π (degree A)

theorem generic_continuous_of_subtype (π : Degree ≃o Degree)
    (D : ℕ → List Bool → Prop) (hD : ∀ n, DenseOpen (D n))
    (f : {A : Oracle // GenericFor D A} → Oracle) (hf : Continuous f)
    (hπ : ∀ A, degree (f A) = π (degree A.val)) : GenericContinuousRepresentation π := by
  classical
  let F : Oracle → Oracle := fun A => if hA : GenericFor D A then f ⟨A,hA⟩ else fun _ => false
  have hF : ContinuousOn F {A | GenericFor D A} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun A : {A : Oracle // GenericFor D A} => F A.val) = f := by
      funext A
      simp [F,A.property]
    change Continuous (fun A : {A : Oracle // GenericFor D A} => F A.val)
    rw [he]
    exact hf
  refine ⟨D,hD,F,hF,?_⟩
  intro A hA
  simpa [F,hA] using hπ ⟨A,hA⟩

/-- One program with a fixed oracle parameter represents the automorphism on a countable
dense-open generic domain. -/
def GenericProgramRepresentation (π : Degree ≃o Degree) : Prop :=
  ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
    ∃ P : Oracle, ∃ p : OracleCode, ∀ A, GenericFor D A →
      ∃ B, OracleCode.eval (oracleFunction (join A P)) p = oracleFunction B ∧ degree B = π (degree
        A)

theorem generic_program_of_continuous (π : Degree ≃o Degree)
    (h : GenericContinuousRepresentation π) : GenericProgramRepresentation π := by
  obtain ⟨D,hD,f,hf,hπ⟩ := h
  obtain ⟨P,p,hp⟩ := ContinuousCode.continuous_uniform_program {A | GenericFor D A} f hf
  exact ⟨D,hD,P,p,fun A hA => ⟨f A,hp A hA,hπ A hA⟩⟩

theorem borel_of_generic_program (π : Degree ≃o Degree) (h : GenericProgramRepresentation π) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  obtain ⟨D,hD,P,p,hp⟩ := h
  obtain ⟨G,hG,hgeneric,hideal⟩ := selected_generic_ideal D hD
  exact representative_from_generic_program π p P G hG
    (fun A b => (hgeneric A b).2.1)
    (fun A b => hp (G b A) (hgeneric A b).1)
    (fun A b => hp (GenericCoding.code A (G b A)) ((hgeneric A b).2.2 A)) hideal

theorem borel_of_generic_continuous (π : Degree ≃o Degree) (h : GenericContinuousRepresentation π) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) :=
  borel_of_generic_program π (generic_program_of_continuous π h)

theorem main_of_generic_continuous (h : ∀ π, GenericContinuousRepresentation π) : MainTheorem :=
  main_of_representation (fun π => borel_of_generic_continuous π (h π))

end TuringRigidity

end OAI
