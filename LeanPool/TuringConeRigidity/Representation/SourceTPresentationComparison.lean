/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTPresentationComparison.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTTreeAbsoluteness
public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticDischarge

/-!
# Source TPresentation Comparison
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelFunctions SetModelReals SetModelSyntax PersistentPresentation
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

def PresentationMatrix (O : Oracles) (v : ℕ) : Prop := Base (O 0) (O 1) ∧ Matrix O v

theorem presentationMatrix_arith : Arith PresentationMatrix := base_arith.and matrix_arith

theorem presentationMatrix_iff (A R : Oracle) :
    (∀ H : Oracle, PresentationMatrix (parameters A R H) 0) ↔ Property A R := by
  rw [property_iff]
  change (∀ H, Base A R ∧ Matrix (parameters A R H) 0) ↔ Base A R ∧ Criterion A R
  exact ⟨fun h => ⟨(h (fun _ => false)).1,fun H => (h H).2⟩,fun h H => ⟨h.1,h.2 H⟩⟩

def InternalPresentation (M : ZFSet.{u}) (A R : Oracle) : Prop :=
  ∀ H ∈ reals M, PresentationMatrix (parameters A R H) 0

def InternalNonidentity (M : ZFSet.{u}) (A : Oracle) : Prop :=
  ∃ R ∈ reals M, InternalPresentation M A R ∧ Moved A R

theorem internalPresentation_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) :
    InternalPresentation M A R ↔ Property A R :=
  (sourceT_piOneOne_matrix M hM hT presentationMatrix_arith A R hA hR 0).trans
    (presentationMatrix_iff A R)

theorem persistent_presentation_mem {M : ZFSet.{u}} (C : Context M)
    {A R : Oracle} (hA : A ∈ reals M) (hR : Property A R) : R ∈ reals M := by
  obtain ⟨I,hIA,hz,ρ,hgraph,hp⟩ := hR
  have hg := PersistenceRealClosure.graph_mem (realClosure C) hIA hA ρ hp hz
  have he : R = PersistentCountability.graphOracle hIA ρ := by
    funext n
    have hi : R n = true ↔ PersistentCountability.graphOracle hIA ρ n = true :=
      (hgraph n).trans (by simp [PersistentCountability.graphOracle])
    cases hr : R n <;> cases hg : PersistentCountability.graphOracle hIA ρ n <;> simp_all
  exact he.symm ▸ hg

theorem internalNonidentity_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ reals M) :
    InternalNonidentity M A ↔ ∃ R : Oracle, Property A R ∧ Moved A R := by
  constructor
  · rintro ⟨R,hR,hp,hm⟩
    exact ⟨R,(internalPresentation_iff M hM hT A R hA hR).mp hp,hm⟩
  · rintro ⟨R,hp,hm⟩
    have hR := persistent_presentation_mem (sourceContext M hM hT) hA hp
    exact ⟨R,hR,(internalPresentation_iff M hM hT A R hA hR).mpr hp,hm⟩

theorem presentation_comparison (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    (A R : Oracle) (hAM : A ∈ reals M) (hAN : A ∈ reals N)
    (hRM : R ∈ reals M) (hRN : R ∈ reals N) :
    (InternalPresentation M A R ↔ InternalPresentation N A R) ∧
    (InternalNonidentity M A ↔ InternalNonidentity N A) :=
  ⟨(internalPresentation_iff M hM hTM A R hAM hRM).trans
      (internalPresentation_iff N hN hTN A R hAN hRN).symm,
    (internalNonidentity_iff M hM hTM A hAM).trans
      (internalNonidentity_iff N hN hTN A hAN).symm⟩

end
end TuringRigidity.ArithmeticTree

end OAI
