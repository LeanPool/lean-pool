/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePersistenceAbsoluteness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePersistenceComplexity
public import LeanPool.TuringConeRigidity.TuringConeRealClosure
public import LeanPool.TuringConeRigidity.Representation.SourceTPresentationComparison

/-!
# Absoluteness of coded cone persistence

The arithmetic-tree absoluteness theorem is independent of the degree-theoretic
meaning of its matrix. Applying it to the checked cone matrix proves agreement
between its interpretation over a transitive SourceT model's reals and ambient
persistence. Graph codes and extension witnesses are also internal to the
model's real collection.

This file concerns the coded presentation property. It does not yet identify
that property with a new native set-theoretic cone-persistence formula, nor
construct extensions of global cone isomorphisms to forcing extensions.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePersistenceAbsoluteness

open UniformArithmetic BoundedSetTheory TransitiveNameModel
open SetModelFunctions SetModelReals SetModelSyntax
open PersistentRestrictions ConePersistence ConePresentation ConePersistenceComplexity

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The same explicit arithmetic matrix, with its real quantifier restricted
to the model. Natural-number quantifiers in the matrix are unchanged. -/
def InternalPresentation (M : ZFSet.{u}) (A R : Oracle) (k : ℕ) : Prop :=
  ∀ H ∈ reals M, PresentationMatrix (ArithmeticPersistence.parameters A R H) k

theorem internalPresentation_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (k : ℕ) :
    InternalPresentation M A R k ↔ Property A R k :=
  (ArithmeticTree.sourceT_piOneOne_matrix M hM hT presentationMatrix_arith
    A R hA hR k).trans (presentationMatrix_iff A R k)

/-- Directly relate the internal numerical extension criterion to persistence
of the actual partial cone map. -/
theorem internal_criterion_iff_persistent (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (hAM : A ∈ reals M) (hRM : R ∈ reals M) (k : ℕ)
    (ρ : I ≃o Cone I (degree (EncodedForcing.columns A k)))
    (hza : OracleJump.degreeJump (degree (EncodedForcing.columns A k)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ Graph ρ hA v) :
    (∀ H ∈ reals M,
      ConeArithmeticCriterion.Matrix (ArithmeticPersistence.parameters A R H) k) ↔
      ConePersistence.Persistent I ρ :=
  (ArithmeticTree.sourceT_piOneOne_matrix M hM hT ConeArithmeticCriterion.matrix_arith
    A R hAM hRM k).trans (ConeArithmeticCriterion.persistent_iff hA k ρ hza hR).symm

/-- Once the presentation is in the model, the code of any persistent graph
on it is there too. This is proved from the eleven-jump bound. -/
theorem persistent_presentation_mem {M : ZFSet.{u}} (C : Context M)
    {A R : Oracle} (hA : A ∈ reals M) {k : ℕ} (hR : Property A R k) :
    R ∈ reals M := by
  obtain ⟨I, hIA, hza, ρ, hgraph, hp⟩ := hR
  have hg := ConeRealClosure.graph_mem (realClosure C) hIA hA ρ hp hza
  have he : R = graphOracle hIA ρ := by
    funext n
    have hi : R n = true ↔ graphOracle hIA ρ n = true :=
      (hgraph n).trans (by simp [graphOracle])
    cases hr : R n <;> cases hg : graphOracle hIA ρ n <;> simp_all
  exact he.symm ▸ hg

def InternalExistence (M : ZFSet.{u}) (A : Oracle) (k : ℕ) : Prop :=
  ∃ R ∈ reals M, InternalPresentation M A R k

/-- The existential graph code adds no loss of absoluteness: all possible
persistent graph codes already belong to the model. -/
theorem internalExistence_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ reals M) (k : ℕ) :
    InternalExistence M A k ↔ ∃ R : Oracle, Property A R k := by
  constructor
  · rintro ⟨R, hR, hp⟩
    exact ⟨R, (internalPresentation_iff M hM hT A R hA hR k).mp hp⟩
  · rintro ⟨R, hp⟩
    have hR := persistent_presentation_mem (ArithmeticTree.sourceContext M hM hT) hA hp
    exact ⟨R, hR, (internalPresentation_iff M hM hT A R hA hR k).mpr hp⟩

/-- Compare any two suitable transitive models containing the parameters;
neither inclusion nor a forcing relationship is needed for the coded claim. -/
theorem presentation_comparison (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    (A R : Oracle) (hAM : A ∈ reals M) (hAN : A ∈ reals N)
    (hRM : R ∈ reals M) (hRN : R ∈ reals N) (k : ℕ) :
    InternalPresentation M A R k ↔ InternalPresentation N A R k :=
  (internalPresentation_iff M hM hTM A R hAM hRM k).trans
    (internalPresentation_iff N hN hTN A R hAN hRN k).symm

theorem existence_comparison (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    (A : Oracle) (hAM : A ∈ reals M) (hAN : A ∈ reals N) (k : ℕ) :
    InternalExistence M A k ↔ InternalExistence N A k :=
  (internalExistence_iff M hM hTM A hAM k).trans
    (internalExistence_iff N hN hTN A hAN k).symm

end
end OAI.TuringRigidity.ConePersistenceAbsoluteness
