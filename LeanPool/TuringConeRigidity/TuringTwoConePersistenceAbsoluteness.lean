/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePersistenceAbsoluteness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePersistenceComplexity
public import LeanPool.TuringConeRigidity.TuringTwoConeRealClosure
public import LeanPool.TuringConeRigidity.Representation.SourceTPresentationComparison

/-!
# Absoluteness of coded persistence between two cones

Apply the existing arithmetic-tree theorem to the checked two-cone matrix.
Its internal universal quantifier ranges over the model's reals. The graph
codes of persistent maps already belong to the model by the eleven-jump bound,
which also yields agreement on existence of a persistent map.

These statements concern real-coded countable maps, not yet native set graphs
or the extension of a global map through forcing.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePersistenceAbsoluteness

open UniformArithmetic BoundedSetTheory TransitiveNameModel
open SetModelFunctions SetModelReals SetModelSyntax
open PersistentRestrictions
open ConePersistence (Cone)
open ConePresentation (Presented)
open TwoConePresentation (RawGraph)
open TwoConeNumerical (graphOracle)
open TwoConePersistenceComplexity

universe u
noncomputable section

/-- k pairs the two base-column indices; A and R are the only real parameters. -/
def InternalPresentation (M : ZFSet.{u}) (A R : Oracle) (k : ℕ) : Prop :=
  ∀ H ∈ reals M, PresentationMatrix (ArithmeticPersistence.parameters A R H) k

theorem internalPresentation_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (k : ℕ) :
    InternalPresentation M A R k ↔ Property A R k :=
  (ArithmeticTree.sourceT_piOneOne_matrix M hM hT presentationMatrix_arith
    A R hA hR k).trans (presentationMatrix_iff A R k)

theorem internal_criterion_iff_persistent (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (hAM : A ∈ reals M) (hRM : R ∈ reals M) (k : ℕ)
    (ρ : Cone I (degree (EncodedForcing.columns A (Nat.unpair k).1)) ≃o
      Cone I (degree (EncodedForcing.columns A (Nat.unpair k).2)))
    (hza : OracleJump.degreeJump (degree (EncodedForcing.columns A (Nat.unpair k).1)) ∈ I.carrier)
    (hzb : OracleJump.degreeJump (degree (EncodedForcing.columns A (Nat.unpair k).2)) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ RawGraph ρ A v) :
    (∀ H ∈ reals M,
      TwoConeArithmeticCriterion.Matrix (ArithmeticPersistence.parameters A R H) k) ↔
      TwoConePersistence.Persistent I ρ :=
  (ArithmeticTree.sourceT_piOneOne_matrix M hM hT TwoConeArithmeticCriterion.matrix_arith
    A R hAM hRM k).trans
      (TwoConeArithmeticCriterion.persistent_iff hA k ρ hza hzb hR).symm

/-- Graph codes require no extra membership hypothesis once persistence holds. -/
theorem persistent_presentation_mem {M : ZFSet.{u}} (C : Context M)
    {A R : Oracle} (hA : A ∈ reals M) {k : ℕ} (hR : Property A R k) :
    R ∈ reals M := by
  obtain ⟨I, hIA, hza, hzb, ρ, hgraph, hp⟩ := hR
  have hg := TwoConeRealClosure.graph_mem (realClosure C) hIA hA ρ hp hza hzb
  have he : R = graphOracle ρ A := by
    funext n
    have hi : R n = true ↔ graphOracle ρ A n = true :=
      (hgraph n).trans (TwoConeNumerical.graphOracle_true ρ A n).symm
    cases hr : R n <;> cases hg : graphOracle ρ A n <;> simp_all
  exact he.symm ▸ hg

def InternalExistence (M : ZFSet.{u}) (A : Oracle) (k : ℕ) : Prop :=
  ∃ R ∈ reals M, InternalPresentation M A R k

theorem internalExistence_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ reals M) (k : ℕ) :
    InternalExistence M A k ↔ ∃ R : Oracle, Property A R k := by
  constructor
  · rintro ⟨R, hR, hp⟩
    exact ⟨R, (internalPresentation_iff M hM hT A R hA hR k).mp hp⟩
  · rintro ⟨R, hp⟩
    have hR := persistent_presentation_mem (ArithmeticTree.sourceContext M hM hT) hA hp
    exact ⟨R, hR, (internalPresentation_iff M hM hT A R hA hR k).mpr hp⟩

/-- No inclusion or forcing relation between the two models is needed here. -/
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
end OAI.TuringRigidity.TwoConePersistenceAbsoluteness
