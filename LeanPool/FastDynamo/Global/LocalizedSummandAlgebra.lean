/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.ParametrixNeumannCorrection
public import LeanPool.FastDynamo.Operator.FixedSector
public import LeanPool.FastDynamo.Operator.WholePlaneLocal

/-!
# Operator algebra of one localised summand

This file carries out the bounded-operator algebra of one localized summand
`ψ R φ` of an approximate inverse, behind `(z - A) R_app = 1 + E`:

* the localization defect `localizationCommutator` (the commutator `[A, ψ]` of the proof of
  `lem:parametrix-error` when the full and local coefficients agree on the output cut-off), its
  same-operator form `operatorCommutator` for a `CompatibleCutoff`, and their agreement;
* the localized summand `localSummand` and its signed error `localError = -[A,ψ] R φ`;
* the exact one-summand identities `pencil_comp_localization` and `pencil_comp_localSummand`,
  derived from embedding intertwining and the model right inverse rather than assumed.

The paper's approximate inverse `eq:Rapp` has two summands, the background one and the
selected cell; `Global/TorusTwoSummandParametrix.lean` applies the one-summand algebra of this
file to each (with the torus as local model for the background summand, and with the whole
plane for the selected cell).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace LocalizedSummandAlgebra

universe u v w t q

variable {X : Type u} {D : Type v} {Y : Type w} {F : Type t}
  {I : Type q}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ## Bounded pieces -/

/-- The exact action commutator/defect of a domain localization.  When the
full and local coefficients agree on the output cutoff, this is exactly
the commutator `[A_{ε,K_n},ψ]` of the proof of `lem:parametrix-error`. -/
def localizationCommutator (A : DomainOperator X D)
    (B : DomainOperator Y F) (extendDomain : F →L[ℂ] D)
    (extendState : Y →L[ℂ] X) : F →L[ℂ] X :=
  A.op.comp extendDomain - extendState.comp B.op

/-- State/domain multiplication by the same cutoff, expressed at the two
regularity levels of a bundled-domain operator. -/
structure CompatibleCutoff (A : DomainOperator X D) where
  /-- Cutoff multiplication on the state space. -/
  state : X →L[ℂ] X
  /-- Compatible cutoff multiplication on the operator domain. -/
  domain : D →L[ℂ] D
  embedding_comp : A.embedding.comp domain = state.comp A.embedding

/-- The literal same-operator commutator `[A,χ] = Aχ-χA`. -/
def operatorCommutator (A : DomainOperator X D) (cutoff : CompatibleCutoff A) :
    D →L[ℂ] X :=
  A.op.comp cutoff.domain - cutoff.state.comp A.op

/-- The same-operator commutator `[A, χ] = Aχ - χA` is the special case of the general localization
defect in which both operators, the domain extension and the state extension are given by `A`
and the two levels of the same cutoff.
-/
theorem operatorCommutator_eq_localizationCommutator
    (A : DomainOperator X D) (cutoff : CompatibleCutoff A) :
    operatorCommutator A cutoff =
      localizationCommutator A A cutoff.domain cutoff.state :=
  rfl

/-- One localized contribution `ψ_i R_i φ_i`, including the chart
restriction and extension maps. -/
def localSummand (Rlocal : Y →L[ℂ] F)
    (restrictInput : X →L[ℂ] Y) (extendDomain : F →L[ℂ] D) :
    X →L[ℂ] D :=
  extendDomain.comp (Rlocal.comp restrictInput)

/-- The signed local error `-[A,ψ_i] R_i φ_i`. -/
def localError (A : DomainOperator X D) (B : DomainOperator Y F)
    (Rlocal : Y →L[ℂ] F) (restrictInput : X →L[ℂ] Y)
    (extendDomain : F →L[ℂ] D) (extendState : Y →L[ℂ] X) :
    X →L[ℂ] X :=
  -((localizationCommutator A B extendDomain extendState).comp
      (Rlocal.comp restrictInput))

/-! ## Exact one-summand identities -/

/-- The pencil-localization identity obtained from equality of the state
embeddings.  Its residual is the explicitly defined action commutator. -/
theorem pencil_comp_localization
    (A : DomainOperator X D) (B : DomainOperator Y F) (z : ℂ)
    (extendDomain : F →L[ℂ] D) (extendState : Y →L[ℂ] X)
    (hemb : A.embedding.comp extendDomain =
      extendState.comp B.embedding) :
    (A.pencil z).comp extendDomain =
      extendState.comp (B.pencil z) -
        localizationCommutator A B extendDomain extendState := by
  apply ContinuousLinearMap.ext
  intro d
  have hembd := DFunLike.congr_fun hemb d
  simp only [DomainOperator.pencil, localizationCommutator,
    ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
    map_sub, map_smul] at hembd ⊢
  rw [hembd]
  abel

/-- Exact localized summand identity.  No pencil identity is assumed: it is
computed from embedding intertwining and the model right inverse. -/
theorem pencil_comp_localSummand
    (A : DomainOperator X D) (B : DomainOperator Y F) (z : ℂ)
    (Rlocal : Y →L[ℂ] F) (restrictInput : X →L[ℂ] Y)
    (extendDomain : F →L[ℂ] D) (extendState : Y →L[ℂ] X)
    (hemb : A.embedding.comp extendDomain =
      extendState.comp B.embedding)
    (hright : (B.pencil z).comp Rlocal = ContinuousLinearMap.id ℂ Y) :
    (A.pencil z).comp
        (localSummand Rlocal restrictInput extendDomain) =
      extendState.comp restrictInput +
        localError A B Rlocal restrictInput extendDomain extendState := by
  apply ContinuousLinearMap.ext
  intro x
  have hpencil := DFunLike.congr_fun
    (pencil_comp_localization A B z extendDomain extendState hemb)
    (Rlocal (restrictInput x))
  have hrightx := DFunLike.congr_fun hright (restrictInput x)
  simp only [localSummand, localError, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, add_apply, sub_apply, neg_apply] at hpencil hrightx ⊢
  rw [hpencil, hrightx]
  abel

end LocalizedSummandAlgebra

end

end FastDynamo
