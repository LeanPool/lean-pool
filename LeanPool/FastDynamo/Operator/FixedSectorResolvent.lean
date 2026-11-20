/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.DomainPencilFredholm
public import LeanPool.FastDynamo.Operator.FixedSectorBasic

/-!
# A Neumann construction of a fixed-sector resolvent

This module isolates the last perturbative step in the formalisation's
large-real-part resolvent construction for Paper Lemma 5.1 (`lem:torus-sector-basic`); the
paper instead obtains a resolvent point from Fredholm index zero and injectivity by coercivity.
The reduced induction pencil is written exactly as

`diffusion pencil - lower-order part`.

Given a two-sided ambient-to-`H²` inverse of the diffusion pencil, the full
reduced pencil is inverted whenever the lower-order part composed with that
inverse has norm less than one.  The construction keeps the inverse
ambient-to-domain valued, proves both inverse identities, and immediately
supplies the closed-graph and compact-state-resolvent conclusions already
developed in `FixedSectorBasic`.

The periodic PDE input (the diagonal diffusion inverse, and the decay of the
transport/stretching correction as the positive real spectral parameter tends
to infinity) is not assumed here; it is supplied by
`FixedSectorDiffusionInverse` and `FixedSectorLowerOrderDecay`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace DomainOperator

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]

/-! ## A generic bounded-perturbation inverse -/

/-- The ambient Neumann correction for a domain-to-ambient perturbation
`P - B`, normalized by a two-sided inverse `T₀` of `P`. -/
def boundedPerturbationCorrection (B : D →L[ℂ] X) (T₀ : X →L[ℂ] D) :
    X →L[ℂ] X :=
  ContinuousLinearMap.id ℂ X - B.comp T₀

/-- The domain-valued inverse produced from the ambient Neumann correction. -/
def boundedPerturbedInverse (B : D →L[ℂ] X) (T₀ : X →L[ℂ] D) :
    X →L[ℂ] D :=
  T₀.comp (Ring.inverse (boundedPerturbationCorrection B T₀))

omit [CompleteSpace X] in
/-- Right factorization of `P - B` through an inverse of `P`. -/
theorem sub_comp_baseInverse
    (P B : D →L[ℂ] X) (T₀ : X →L[ℂ] D)
    (hright : P.comp T₀ = ContinuousLinearMap.id ℂ X) :
    (P - B).comp T₀ = boundedPerturbationCorrection B T₀ := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun L : X →L[ℂ] X ↦ L x) hright
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hx ⊢
  simp only [boundedPerturbationCorrection, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [hx]

omit [CompleteSpace X] in
/-- Left factorization of `P - B` through an inverse of `P`. -/
theorem correction_comp_principal
    (P B : D →L[ℂ] X) (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp P = ContinuousLinearMap.id ℂ D) :
    (boundedPerturbationCorrection B T₀).comp P = P - B := by
  apply ContinuousLinearMap.ext
  intro d
  have hd := congrArg (fun L : D →L[ℂ] D ↦ L d) hleft
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hd ⊢
  simp only [boundedPerturbationCorrection, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [hd]

/-- The usual norm-smallness condition makes the normalized correction a
unit in the Banach algebra of continuous endomorphisms. -/
theorem isUnit_boundedPerturbationCorrection_of_norm_lt_one
    (B : D →L[ℂ] X) (T₀ : X →L[ℂ] D)
    (hsmall : ‖B.comp T₀‖ < 1) :
    IsUnit (boundedPerturbationCorrection B T₀) := by
  change IsUnit (1 - B.comp T₀)
  exact isUnit_one_sub_of_norm_lt_one hsmall

omit [CompleteSpace X] in
/-- If the normalized ambient correction is a unit, then `P - B` is
injective.  This is the domain-valued half of the Neumann argument. -/
theorem sub_injective_of_isUnit_correction
    (P B : D →L[ℂ] X) (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp P = ContinuousLinearMap.id ℂ D)
    (hunit : IsUnit (boundedPerturbationCorrection B T₀)) :
    Function.Injective (P - B) := by
  intro d e hde
  let C := boundedPerturbationCorrection B T₀
  have hfactor : C.comp P = P - B :=
    correction_comp_principal P B T₀ hleft
  have hCeq : C (P d) = C (P e) := by
    calc
      C (P d) = (P - B) d := by
        have hd := congrArg (fun L : D →L[ℂ] X ↦ L d) hfactor
        simpa only [ContinuousLinearMap.comp_apply] using hd
      _ = (P - B) e := hde
      _ = C (P e) := by
        have he := congrArg (fun L : D →L[ℂ] X ↦ L e) hfactor
        simpa only [ContinuousLinearMap.comp_apply] using he.symm
  have hCinv : Function.Injective C :=
    (ContinuousLinearMap.isInvertible_iff_isUnit.mpr hunit).injective
  have hPeq : P d = P e := hCinv hCeq
  have hd := congrArg (fun L : D →L[ℂ] D ↦ L d) hleft
  have he := congrArg (fun L : D →L[ℂ] D ↦ L e) hleft
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hd he
  calc
    d = T₀ (P d) := hd.symm
    _ = T₀ (P e) := by rw [hPeq]
    _ = e := he

omit [CompleteSpace X] in
/-- The constructed domain-valued map is a right inverse of `P - B`. -/
theorem boundedPerturbedInverse_right_inv
    (P B : D →L[ℂ] X) (T₀ : X →L[ℂ] D)
    (hright : P.comp T₀ = ContinuousLinearMap.id ℂ X)
    (hunit : IsUnit (boundedPerturbationCorrection B T₀)) :
    (P - B).comp (boundedPerturbedInverse B T₀) =
      ContinuousLinearMap.id ℂ X := by
  rw [boundedPerturbedInverse, ← ContinuousLinearMap.comp_assoc,
    sub_comp_baseInverse P B T₀ hright]
  exact Ring.mul_inverse_cancel _ hunit

omit [CompleteSpace X] in
/-- The constructed domain-valued map is also a left inverse of `P - B`. -/
theorem boundedPerturbedInverse_left_inv
    (P B : D →L[ℂ] X) (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp P = ContinuousLinearMap.id ℂ D)
    (hright : P.comp T₀ = ContinuousLinearMap.id ℂ X)
    (hunit : IsUnit (boundedPerturbationCorrection B T₀)) :
    (boundedPerturbedInverse B T₀).comp (P - B) =
      ContinuousLinearMap.id ℂ D := by
  apply ContinuousLinearMap.ext
  intro d
  apply sub_injective_of_isUnit_correction P B T₀ hleft hunit
  have hright' := congrArg (fun L : X →L[ℂ] X ↦ L ((P - B) d))
    (boundedPerturbedInverse_right_inv P B T₀ hright hunit)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using hright'

/--
Fibre-blind Neumann step.  If the pencil of `A` at `z` splits exactly as `P - B`, with `P`
inverted two-sidedly by `T₀` and `‖B ∘ T₀‖ < 1`, then `A` has a resolvent at `z`.

This is the velocity-free core of the fixed-sector resolvent construction: it is generic in the
ambient and domain spaces, so the three-component
`reducedInductionHasResolventOnSingletonOfDiffusionInverse` below and the two-component
horizontal torus operator of the paper are both instances of it.
-/
def hasResolventOnSingletonOfPencilSplitting
    (A : DomainOperator X D) (z : ℂ) (P B : D →L[ℂ] X)
    (hsplit : A.pencil z = P - B)
    (T₀ : X →L[ℂ] D)
    (hleft : T₀.comp P = ContinuousLinearMap.id ℂ D)
    (hright : P.comp T₀ = ContinuousLinearMap.id ℂ X)
    (hsmall : ‖B.comp T₀‖ < 1) :
    HasResolventOn A {z} := by
  have hunit : IsUnit (boundedPerturbationCorrection B T₀) :=
    isUnit_boundedPerturbationCorrection_of_norm_lt_one B T₀ hsmall
  refine A.hasResolventOnSingleton z (boundedPerturbedInverse B T₀) ?_ ?_
  · rw [hsplit]
    exact boundedPerturbedInverse_left_inv P B T₀ hleft hright hunit
  · rw [hsplit]
    exact boundedPerturbedInverse_right_inv P B T₀ hright hunit

end DomainOperator

/-! ## Exact splitting of the reduced induction pencil -/

/--
The diffusion-only part of the fixed-sector pencil on the fibre `ℂ^ι`.

Like the diffusion term itself this is fibre-blind, so the diagonal Fourier inverse built in
`FastDynamo/Operator/FixedSectorDiffusionInverse.lean` inverts it at every finite fibre.
-/
def transverseVecDiffusionPencil (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (K : ℤ) (z : ℂ) :
    TransverseVecH2 ι →L[ℂ] TransverseVecL2 ι :=
  z • transverseH2Embedding -
    (ε : ℂ) • transverseVecDiffusion ι K

/-- The diffusion-only part of the reduced fixed-sector pencil. -/
def reducedInductionDiffusionPencil (ε : ℝ) (K : ℤ) (z : ℂ) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  z • transverseH2Embedding -
    (ε : ℂ) • reducedInductionDiffusion K

/-- All first- and zeroth-order terms in the reduced induction action. -/
def reducedInductionLowerOrder (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  -reducedInductionTransport u - reducedInductionAxialTransport u K +
    reducedInductionStretching u

/-- The full reduced pencil is exactly its diffusion pencil minus the
lower-order perturbation. -/
theorem reducedInductionPencil_eq_diffusionPencil_sub_lowerOrder
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ) :
    (reducedInductionOperator u ε K).pencil z =
      reducedInductionDiffusionPencil ε K z -
        reducedInductionLowerOrder u K := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [DomainOperator.pencil, reducedInductionOperator,
    reducedInductionAction, reducedInductionDiffusionPencil,
    reducedInductionLowerOrder, add_apply, sub_apply, neg_apply, smul_apply]
  module

/--
Triangle inequality in the shape `‖-a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖`, matching the sign pattern of
the assembled lower-order fixed-sector action.
-/
private theorem norm_neg_sub_add_le {E : Type*} [SeminormedAddCommGroup E]
    (a b c : E) :
    ‖-a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  calc
    ‖-a - b + c‖ ≤ ‖-a - b‖ + ‖c‖ := norm_add_le _ _
    _ ≤ (‖-a‖ + ‖b‖) + ‖c‖ :=
      add_le_add (norm_sub_le _ _) (le_refl ‖c‖)
    _ = ‖a‖ + ‖b‖ + ‖c‖ := by rw [norm_neg]

/-- Relative version of the lower-order norm bound.  This form is sharper
than multiplying by the full `L² → H²` norm of a diffusion inverse: the
transport, axial-transport, and stretching pieces can be estimated at their
natural derivative orders separately. -/
theorem norm_reducedInductionLowerOrder_comp_le
    (u : TransverseRealW1Inf) (K : ℤ)
    (T : TransverseC3L2 →L[ℂ] TransverseC3H2) :
    ‖(reducedInductionLowerOrder u K).comp T‖ ≤
      ‖(reducedInductionTransport u).comp T‖ +
        ‖(reducedInductionAxialTransport u K).comp T‖ +
          ‖(reducedInductionStretching u).comp T‖ := by
  have heq : (reducedInductionLowerOrder u K).comp T =
      -((reducedInductionTransport u).comp T) -
        (reducedInductionAxialTransport u K).comp T +
          (reducedInductionStretching u).comp T := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [heq]
  exact norm_neg_sub_add_le ((reducedInductionTransport u).comp T)
    ((reducedInductionAxialTransport u K).comp T)
    ((reducedInductionStretching u).comp T)

/-- Termwise relative decay of transport and stretching through a diffusion
inverse implies decay of the actual normalized lower-order correction. -/
theorem tendsto_norm_reducedInductionLowerOrder_comp_zero_of_terms
    (u : TransverseRealW1Inf) (K : ℤ)
    {I : Type*} {l : Filter I}
    (T : I → TransverseC3L2 →L[ℂ] TransverseC3H2)
    (htransport : Filter.Tendsto
      (fun i ↦ ‖(reducedInductionTransport u).comp (T i)‖) l (nhds 0))
    (haxial : Filter.Tendsto
      (fun i ↦ ‖(reducedInductionAxialTransport u K).comp (T i)‖)
        l (nhds 0))
    (hstretching : Filter.Tendsto
      (fun i ↦ ‖(reducedInductionStretching u).comp (T i)‖)
        l (nhds 0)) :
    Filter.Tendsto
      (fun i ↦ ‖(reducedInductionLowerOrder u K).comp (T i)‖)
        l (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun i ↦ norm_nonneg _
  · exact Filter.Eventually.of_forall fun i ↦
      norm_reducedInductionLowerOrder_comp_le u K (T i)
  · simpa only [zero_add] using
      (htransport.add haxial).add hstretching

/-! ## The reduced fixed-sector resolvent -/

/-- A two-sided inverse of the diffusion pencil, together with the
Neumann smallness condition, gives a resolvent of the full reduced operator
at the same spectral point. -/
def reducedInductionHasResolventOnSingletonOfDiffusionInverse
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ)
    (T₀ : TransverseC3L2 →L[ℂ] TransverseC3H2)
    (hleft : T₀.comp (reducedInductionDiffusionPencil ε K z) =
      ContinuousLinearMap.id ℂ TransverseC3H2)
    (hright : (reducedInductionDiffusionPencil ε K z).comp T₀ =
      ContinuousLinearMap.id ℂ TransverseC3L2)
    (hsmall : ‖(reducedInductionLowerOrder u K).comp T₀‖ < 1) :
    HasResolventOn (reducedInductionOperator u ε K) {z} := by
  let B := reducedInductionLowerOrder u K
  let P := reducedInductionDiffusionPencil ε K z
  let T := DomainOperator.boundedPerturbedInverse B T₀
  have hunit : IsUnit (DomainOperator.boundedPerturbationCorrection B T₀) :=
    DomainOperator.isUnit_boundedPerturbationCorrection_of_norm_lt_one
      B T₀ hsmall
  have hpencil : (reducedInductionOperator u ε K).pencil z = P - B :=
    reducedInductionPencil_eq_diffusionPencil_sub_lowerOrder u ε K z
  have hTleft : T.comp ((reducedInductionOperator u ε K).pencil z) =
      ContinuousLinearMap.id ℂ TransverseC3H2 := by
    rw [hpencil]
    exact DomainOperator.boundedPerturbedInverse_left_inv
      P B T₀ hleft hright hunit
  have hTright : ((reducedInductionOperator u ε K).pencil z).comp T =
      ContinuousLinearMap.id ℂ TransverseC3L2 := by
    rw [hpencil]
    exact DomainOperator.boundedPerturbedInverse_right_inv
      P B T₀ hright hunit
  exact (reducedInductionOperator u ε K).hasResolventOnSingleton
    z T hTleft hTright

end

end FastDynamo
