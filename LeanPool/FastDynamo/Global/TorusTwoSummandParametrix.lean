/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.HorizontalCutoffCommutator

/-!
# The two-summand approximate inverse of Section 7

The paper (`eq:Rapp`) builds the global approximate inverse out of exactly two summands,

`R_app(z) = χ_n R_bg(z)(1 - φ_n) + ψ_n R_n(z)φ_n`,   `z ∈ Γ_τ`,

and proves (`lem:parametrix-error`, `eq:parametrix` and its proof)

`(z - A_{ε,K_n})R_app(z) = id + E_n(z)`,
`E_n(z) = -[A_{ε,K_n}, χ_n]R_bg(z)(1 - φ_n) - [A_{ε,K_n}, ψ_n]R_n(z)φ_n`.

Two features are worth naming.  Only the selected cell `n` carries a local summand (to which
the one-summand algebra of `LocalizedSummandAlgebra` is applied), and the
*background* summand carries an output cut-off `χ_n`.  The second is what removes the
background coefficient defect altogether: since `supp u_n^loc ⊂ D(p_n, R_n/10)` and `χ_n = 0`
there, the full and background coefficients agree identically wherever `χ_n ≠ 0`, so the
background summand is an *instance of the localized summand* (with the torus itself as local
model), and its error is a cut-off commutator.

Accordingly the file is organised as follows.

* An abstract two-summand assembly, `pencil_comp_twoSummandParametrix`, obtained by applying
  `LocalizedSummandAlgebra.pencil_comp_localSummand` twice.  It is stated for two entirely
  independent local models `(Y₁,F₁)` and `(Y₂,F₂)`, which is exactly what the two-summand
  parametrix needs: the background model is the torus itself, the selected model is the whole
  plane.  The partition hypothesis is `χ_n(1-φ_n) + ψ_nφ_n = id`, the sum of the two
  identities of `eq:parametrix-cutoff-identities`.
* Two interface records, `BackgroundParametrixData` and `SelectedLocalResolventData`, holding
  exactly what §6 supplies: `prop:background-resolvent`/`eq:bg-resolvent` for
  the background, and `cor:scaled-local-resolvents`/`eq:local-gradient` for the
  selected cell, in each case the right-inverse identity together with the two bounds
  `‖Rf‖ ≤ C‖f‖` and `√ε‖∇Rf‖ ≤ C‖f‖`.
* The concrete `R_app`, its error, `eq:parametrix`, and the identification of the error with the
  `ParametrixNeumannCorrection.rightError` consumed by the Neumann correction.

The support and agreement hypotheses of the paper's proof of `lem:parametrix-error` are taken
as explicit fields; they
are listed in the docstrings of the two records and of `TwoSummandParametrixData`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace TorusTwoSummandParametrix

open HorizontalCutoffCommutator ParametrixCutoffs LocalizedSummandAlgebra

/-! ## Abstract two-summand assembly -/

universe u v w t w' t'

section Abstract

variable {X : Type u} {D : Type v} {Y₁ : Type w} {F₁ : Type t} {Y₂ : Type w'} {F₂ : Type t'}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup Y₂] [NormedSpace ℂ Y₂]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]

/-- The sum of two localized parametrix summands, each with its own local model.  This is the
shape of `eq:Rapp`: the first summand is the background one, the second the selected cell. -/
def twoSummandParametrix
    (R₁ : Y₁ →L[ℂ] F₁) (in₁ : X →L[ℂ] Y₁) (ed₁ : F₁ →L[ℂ] D)
    (R₂ : Y₂ →L[ℂ] F₂) (in₂ : X →L[ℂ] Y₂) (ed₂ : F₂ →L[ℂ] D) : X →L[ℂ] D :=
  localSummand R₁ in₁ ed₁ + localSummand R₂ in₂ ed₂

/-- The error of the two-summand parametrix: the sum of the two signed localization defects. -/
def twoSummandError (A : DomainOperator X D)
    (B₁ : DomainOperator Y₁ F₁) (R₁ : Y₁ →L[ℂ] F₁) (in₁ : X →L[ℂ] Y₁)
    (ed₁ : F₁ →L[ℂ] D) (es₁ : Y₁ →L[ℂ] X)
    (B₂ : DomainOperator Y₂ F₂) (R₂ : Y₂ →L[ℂ] F₂) (in₂ : X →L[ℂ] Y₂)
    (ed₂ : F₂ →L[ℂ] D) (es₂ : Y₂ →L[ℂ] X) : X →L[ℂ] X :=
  localError A B₁ R₁ in₁ ed₁ es₁ + localError A B₂ R₂ in₂ ed₂ es₂

/-- The error is minus the sum of the two localization commutators, the exact sign of the error
`E_n(z)` in the proof of `lem:parametrix-error`. -/
theorem twoSummandError_eq_neg_commutators (A : DomainOperator X D)
    (B₁ : DomainOperator Y₁ F₁) (R₁ : Y₁ →L[ℂ] F₁) (in₁ : X →L[ℂ] Y₁)
    (ed₁ : F₁ →L[ℂ] D) (es₁ : Y₁ →L[ℂ] X)
    (B₂ : DomainOperator Y₂ F₂) (R₂ : Y₂ →L[ℂ] F₂) (in₂ : X →L[ℂ] Y₂)
    (ed₂ : F₂ →L[ℂ] D) (es₂ : Y₂ →L[ℂ] X) :
    twoSummandError A B₁ R₁ in₁ ed₁ es₁ B₂ R₂ in₂ ed₂ es₂ =
      -((localizationCommutator A B₁ ed₁ es₁).comp (R₁.comp in₁) +
        (localizationCommutator A B₂ ed₂ es₂).comp (R₂.comp in₂)) := by
  unfold twoSummandError localError
  abel

/-- **`eq:parametrix`** in abstract form:
`(z - A)R_app = id + E`, obtained by applying `pencil_comp_localSummand` to each summand and
closing with the partition `es₁ ∘ in₁ + es₂ ∘ in₂ = id`. -/
theorem pencil_comp_twoSummandParametrix (A : DomainOperator X D) (z : ℂ)
    (B₁ : DomainOperator Y₁ F₁) (R₁ : Y₁ →L[ℂ] F₁) (in₁ : X →L[ℂ] Y₁)
    (ed₁ : F₁ →L[ℂ] D) (es₁ : Y₁ →L[ℂ] X)
    (B₂ : DomainOperator Y₂ F₂) (R₂ : Y₂ →L[ℂ] F₂) (in₂ : X →L[ℂ] Y₂)
    (ed₂ : F₂ →L[ℂ] D) (es₂ : Y₂ →L[ℂ] X)
    (hemb₁ : A.embedding.comp ed₁ = es₁.comp B₁.embedding)
    (hright₁ : (B₁.pencil z).comp R₁ = ContinuousLinearMap.id ℂ Y₁)
    (hemb₂ : A.embedding.comp ed₂ = es₂.comp B₂.embedding)
    (hright₂ : (B₂.pencil z).comp R₂ = ContinuousLinearMap.id ℂ Y₂)
    (hpartition : es₁.comp in₁ + es₂.comp in₂ = ContinuousLinearMap.id ℂ X) :
    (A.pencil z).comp (twoSummandParametrix R₁ in₁ ed₁ R₂ in₂ ed₂) =
      ContinuousLinearMap.id ℂ X +
        twoSummandError A B₁ R₁ in₁ ed₁ es₁ B₂ R₂ in₂ ed₂ es₂ := by
  have h₁ := pencil_comp_localSummand A B₁ z R₁ in₁ ed₁ es₁ hemb₁ hright₁
  have h₂ := pencil_comp_localSummand A B₂ z R₂ in₂ ed₂ es₂ hemb₂ hright₂
  apply ContinuousLinearMap.ext
  intro x
  have h₁x := DFunLike.congr_fun h₁ x
  have h₂x := DFunLike.congr_fun h₂ x
  have hpx := DFunLike.congr_fun hpartition x
  simp only [twoSummandParametrix, twoSummandError, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, add_apply] at h₁x h₂x hpx ⊢
  rw [map_add, h₁x, h₂x]
  rw [show es₁ (in₁ x) + localError A B₁ R₁ in₁ ed₁ es₁ x +
        (es₂ (in₂ x) + localError A B₂ R₂ in₂ ed₂ es₂ x) =
      (es₁ (in₁ x) + es₂ (in₂ x)) +
        (localError A B₁ R₁ in₁ ed₁ es₁ x + localError A B₂ R₂ in₂ ed₂ es₂ x) by abel]
  rw [hpx]

end Abstract

/-! ## The background resolvent interface -/

/-- The data `prop:background-resolvent` supplies to
Section 7 for the background operator `A^bg_{ε,n} = horizontalInductionOperator ubg ε K`.

The §6 producer of exactly these fields is `TorusBackgroundResolventData` of
`Global/TorusBackgroundResolvent.lean`; the bridge
`BackgroundParametrixData.ofTorusBackgroundResolventData`
(`Global/TorusBackgroundParametrixBridge.lean`) is one application of `ofHasResolventOn` to
its `resolvent`, `norm_le` and
`sqrt_eps_gradient_le` (the latter after `Real.sqrt_mul`, `√ε√E = √(εE)`).  Section 7 is kept
independent of the §6 build on purpose.

The two bounds are the two halves of `eq:bg-resolvent`, `‖R_bg f‖₂ + √ε‖∇_⊥R_bg f‖₂ ≤ C‖f‖₂`;
`Global/TorusBackgroundWeightedEnergy.norm_add_sqrt_eps_gradientEnergy_le` proves exactly their
sum, with `C = √2/g + 2/√g`, so both fields are immediate from it (see `ofHasResolventOn`).
Holomorphy of the background resolvent (which `prop:background-resolvent` does not state) is not
required anywhere in the proofs of §7; only the continuity already carried by `HasResolventOn` is,
and it enters through `continuousOn`. -/
structure BackgroundParametrixData (ubg : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (S : Set ℂ) where
  /-- The background resolvent family `z ↦ R_bg(z)`, `L²(T²;ℂ²) → H²(T²;ℂ²)`. -/
  resolvent : ℂ → TransverseC2L2 →L[ℂ] TransverseC2H2
  /-- The constant `C` of `eq:bg-resolvent`. -/
  bound : ℝ
  /-- The constant of `eq:bg-resolvent` is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- `(z - A^bg)R_bg(z) = id` on the parameter set. -/
  right_inv : ∀ z ∈ S,
    ((horizontalInductionOperator ubg ε K).pencil z).comp (resolvent z) =
      ContinuousLinearMap.id ℂ TransverseC2L2
  /-- The resolvent depends continuously on the spectral parameter. -/
  continuousOn : ContinuousOn resolvent S
  /-- `‖R_bg(z)f‖₂ ≤ C‖f‖₂` (`eq:bg-resolvent`). -/
  norm_le : ∀ z ∈ S, ∀ f, ‖transverseH2Embedding (resolvent z f)‖ ≤ bound * ‖f‖
  /-- `√ε‖∇_⊥R_bg(z)f‖₂ ≤ C‖f‖₂` (`eq:bg-resolvent`). -/
  sqrt_gradient_le : ∀ z ∈ S, ∀ f,
    Real.sqrt (ε * transverseGradientEnergy (resolvent z f)) ≤ bound * ‖f‖

/-- Build the background interface from a resolvent certificate on the set together with the two
`eq:bg-resolvent` bounds written for the resolvent's own inverse. -/
def BackgroundParametrixData.ofHasResolventOn
    {ubg : TransverseRealW1Inf} {ε : ℝ} {K : ℤ} {S : Set ℂ}
    (h : HasResolventOn (horizontalInductionOperator ubg ε K) S) (C : ℝ) (hC : 0 ≤ C)
    (hnorm : ∀ z ∈ S, ∀ f, ‖transverseH2Embedding (h.inv z f)‖ ≤ C * ‖f‖)
    (hgrad : ∀ z ∈ S, ∀ f,
      Real.sqrt (ε * transverseGradientEnergy (h.inv z f)) ≤ C * ‖f‖) :
    BackgroundParametrixData ubg ε K S where
  resolvent := h.inv
  bound := C
  bound_nonneg := hC
  right_inv := h.right_inv
  continuousOn := h.continuousOn
  norm_le := hnorm
  sqrt_gradient_le := hgrad

/-! ## The selected local resolvent interface -/

/-- The data `cor:scaled-local-resolvents` together
with the chart transport supplies to Section 7 for the selected cell.

The local model `(Y, F)` is left abstract: in the concrete instance it is the whole plane,
`Y = WholePlaneC2L2`, `F = WholePlaneC2H2`, `localOperator` is the selected two-component local
operator of `FastDynamo/Operator/WholePlaneLocalC2.lean` and `resolvent z` is
`R_n(z) = U_n R_{δ_n}(z + iτ)U_n⁻¹` produced by `lem:exact-renormalization` through
`FastDynamo/Reduction/ExactScalingC2.lean`.  `restrictInput` is "multiply by `φ_n`, extend by
zero to the plane", `extendDomain`/`extendState` are "multiply by `ψ_n`, restrict to the torus".

The fields that carry the paper's support and agreement hypotheses are:

* `roundTrip`: `ψ_n ∘ φ_n = φ_n` after the chart round trip, i.e. the second identity of
  `eq:parametrix-cutoff-identities` read through the chart;
* `commutator_eq`: "the coefficients of the horizontal operator on `T²` and the operator on `ℝ²` for
  the selected cell agree on `supp ψ_n`, since the added axial velocity profile in the selected cell
  of `T²` is constant there and all other cells are disjoint" (proof of `lem:parametrix-error`).  It
  says that the localization defect of the selected summand *is* the torus commutator
  `[A_{ε,K_n}, ψ_n]` evaluated on the transported local solution.
`transported z` is the transported local solution `R_n(z)φ_n` read as a torus `H²` field (any
field agreeing with it on `supp ∇ψ_n`, concretely a slightly larger cut-off of it); the two
bounds `norm_le` and `sqrt_gradient_le` are the two halves of `eq:local-gradient` for it,
and `norm_summand_le` is the same bound for the whole summand `ψ_nR_n(z)φ_n`, which is what
`eq:parametrix-uniform-bound` needs. -/
structure SelectedLocalResolventData (Y : Type w) (F : Type t)
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (S : Set ℂ)
    (phi psi : HorizontalSecondOrderCutoff) where
  /-- The selected local operator `A^{(n)}_{ε,n}` on its own model spaces. -/
  localOperator : DomainOperator Y F
  /-- The local resolvent family `z ↦ R_n(z)`. -/
  resolvent : ℂ → Y →L[ℂ] F
  /-- Multiply by `φ_n` and transport into the local model. -/
  restrictInput : TransverseC2L2 →L[ℂ] Y
  /-- Multiply by `ψ_n` and transport back, at graph-domain regularity. -/
  extendDomain : F →L[ℂ] TransverseC2H2
  /-- Multiply by `ψ_n` and transport back, at state regularity. -/
  extendState : Y →L[ℂ] TransverseC2L2
  /-- The transported local solution `R_n(z)φ_n` read on the torus. -/
  transported : ℂ → TransverseC2L2 →L[ℂ] TransverseC2H2
  /-- The constant of `eq:local-gradient`. -/
  bound : ℝ
  /-- That constant is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- The chart transport intertwines the two domain embeddings. -/
  embedding_intertwining :
    (horizontalInductionOperator u ε K).embedding.comp extendDomain =
      extendState.comp localOperator.embedding
  /-- `(z - A^{(n)})R_n(z) = id` on the parameter set. -/
  right_inv : ∀ z ∈ S,
    (localOperator.pencil z).comp (resolvent z) = ContinuousLinearMap.id ℂ Y
  /-- The chart round trip is multiplication by `φ_n`: this is `ψ_nφ_n = φ_n`. -/
  roundTrip : extendState.comp restrictInput = phi.stateMul
  /-- The selected summand depends continuously on the spectral parameter. -/
  continuousOn :
    ContinuousOn (fun z ↦ extendDomain.comp ((resolvent z).comp restrictInput)) S
  /-- The localization defect of the selected summand is the torus commutator `[A, ψ_n]` on the
  transported local solution: the coefficients agree on `supp ψ_n`. -/
  commutator_eq : ∀ z ∈ S,
    (localizationCommutator (horizontalInductionOperator u ε K) localOperator
        extendDomain extendState).comp ((resolvent z).comp restrictInput) =
      (commutator psi u ε K).comp (transported z)
  /-- `‖R_n(z)φ_nf‖₂ ≤ C‖f‖₂` (the `L²` half of `eq:local-gradient`). -/
  norm_le : ∀ z ∈ S, ∀ f,
    ‖transverseH2Embedding (transported z f)‖ ≤ bound * ‖f‖
  /-- `√ε‖∇_⊥R_n(z)φ_nf‖₂ ≤ C‖f‖₂` (`eq:local-gradient`). -/
  sqrt_gradient_le : ∀ z ∈ S, ∀ f,
    Real.sqrt (ε * transverseGradientEnergy (transported z f)) ≤ bound * ‖f‖
  /-- `‖ψ_nR_n(z)φ_nf‖₂ ≤ C‖f‖₂`, the selected half of `eq:parametrix-uniform-bound`. -/
  norm_summand_le : ∀ z ∈ S, ∀ f,
    ‖transverseH2Embedding (extendDomain (resolvent z (restrictInput f)))‖ ≤ bound * ‖f‖

/-! ## The concrete two-summand parametrix -/

/-- All the data of `eq:Rapp` at one cell: the three placed cut-offs, the background resolvent,
the selected local resolvent, and the two support hypotheses of the proof of
`lem:parametrix-error`.

* `backgroundAgreement` is "the coefficients of the horizontal and background operators on `T²`
  agree wherever `χ_n ≠ 0`, since `supp u_n^loc ⊂ D(p_n, R_n/10)`" (proof of
  `lem:parametrix-error`).  It is exactly what turns the background localization defect into the
  commutator `[A_{ε,K_n}, χ_n]`.
* `backgroundVanishes` and `outputVanishes` are "the horizontal velocity vanishes on the
  transition regions of both output cut-offs" (same proof), which is what makes both
  commutators diffusion-only. -/
structure TwoSummandParametrixData (Y : Type w) (F : Type t)
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u ubg : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (R : ℝ) (S : Set ℂ) where
  /-- The three placed cut-offs `φ_n`, `ψ_n`, `χ_n` of the cell, of reserved radius `R = R_n`. -/
  cutoffs : HorizontalParametrixCutoffs R
  /-- `prop:background-resolvent` for `A^bg_{ε,n}`. -/
  background : BackgroundParametrixData ubg ε K S
  /-- `cor:scaled-local-resolvents` for the selected cell, transported to the torus. -/
  selected : SelectedLocalResolventData Y F u ε K S cutoffs.input cutoffs.output
  /-- The full and background actions agree after multiplication by `χ_n`. -/
  backgroundAgreement :
    cutoffs.background.stateMul.comp (horizontalInductionAction u ε K) =
      cutoffs.background.stateMul.comp (horizontalInductionAction ubg ε K)
  /-- `u_⊥ = 0` on `supp ∇χ_n`. -/
  backgroundVanishes : VelocityVanishesOnGradient cutoffs.background u
  /-- `u_⊥ = 0` on `supp ∇ψ_n`. -/
  outputVanishes : VelocityVanishesOnGradient cutoffs.output u

namespace TwoSummandParametrixData

variable {Y : Type w} {F : Type t}
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {u ubg : TransverseRealW1Inf} {ε : ℝ} {K : ℤ} {R : ℝ} {S : Set ℂ}

/-- **`eq:Rapp`**:
`R_app(z) = χ_nR_bg(z)(1 - φ_n) + ψ_nR_n(z)φ_n`. -/
def approximateInverse (P : TwoSummandParametrixData Y F u ubg ε K R S) (z : ℂ) :
    TransverseC2L2 →L[ℂ] TransverseC2H2 :=
  twoSummandParametrix (P.background.resolvent z) P.cutoffs.inputComplement
    P.cutoffs.background.domainMul
    (P.selected.resolvent z) P.selected.restrictInput P.selected.extendDomain

/-- The error `E_n(z)` of `eq:parametrix`. -/
def error (P : TwoSummandParametrixData Y F u ubg ε K R S) (z : ℂ) :
    TransverseC2L2 →L[ℂ] TransverseC2L2 :=
  twoSummandError (horizontalInductionOperator u ε K)
    (horizontalInductionOperator ubg ε K) (P.background.resolvent z)
      P.cutoffs.inputComplement P.cutoffs.background.domainMul P.cutoffs.background.stateMul
    P.selected.localOperator (P.selected.resolvent z) P.selected.restrictInput
      P.selected.extendDomain P.selected.extendState

/-- The background localization defect is the torus commutator `[A_{ε,K_n}, χ_n]`: this is
where `backgroundAgreement` is used. -/
theorem background_localizationCommutator_eq
    (P : TwoSummandParametrixData Y F u ubg ε K R S) :
    localizationCommutator (horizontalInductionOperator u ε K)
        (horizontalInductionOperator ubg ε K) P.cutoffs.background.domainMul
        P.cutoffs.background.stateMul =
      commutator P.cutoffs.background u ε K := by
  rw [commutator_eq_localizationCommutator]
  unfold localizationCommutator
  simp only [horizontalInductionOperator_op]
  rw [P.backgroundAgreement]

/-- **`eq:parametrix`**:
`(z - A_{ε,K_n})R_app(z) = id + E_n(z)`. -/
theorem right_error_identity (P : TwoSummandParametrixData Y F u ubg ε K R S)
    {z : ℂ} (hz : z ∈ S) :
    ((horizontalInductionOperator u ε K).pencil z).comp (P.approximateInverse z) =
      ContinuousLinearMap.id ℂ TransverseC2L2 + P.error z := by
  have hemb₁ : (horizontalInductionOperator u ε K).embedding.comp
      P.cutoffs.background.domainMul =
      P.cutoffs.background.stateMul.comp
        (horizontalInductionOperator ubg ε K).embedding :=
    P.cutoffs.background.embedding_comp_domainMul
  have hpartition :
      P.cutoffs.background.stateMul.comp P.cutoffs.inputComplement +
          P.selected.extendState.comp P.selected.restrictInput =
        ContinuousLinearMap.id ℂ TransverseC2L2 := by
    rw [P.selected.roundTrip, ← P.cutoffs.output_mul_input]
    exact P.cutoffs.partition
  exact pencil_comp_twoSummandParametrix (horizontalInductionOperator u ε K) z
    (horizontalInductionOperator ubg ε K) (P.background.resolvent z)
      P.cutoffs.inputComplement P.cutoffs.background.domainMul P.cutoffs.background.stateMul
    P.selected.localOperator (P.selected.resolvent z) P.selected.restrictInput
      P.selected.extendDomain P.selected.extendState
    hemb₁ (P.background.right_inv z hz) P.selected.embedding_intertwining
    (P.selected.right_inv z hz) hpartition

/-- **The explicit error** in the proof of `lem:parametrix-error`:
`E_n(z) = -[A_{ε,K_n}, χ_n]R_bg(z)(1 - φ_n) - [A_{ε,K_n}, ψ_n]R_n(z)φ_n`. -/
theorem error_eq (P : TwoSummandParametrixData Y F u ubg ε K R S) {z : ℂ} (hz : z ∈ S) :
    P.error z =
      -((commutator P.cutoffs.background u ε K).comp
          ((P.background.resolvent z).comp P.cutoffs.inputComplement) +
        (commutator P.cutoffs.output u ε K).comp (P.selected.transported z)) := by
  unfold error
  rw [twoSummandError_eq_neg_commutators, P.background_localizationCommutator_eq,
    P.selected.commutator_eq z hz]

/-- The error applied to one state, in the form the norm estimate consumes. -/
theorem error_apply (P : TwoSummandParametrixData Y F u ubg ε K R S) {z : ℂ} (hz : z ∈ S)
    (f : TransverseC2L2) :
    P.error z f =
      -(commutator P.cutoffs.background u ε K
            (P.background.resolvent z (P.cutoffs.inputComplement f)) +
          commutator P.cutoffs.output u ε K (P.selected.transported z f)) := by
  rw [P.error_eq hz]
  simp only [neg_apply, add_apply, ContinuousLinearMap.comp_apply]

/-- Identification of the error with the right error consumed by the Neumann correction of
`FastDynamo/Global/ParametrixNeumannCorrection.lean`. -/
theorem transfer_rightError_eq (P : TwoSummandParametrixData Y F u ubg ε K R S)
    {z : ℂ} (hz : z ∈ S) :
    ParametrixNeumannCorrection.rightError (horizontalInductionOperator u ε K)
        P.approximateInverse z = P.error z := by
  unfold ParametrixNeumannCorrection.rightError
  rw [P.right_error_identity hz]
  apply ContinuousLinearMap.ext
  intro x
  simp only [sub_apply, add_apply, ContinuousLinearMap.id_apply]
  abel

/-- The approximate inverse depends continuously on the spectral parameter, as
`hasResolventOnOfRightParametrixIndexZero` requires. -/
theorem continuousOn_approximateInverse (P : TwoSummandParametrixData Y F u ubg ε K R S) :
    ContinuousOn P.approximateInverse S := by
  have hgroup : IsTopologicalAddGroup (TransverseC2L2 →L[ℂ] TransverseC2H2) :=
    ContinuousLinearMap.isTopologicalAddGroup
  have hadd : ContinuousAdd (TransverseC2L2 →L[ℂ] TransverseC2H2) := hgroup.toContinuousAdd
  have hbg : ContinuousOn (fun z ↦ P.cutoffs.background.domainMul.comp
      ((P.background.resolvent z).comp P.cutoffs.inputComplement)) S :=
    continuousOn_const.clm_comp (P.background.continuousOn.clm_comp continuousOn_const)
  exact hbg.add P.selected.continuousOn

end TwoSummandParametrixData

end TorusTwoSummandParametrix

end

end FastDynamo
