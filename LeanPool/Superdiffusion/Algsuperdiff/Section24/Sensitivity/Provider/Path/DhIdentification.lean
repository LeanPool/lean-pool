/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.CoarseMatrixDerivativeCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.MuExpansion
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Existence

/-!
# DhIdentification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Identification of the linear path term with the `D_h` quadratic form

The linear response term of a doubled-`mu` minimizer at loading `(-p, q)` is
exactly `½ (p,-q) · D_h(U; a) (p,-q)`: the source display
`⨍ 2(∇w + ∇w*)·h(∇w - ∇w*) = ⨍ ∇v*·h∇v = P·D_h(U;a)P`.

The doubled-`mu` minimizer encodes both scalar maximizers.  The primal one is
extracted by the public CoarseGraining lemma
`doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient`; the adjoint
one is extracted here by transporting the minimizer through the exact symmetry
`mu(U, (P₁,P₂); aᵗ) = mu(U, (P₁,-P₂); a)` realized by the flux flip, and then
applying the same public extraction lemma at the transposed field.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The flux flip and the transpose symmetry of the `mu` problem -/

/-- Flux flip of a doubled field. -/
def fluxFlip (X : DoubledField d) : DoubledField d where
  potential := X.potential
  flux := fun x => -X.flux x

/-- The flux flip is an involution. -/
theorem fluxFlip_fluxFlip (X : DoubledField d) : fluxFlip (fluxFlip X) = X := by
  show DoubledField.mk X.potential (fun x => - -X.flux x) = X
  rw [show (fun x => - -X.flux x) = X.flux by funext x; rw [neg_neg]]

/-- The solenoidal zero-normal-trace class is closed under negation. -/
theorem solenoidalZeroNormalTraceFieldOn_neg {U : Set (Vec d)}
    {g : Vec d → Vec d}
    (hg : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (fun x => -g x) := by
  refine ⟨hg.1.neg, fun φ => ?_⟩
  calc
    ∫ x in U, vecDot (-g x) (φ.grad x) ∂MeasureTheory.volume
        = ∫ x in U, -vecDot (g x) (φ.grad x) ∂MeasureTheory.volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show vecDot (-g x) (φ.grad x) = -vecDot (g x) (φ.grad x)
          rw [vecDot_neg_left]
    _ = -∫ x in U, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume :=
          integral_neg _
    _ = 0 := by rw [hg.2 φ, neg_zero]

/-- The flux flip maps the admissible class at `(P₁, P₂)` onto the admissible
class at `(P₁, -P₂)`. -/
theorem isDoubledMuAdmissible_fluxFlip {U : Domain d} {P : BlockVec d}
    {X : DoubledField d} (hX : IsDoubledMuAdmissible U P X) :
    IsDoubledMuAdmissible U (P.1, -P.2) (fluxFlip X) := by
  refine ⟨hX.1, ?_⟩
  have hneg := solenoidalZeroNormalTraceFieldOn_neg hX.2
  have hfun : (fun x => (fluxFlip X).flux x - ((P.1, -P.2) : BlockVec d).2)
      = fun x => -(X.flux x - P.2) := by
    funext x
    show -X.flux x - -P.2 = -(X.flux x - P.2)
    abel
  rw [hfun]
  exact hneg

/-- The doubled energy value is invariant under simultaneous transpose of the
coefficient and flux flip of the field: pointwise exact, no null sets. -/
theorem doubledMuValue_transpose_fluxFlip {U : Domain d} (a : CoeffOn U)
    (X : DoubledField d) :
    doubledMuValue U a.transpose (fluxFlip X) = doubledMuValue U a X := by
  unfold doubledMuValue
  have hfun : (fun x => blockEnergyDensityAt a.transpose ((fluxFlip X).eval x) x)
      = fun x => blockEnergyDensityAt a (X.eval x) x := by
    funext x
    unfold blockEnergyDensityAt
    congr 1
    exact blockQuadForm_transpose_fluxFlip (a.toCoeffField x) (X.eval x)
  rw [hfun]

/-- The flux flip transports `mu`-minimizers of the base problem to
`mu`-minimizers of the transposed problem at the flux-flipped loading. -/
theorem isDoubledMuMinimizer_transpose_fluxFlip {U : Domain d}
    {a : CoeffOn U} {P : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a P X) :
    IsDoubledMuMinimizer U a.transpose (P.1, -P.2) (fluxFlip X) := by
  refine ⟨isDoubledMuAdmissible_fluxFlip hX.1, ?_⟩
  intro Y hY
  have hYflip : IsDoubledMuAdmissible U P (fluxFlip Y) := by
    have h2 := isDoubledMuAdmissible_fluxFlip hY
    simpa using h2
  have hle := hX.2 (fluxFlip Y) hYflip
  have hR : doubledMuValue U a.transpose Y =
      doubledMuValue U a (fluxFlip Y) := by
    conv_lhs => rw [← fluxFlip_fluxFlip Y]
    exact doubledMuValue_transpose_fluxFlip a (fluxFlip Y)
  rw [hR, doubledMuValue_transpose_fluxFlip a X]
  exact hle

/-! ## The adjoint extraction -/

/-- A doubled-`mu` minimizer at loading `(-p, q)` extracts the gradient of the
*adjoint* scalar canonical response maximizer from the difference of its
potential and its lower block image.  Companion of the public CoarseGraining
lemma `doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient`,
obtained by transporting the minimizer through the flux-flip/transpose
symmetry. -/
theorem doubledMuMinimizer_neg_left_extracts_adjointMaximizerGradient
    {U : Domain d} (a : CoeffOn U) (p q : Vec d) {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    (fun x => X.potential x -
        (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x =>
      (canonicalMaximizer (responseExistenceTheory U a.transpose)
        p (-q)).toSolution.toH1.grad x := by
  have hflip : IsDoubledMuMinimizer U a.transpose (-p, -q) (fluxFlip X) := by
    have h := isDoubledMuMinimizer_transpose_fluxFlip hX
    exact h
  have hextract :=
    doubledMuMinimizer_negLeft_eq_canonicalGradient
      U a.transpose p (-q) hflip
  have hfun : (fun x => (fluxFlip X).potential x +
      (blockMatVecMul (blockCoeffField a.transpose.toCoeffField x)
        ((fluxFlip X).eval x)).2)
      = fun x => X.potential x -
        (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2 := by
    funext x
    show X.potential x +
        (blockMatVecMul (blockCoeffField a.transpose.toCoeffField x)
          ((fluxFlip X).eval x)).2 = _
    rw [show (blockMatVecMul (blockCoeffField a.transpose.toCoeffField x)
          ((fluxFlip X).eval x)).2
        = -(blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2 from
      blockMatVecMul_blockMatrixOfCoeff_transpose_fluxFlip_snd
        (a.toCoeffField x) (X.eval x), sub_eq_add_neg]
  rw [hfun] at hextract
  exact hextract

/-! ## The identification of the linear path term -/

/-- **The linear path term of a `mu`-minimizer is the `D_h` quadratic form.**
For a doubled-`mu` minimizer `X` at loading `(-p, q)`,

`ℓ(X) = ½ (p,-q) · D_h(U; a) (p,-q)`,

which is exactly the response-derivative slope in the frozen target
`responseJ_derivative`.  Source: the display chain
`⨍ 2(∇w + ∇w*)·h(∇w - ∇w*) = ⨍ ∇v*·h∇v = P·D_h(U;a)P` combined with the
characterization theorem of the coarse-matrix derivative. -/
theorem pathLinearTerm_isDoubledMuMinimizer_eq {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (p q : Vec d) {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a (-p, q) X) :
    pathLinearTerm a h.1.1 X =
      (1 / 2 : ℝ) * blockVecDot (p, -q)
        (blockMatVecMul (coarseMatrixDerivative U a h.1) (p, -q)) := by
  obtain ⟨-, hFormula, -⟩ := coarseMatrixDerivative_characterization U a h.1
  have hvAdj := canonicalMaximizer_isMaximizer
    (responseExistenceTheory U a.transpose) p (-q)
  have hv := canonicalMaximizer_isMaximizer (responseExistenceTheory U a) p q
  have hv' : IsResponseMaximizer U a p (- -q)
      (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution := by
    rw [neg_neg]
    exact hv
  have hchar := hFormula p (-q)
    (canonicalMaximizer (responseExistenceTheory U a.transpose)
      p (-q)).toSolution
    (canonicalMaximizer (responseExistenceTheory U a) p q).toSolution
    hvAdj hv'
  rw [hchar]
  have hplus :=
    doubledMuMinimizer_negLeft_eq_canonicalGradient
      U a p q hX
  have hminus :=
    doubledMuMinimizer_neg_left_extracts_adjointMaximizerGradient a p q hX
  have hsmul := volumeAverage_smul (U : Set (Vec d)) (1 / 2 : ℝ)
    (fun x => vecDot
      ((canonicalMaximizer (responseExistenceTheory U a.transpose)
        p (-q)).toSolution.toH1.grad x)
      (matVecMul (h.1.1 x)
        ((canonicalMaximizer (responseExistenceTheory U a)
          p q).toSolution.toH1.grad x)))
  show volumeAverage (U : Set (Vec d)) (pathLinearDensity a h.1.1 X) = _
  rw [show ((1 / 2 : ℝ) * average U (fun x => vecDot
        ((canonicalMaximizer (responseExistenceTheory U a.transpose)
          p (-q)).toSolution.toH1.grad x)
        (matVecMul (h.1.1 x)
          ((canonicalMaximizer (responseExistenceTheory U a)
            p q).toSolution.toH1.grad x))))
      = volumeAverage (U : Set (Vec d)) ((1 / 2 : ℝ) • fun x => vecDot
        ((canonicalMaximizer (responseExistenceTheory U a.transpose)
          p (-q)).toSolution.toH1.grad x)
        (matVecMul (h.1.1 x)
          ((canonicalMaximizer (responseExistenceTheory U a)
            p q).toSolution.toH1.grad x))) from hsmul.symm]
  apply volumeAverage_congr_ae
  filter_upwards [h.2, hplus, hminus] with x hskew hpx hmx
  set B : Vec d :=
    (blockMatVecMul (blockCoeffField a.toCoeffField x) (X.eval x)).2 with hB
  show -vecDot (matVecMul (h.1.1 x) (X.potential x)) B =
    (1 / 2 : ℝ) * vecDot
      ((canonicalMaximizer (responseExistenceTheory U a.transpose)
        p (-q)).toSolution.toH1.grad x)
      (matVecMul (h.1.1 x)
        ((canonicalMaximizer (responseExistenceTheory U a)
          p q).toSolution.toH1.grad x))
  rw [← hpx, ← hmx]
  have hz1 : vecDot (X.potential x)
      (matVecMul (h.1.1 x) (X.potential x)) = 0 :=
    vecDot_matVecMul_self_eq_zero_of_symmPart_eq_zero hskew (X.potential x)
  have hz2 : vecDot B (matVecMul (h.1.1 x) B) = 0 :=
    vecDot_matVecMul_self_eq_zero_of_symmPart_eq_zero hskew B
  have hanti : vecDot (X.potential x) (matVecMul (h.1.1 x) B) =
      -vecDot B (matVecMul (h.1.1 x) (X.potential x)) :=
    vecDot_matVecMul_antisymm_of_symmPart_eq_zero hskew (X.potential x) B
  have hcomm : vecDot (matVecMul (h.1.1 x) (X.potential x)) B =
      vecDot B (matVecMul (h.1.1 x) (X.potential x)) :=
    vecDot_comm _ _
  rw [sub_eq_add_neg, matVecMul_add, vecDot_add_left, vecDot_neg_left,
    vecDot_add_right, vecDot_add_right, hz1, hz2, hanti, hcomm]
  ring

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
