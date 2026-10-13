/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.PerturbCoeffOn
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.CoarseMatrixDerivative.BoundedField
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.PointwiseExpansion
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMuDefinitions
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Representatives

/-!
# Densities

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Path densities for the coefficient perturbation `a + t h`

Along the canonical perturbation path `t ↦ perturbCoeffOn U a h t` the doubled
energy density of a fixed doubled field expands *exactly* in `t`:

`E_t(X)(x) = E_0(X)(x) + t · L(X)(x) + t² · Q(X)(x)`

with the linear density `L(X) = -(h X₁)·(bfA(a) X)₂` and the quadratic density
`Q(X) = ½ (h X₁)·s⁻¹(h X₁)`.  This module defines the two densities, proves
the a.e. expansion from the pointwise algebra in `PointwiseExpansion`, and
establishes the `L¹` integrability needed to pass to averaged values.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Path

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Averages only see the a.e. class of the integrand. -/
theorem volumeAverage_congr_ae {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact integral_congr_ae hfg

/-! ## The canonical path through the frozen perturbation -/

/-- The frozen perturbation body evaluated at a point. -/
theorem perturbCoeffOn_toCoeffField_apply (U : Domain d) (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (t : ℝ) (x : Vec d) :
    (perturbCoeffOn U a h t).toCoeffField x = a.toCoeffField x + t • h.1.1 x :=
  rfl

/-- At `t = 0` the canonical path starts at the base field, up to a null set. -/
theorem perturbCoeffOn_zero_aeeq (U : Domain d) (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) :
    CoeffOn.AEEq (perturbCoeffOn U a h 0) a := by
  refine Filter.Eventually.of_forall fun x => ?_
  rw [perturbCoeffOn_toCoeffField_apply]
  simp

/-! ## The linear and quadratic path densities -/

/-- Linear-response density of a doubled field along the path: the exact
cross term `-(h X₁) · (bfA(a) X)₂` produced by the shear conjugation. -/
def pathLinearDensity {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X : DoubledField d) : Vec d → ℝ :=
  fun x =>
    -vecDot (matVecMul (hField x) (X.potential x))
      ((blockMatVecMul (blockMatrixField a x) (X.eval x)).2)

/-- Quadratic-response density of a doubled field along the path:
`½ (h X₁) · s⁻¹ (h X₁)`. -/
def pathQuadraticDensity {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X : DoubledField d) : Vec d → ℝ :=
  fun x =>
    (1 / 2 : ℝ) * vecDot (matVecMul (hField x) (X.potential x))
      (matVecMul (symmPart (a.toCoeffField x))⁻¹
        (matVecMul (hField x) (X.potential x)))

/-- Averaged linear-response term. -/
def pathLinearTerm {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X : DoubledField d) : ℝ :=
  average U (pathLinearDensity a hField X)

/-- Averaged quadratic-response term. -/
def pathQuadraticTerm {U : Domain d} (a : CoeffOn U)
    (hField : CoeffField d) (X : DoubledField d) : ℝ :=
  average U (pathQuadraticDensity a hField X)

/-! ## The exact pointwise and a.e. expansions along the path -/

/-- Exact expansion of the doubled energy density along the canonical path at
a point where the perturbation is skew. -/
theorem blockEnergyDensityAt_perturbCoeffOn {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (t : ℝ) {x : Vec d}
    (hx : symmPart (h.1.1 x) = 0) (X : BlockVec d) :
    blockEnergyDensityAt (perturbCoeffOn U a h t) X x =
      blockEnergyDensityAt a X x
        + t * (-vecDot (matVecMul (h.1.1 x) X.1)
            ((blockMatVecMul (blockMatrixField a x) X).2))
        + t ^ 2 * ((1 / 2 : ℝ) * vecDot (matVecMul (h.1.1 x) X.1)
            (matVecMul (symmPart (a.toCoeffField x))⁻¹
              (matVecMul (h.1.1 x) X.1))) := by
  unfold blockEnergyDensityAt
  simp only [blockMatrixField_eq_blockMatrixOfCoeff]
  rw [show (perturbCoeffOn U a h t).toCoeffField x =
      a.toCoeffField x + t • h.1.1 x from rfl]
  have hg : symmPart (t • h.1.1 x) = 0 := by
    rw [symmPart_smul, hx, smul_zero]
  rw [blockQuadForm_add_skew (a.toCoeffField x) hg X]
  simp only [smul_matVecMul, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

/-- The a.e. exact expansion of the doubled energy density of a doubled field
along the canonical path. -/
theorem blockEnergyDensity_expansion_ae {U : Domain d} (a : CoeffOn U)
    (h : LInfSkewMatrixFieldOn U) (t : ℝ) (X : DoubledField d) :
    (fun x => blockEnergyDensityAt (perturbCoeffOn U a h t) (X.eval x) x)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x => blockEnergyDensityAt a (X.eval x) x
      + t * pathLinearDensity a h.1.1 X x
      + t ^ 2 * pathQuadraticDensity a h.1.1 X x := by
  filter_upwards [h.2] with x hx
  rw [blockEnergyDensityAt_perturbCoeffOn a h t hx (X.eval x)]
  rfl

/-! ## Square integrability of the block image of an `L²` doubled field -/

/-- The second block component of `bfA(a) X` is vector `L²` when the doubled
field has vector `L²` components. -/
theorem memVectorL2_blockMatrixField_snd {U : Domain d} (a : CoeffOn U)
    {X : DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => (blockMatVecMul (blockMatrixField a x) (X.eval x)).2) := by
  set b : CoeffOn U := HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn U a
    with hb
  have hEll :=
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hae : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      a.toCoeffField :=
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hk : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (skewPart (b.toCoeffField x)) (X.potential x)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hpot
  have hsub : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (skewPart (b.toCoeffField x)) (X.potential x)
        - X.flux x) :=
    hk.sub hflux
  have hw : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (symmPart (b.toCoeffField x))⁻¹
        (matVecMul (skewPart (b.toCoeffField x)) (X.potential x)
          - X.flux x)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hsub
  refine MeasureTheory.MemLp.ae_eq ?_ hw.neg
  filter_upwards [hae] with x hx
  rw [blockMatrixField_eq_blockMatrixOfCoeff,
    blockMatVecMul_blockMatrixOfCoeff_snd, ← hx]
  rfl

/-- The first block component of `bfA(a) X` is vector `L²` when the doubled
field has vector `L²` components. -/
theorem memVectorL2_blockMatrixField_fst {U : Domain d} (a : CoeffOn U)
    {X : DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => (blockMatVecMul (blockMatrixField a x) (X.eval x)).1) := by
  set b : CoeffOn U := HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn U a
    with hb
  have hEll :=
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hae : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      a.toCoeffField :=
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hsnd : MemVectorL2 (U : Set (Vec d))
      (fun x => (blockMatVecMul (blockMatrixField b x) (X.eval x)).2) :=
    memVectorL2_blockMatrixField_snd b hpot hflux
  have hs : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (symmPart (b.toCoeffField x)) (X.potential x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hpot
  have hkim : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (skewPart (b.toCoeffField x))
        ((blockMatVecMul (blockMatrixField b x) (X.eval x)).2)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hsnd
  refine MeasureTheory.MemLp.ae_eq ?_ (hs.add hkim)
  filter_upwards [hae] with x hx
  change matVecMul (symmPart (b.toCoeffField x)) (X.potential x) +
      matVecMul (skewPart (b.toCoeffField x))
        ((blockMatVecMul (blockMatrixField b x) (X.eval x)).2) = _
  rw [blockMatrixField_eq_blockMatrixOfCoeff,
    blockMatrixField_eq_blockMatrixOfCoeff,
    blockMatVecMul_blockMatrixOfCoeff_fst, hx]
  rfl

/-- Applying the a.e. inverse of the symmetric part preserves vector `L²`. -/
theorem memVectorL2_matVecMul_symmPartInv {U : Domain d} (a : CoeffOn U)
    {f : Vec d → Vec d} (hf : MemVectorL2 (U : Set (Vec d)) f) :
    MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (symmPart (a.toCoeffField x))⁻¹ (f x)) := by
  have hEll :=
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hae : (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn
        U a).toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      a.toCoeffField :=
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hw : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul
        (symmPart ((HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn
          U a).toCoeffField x))⁻¹ (f x)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hf
  refine MeasureTheory.MemLp.ae_eq ?_ hw
  filter_upwards [hae] with x hx
  rw [hx]

/-! ## Memberships from `mu`-admissibility -/

/-- The potential component of a `mu`-admissible doubled field is vector `L²`. -/
theorem memVectorL2_potential_of_isDoubledMuAdmissible {U : Domain d}
    {P : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledMuAdmissible U P X) :
    MemVectorL2 (U : Set (Vec d)) X.potential := by
  have h1 : MemVectorL2 (U : Set (Vec d)) (fun x => X.potential x - P.1) :=
    hX.1.1
  have h2 : MemVectorL2 (U : Set (Vec d)) (fun _ : Vec d => P.1) :=
    memVectorL2_const P.1
  refine MeasureTheory.MemLp.ae_eq
    (Filter.Eventually.of_forall fun x => ?_) (h1.add h2)
  change (X.potential x - P.1) + P.1 = X.potential x
  abel

/-- The flux component of a `mu`-admissible doubled field is vector `L²`. -/
theorem memVectorL2_flux_of_isDoubledMuAdmissible {U : Domain d}
    {P : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledMuAdmissible U P X) :
    MemVectorL2 (U : Set (Vec d)) X.flux := by
  have h1 : MemVectorL2 (U : Set (Vec d)) (fun x => X.flux x - P.2) :=
    hX.2.1
  have h2 : MemVectorL2 (U : Set (Vec d)) (fun _ : Vec d => P.2) :=
    memVectorL2_const P.2
  refine MeasureTheory.MemLp.ae_eq
    (Filter.Eventually.of_forall fun x => ?_) (h1.add h2)
  change (X.flux x - P.2) + P.2 = X.flux x
  abel

/-! ## Integrability of the densities -/

/-- The base doubled energy density of an `L²` doubled field is integrable. -/
theorem integrableOn_blockEnergyDensity {U : Domain d} (a : CoeffOn U)
    {X : DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    IntegrableOn (fun x => blockEnergyDensityAt a (X.eval x) x)
      (U : Set (Vec d)) := by
  have h1 := integrableOn_vecDot_of_memVectorL2 hpot
    (memVectorL2_blockMatrixField_fst a hpot hflux)
  have h2 := integrableOn_vecDot_of_memVectorL2 hflux
    (memVectorL2_blockMatrixField_snd a hpot hflux)
  have hsum := (h1.add h2).const_mul (1 / 2 : ℝ)
  exact hsum

/-- The linear path density is integrable for `L²` doubled fields and `L∞`
perturbations. -/
theorem integrableOn_pathLinearDensity {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) {X : DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) X.flux) :
    IntegrableOn (pathLinearDensity a h.1 X) (U : Set (Vec d)) := by
  have hmul :=
    Algsuperdiff.Section24.memVectorL2_matVecMul_of_lInfMatrixFieldOn U h hpot
  have hdot := integrableOn_vecDot_of_memVectorL2 hmul
    (memVectorL2_blockMatrixField_snd a hpot hflux)
  exact hdot.neg

/-- The quadratic path density is integrable for `L²` doubled fields and `L∞`
perturbations. -/
theorem integrableOn_pathQuadraticDensity {U : Domain d} (a : CoeffOn U)
    (h : LInfMatrixFieldOn U) {X : DoubledField d}
    (hpot : MemVectorL2 (U : Set (Vec d)) X.potential) :
    IntegrableOn (pathQuadraticDensity a h.1 X) (U : Set (Vec d)) := by
  have hmul :=
    Algsuperdiff.Section24.memVectorL2_matVecMul_of_lInfMatrixFieldOn U h hpot
  have hdot := integrableOn_vecDot_of_memVectorL2 hmul
    (memVectorL2_matVecMul_symmPartInv a hmul)
  exact hdot.const_mul (1 / 2 : ℝ)

end

end Algsuperdiff.Section24.Sensitivity.Provider.Path
