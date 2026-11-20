/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.ProductFourier
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The axial sector decomposition of product `L²` as a Hilbert sum

The operator theory of the induction equation is built one axial Fourier sector
at a time: the isometry `axialLiftL2 K : TransverseC3L2 →ₗᵢ[ℂ] ProductC3L2`
(`FastDynamo/Fourier/AxialL2.lean`) sends a transverse amplitude `b` to the mode
`(y, x₃) ↦ e^{2π i K x₃} b(y)`.  This module proves that the family of those
sectors decomposes the whole product space: `ProductC3L2` is the `ℤ`-indexed
Hilbert sum of copies of `TransverseC3L2`.

## Contents

* **Sector orthogonality.**  `inner_axialLiftL2` computes the inner product of
  two lifted amplitudes by Fubini and orthonormality of the circle characters:
  it is the transverse inner product on the diagonal and `0` off it.  Hence
  `orthogonalFamily_axialLiftL2`.
* **Totality.**  `transverseInsertL2` places a transverse scalar field in one
  vector coordinate, `inner_axialLiftL2_insert` identifies the pairing of such
  an inserted lifted field with a product Fourier coefficient functional, and
  `axialSectors_total` deduces from the completeness of the product Fourier
  system (`productC3L2_ext_coeff`) that the span of the sectors is dense.
* **The decomposition.**  `isHilbertSum_axialLiftL2` and the isometric
  identification `axialDecomposition : ProductC3L2 ≃ₗᵢ[ℂ] ℓ²(ℤ; TransverseC3L2)`,
  with `axialDecomposition_symm_single` and `axialDecomposition_axialLiftL2`.
* **Sector projections.**  `axialSectorProjL2 K : ProductC3L2 →L[ℂ] TransverseC3L2`
  with `axialSectorProjL2_axialLiftL2` (`= b` on its own sector, `= 0` off it).

Nothing here uses the operator layer: the whole module is Fourier analysis on
the product torus together with Mathlib's `IsHilbertSum` API.  The sign and
normalization conventions are those of `FastDynamo.Conventions`: all three
measures are normalized, and `axialCharacter K x = e^{2π i K x}`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Orthogonality of the axial sectors -/

/--
Distinct axial sectors are orthogonal, and each lift is isometric: the inner
product of two lifted transverse amplitudes is the transverse inner product when
the axial frequencies agree and `0` otherwise.  This is Fubini on the split
product measure together with orthonormality of the circle characters, and it is
the vector-valued form of `inner_scalarAxialLiftL2`.
-/
theorem inner_axialLiftL2 (k K : ℤ) (b c : TransverseC3L2) :
    inner ℂ (axialLiftL2 k b) (axialLiftL2 K c) =
      if k = K then inner ℂ b c else 0 := by
  have haxial :
      ∫ x : AxialCircle, starRingEnd ℂ (axialCharacter k x) * axialCharacter K x
        ∂axialMeasure = if k = K then 1 else 0 := by
    have h := (orthonormal_iff_ite.mp
      (orthonormal_fourier (T := (1 : ℝ)))) k K
    simpa [MeasureTheory.ContinuousMap.inner_toLp, axialCharacter, mul_comm] using h
  rw [MeasureTheory.L2.inner_def]
  have hpoint :
      (fun x : ProductTorus3 =>
        inner ℂ ((axialLiftL2 k b : ProductC3L2) x)
          ((axialLiftL2 K c : ProductC3L2) x)) =ᵐ[productMeasure]
      fun x => (inner ℂ (b x.1) (c x.1) : ℂ) *
        (starRingEnd ℂ (axialCharacter k x.2) * axialCharacter K x.2) := by
    filter_upwards [axialLiftL2_coe_ae k b, axialLiftL2_coe_ae K c] with x hb hc
    rw [hb, hc, inner_smul_left, inner_smul_right]
    ring
  rw [integral_congr_ae hpoint]
  change
    ∫ x : TransverseTorus × AxialCircle,
      ((inner ℂ (b x.1) (c x.1) : ℂ) *
        (starRingEnd ℂ (axialCharacter k x.2) * axialCharacter K x.2))
      ∂transverseMeasure.prod axialMeasure = _
  rw [integral_prod_mul (f := fun y : TransverseTorus => (inner ℂ (b y) (c y) : ℂ))
    (g := fun x : AxialCircle => starRingEnd ℂ (axialCharacter k x) * axialCharacter K x)]
  have htrans : (∫ y : TransverseTorus, (inner ℂ (b y) (c y) : ℂ) ∂transverseMeasure)
      = inner ℂ b c := (MeasureTheory.L2.inner_def b c).symm
  rw [haxial, htrans]
  split_ifs <;> simp

/--
The axial lifts form an orthogonal family of isometries indexed by the axial
frequency; this is the off-diagonal half of `inner_axialLiftL2`.
-/
theorem orthogonalFamily_axialLiftL2 :
    OrthogonalFamily ℂ (fun _ : ℤ => TransverseC3L2) (fun K => axialLiftL2 K) := by
  intro k K hne b c
  rw [inner_axialLiftL2, ite_eq_right hne]

/-! ## Totality of the axial sectors -/

/--
Place a transverse scalar field into the `i`-th coordinate of a transverse
vector field.  This is the test-vector constructor used to reduce totality of
the axial sectors to the completeness of the scalar product Fourier system.
-/
def transverseInsertL2 (i : Fin 3) : TransverseScalarL2 →L[ℂ] TransverseC3L2 :=
  (ContinuousLinearMap.toSpanSingleton ℂ (EuclideanSpace.single i (1 : ℂ))).compLpL 2
    transverseMeasure

/-- A representative of `transverseInsertL2 i g` is `y ↦ g y • eᵢ`. -/
theorem transverseInsertL2_coe_ae (i : Fin 3) (g : TransverseScalarL2) :
    (transverseInsertL2 i g : TransverseTorus → C3) =ᵐ[transverseMeasure]
      fun y => (g y) • EuclideanSpace.single i (1 : ℂ) := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ
    (EuclideanSpace.single i (1 : ℂ))).coeFn_compLpL (p := 2) (μ := transverseMeasure) g]
    with y hy
  simpa [transverseInsertL2, ContinuousLinearMap.toSpanSingleton_apply] using hy

/--
Adjointness of the inserted lift: pairing a product field against the axial lift
of an inserted transverse scalar field is the scalar pairing of the lifted
scalar field against the `i`-th coordinate of the product field.  Together with
`productC3L2_ext_coeff` this converts the completeness of the scalar product
Fourier system into totality of the axial sectors.
-/
theorem inner_axialLiftL2_insert (k : ℤ) (i : Fin 3) (g : TransverseScalarL2)
    (f : ProductC3L2) :
    inner ℂ (axialLiftL2 k (transverseInsertL2 i g)) f
      = inner ℂ (scalarAxialLiftL2 k g) (productCoordL2 i f) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have hprod : ((fun x : ProductTorus3 =>
      (transverseInsertL2 i g : TransverseTorus → C3) x.1)) =ᵐ[productMeasure]
      fun x => ((g x.1 : ℂ)) • EuclideanSpace.single i (1 : ℂ) :=
    (measurePreserving_fst (μ := transverseMeasure)
      (ν := axialMeasure)).quasiMeasurePreserving.ae_eq_comp
        (transverseInsertL2_coe_ae i g)
  filter_upwards [axialLiftL2_coe_ae k (transverseInsertL2 i g),
    scalarAxialLiftL2Fun_ae k g, hprod,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := productMeasure) f]
    with x h1 h2 h3 h4
  rw [h1, h3]
  have h2' : ((scalarAxialLiftL2 k g : ProductScalarL2) : ProductTorus3 → ℂ) x
      = axialCharacter k x.2 * g x.1 := h2
  rw [h2']
  have h4' : ((productCoordL2 i f : ProductScalarL2) : ProductTorus3 → ℂ) x = (f x) i := h4
  rw [h4']
  rw [inner_smul_left, inner_smul_left]
  simp only [EuclideanSpace.inner_single_left, RCLike.inner_apply, map_mul, map_one]
  ring

/--
The axial sectors are total: the closure of the span of their ranges is the
whole of `ProductC3L2`.  A vector orthogonal to every sector is orthogonal to
every axial lift of an inserted transverse monomial, hence has vanishing
product Fourier coefficients, hence vanishes by `productC3L2_ext_coeff`.
-/
theorem axialSectors_total :
    (⊤ : Submodule ℂ ProductC3L2) ≤
      (⨆ K : ℤ, (axialLiftL2 K).range).topologicalClosure := by
  rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_orthogonal] at hf
  refine productC3L2_ext_coeff ?_
  intro n k i
  rw [map_zero]
  have hmem : axialLiftL2 k (transverseInsertL2 i (transverseMonomialL2 n)) ∈
      ⨆ K : ℤ, (axialLiftL2 K).range :=
    Submodule.mem_iSup_of_mem k ⟨_, rfl⟩
  have h0 := hf _ hmem
  rw [inner_axialLiftL2_insert] at h0
  simpa [productCoeffCLM, productMonomialL2] using h0

/--
`ProductC3L2` is the `ℤ`-indexed Hilbert sum of copies of `TransverseC3L2`,
embedded by the axial lifts.
-/
theorem isHilbertSum_axialLiftL2 :
    IsHilbertSum ℂ (fun _ : ℤ => TransverseC3L2) (fun K => axialLiftL2 K) :=
  IsHilbertSum.mk orthogonalFamily_axialLiftL2 axialSectors_total

/--
The axial decomposition `L²(T² × T¹; ℂ³) ≃ ℓ²(ℤ; L²(T²; ℂ³))`: an isometric
isomorphism putting the axial Fourier frequency outside and the transverse
variable inside.
-/
def axialDecomposition : ProductC3L2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => TransverseC3L2) 2 :=
  isHilbertSum_axialLiftL2.linearIsometryEquiv

/-- The decomposition sends an elementary `ℓ²` vector back to the axial lift it came from. -/
theorem axialDecomposition_symm_single (K : ℤ) (b : TransverseC3L2) :
    axialDecomposition.symm (lp.single 2 K b) = axialLiftL2 K b :=
  isHilbertSum_axialLiftL2.linearIsometryEquiv_symm_apply_single (i := K) b

/-- The decomposition sends an axial lift to the elementary `ℓ²` vector at its frequency. -/
theorem axialDecomposition_axialLiftL2 (K : ℤ) (b : TransverseC3L2) :
    axialDecomposition (axialLiftL2 K b) = lp.single 2 K b := by
  rw [← axialDecomposition_symm_single K b, LinearIsometryEquiv.apply_symm_apply]

/-! ## Sector projections and Parseval -/

/--
The orthogonal projection of a product field onto its `K`-th axial sector,
read as a transverse amplitude: the `K`-th coordinate of the axial
decomposition.
-/
def axialSectorProjL2 (K : ℤ) : ProductC3L2 →L[ℂ] TransverseC3L2 :=
  (lp.evalCLM ℂ (fun _ : ℤ => TransverseC3L2) 2 K).comp
    axialDecomposition.toLinearIsometry.toContinuousLinearMap

/-- The sector projection is evaluation of the axial decomposition at the frequency `K`. -/
theorem axialSectorProjL2_apply (K : ℤ) (V : ProductC3L2) :
    axialSectorProjL2 K V = axialDecomposition V K := rfl

/--
The sector projections are dual to the sector lifts: `axialSectorProjL2 K`
recovers the amplitude of a `K`-mode and kills every other mode.
-/
theorem axialSectorProjL2_axialLiftL2 (k K : ℤ) (b : TransverseC3L2) :
    axialSectorProjL2 K (axialLiftL2 k b) = if k = K then b else 0 := by
  rw [axialSectorProjL2_apply, axialDecomposition_axialLiftL2]
  by_cases hk : k = K
  · subst hk
    simp
  · rw [ite_eq_right hk]
    exact lp.single_apply_ne (E := fun _ : ℤ => TransverseC3L2) 2 k b (Ne.symm hk)

end

end FastDynamo
