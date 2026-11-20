/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusVelocityConcrete
public import LeanPool.FastDynamo.Global.TorusAxialVelocityWeakTransfer
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# The full concrete transverse global velocity

The helical cell derivatives are not summable in `L∞`, so the global
helical Fourier graph cannot be obtained by summing the cell graph norms.
Instead this file bundles the constructed pointwise disjoint-support
limits, and derives their Fourier weak-derivative identities by passing the
finite-cell identities through the established dominated integral limits.

The axial corrections do have summable `L∞` value and derivative norms.
They are summed coefficientwise, using the cell weak-transfer
theorem.  Adding the two independently constructed graph elements gives the
single global velocity, with its literal pointwise representatives.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped BigOperators ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

namespace FullVelocityConcrete

open EuclideanCellSourceCertificate
open AxialWeakTransfer

/-! ## A reusable coefficient/representative bridge -/

/-- A Fourier coefficient of an `L²` field can be computed from any of its
raw almost-everywhere representatives. -/
theorem transverseCoeffCLM_eq_integral_of_coe_ae
    (u : TransverseC3L2) (v : TransverseTorus → C3)
    (hu : (u : TransverseTorus → C3) =ᵐ[transverseMeasure] v)
    (frequency : TransverseFrequency) (i : Fin 3) :
    transverseCoeffCLM frequency i u =
      ∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * v q i
          ∂transverseMeasure := by
  rw [← transverseMonomialComponentPairing_eq_coeff,
    transverseMonomialComponentPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae frequency,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL u, hu]
      with q hmono hcoord hvalue
  change ((transverseCoordL2 i u : TransverseScalarL2) :
      TransverseTorus → ℂ) q = _ at hcoord
  rw [hmono, hcoord, hvalue]
  rw [← UnitAddTorus.mFourier_neg]
  rfl

/-! ## The raw real helical global field -/

section Helical

variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed : ℝ)

/-- Real representative of the pointwise disjoint helical value series. -/
def parameterizedHelicalGlobalRealTorusSource
    (q : TransverseTorus) : R3 :=
  vecRe (parameterizedHelicalGlobalTorusSource
    h P angularSpeed axialSpeed q)

/-- Real representative of one pointwise disjoint helical derivative
series. -/
def parameterizedHelicalGlobalRealTorusFirstDerivative
    (j : Fin 2) (q : TransverseTorus) : R3 :=
  vecRe (parameterizedHelicalGlobalTorusFirstDerivative
    h P angularSpeed axialSpeed j q)

/-- Complexifying the real part of the global helical value returns the original field, the
helical series being pointwise real. -/
theorem complexify_parameterizedHelicalGlobalRealTorusSource
    (q : TransverseTorus) :
    complexifyR3
        (parameterizedHelicalGlobalRealTorusSource
          h P angularSpeed axialSpeed q) =
      parameterizedHelicalGlobalTorusSource
        h P angularSpeed axialSpeed q := by
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simp [parameterizedHelicalGlobalRealTorusSource, vecRe,
      complexifyR3_apply]
  · simp [parameterizedHelicalGlobalRealTorusSource, vecRe,
      complexifyR3_apply,
      parameterizedHelicalGlobalTorusSource_pointwiseReal]

/-- Complexifying the real part of a global helical displayed derivative returns the original
field, the derivative series being pointwise real. -/
theorem complexify_parameterizedHelicalGlobalRealTorusFirstDerivative
    (j : Fin 2) (q : TransverseTorus) :
    complexifyR3
        (parameterizedHelicalGlobalRealTorusFirstDerivative
          h P angularSpeed axialSpeed j q) =
      parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed j q := by
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simp [parameterizedHelicalGlobalRealTorusFirstDerivative, vecRe,
      complexifyR3_apply]
  · simp [parameterizedHelicalGlobalRealTorusFirstDerivative, vecRe,
      complexifyR3_apply,
      parameterizedHelicalGlobalTorusFirstDerivative_pointwiseReal]

/-- The real global helical value is measurable, being the real part of a measurable complex
field. -/
theorem measurable_parameterizedHelicalGlobalRealTorusSource :
    Measurable (parameterizedHelicalGlobalRealTorusSource
      h P angularSpeed axialSpeed) :=
  vecReCLM.measurable.comp
    (measurable_parameterizedHelicalGlobalTorusSource
      h P angularSpeed axialSpeed)

/-- Each real global helical displayed derivative is measurable. -/
theorem measurable_parameterizedHelicalGlobalRealTorusFirstDerivative
    (j : Fin 2) :
    Measurable (parameterizedHelicalGlobalRealTorusFirstDerivative
      h P angularSpeed axialSpeed j) :=
  vecReCLM.measurable.comp
    (measurable_parameterizedHelicalGlobalTorusFirstDerivative
      h P angularSpeed axialSpeed j)

/-- Pointwise bound on the real global helical value: it is at most the profile value bound times
the largest cell scale `ell 0`, the cells having disjoint supports. -/
theorem norm_parameterizedHelicalGlobalRealTorusSource_le
    (q : TransverseTorus) :
    ‖parameterizedHelicalGlobalRealTorusSource
        h P angularSpeed axialSpeed q‖ ≤
      parameterizedHelicalValueBound h angularSpeed axialSpeed *
        P.scaleFamily.ell 0 :=
  (norm_vecRe_le _).trans
    (norm_parameterizedHelicalGlobalTorusSource_le
      h P angularSpeed axialSpeed q)

/-- Pointwise bound on a real global helical displayed derivative: it is at most the fixed profile
first-derivative bound, uniformly in the cell index. -/
theorem norm_parameterizedHelicalGlobalRealTorusFirstDerivative_le
    (j : Fin 2) (q : TransverseTorus) :
    ‖parameterizedHelicalGlobalRealTorusFirstDerivative
        h P angularSpeed axialSpeed j q‖ ≤
      parameterizedHelicalFirstDerivativeBound
        h angularSpeed axialSpeed :=
  (norm_vecRe_le _).trans
    (norm_parameterizedHelicalGlobalTorusFirstDerivative_le
      h P angularSpeed axialSpeed j q)

/-- The real global helical value is essentially bounded, by its uniform pointwise bound. -/
theorem parameterizedHelicalGlobalRealTorusSource_memLp_top :
    MemLp (parameterizedHelicalGlobalRealTorusSource
      h P angularSpeed axialSpeed) ∞ transverseMeasure :=
  memLp_top_of_bound
    (measurable_parameterizedHelicalGlobalRealTorusSource
      h P angularSpeed axialSpeed).aestronglyMeasurable
    (parameterizedHelicalValueBound h angularSpeed axialSpeed *
      P.scaleFamily.ell 0)
    (Filter.Eventually.of_forall
      (norm_parameterizedHelicalGlobalRealTorusSource_le
        h P angularSpeed axialSpeed))

/-- Each real global helical displayed derivative is essentially bounded, by its uniform pointwise
bound. -/
theorem parameterizedHelicalGlobalRealTorusFirstDerivative_memLp_top
    (j : Fin 2) :
    MemLp (parameterizedHelicalGlobalRealTorusFirstDerivative
      h P angularSpeed axialSpeed j) ∞ transverseMeasure :=
  memLp_top_of_bound
    (measurable_parameterizedHelicalGlobalRealTorusFirstDerivative
      h P angularSpeed axialSpeed j).aestronglyMeasurable
    (parameterizedHelicalFirstDerivativeBound
      h angularSpeed axialSpeed)
    (Filter.Eventually.of_forall
      (norm_parameterizedHelicalGlobalRealTorusFirstDerivative_le
        h P angularSpeed axialSpeed j))

/-- Bundled value of the global helical pointwise series. -/
def parameterizedHelicalGlobalValueLInf : TransverseR3LInf :=
  (parameterizedHelicalGlobalRealTorusSource_memLp_top
    h P angularSpeed axialSpeed).toLp
      (parameterizedHelicalGlobalRealTorusSource
        h P angularSpeed axialSpeed)

/-- Bundled displayed derivative of the global helical pointwise series. -/
def parameterizedHelicalGlobalDerivativeLInf
    (j : Fin 2) : TransverseR3LInf :=
  (parameterizedHelicalGlobalRealTorusFirstDerivative_memLp_top
    h P angularSpeed axialSpeed j).toLp
      (parameterizedHelicalGlobalRealTorusFirstDerivative
        h P angularSpeed axialSpeed j)

/-- The bundled `L∞` class of the global helical value is represented a.e. by the pointwise
disjoint-support series. -/
theorem parameterizedHelicalGlobalValueLInf_coe_ae :
    (parameterizedHelicalGlobalValueLInf
        h P angularSpeed axialSpeed : TransverseTorus → R3)
      =ᵐ[transverseMeasure]
        parameterizedHelicalGlobalRealTorusSource
          h P angularSpeed axialSpeed :=
  MemLp.coeFn_toLp _

/-- The bundled `L∞` class of a global helical derivative is represented a.e. by the pointwise
series of cell derivatives. -/
theorem parameterizedHelicalGlobalDerivativeLInf_coe_ae
    (j : Fin 2) :
    (parameterizedHelicalGlobalDerivativeLInf
        h P angularSpeed axialSpeed j : TransverseTorus → R3)
      =ᵐ[transverseMeasure]
        parameterizedHelicalGlobalRealTorusFirstDerivative
          h P angularSpeed axialSpeed j :=
  MemLp.coeFn_toLp _

/-- The complexified global helical value class is represented a.e. by the complex pointwise
series. -/
theorem complexifyR3LTwo_parameterizedHelicalGlobalValueLInf_coe_ae :
    (complexifyR3LTwo (parameterizedHelicalGlobalValueLInf
        h P angularSpeed axialSpeed) : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        parameterizedHelicalGlobalTorusSource
          h P angularSpeed axialSpeed := by
  filter_upwards [complexifyR3LTwo_coe_ae
      (parameterizedHelicalGlobalValueLInf h P angularSpeed axialSpeed),
    parameterizedHelicalGlobalValueLInf_coe_ae
      h P angularSpeed axialSpeed] with q hcomplex hvalue
  rw [hcomplex, hvalue]
  exact complexify_parameterizedHelicalGlobalRealTorusSource
    h P angularSpeed axialSpeed q

/-- The complexified global helical derivative class is represented a.e. by the complex pointwise
derivative series. -/
theorem complexifyR3LTwo_parameterizedHelicalGlobalDerivativeLInf_coe_ae
    (j : Fin 2) :
    (complexifyR3LTwo (parameterizedHelicalGlobalDerivativeLInf
        h P angularSpeed axialSpeed j) : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        parameterizedHelicalGlobalTorusFirstDerivative
          h P angularSpeed axialSpeed j := by
  filter_upwards [complexifyR3LTwo_coe_ae
      (parameterizedHelicalGlobalDerivativeLInf
        h P angularSpeed axialSpeed j),
    parameterizedHelicalGlobalDerivativeLInf_coe_ae
      h P angularSpeed axialSpeed j] with q hcomplex hderiv
  rw [hcomplex, hderiv]
  exact complexify_parameterizedHelicalGlobalRealTorusFirstDerivative
    h P angularSpeed axialSpeed j q

/-! ### Weak transfer through the disjoint-support limit -/

/-- The raw torus representatives of one helical cell satisfy the Fourier
integration-by-parts identity.  This is expanded through the Euclidean
certificate, rather than imported as a global weak-derivative premise. -/
theorem integral_parameterizedHelicalCell_weakDerivative
    (n : ℕ) (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    (∫ q : TransverseTorus,
        parameterizedHelicalFourierIntegrand frequency i
          ((parameterizedHelicalEuclideanCellCertificate
            h P angularSpeed axialSpeed n).torusFirstDerivative j) q
          ∂transverseMeasure) =
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ q : TransverseTorus,
          parameterizedHelicalFourierIntegrand frequency i
            (parameterizedHelicalEuclideanCellCertificate
              h P angularSpeed axialSpeed n).torusSource q
            ∂transverseMeasure := by
  let C := parameterizedHelicalEuclideanCellCertificate
    h P angularSpeed axialSpeed n
  change (∫ q : TransverseTorus,
      UnitAddTorus.mFourier (-frequency) q *
        C.torusFirstDerivative j q i ∂transverseMeasure) = _
  calc
    _ = ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x *
            C.euclideanFirstDerivativeCoord j i x :=
      C.torusIntegral_mFourier_mul_firstDerivativeCoord_eq_euclidean
        frequency j i
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          ∫ x : Fin 2 → ℝ,
            euclideanMonomial (-frequency) x *
              C.euclideanSourceCoord i x :=
      C.integral_euclideanMonomial_mul_firstDerivativeCoord frequency j i
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          ∫ q : TransverseTorus,
            UnitAddTorus.mFourier (-frequency) q * C.torusSource q i
              ∂transverseMeasure := by
      rw [C.torusIntegral_mFourier_mul_sourceCoord_eq_euclidean]

/-- The Fourier integrand of a finite partial sum of cell sources is the finite sum of the
integrands of the individual cells. -/
theorem parameterizedHelicalFourierIntegrand_partialSource
    (N : ℕ) (frequency : TransverseFrequency) (i : Fin 3) :
    parameterizedHelicalFourierIntegrand frequency i
        (parameterizedHelicalPartialTorusSource
          h P angularSpeed axialSpeed N) =
      fun q ↦ ∑ n ∈ Finset.range N,
        parameterizedHelicalFourierIntegrand frequency i
          (parameterizedHelicalEuclideanCellCertificate
            h P angularSpeed axialSpeed n).torusSource q := by
  funext q
  simp [parameterizedHelicalFourierIntegrand,
    parameterizedHelicalPartialTorusSource, Finset.mul_sum]

/-- The Fourier integrand of a finite partial sum of cell derivatives is the finite sum of the
integrands of the individual cell derivatives. -/
theorem parameterizedHelicalFourierIntegrand_partialDerivative
    (N : ℕ) (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    parameterizedHelicalFourierIntegrand frequency i
        (parameterizedHelicalPartialTorusFirstDerivative
          h P angularSpeed axialSpeed j N) =
      fun q ↦ ∑ n ∈ Finset.range N,
        parameterizedHelicalFourierIntegrand frequency i
          ((parameterizedHelicalEuclideanCellCertificate
            h P angularSpeed axialSpeed n).torusFirstDerivative j) q := by
  funext q
  simp [parameterizedHelicalFourierIntegrand,
    parameterizedHelicalPartialTorusFirstDerivative, Finset.mul_sum]

/-- Every finite initial collection of helical cells satisfies the same
Fourier weak-derivative identity. -/
theorem integral_parameterizedHelicalPartial_weakDerivative
    (N : ℕ) (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    (∫ q : TransverseTorus,
        parameterizedHelicalFourierIntegrand frequency i
          (parameterizedHelicalPartialTorusFirstDerivative
            h P angularSpeed axialSpeed j N) q ∂transverseMeasure) =
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ q : TransverseTorus,
          parameterizedHelicalFourierIntegrand frequency i
            (parameterizedHelicalPartialTorusSource
              h P angularSpeed axialSpeed N) q ∂transverseMeasure := by
  rw [parameterizedHelicalFourierIntegrand_partialDerivative,
    integral_finsetSum (Finset.range N) (fun n _ ↦
      integrable_parameterizedHelicalFourierIntegrand_torusFirstDerivative
        h P angularSpeed axialSpeed frequency i j n)]
  rw [parameterizedHelicalFourierIntegrand_partialSource,
    integral_finsetSum (Finset.range N) (fun n _ ↦
      integrable_parameterizedHelicalFourierIntegrand_torusSource
        h P angularSpeed axialSpeed frequency i n)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_parameterizedHelicalCell_weakDerivative
    h P angularSpeed axialSpeed n frequency j i

/-- Dominated convergence transfers the finite-cell integration-by-parts
identities to the pointwise disjoint global helical series. -/
theorem integral_parameterizedHelicalGlobal_weakDerivative
    (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    (∫ q : TransverseTorus,
        parameterizedHelicalFourierIntegrand frequency i
          (parameterizedHelicalGlobalTorusFirstDerivative
            h P angularSpeed axialSpeed j) q ∂transverseMeasure) =
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ q : TransverseTorus,
          parameterizedHelicalFourierIntegrand frequency i
            (parameterizedHelicalGlobalTorusSource
              h P angularSpeed axialSpeed) q ∂transverseMeasure := by
  have hleft :=
    tendsto_integral_parameterizedHelicalPartialTorusFirstDerivative
      h P angularSpeed axialSpeed frequency j i
  have hsource := tendsto_integral_parameterizedHelicalPartialTorusSource
    h P angularSpeed axialSpeed frequency i
  have hright : Tendsto (fun N : ℕ ↦
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ q : TransverseTorus,
          parameterizedHelicalFourierIntegrand frequency i
            (parameterizedHelicalPartialTorusSource
              h P angularSpeed axialSpeed N) q ∂transverseMeasure)
      atTop
      (nhds ((2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ q : TransverseTorus,
          parameterizedHelicalFourierIntegrand frequency i
            (parameterizedHelicalGlobalTorusSource
              h P angularSpeed axialSpeed) q ∂transverseMeasure)) :=
    tendsto_const_nhds.mul hsource
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall fun N ↦
    (integral_parameterizedHelicalPartial_weakDerivative
      h P angularSpeed axialSpeed N frequency j i).symm)

/-- The raw helical global value and derivatives satisfy the quotient
Fourier graph equations. -/
theorem parameterizedHelicalGlobal_hasFourierWeakDerivative
    (j : Fin 2) :
    HasTransverseFourierDerivative j
      (complexifyR3LTwo (parameterizedHelicalGlobalValueLInf
        h P angularSpeed axialSpeed))
      (complexifyR3LTwo (parameterizedHelicalGlobalDerivativeLInf
        h P angularSpeed axialSpeed j)) := by
  intro frequency i
  calc
    transverseCoeffCLM frequency i
        (complexifyR3LTwo (parameterizedHelicalGlobalDerivativeLInf
          h P angularSpeed axialSpeed j)) =
        ∫ q : TransverseTorus,
          parameterizedHelicalFourierIntegrand frequency i
            (parameterizedHelicalGlobalTorusFirstDerivative
              h P angularSpeed axialSpeed j) q ∂transverseMeasure :=
      transverseCoeffCLM_eq_integral_of_coe_ae _ _
        (complexifyR3LTwo_parameterizedHelicalGlobalDerivativeLInf_coe_ae
          h P angularSpeed axialSpeed j) frequency i
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          ∫ q : TransverseTorus,
            parameterizedHelicalFourierIntegrand frequency i
              (parameterizedHelicalGlobalTorusSource
                h P angularSpeed axialSpeed) q ∂transverseMeasure :=
      integral_parameterizedHelicalGlobal_weakDerivative
        h P angularSpeed axialSpeed frequency j i
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          transverseCoeffCLM frequency i
            (complexifyR3LTwo (parameterizedHelicalGlobalValueLInf
              h P angularSpeed axialSpeed)) := by
      rw [transverseCoeffCLM_eq_integral_of_coe_ae _ _
        (complexifyR3LTwo_parameterizedHelicalGlobalValueLInf_coe_ae
          h P angularSpeed axialSpeed) frequency i]
      rfl

/-- The two bundled helical derivative components. -/
def parameterizedHelicalGlobalGradientLInf : TransverseR3GradientLInf :=
  toLp ∞ fun j ↦
    parameterizedHelicalGlobalDerivativeLInf
      h P angularSpeed axialSpeed j

/-- The global helical `W¹⁻∞` graph element, constructed
from the raw dominated limits rather than an invalid graph-norm series. -/
def parameterizedHelicalGlobalW1Inf : TransverseRealW1Inf := by
  refine ⟨(parameterizedHelicalGlobalValueLInf h P angularSpeed axialSpeed,
    parameterizedHelicalGlobalGradientLInf h P angularSpeed axialSpeed), ?_⟩
  rw [mem_transverseW1InfSubmodule_iff]
  intro j frequency i
  exact parameterizedHelicalGlobal_hasFourierWeakDerivative
    h P angularSpeed axialSpeed j frequency i

end Helical

/-! ## The summable axial global graph -/

section Axial

variable {supportRadius : ℝ}
variable (P : TorusCellPlacement (r := r) supportRadius)
variable {tau : ℝ} (htau : 0 ≤ tau)

/-- The axial cell values are absolutely summable in `L∞`, their norms being dominated by the
summable axial amplitudes `a_n`. -/
theorem summable_axialGlobalValueLInf :
    Summable (fun n : ℕ ↦ valueLInf P htau n) :=
  P.scaleFamily.summable_of_norm_le_axialAmplitude tau
    (fun n : ℕ ↦ valueLInf P htau n) 1 (fun n ↦ by
      simpa using norm_valueLInf_le P htau n)

/-- The axial cell derivatives are absolutely summable in `L∞`, their norms being dominated by the
summable axial gradient scales `a_n / R_n`. -/
theorem summable_axialGlobalDerivativeLInf (j : Fin 2) :
    Summable (fun n : ℕ ↦ derivativeLInf P htau n j) :=
  P.scaleFamily.summable_of_norm_le_axialGradientScale tau
    (fun n : ℕ ↦ derivativeLInf P htau n j)
      (axialPlateauLipschitzConstant : ℝ) (fun n ↦
        norm_derivativeLInf_le P htau n j)

/-- The global axial value as an absolutely convergent `L∞` series. -/
def axialGlobalValueLInf : TransverseR3LInf :=
  ∑' n : ℕ, valueLInf P htau n

/-- One global axial derivative as an absolutely convergent `L∞` series. -/
def axialGlobalDerivativeLInf (j : Fin 2) : TransverseR3LInf :=
  ∑' n : ℕ, derivativeLInf P htau n j

/-- The `L∞` sum of the axial cell values is represented a.e. by the pointwise disjoint-support
sum `axialOffsetGlobalTorus`. -/
theorem axialGlobalValueLInf_coe_ae :
    (axialGlobalValueLInf P htau : TransverseTorus → R3)
      =ᵐ[transverseMeasure] P.axialOffsetGlobalTorus tau := by
  have hnorm : Summable (fun n : ℕ ↦ ‖valueLInf P htau n‖) :=
    (P.scaleFamily.summable_axialAmplitude tau).of_nonneg_of_le
      (fun n ↦ norm_nonneg _) (fun n ↦ norm_valueLInf_le P htau n)
  have henorm : ∑' n : ℕ, ‖valueLInf P htau n‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hnorm
  have hcoe := Lp.coeFn_tsum henorm
  have hcell : ∀ᵐ q ∂transverseMeasure, ∀ n : ℕ,
      (valueLInf P htau n : TransverseTorus → R3) q =
        P.axialOffsetTorus tau n q :=
    ae_all_iff.mpr (fun n ↦ valueLInf_coe_ae P htau n)
  filter_upwards [hcoe, hcell] with q hsum hq
  change (((∑' n : ℕ, valueLInf P htau n) : TransverseR3LInf) :
      TransverseTorus → R3) q = _
  rw [hsum]
  unfold axialOffsetGlobalTorus
  exact tsum_congr fun n ↦ hq n

/-- The `L∞` sum of the axial cell derivatives is represented a.e. by the pointwise
disjoint-support sum `axialOffsetGlobalTorusDerivative`. -/
theorem axialGlobalDerivativeLInf_coe_ae (j : Fin 2) :
    (axialGlobalDerivativeLInf P htau j : TransverseTorus → R3)
      =ᵐ[transverseMeasure]
        P.axialOffsetGlobalTorusDerivative tau j := by
  have hnorm : Summable
      (fun n : ℕ ↦ ‖derivativeLInf P htau n j‖) :=
    ((P.scaleFamily.summable_axialGradientScale tau).mul_left
      (axialPlateauLipschitzConstant : ℝ)).of_nonneg_of_le
        (fun n ↦ norm_nonneg _)
        (fun n ↦ norm_derivativeLInf_le P htau n j)
  have henorm : ∑' n : ℕ, ‖derivativeLInf P htau n j‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hnorm
  have hcoe := Lp.coeFn_tsum henorm
  have hcell : ∀ᵐ q ∂transverseMeasure, ∀ n : ℕ,
      (derivativeLInf P htau n j : TransverseTorus → R3) q =
        P.axialOffsetTorusDerivative tau n j q :=
    ae_all_iff.mpr (fun n ↦ derivativeLInf_coe_ae P htau n j)
  filter_upwards [hcoe, hcell] with q hsum hq
  change (((∑' n : ℕ, derivativeLInf P htau n j) :
      TransverseR3LInf) : TransverseTorus → R3) q = _
  rw [hsum]
  unfold axialOffsetGlobalTorusDerivative
  exact tsum_congr fun n ↦ hq n

/-- The summed axial derivative field is the Fourier weak derivative of the summed axial
value: the coefficient functional is continuous, so it may be exchanged with the absolutely
convergent `L∞` series and applied to each cell's identity. -/
theorem axialGlobal_hasFourierWeakDerivative (j : Fin 2) :
    HasTransverseFourierDerivative j
      (complexifyR3LTwo (axialGlobalValueLInf P htau))
      (complexifyR3LTwo (axialGlobalDerivativeLInf P htau j)) := by
  intro frequency i
  let multiplier : ℂ :=
    2 * Real.pi * Complex.I * (frequency j : ℂ)
  change transverseRealCoeffCLM frequency i
      (axialGlobalDerivativeLInf P htau j) =
    multiplier * transverseRealCoeffCLM frequency i
      (axialGlobalValueLInf P htau)
  calc
    transverseRealCoeffCLM frequency i
        (axialGlobalDerivativeLInf P htau j) =
        ∑' n : ℕ, transverseRealCoeffCLM frequency i
          (derivativeLInf P htau n j) :=
      (transverseRealCoeffCLM frequency i).map_tsum
        (summable_axialGlobalDerivativeLInf P htau j)
    _ = ∑' n : ℕ, multiplier *
          transverseRealCoeffCLM frequency i (valueLInf P htau n) := by
      apply tsum_congr
      intro n
      change transverseCoeffCLM frequency i
          (complexifyR3LTwo (derivativeLInf P htau n j)) =
        multiplier * transverseCoeffCLM frequency i
          (complexifyR3LTwo (valueLInf P htau n))
      simpa only [multiplier] using
        hasFourierWeakDerivative P htau n j frequency i
    _ = multiplier * ∑' n : ℕ,
          transverseRealCoeffCLM frequency i (valueLInf P htau n) := by
      rw [tsum_mul_left]
    _ = multiplier * transverseRealCoeffCLM frequency i
          (axialGlobalValueLInf P htau) := by
      change multiplier * ∑' n : ℕ,
          transverseRealCoeffCLM frequency i (valueLInf P htau n) =
        multiplier * transverseRealCoeffCLM frequency i
          (∑' n : ℕ, valueLInf P htau n)
      rw [(transverseRealCoeffCLM frequency i).map_tsum
        (summable_axialGlobalValueLInf P htau)]

/-- The two bundled derivatives of the summed global axial field. -/
def axialGlobalGradientLInf : TransverseR3GradientLInf :=
  toLp ∞ fun j ↦ axialGlobalDerivativeLInf P htau j

/-- The global axial Fourier graph element. -/
def axialGlobalW1Inf : TransverseRealW1Inf := by
  refine ⟨(axialGlobalValueLInf P htau,
    axialGlobalGradientLInf P htau), ?_⟩
  rw [mem_transverseW1InfSubmodule_iff]
  intro j frequency i
  exact axialGlobal_hasFourierWeakDerivative P htau j frequency i

end Axial

/-! ## The single full global velocity -/

section Full

variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ) (htau : 0 ≤ tau)

/-- Literal complex representative of the full global value. -/
def parameterizedFullGlobalTorusSource (q : TransverseTorus) : C3 :=
  parameterizedHelicalGlobalTorusSource h P angularSpeed axialSpeed q +
    complexifyR3 (P.axialOffsetGlobalTorus tau q)

/-- Literal complex representative of one full global derivative. -/
def parameterizedFullGlobalTorusFirstDerivative
    (j : Fin 2) (q : TransverseTorus) : C3 :=
  parameterizedHelicalGlobalTorusFirstDerivative
      h P angularSpeed axialSpeed j q +
    complexifyR3 (P.axialOffsetGlobalTorusDerivative tau j q)

/-- The single global graph velocity.  The helical summand was constructed
by dominated coefficient limits; the axial summand by absolutely summable
cell coefficients. -/
def parameterizedFullGlobalW1Inf : TransverseRealW1Inf :=
  parameterizedHelicalGlobalW1Inf h P angularSpeed axialSpeed +
    axialGlobalW1Inf P htau

/-- The value of the full global velocity is represented a.e. by the pointwise sum of the helical
series and the added axial series, matching the paper's global formula `eq:global-u`. -/
theorem transverseW1InfValue_parameterizedFullGlobalW1Inf_coe_ae :
    (transverseW1InfValue (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau) : TransverseTorus → R3)
      =ᵐ[transverseMeasure] fun q ↦
        parameterizedHelicalGlobalRealTorusSource
            h P angularSpeed axialSpeed q +
          P.axialOffsetGlobalTorus tau q := by
  change (((parameterizedHelicalGlobalValueLInf
      h P angularSpeed axialSpeed) + axialGlobalValueLInf P htau :
        TransverseR3LInf) : TransverseTorus → R3) =ᵐ[transverseMeasure] _
  filter_upwards [Lp.coeFn_add
      (parameterizedHelicalGlobalValueLInf h P angularSpeed axialSpeed)
      (axialGlobalValueLInf P htau),
    parameterizedHelicalGlobalValueLInf_coe_ae
      h P angularSpeed axialSpeed,
    axialGlobalValueLInf_coe_ae P htau] with q hadd hhel hax
  rw [hadd]
  change ((parameterizedHelicalGlobalValueLInf
      h P angularSpeed axialSpeed : TransverseTorus → R3) q) +
    ((axialGlobalValueLInf P htau : TransverseTorus → R3) q) = _
  rw [hhel, hax]

/-- Each derivative of the full global velocity is represented a.e. by the pointwise sum of the
helical and axial displayed derivatives. -/
theorem transverseW1InfDeriv_parameterizedFullGlobalW1Inf_coe_ae
    (j : Fin 2) :
    (transverseW1InfDeriv j (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau) : TransverseTorus → R3)
      =ᵐ[transverseMeasure] fun q ↦
        parameterizedHelicalGlobalRealTorusFirstDerivative
            h P angularSpeed axialSpeed j q +
          P.axialOffsetGlobalTorusDerivative tau j q := by
  change (((parameterizedHelicalGlobalDerivativeLInf
      h P angularSpeed axialSpeed j) + axialGlobalDerivativeLInf P htau j :
        TransverseR3LInf) : TransverseTorus → R3) =ᵐ[transverseMeasure] _
  filter_upwards [Lp.coeFn_add
      (parameterizedHelicalGlobalDerivativeLInf
        h P angularSpeed axialSpeed j)
      (axialGlobalDerivativeLInf P htau j),
    parameterizedHelicalGlobalDerivativeLInf_coe_ae
      h P angularSpeed axialSpeed j,
    axialGlobalDerivativeLInf_coe_ae P htau j] with q hadd hhel hax
  rw [hadd]
  change ((parameterizedHelicalGlobalDerivativeLInf
      h P angularSpeed axialSpeed j : TransverseTorus → R3) q) +
    ((axialGlobalDerivativeLInf P htau j : TransverseTorus → R3) q) = _
  rw [hhel, hax]

/-- The complexified value of the full global velocity is represented a.e. by the pointwise
complex field `parameterizedFullGlobalTorusSource`. -/
theorem transverseW1InfComplexValue_parameterizedFullGlobalW1Inf_coe_ae :
    (transverseW1InfComplexValueLInf (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau) : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        parameterizedFullGlobalTorusSource
          h P angularSpeed axialSpeed tau := by
  filter_upwards [transverseW1InfComplexValueLInf_coe_ae
      (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau),
    transverseW1InfValue_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau] with q hcomplex hvalue
  rw [hcomplex, hvalue, map_add,
    complexify_parameterizedHelicalGlobalRealTorusSource]
  rfl

/-- The complexified `j`-th derivative of the full global velocity is represented a.e. by the
pointwise complex field `parameterizedFullGlobalTorusFirstDerivative`. -/
theorem transverseW1InfComplexDeriv_parameterizedFullGlobalW1Inf_coe_ae
    (j : Fin 2) :
    (transverseW1InfComplexDerivLInf j (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau) : TransverseTorus → C3)
      =ᵐ[transverseMeasure]
        parameterizedFullGlobalTorusFirstDerivative
          h P angularSpeed axialSpeed tau j := by
  filter_upwards [transverseW1InfComplexDerivLInf_coe_ae j
      (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau),
    transverseW1InfDeriv_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau j] with q hcomplex hderiv
  rw [hcomplex, hderiv, map_add,
    complexify_parameterizedHelicalGlobalRealTorusFirstDerivative]
  rfl

/-- The full global velocity is pointwise real: every component of its complex representative has
vanishing imaginary part. -/
theorem parameterizedFullGlobalTorusSource_pointwiseReal
    (q : TransverseTorus) (i : Fin 3) :
    (parameterizedFullGlobalTorusSource
      h P angularSpeed axialSpeed tau q i).im = 0 := by
  simp [parameterizedFullGlobalTorusSource, complexifyR3_apply,
    parameterizedHelicalGlobalTorusSource_pointwiseReal]

/-- The full global velocity is pointwise transversally divergence free,
`∂_1 u_1 + ∂_2 u_2 = 0`: both the helical cells and the added axial fields have this property
separately. -/
theorem parameterizedFullGlobalTorusFirstDerivative_transverseDivergence
    (q : TransverseTorus) :
    parameterizedFullGlobalTorusFirstDerivative
          h P angularSpeed axialSpeed tau 0 q 0 +
      parameterizedFullGlobalTorusFirstDerivative
          h P angularSpeed axialSpeed tau 1 q 1 = 0 := by
  change
    (parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed 0 q 0 +
      ((P.axialOffsetGlobalTorusDerivative tau 0 q 0 : ℝ) : ℂ)) +
    (parameterizedHelicalGlobalTorusFirstDerivative
        h P angularSpeed axialSpeed 1 q 1 +
      ((P.axialOffsetGlobalTorusDerivative tau 1 q 1 : ℝ) : ℂ)) = 0
  rw [add_add_add_comm,
    parameterizedHelicalGlobalTorusFirstDerivative_transverseDivergence]
  simp only [zero_add]
  rw [← Complex.ofReal_add,
    P.axialOffsetGlobalTorusDerivative_transverseDivergence tau q]
  rfl

/-- The full global velocity is divergence-free in the quotient `W¹⁻∞`
graph sense. -/
theorem parameterizedFullGlobalW1Inf_isTransverseDivergenceFree :
    IsTransverseDivergenceFree (parameterizedFullGlobalW1Inf
      h P angularSpeed axialSpeed tau htau) := by
  unfold IsTransverseDivergenceFree
  apply Lp.ext
  let d0 : TransverseScalarLInf :=
    transverseW1InfComplexDerivCoordLInf 0 0
      (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau)
  let d1 : TransverseScalarLInf :=
    transverseW1InfComplexDerivCoordLInf 1 1
      (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau)
  have hfull0 :=
    transverseW1InfComplexDeriv_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau 0
  have hfull1 :=
    transverseW1InfComplexDeriv_parameterizedFullGlobalW1Inf_coe_ae
      h P angularSpeed axialSpeed tau htau 1
  have hproj0 := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3)).coeFn_compLpL
    (transverseW1InfComplexDerivLInf 0
      (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau))
  have hproj1 := (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3)).coeFn_compLpL
    (transverseW1InfComplexDerivLInf 1
      (parameterizedFullGlobalW1Inf
        h P angularSpeed axialSpeed tau htau))
  have hadd := Lp.coeFn_add d0 d1
  have hzero := Lp.coeFn_zero ℂ ∞ transverseMeasure
  filter_upwards [hfull0, hfull1, hproj0, hproj1, hadd, hzero]
    with q hf0 hf1 hp0 hp1 haddq hzeroq
  change ((d0 + d1 : TransverseScalarLInf) q) =
    ((0 : TransverseScalarLInf) q)
  rw [haddq, hzeroq]
  change d0 q + d1 q = 0
  have hp0' : d0 q =
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 3))
        ((transverseW1InfComplexDerivLInf 0
          (parameterizedFullGlobalW1Inf
            h P angularSpeed axialSpeed tau htau) :
              TransverseTorus → C3) q) := by
    simpa only [d0, transverseW1InfComplexDerivCoordLInf_apply,
      transverseCoordLInf] using hp0
  have hp1' : d1 q =
      (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 3))
        ((transverseW1InfComplexDerivLInf 1
          (parameterizedFullGlobalW1Inf
            h P angularSpeed axialSpeed tau htau) :
              TransverseTorus → C3) q) := by
    simpa only [d1, transverseW1InfComplexDerivCoordLInf_apply,
      transverseCoordLInf] using hp1
  rw [hp0', hp1', hf0, hf1]
  exact parameterizedFullGlobalTorusFirstDerivative_transverseDivergence
    h P angularSpeed axialSpeed tau q

/-- On the local-flow core, the full global field is exactly the helical
cell value plus the paper's constant axial shift. -/
theorem parameterizedFullGlobalTorusSource_eq_cell_add_axialShift_of_mem_core
    (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    parameterizedFullGlobalTorusSource h P angularSpeed axialSpeed tau
        (transverseTorusPoint x) =
      (parameterizedHelicalEuclideanCellCertificate
          h P angularSpeed axialSpeed n).torusSource
            (transverseTorusPoint x) +
        complexifyR3
          (P.scaleFamily.axialAmplitude tau n • axialUnitR3) := by
  have hbuffer : x ∈ P.scaleFamily.bufferDisk n :=
    P.scaleFamily.localCoreDisk_subset_bufferDisk P.supportFit n hx
  have hq : transverseTorusPoint x ∈ P.torusBufferDisk n :=
    ⟨x, hbuffer, rfl⟩
  have hplateau : pairEuclideanDist x (P.scaleFamily.cellCenter n) ≤
      3 * P.scaleFamily.bufferRadius n / 4 := by
    have hcore : dist x (P.scaleFamily.cellCenter n) <
        (1 + (h : ℝ)) * P.scaleFamily.ell n := hx
    have hfit := P.supportFit n
    have hcmp :=
      pairEuclideanDist_le_two_mul_dist x (P.scaleFamily.cellCenter n)
    linarith [P.scaleFamily.bufferRadius_pos n]
  rw [parameterizedFullGlobalTorusSource,
    parameterizedHelicalGlobalTorusSource_eq_cell_of_mem_buffer
      h P angularSpeed axialSpeed hq,
    P.axialOffsetGlobalTorus_eq_cell_of_mem_buffer tau hq,
    P.axialOffsetTorus_eq_axialAmplitude_of_core tau n hplateau]

end Full

end FullVelocityConcrete

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
