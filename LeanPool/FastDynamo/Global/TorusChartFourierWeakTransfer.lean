/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusChartWeakTransfer
public import LeanPool.FastDynamo.Global.CellSeriesSummability

/-!
# Fourier weak derivatives for quotient-periodized cell sources

This module proves the Fourier weak-derivative identity isolated in `TorusChartWeakTransfer`.
It computes torus Fourier coefficients on the canonical `(0,1]²`
fundamental domain and applies Euclidean integration by parts to the
compactly supported source.  No quotient differentiability or integration-
by-parts hypothesis is added to the source certificate.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped ENNReal Topology

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}
variable {P : TorusCellPlacement (r := r) supportRadius} {n : ℕ}

namespace EuclideanCellSourceCertificate

/-! ## Euclidean representatives of torus monomials -/

/-- The linear identification from `Fin 2 → ℝ` to pair coordinates. -/
def finTwoToPair : (Fin 2 → ℝ) →L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2))
    (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2))

/-- The linear identification `Fin 2 → ℝ ≃ ℝ × ℝ` evaluates to the pair of coordinates,
`finTwoToPair x = (x 0, x 1)`. -/
@[simp] theorem finTwoToPair_apply (x : Fin 2 → ℝ) :
    finTwoToPair x = (x 0, x 1) :=
  rfl

/-- The identification carries the `j`-th standard basis vector of `Fin 2 → ℝ` to the `j`-th
vector of `pairBasis`. -/
theorem finTwoToPair_single (j : Fin 2) :
    finTwoToPair (Pi.single j (1 : ℝ)) = pairBasis j := by
  fin_cases j <;> ext <;> simp [finTwoToPair, pairBasis]

/-- Pull a torus Fourier monomial back to the Euclidean covering space. -/
def euclideanMonomial (frequency : TransverseFrequency)
    (x : Fin 2 → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
      (frequency 0 : ℂ) * (x 0 : ℂ)) *
    Complex.exp (2 * Real.pi * Complex.I *
      (frequency 1 : ℂ) * (x 1 : ℂ))

/-- The explicit exponential is exactly Mathlib's torus monomial on the
quotient image of the Euclidean point. -/
theorem euclideanMonomial_eq_mFourier
    (frequency : TransverseFrequency) (x : Fin 2 → ℝ) :
    euclideanMonomial frequency x =
      UnitAddTorus.mFourier frequency
        (fun k ↦ (x k : UnitAddCircle)) := by
  simp only [euclideanMonomial, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, Fin.prod_univ_two, fourier_coe_apply]
  congr 1 <;> norm_num

/-- A pulled-back torus Fourier monomial is unimodular: `‖e^{2πi m·x}‖ = 1` at every point of the
covering plane. -/
@[simp] theorem norm_euclideanMonomial
    (frequency : TransverseFrequency) (x : Fin 2 → ℝ) :
    ‖euclideanMonomial frequency x‖ = 1 := by
  simp [euclideanMonomial, Complex.norm_exp, Complex.mul_re]

/-- The Euclidean pullback of a monomial has the expected coordinate line
derivative. -/
theorem euclideanMonomial_hasLineDerivAt
    (frequency : TransverseFrequency) (j : Fin 2) (x : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (euclideanMonomial frequency)
      ((2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        euclideanMonomial frequency x)
      x (Pi.single j (1 : ℝ)) := by
  fin_cases j
  · unfold HasLineDerivAt
    have hadd : HasDerivAt (fun t : ℝ ↦ x 0 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
    have hbase : HasDerivAt (fun y : ℝ ↦
        fourier (frequency 0) (y : UnitAddCircle))
        (2 * Real.pi * Complex.I * (frequency 0 : ℂ) / (1 : ℂ) *
          fourier (frequency 0) (x 0 : UnitAddCircle)) (x 0 + 0) := by
      simpa using hasDerivAt_fourier (1 : ℝ) (frequency 0) (x 0)
    have hcomp := hbase.scomp (0 : ℝ) hadd
    have hzero : HasDerivAt
        (fun t : ℝ ↦ Complex.exp
          (2 * Real.pi * Complex.I * (frequency 0 : ℂ) *
            ((x 0 : ℂ) + (t : ℂ))))
        ((2 * Real.pi * Complex.I * (frequency 0 : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I *
            (frequency 0 : ℂ) * (x 0 : ℂ))) 0 := by
      simpa [Function.comp_def, fourier_coe_apply] using hcomp
    have hmul := hzero.mul_const
      (Complex.exp (2 * Real.pi * Complex.I *
        (frequency 1 : ℂ) * (x 1 : ℂ)))
    have hderiv :
        (2 * Real.pi * Complex.I * (frequency 0 : ℂ)) *
            euclideanMonomial frequency x =
          (2 * Real.pi * Complex.I * (frequency 0 : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I *
                (frequency 0 : ℂ) * (x 0 : ℂ))) *
            Complex.exp (2 * Real.pi * Complex.I *
              (frequency 1 : ℂ) * (x 1 : ℂ)) := by
      rw [euclideanMonomial]
      ring
    have hmul' := hmul.congr_deriv (by simpa using hderiv.symm)
    simpa [euclideanMonomial] using hmul'
  · unfold HasLineDerivAt
    have hadd : HasDerivAt (fun t : ℝ ↦ x 1 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 1)
    have hbase : HasDerivAt (fun y : ℝ ↦
        fourier (frequency 1) (y : UnitAddCircle))
        (2 * Real.pi * Complex.I * (frequency 1 : ℂ) / (1 : ℂ) *
          fourier (frequency 1) (x 1 : UnitAddCircle)) (x 1 + 0) := by
      simpa using hasDerivAt_fourier (1 : ℝ) (frequency 1) (x 1)
    have hcomp := hbase.scomp (0 : ℝ) hadd
    have hone : HasDerivAt
        (fun t : ℝ ↦ Complex.exp
          (2 * Real.pi * Complex.I * (frequency 1 : ℂ) *
            ((x 1 : ℂ) + (t : ℂ))))
        ((2 * Real.pi * Complex.I * (frequency 1 : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I *
            (frequency 1 : ℂ) * (x 1 : ℂ))) 0 := by
      simpa [Function.comp_def, fourier_coe_apply] using hcomp
    have hmul :=
      (hasDerivAt_const (x := (0 : ℝ))
        (Complex.exp (2 * Real.pi * Complex.I *
          (frequency 0 : ℂ) * (x 0 : ℂ)))).mul hone
    have hderiv :
        (2 * Real.pi * Complex.I * (frequency 1 : ℂ)) *
            euclideanMonomial frequency x =
          Complex.exp (2 * Real.pi * Complex.I *
              (frequency 0 : ℂ) * (x 0 : ℂ)) *
            (2 * Real.pi * Complex.I * (frequency 1 : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I *
                (frequency 1 : ℂ) * (x 1 : ℂ))) := by
      rw [euclideanMonomial]
      ring
    have hmul' := hmul.congr_deriv (by simpa using hderiv.symm)
    have htarget : HasDerivAt
        (fun t : ℝ ↦
          Complex.exp (2 * Real.pi * Complex.I *
              (frequency 0 : ℂ) * (x 0 : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I *
              (frequency 1 : ℂ) * ((x 1 : ℂ) + (t : ℂ))))
        ((2 * Real.pi * Complex.I * (frequency 1 : ℂ)) *
          euclideanMonomial frequency x) 0 := by
      exact hmul'.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ ↦ rfl)
    simpa [euclideanMonomial] using htarget

/-! ## Scalar source coordinates on `ℝ²` -/

/-- One complex coordinate of the Euclidean source, written on `Fin 2 → ℝ`
to match Mathlib's product fundamental-domain formula. -/
def euclideanSourceCoord (C : EuclideanCellSourceCertificate P n)
    (i : Fin 3) (x : Fin 2 → ℝ) : ℂ :=
  C.source (finTwoToPair x) i

/-- The corresponding stored coordinate derivative on `Fin 2 → ℝ`. -/
def euclideanFirstDerivativeCoord
    (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) (i : Fin 3) (x : Fin 2 → ℝ) : ℂ :=
  C.firstDerivative j (finTwoToPair x) i

/-- The source coordinate has the displayed coordinate derivative as its
Euclidean line derivative. -/
theorem euclideanSourceCoord_hasLineDerivAt
    (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) (i : Fin 3) (x : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (C.euclideanSourceCoord i)
      (C.euclideanFirstDerivativeCoord j i x) x
      (Pi.single j (1 : ℝ)) := by
  let projR : C3 →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  have hsource := (C.source_hasFDerivAt (finTwoToPair x)).comp x
    finTwoToPair.hasFDerivAt
  have hcoord := projR.hasFDerivAt.comp x hsource
  have hline := hcoord.hasLineDerivAt (Pi.single j (1 : ℝ))
  have hfun : C.euclideanSourceCoord i =
      projR ∘ C.source ∘ finTwoToPair := by
    funext y
    rfl
  rw [hfun]
  apply hline.congr_deriv
  change (C.sourceFDeriv (finTwoToPair x)
      (finTwoToPair (Pi.single j (1 : ℝ)))) i =
    C.euclideanFirstDerivativeCoord j i x
  rw [finTwoToPair_single, C.sourceFDeriv_apply_pairBasis]
  rfl

/-- Source coordinates are continuous. -/
theorem continuous_euclideanSourceCoord
    (C : EuclideanCellSourceCertificate P n) (i : Fin 3) :
    Continuous (C.euclideanSourceCoord i) := by
  have hsource : Continuous C.source :=
    continuous_iff_continuousAt.2 fun x ↦ (C.source_hasFDerivAt x).continuousAt
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp
    (hsource.comp finTwoToPair.continuous)

/-- Stored derivative coordinates are measurable. -/
theorem measurable_euclideanFirstDerivativeCoord
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) (i : Fin 3) :
    Measurable (C.euclideanFirstDerivativeCoord j i) := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).measurable.comp
    ((C.measurable_firstDerivative j).comp finTwoToPair.measurable)

/-- The canonical closed unit square in `Fin 2 → ℝ` coordinates. -/
def closedFundamentalBox : Set (Fin 2 → ℝ) :=
  {x | ∀ k, x k ∈ Set.Icc (0 : ℝ) (0 + 1)}

/-- The half-open fundamental domain used by `UnitAddTorus.integral_preimage`. -/
def iocFundamentalBox : Set (Fin 2 → ℝ) :=
  {x | ∀ k, x k ∈ Set.Ioc (0 : ℝ) (0 + 1)}

/-- The closed unit box `[0,1]²` in `Fin 2 → ℝ` coordinates is compact. -/
theorem isCompact_closedFundamentalBox :
    IsCompact (closedFundamentalBox : Set (Fin 2 → ℝ)) := by
  have hbox : closedFundamentalBox =
      Set.Icc (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ (0 + 1 : ℝ)) := by
    ext x
    simp [closedFundamentalBox, Set.mem_Icc, Pi.le_def, forall_and]
  rw [hbox]
  exact isCompact_Icc

/-- The half-open fundamental domain `(0,1]²` is contained in the closed unit box. -/
theorem iocFundamentalBox_subset_closedFundamentalBox :
    iocFundamentalBox ⊆ closedFundamentalBox := by
  intro x hx k
  exact Set.Ioc_subset_Icc_self (hx k)

/-- Nonzero source coordinates occur strictly inside the canonical
fundamental box. -/
theorem support_euclideanSourceCoord_subset_iocFundamentalBox
    (C : EuclideanCellSourceCertificate P n) (i : Fin 3) :
    Function.support (C.euclideanSourceCoord i) ⊆ iocFundamentalBox := by
  intro x hx
  have hsource : C.source (finTwoToPair x) ≠ 0 := by
    intro hzero
    apply hx
    exact congrArg (fun v : C3 ↦ v i) hzero
  have hcore := C.source_support hsource
  have hchart := P.bufferDisk_subset_chart n
    (P.localCoreDisk_subset_bufferDisk n hcore)
  rw [ScaleFamily.placementChart, Set.mem_prod, finTwoToPair_apply] at hchart
  have hx0lo : 0 < x 0 := by simpa using hchart.1.1
  have hx0hi : x 0 < 1 / 4 := by simpa using hchart.1.2
  have hx1lo : 1 / 4 < x 1 := by simpa using hchart.2.1
  have hx1hi : x 1 < 3 / 4 := by simpa using hchart.2.2
  intro k
  fin_cases k
  · change x 0 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨hx0lo, by linarith⟩
  · change x 1 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨by linarith, by linarith⟩

/-- Nonzero stored derivative coordinates have the same strict support. -/
theorem support_euclideanFirstDerivativeCoord_subset_iocFundamentalBox
    (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) (i : Fin 3) :
    Function.support (C.euclideanFirstDerivativeCoord j i) ⊆
      iocFundamentalBox := by
  intro x hx
  have hderiv : C.firstDerivative j (finTwoToPair x) ≠ 0 := by
    intro hzero
    apply hx
    exact congrArg (fun v : C3 ↦ v i) hzero
  have hcore := C.firstDerivative_support j hderiv
  have hchart := P.bufferDisk_subset_chart n
    (P.localCoreDisk_subset_bufferDisk n hcore)
  rw [ScaleFamily.placementChart, Set.mem_prod, finTwoToPair_apply] at hchart
  have hx0lo : 0 < x 0 := by simpa using hchart.1.1
  have hx0hi : x 0 < 1 / 4 := by simpa using hchart.1.2
  have hx1lo : 1 / 4 < x 1 := by simpa using hchart.2.1
  have hx1hi : x 1 < 3 / 4 := by simpa using hchart.2.2
  intro k
  fin_cases k
  · change x 0 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨hx0lo, by linarith⟩
  · change x 1 ∈ Set.Ioc (0 : ℝ) (0 + 1)
    exact ⟨by linarith, by linarith⟩

/-! ## Whole-plane integrability -/

/-- Pulled-back torus Fourier monomials are continuous on the covering plane. -/
theorem continuous_euclideanMonomial
    (frequency : TransverseFrequency) :
    Continuous (euclideanMonomial frequency) := by
  unfold euclideanMonomial
  fun_prop

/-- Each Euclidean source coordinate of a cell certificate is integrable on the plane, being
continuous with support in the compact fundamental box. -/
theorem integrable_euclideanSourceCoord
    (C : EuclideanCellSourceCertificate P n) (i : Fin 3) :
    Integrable (C.euclideanSourceCoord i) := by
  apply C.continuous_euclideanSourceCoord i |>.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    isCompact_closedFundamentalBox
  exact (C.support_euclideanSourceCoord_subset_iocFundamentalBox i).trans
    iocFundamentalBox_subset_closedFundamentalBox

/-- Each stored Euclidean first-derivative coordinate is bounded by the certificate's
`firstDerivativeBound`, componentwise from the vector bound. -/
theorem norm_euclideanFirstDerivativeCoord_le
    (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) (i : Fin 3) (x : Fin 2 → ℝ) :
    ‖C.euclideanFirstDerivativeCoord j i x‖ ≤
      C.firstDerivativeBound := by
  exact (PiLp.norm_apply_le (C.firstDerivative j (finTwoToPair x)) i).trans
    (C.norm_firstDerivative_le j (finTwoToPair x))

/-- Each stored Euclidean first-derivative coordinate is integrable, from its uniform bound and
its support in the compact fundamental box. -/
theorem integrable_euclideanFirstDerivativeCoord
    (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) (i : Fin 3) :
    Integrable (C.euclideanFirstDerivativeCoord j i) := by
  have hfinite : volume (closedFundamentalBox : Set (Fin 2 → ℝ)) < ∞ :=
    isCompact_closedFundamentalBox.measure_lt_top
  have hon : IntegrableOn (C.euclideanFirstDerivativeCoord j i)
      closedFundamentalBox := by
    exact IntegrableOn.of_bound hfinite
      (C.measurable_euclideanFirstDerivativeCoord j i).aestronglyMeasurable.restrict
      C.firstDerivativeBound
      (Filter.Eventually.of_forall fun x ↦
        C.norm_euclideanFirstDerivativeCoord_le j i x)
  apply hon.integrable_of_forall_notMem_eq_zero
  intro x hx
  by_contra hne
  exact hx ((C.support_euclideanFirstDerivativeCoord_subset_iocFundamentalBox
    j i hne) |> iocFundamentalBox_subset_closedFundamentalBox)

/-- A Euclidean monomial is globally essentially bounded by one, even
though the covering space has infinite measure. -/
theorem euclideanMonomial_memLp_top
    (frequency : TransverseFrequency) :
    MemLp (euclideanMonomial frequency) ∞ :=
  memLp_top_of_bound
    (continuous_euclideanMonomial frequency).aestronglyMeasurable
    1 (Filter.Eventually.of_forall fun x ↦
      (norm_euclideanMonomial frequency x).le)

/-- Euclidean integration by parts against every pulled-back torus
monomial. -/
theorem integral_euclideanMonomial_mul_firstDerivativeCoord
    (C : EuclideanCellSourceCertificate P n)
    (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    (∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          C.euclideanFirstDerivativeCoord j i x) =
      (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
        ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x *
            C.euclideanSourceCoord i x := by
  let multiplier : ℂ :=
    2 * Real.pi * Complex.I * ((-frequency) j : ℂ)
  have hsource := C.integrable_euclideanSourceCoord i
  have hderiv := C.integrable_euclideanFirstDerivativeCoord j i
  have hmonomial := euclideanMonomial_memLp_top (-frequency)
  have hmono_source : Integrable (fun x : Fin 2 → ℝ ↦
      euclideanMonomial (-frequency) x * C.euclideanSourceCoord i x) :=
    hsource.mul_of_top_right hmonomial
  have hmono_deriv : Integrable (fun x : Fin 2 → ℝ ↦
      euclideanMonomial (-frequency) x *
        C.euclideanFirstDerivativeCoord j i x) :=
    hderiv.mul_of_top_right hmonomial
  have hderivMono : MemLp
      (fun x : Fin 2 → ℝ ↦ multiplier * euclideanMonomial (-frequency) x)
      ∞ := by
    exact hmonomial.const_mul multiplier
  have hderivMono_source : Integrable (fun x : Fin 2 → ℝ ↦
      (multiplier * euclideanMonomial (-frequency) x) *
        C.euclideanSourceCoord i x) :=
    hsource.mul_of_top_right hderivMono
  have hibp :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (E := Fin 2 → ℝ) (F := ℂ) (G := ℂ) (W := ℂ)
      (B := ContinuousLinearMap.mul ℝ ℂ)
      hderivMono_source hmono_deriv hmono_source
      (fun x _ ↦ by
        simpa [multiplier] using
          euclideanMonomial_hasLineDerivAt (-frequency) j x)
      (fun x _ ↦ C.euclideanSourceCoord_hasLineDerivAt j i x)
  change (∫ x : Fin 2 → ℝ,
      euclideanMonomial (-frequency) x *
        C.euclideanFirstDerivativeCoord j i x) = _ at hibp
  calc
    (∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          C.euclideanFirstDerivativeCoord j i x) =
        -∫ x : Fin 2 → ℝ,
          (multiplier * euclideanMonomial (-frequency) x) *
            C.euclideanSourceCoord i x := hibp
    _ = -multiplier * ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x *
            C.euclideanSourceCoord i x := by
      rw [← integral_neg, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          ∫ x : Fin 2 → ℝ,
            euclideanMonomial (-frequency) x *
              C.euclideanSourceCoord i x := by
      simp [multiplier]

/-! ## Exact fundamental-domain transfer -/

/-- The half-open fundamental domain `(0,1]²` is measurable, being a product of `Ioc`
intervals. -/
theorem measurableSet_iocFundamentalBox :
    MeasurableSet (iocFundamentalBox : Set (Fin 2 → ℝ)) := by
  have h := MeasurableSet.univ_pi'
    (fun _ : Fin 2 ↦ measurableSet_Ioc (a := (0 : ℝ)) (b := 0 + 1))
  simpa [iocFundamentalBox] using h

/-- Transfer of the value pairing from the torus to the covering plane: the torus integral of
`e^{-2πi m·q}` against a coordinate of the periodized source equals the corresponding Euclidean
integral, because `(0,1]²` is a fundamental domain and the source is supported in it. -/
theorem torusIntegral_mFourier_mul_sourceCoord_eq_euclidean
    (C : EuclideanCellSourceCertificate P n)
    (frequency : TransverseFrequency) (i : Fin 3) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * C.torusSource q i
          ∂transverseMeasure) =
      ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x * C.euclideanSourceCoord i x := by
  calc
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * C.torusSource q i
          ∂transverseMeasure) =
        ∫ x : Fin 2 → ℝ in iocFundamentalBox,
            UnitAddTorus.mFourier (-frequency)
              (fun k ↦ (x k : UnitAddCircle)) *
            C.torusSource (fun k ↦ (x k : UnitAddCircle)) i := by
      rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
        volume_unitAddTorus_eq_haar]
      have hpre := UnitAddTorus.integral_preimage
          (f := fun q : TransverseTorus ↦
            UnitAddTorus.mFourier (-frequency) q * C.torusSource q i)
          (fun _ : Fin 2 ↦ (0 : ℝ))
      change (∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q * C.torusSource q i
            ∂torusHaarMeasure (Fin 2)) = _ at hpre
      simpa [iocFundamentalBox] using hpre
    _ = ∫ x : Fin 2 → ℝ in iocFundamentalBox,
          euclideanMonomial (-frequency) x * C.euclideanSourceCoord i x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_iocFundamentalBox] with x hx
      have hx0 : (finTwoToPair x).1 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (0 : Fin 2)
      have hx1 : (finTwoToPair x).2 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (1 : Fin 2)
      have hq : (fun k ↦ (x k : UnitAddCircle)) =
          transverseTorusPoint (finTwoToPair x) := by
        funext k
        fin_cases k <;> simp
      rw [hq, C.torusSource_transverseTorusPoint_eq_source_of_mem_Ioc
        hx0 hx1]
      rw [euclideanMonomial_eq_mFourier]
      rfl
    _ = ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x * C.euclideanSourceCoord i x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hzero : C.euclideanSourceCoord i x = 0 := by
        by_contra hne
        exact hx (C.support_euclideanSourceCoord_subset_iocFundamentalBox i hne)
      rw [hzero, mul_zero]

/-- Transfer of the derivative pairing from the torus to the covering plane: the torus integral of
`e^{-2πi m·q}` against a coordinate of the periodized stored derivative equals the corresponding
Euclidean integral. -/
theorem torusIntegral_mFourier_mul_firstDerivativeCoord_eq_euclidean
    (C : EuclideanCellSourceCertificate P n)
    (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          C.torusFirstDerivative j q i ∂transverseMeasure) =
      ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          C.euclideanFirstDerivativeCoord j i x := by
  calc
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          C.torusFirstDerivative j q i ∂transverseMeasure) =
        ∫ x : Fin 2 → ℝ in iocFundamentalBox,
            UnitAddTorus.mFourier (-frequency)
              (fun k ↦ (x k : UnitAddCircle)) *
            C.torusFirstDerivative j
              (fun k ↦ (x k : UnitAddCircle)) i := by
      rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
        volume_unitAddTorus_eq_haar]
      have hpre := UnitAddTorus.integral_preimage
          (f := fun q : TransverseTorus ↦
            UnitAddTorus.mFourier (-frequency) q *
              C.torusFirstDerivative j q i)
          (fun _ : Fin 2 ↦ (0 : ℝ))
      change (∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q *
            C.torusFirstDerivative j q i
              ∂torusHaarMeasure (Fin 2)) = _ at hpre
      simpa [iocFundamentalBox] using hpre
    _ = ∫ x : Fin 2 → ℝ in iocFundamentalBox,
          euclideanMonomial (-frequency) x *
            C.euclideanFirstDerivativeCoord j i x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_iocFundamentalBox] with x hx
      have hx0 : (finTwoToPair x).1 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (0 : Fin 2)
      have hx1 : (finTwoToPair x).2 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        simpa using hx (1 : Fin 2)
      have hq : (fun k ↦ (x k : UnitAddCircle)) =
          transverseTorusPoint (finTwoToPair x) := by
        funext k
        fin_cases k <;> simp
      rw [hq,
        C.torusFirstDerivative_transverseTorusPoint_eq_firstDerivative_of_mem_Ioc
          j hx0 hx1]
      rw [euclideanMonomial_eq_mFourier]
      rfl
    _ = ∫ x : Fin 2 → ℝ,
          euclideanMonomial (-frequency) x *
            C.euclideanFirstDerivativeCoord j i x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hzero : C.euclideanFirstDerivativeCoord j i x = 0 := by
        by_contra hne
        exact hx
          (C.support_euclideanFirstDerivativeCoord_subset_iocFundamentalBox
            j i hne)
      rw [hzero, mul_zero]

/-! ## Fourier coefficients of the bundled fields -/

/-- The complexified `L∞` value class of a cell certificate is represented a.e. by the periodized
torus source. -/
theorem complexifyR3LTwo_transverseValueLInf_coe_ae
    (C : EuclideanCellSourceCertificate P n) :
    (complexifyR3LTwo C.transverseValueLInf : TransverseTorus → C3)
      =ᵐ[transverseMeasure] C.torusSource := by
  filter_upwards [complexifyR3LTwo_coe_ae C.transverseValueLInf,
    C.transverseValueLInf_coe_ae] with q hcomplex hvalue
  rw [hcomplex, hvalue]
  exact C.complexifyR3_realTorusSource q

/-- The complexified `L∞` class of the `j`-th stored derivative is represented a.e. by the
periodized torus derivative. -/
theorem complexifyR3LTwo_transverseFirstDerivativeLInf_coe_ae
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    (complexifyR3LTwo (C.transverseFirstDerivativeLInf j) :
        TransverseTorus → C3)
      =ᵐ[transverseMeasure] C.torusFirstDerivative j := by
  filter_upwards [
    complexifyR3LTwo_coe_ae (C.transverseFirstDerivativeLInf j),
    C.transverseFirstDerivativeLInf_coe_ae j] with q hcomplex hderiv
  rw [hcomplex, hderiv]
  exact C.complexifyR3_realTorusFirstDerivative j q

/-- The transverse Fourier coefficient of a coordinate of the complexified value equals the torus
integral of `e^{-2πi m·q}` against that coordinate of the periodized source. -/
theorem transverseCoeffCLM_complexify_value_eq_torusIntegral
    (C : EuclideanCellSourceCertificate P n)
    (frequency : TransverseFrequency) (i : Fin 3) :
    transverseCoeffCLM frequency i
        (complexifyR3LTwo C.transverseValueLInf) =
      ∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q * C.torusSource q i
          ∂transverseMeasure := by
  rw [← transverseMonomialComponentPairing_eq_coeff,
    transverseMonomialComponentPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae frequency,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (complexifyR3LTwo C.transverseValueLInf),
    C.complexifyR3LTwo_transverseValueLInf_coe_ae]
      with q hmono hcoord hvalue
  change ((transverseCoordL2 i
      (complexifyR3LTwo C.transverseValueLInf) : TransverseScalarL2) :
        TransverseTorus → ℂ) q = _ at hcoord
  rw [hmono, hcoord, hvalue]
  rw [← UnitAddTorus.mFourier_neg]
  rfl

/-- The transverse Fourier coefficient of a coordinate of the complexified `j`-th derivative
equals the torus integral of `e^{-2πi m·q}` against that coordinate of the periodized
derivative. -/
theorem transverseCoeffCLM_complexify_firstDerivative_eq_torusIntegral
    (C : EuclideanCellSourceCertificate P n)
    (frequency : TransverseFrequency) (j : Fin 2) (i : Fin 3) :
    transverseCoeffCLM frequency i
        (complexifyR3LTwo (C.transverseFirstDerivativeLInf j)) =
      ∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          C.torusFirstDerivative j q i ∂transverseMeasure := by
  rw [← transverseMonomialComponentPairing_eq_coeff,
    transverseMonomialComponentPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [transverseMonomialL2_coe_ae frequency,
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (complexifyR3LTwo (C.transverseFirstDerivativeLInf j)),
    C.complexifyR3LTwo_transverseFirstDerivativeLInf_coe_ae j]
      with q hmono hcoord hderiv
  change ((transverseCoordL2 i
      (complexifyR3LTwo (C.transverseFirstDerivativeLInf j)) :
        TransverseScalarL2) : TransverseTorus → ℂ) q = _ at hcoord
  rw [hmono, hcoord, hderiv]
  rw [← UnitAddTorus.mFourier_neg]
  rfl

/-! ## Weak transfer -/

/-- Every certified compactly supported Euclidean cell source satisfies the
Fourier weak-transfer condition required by the transverse `W¹⁻∞` graph. -/
theorem hasFourierWeakTransfer
    (C : EuclideanCellSourceCertificate P n) :
    C.HasFourierWeakTransfer := by
  intro j frequency i
  calc
    transverseCoeffCLM frequency i
        (complexifyR3LTwo (C.transverseFirstDerivativeLInf j)) =
        ∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q *
            C.torusFirstDerivative j q i ∂transverseMeasure :=
      C.transverseCoeffCLM_complexify_firstDerivative_eq_torusIntegral
        frequency j i
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
    _ = (2 * Real.pi * Complex.I * (frequency j : ℂ)) *
          transverseCoeffCLM frequency i
            (complexifyR3LTwo C.transverseValueLInf) := by
      rw [C.transverseCoeffCLM_complexify_value_eq_torusIntegral]

/-- The transverse real `W¹⁻∞` field associated to a
Euclidean source certificate. -/
def toTransverseRealW1InfConcrete
    (C : EuclideanCellSourceCertificate P n) : TransverseRealW1Inf :=
  C.toTransverseRealW1Inf C.hasFourierWeakTransfer

/-- The `W^{1,∞}` field built from a Euclidean cell source certificate is transversally
divergence free, inheriting the certificate's pointwise divergence cancellation. -/
theorem toTransverseRealW1InfConcrete_isTransverseDivergenceFree
    (C : EuclideanCellSourceCertificate P n) :
    IsTransverseDivergenceFree C.toTransverseRealW1InfConcrete :=
  C.toTransverseRealW1Inf_isTransverseDivergenceFree
    C.hasFourierWeakTransfer

end EuclideanCellSourceCertificate

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
