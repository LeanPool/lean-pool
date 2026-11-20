/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Fourier.AxialL2
public import LeanPool.FastDynamo.Operator.Domain
public import Mathlib.Analysis.Normed.Lp.lpHolder

/-!
# Fourier-graph periodic `H²`

Mathlib has no bundled periodic Sobolev space.  This file defines
the transverse vector-valued `H²` domain used by the paper as a closed graph
over physical `L²`.  An element consists of a physical field together with its
weighted scalar Fourier coefficients, subject to

`aᵢ(n) = (1 + 4π² |n|²) * b̂ᵢ(n)`.

The closed-graph realization is important: the subtype of `L²` fields merely
satisfying weighted summability would inherit the incomplete `L²` norm.  The
graph instead carries a complete norm and has an injective continuous
projection to physical `L²`.

For a fixed axial index, the lift is a continuous injective map from this
domain to product `L²`.  Fourier-defined axial derivatives are exact scalar
multipliers.  The product `H²` graph is constructed in
`FastDynamo/Fourier/ProductH2.lean`; identifying these maps with distributional
derivatives is not part of this module.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Integer Fourier frequencies on the transverse two-torus. -/
abbrev TransverseFrequency := Fin 2 → ℤ

/-- Scalar physical `L²` on the transverse torus. -/
abbrev TransverseScalarL2 := Lp ℂ 2 transverseMeasure

/-- Square-summable scalar arrays indexed by transverse frequencies. -/
abbrev TransverseScalarFourierL2 :=
  lp (fun _ : TransverseFrequency ↦ ℂ) 2

/-- Two-dimensional complex Euclidean space: the fibre of a horizontal torus field. -/
abbrev C2 := EuclideanSpace ℂ (Fin 2)

/--
Physical `L²` on the transverse torus with values in the complex Euclidean space `ℂ^ι`.

The fibre index `ι` is a parameter of the whole torus Sobolev layer: `ι = Fin 3` is the
three-component model used by the reduced induction operator, `ι = Fin 2` the horizontal
model of the paper.  `TransverseC3L2` (`FastDynamo/Fourier/AxialL2.lean`)
is definitionally `TransverseVecL2 (Fin 3)`.
-/
abbrev TransverseVecL2 (ι : Type*) [Fintype ι] :=
  Lp (EuclideanSpace ℂ ι) 2 transverseMeasure

/-- Weighted coefficient arrays for a fibre indexed by `ι`. -/
abbrev WeightedTransverseCoeffs (ι : Type*) :=
  PiLp 2 (fun _ : ι ↦ TransverseScalarFourierL2)

/-- Transverse physical `L²` with a two-component fibre. -/
abbrev TransverseC2L2 := TransverseVecL2 (Fin 2)

/-- Weighted coefficient arrays for three complex components. -/
abbrev WeightedTransverseC3Coeffs := WeightedTransverseCoeffs (Fin 3)

/-- Weighted coefficient arrays for two complex components. -/
abbrev WeightedTransverseC2Coeffs := WeightedTransverseCoeffs (Fin 2)

variable {ι : Type*} [Fintype ι]

/--
The inhomogeneous Bessel-potential weight used for `H²` on the normalized unit
two-torus.  The graph stores this weight times each Fourier coefficient.  A
later comparison theorem will identify the resulting graph norm with a
distributional periodic `H²` norm.
-/
def transverseFrequencyEnergy (n : TransverseFrequency) : ℝ :=
  (2 * Real.pi) ^ 2 * ∑ j, (n j : ℝ) ^ 2

/-- The inhomogeneous order-two Fourier weight. -/
def transverseH2Weight (n : TransverseFrequency) : ℝ :=
  1 + transverseFrequencyEnergy n

/-- The transverse frequency energy `(2π)²|n|²` is nonnegative. -/
lemma transverseFrequencyEnergy_nonneg (n : TransverseFrequency) :
    0 ≤ transverseFrequencyEnergy n := by
  unfold transverseFrequencyEnergy
  positivity

/--
The inhomogeneous order-two weight is at least `1`, so the weighted coefficient certificate
dominates the plain Fourier coefficients.
-/
lemma one_le_transverseH2Weight (n : TransverseFrequency) :
    1 ≤ transverseH2Weight n := by
  simp only [transverseH2Weight, le_add_iff_nonneg_right]
  exact transverseFrequencyEnergy_nonneg n

/--
The inhomogeneous order-two weight is strictly positive, hence invertible; this is what makes
the graph equation solvable for the physical coefficients.
-/
lemma transverseH2Weight_pos (n : TransverseFrequency) :
    0 < transverseH2Weight n :=
  lt_of_lt_of_le zero_lt_one (one_le_transverseH2Weight n)

/-! ## The scalar Fourier synthesis bridge -/

/-- The explicit normalized product Haar measure used internally by Mathlib's basis. -/
def torusHaarMeasure (d : Type*) [Fintype d] : Measure (UnitAddTorus d) :=
  MeasureTheory.Measure.pi (fun _ : d => AddCircle.haarAddCircle)

/--
On the unit-period additive circle the ordinary volume coincides with normalized additive Haar
measure, so no normalization constant enters the Fourier basis.
-/
lemma volume_unitAddCircle_eq_haar :
    (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))

/-- The ordinary volume on the unit torus is normalized product Haar measure. -/
lemma volume_unitAddTorus_eq_haar {d : Type*} [Fintype d] :
    (volume : Measure (UnitAddTorus d)) = torusHaarMeasure d := by
  rw [MeasureTheory.volume_pi]
  congr 1
  funext i
  exact volume_unitAddCircle_eq_haar

/-- The scalar Fourier basis transported to the project's physical-volume model. -/
def transverseScalarFourierBasis :
    HilbertBasis TransverseFrequency ℂ TransverseScalarL2 := by
  change HilbertBasis TransverseFrequency ℂ
    (Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
  rw [volume_unitAddTorus_eq_haar]
  exact UnitAddTorus.mFourierBasis (d := Fin 2)

/-- Scalar Fourier analysis in the project's physical-volume model. -/
def transverseScalarFourierAnalysis :
    TransverseScalarL2 ≃ₗᵢ[ℂ] TransverseScalarFourierL2 :=
  transverseScalarFourierBasis.repr

/-- Synthesis of scalar square-summable coefficients into physical transverse `L²`. -/
def transverseScalarFourierSynthesis :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarL2 :=
  transverseScalarFourierAnalysis.symm.toContinuousLinearEquiv.toContinuousLinearMap

/--
Fourier analysis undoes synthesis: the coefficient array of `transverseScalarFourierSynthesis a`
is `a`.
-/
@[simp] theorem transverseScalarFourierAnalysis_synthesis
    (a : TransverseScalarFourierL2) :
    transverseScalarFourierAnalysis (transverseScalarFourierSynthesis a) = a :=
  transverseScalarFourierAnalysis.apply_symm_apply a

/--
Fourier synthesis undoes analysis: re-summing the coefficient array of a scalar transverse `L²`
field recovers the field.
-/
@[simp] theorem transverseScalarFourierSynthesis_analysis
    (f : TransverseScalarL2) :
    transverseScalarFourierSynthesis (transverseScalarFourierAnalysis f) = f :=
  transverseScalarFourierAnalysis.symm_apply_apply f

/-! ## Continuous Fourier coefficient functionals -/

/-- Extract one scalar coordinate from a vector-valued transverse `L²` field. -/
def transverseCoordL2 (i : ι) :
    TransverseVecL2 ι →L[ℂ] TransverseScalarL2 :=
  (EuclideanSpace.proj i).compLpL 2 transverseMeasure

/-- A scalar transverse Fourier monomial in the project's physical-volume model. -/
def transverseMonomialL2 (n : TransverseFrequency) : TransverseScalarL2 :=
  transverseScalarFourierBasis n

/-- One scalar Fourier coefficient in the project's physical-volume model. -/
def transverseScalarCoeffCLM (n : TransverseFrequency) :
    TransverseScalarL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : TransverseFrequency ↦ ℂ) 2 n).comp
    transverseScalarFourierAnalysis.toContinuousLinearEquiv.toContinuousLinearMap

/--
The `n`-th scalar Fourier coefficient functional is the inner product against the Fourier
monomial `transverseMonomialL2 n`, in Mathlib's convention (conjugate-linear in the first slot).
-/
theorem transverseScalarCoeffCLM_eq_inner
    (f : TransverseScalarL2) (n : TransverseFrequency) :
    transverseScalarCoeffCLM n f = inner ℂ (transverseMonomialL2 n) f := by
  exact HilbertBasis.repr_apply_apply transverseScalarFourierBasis f n

/--
The `n`-th Fourier coefficient of a synthesized field is the `n`-th entry of the coefficient
array it was built from.
-/
@[simp] theorem transverseScalarCoeffCLM_synthesis
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    transverseScalarCoeffCLM n (transverseScalarFourierSynthesis a) = a n := by
  change (transverseScalarFourierAnalysis
    (transverseScalarFourierSynthesis a)) n = a n
  rw [transverseScalarFourierAnalysis_synthesis]

/-- The `i`-th scalar Fourier coefficient as a continuous functional on physical `L²`. -/
def transverseCoeffCLM (n : TransverseFrequency) (i : ι) :
    TransverseVecL2 ι →L[ℂ] ℂ :=
  (transverseScalarCoeffCLM n).comp (transverseCoordL2 i)

/-- Read one entry of the stored weighted Fourier-coefficient array. -/
def weightedTransverseCoeffCLM (n : TransverseFrequency) (i : ι) :
    WeightedTransverseCoeffs ι →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : TransverseFrequency ↦ ℂ) 2 n).comp
    (PiLp.proj 2 (fun _ : ι ↦ TransverseScalarFourierL2) i)

/-! ## Coordinatewise scalar synthesis -/

/-- Scalar physical `L²` fields on each fibre coordinate, with their Euclidean product norm. -/
abbrev TransverseVecCoordinateL2 (ι : Type*) :=
  PiLp 2 (fun _ : ι => TransverseScalarL2)

/-- Three scalar physical `L²` fields, equipped with their Euclidean product norm. -/
abbrev TransverseC3CoordinateL2 := TransverseVecCoordinateL2 (Fin 3)

/-- Insert a scalar into one coordinate of `ℂ^ι`. -/
def scalarToVecPoint [DecidableEq ι] (i : ι) : ℂ →L[ℂ] EuclideanSpace ℂ ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => ℂ) i)

/--
Insert a scalar into one coordinate of `ℂ³`.  This is `scalarToVecPoint` at `ι = Fin 3`,
but it is kept as a stand-alone definition because several whole-plane and product modules
unfold it with `simp [scalarToC3Point]`.
-/
def scalarToC3Point (i : Fin 3) : ℂ →L[ℂ] C3 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin 3 => ℂ) i)

/-- Insert a scalar `L²` field into one coordinate of a `ℂ^ι`-valued field. -/
def scalarToVecCoordL2 [DecidableEq ι] (i : ι) :
    TransverseScalarL2 →L[ℂ] TransverseVecL2 ι :=
  (scalarToVecPoint i).compLpL 2 transverseMeasure

/-- Assemble scalar `L²` coordinate fields into a `ℂ^ι`-valued field. -/
def transverseVecOfCoordsL2 [DecidableEq ι] :
    TransverseVecCoordinateL2 ι →L[ℂ] TransverseVecL2 ι :=
  ∑ i : ι, (scalarToVecCoordL2 i).comp
    (PiLp.proj 2 (fun _ : ι => TransverseScalarL2) i)

/-- Assemble three scalar `L²` coordinate fields into a `ℂ³`-valued field. -/
abbrev transverseC3OfCoordsL2 :
    TransverseC3CoordinateL2 →L[ℂ] TransverseC3L2 :=
  transverseVecOfCoordsL2

/-- Coordinate extraction is a left inverse to coordinatewise assembly. -/
theorem transverseCoordL2_transverseVecOfCoordsL2 [DecidableEq ι]
    (j : ι) (a : TransverseVecCoordinateL2 ι) :
    transverseCoordL2 j (transverseVecOfCoordsL2 a) = a j := by
  rw [show (transverseVecOfCoordsL2 a : TransverseVecL2 ι) =
      ∑ i : ι, scalarToVecCoordL2 i (a i) by
    simp [transverseVecOfCoordsL2]]
  rw [map_sum]
  ext1
  have hterm : ∀ i : ι,
      ((transverseCoordL2 j (scalarToVecCoordL2 i (a i)) : TransverseScalarL2) :
        TransverseTorus → ℂ) =ᵐ[transverseMeasure]
        fun x => if i = j then (a i : TransverseTorus → ℂ) x else 0 := by
    intro i
    have hsingle := (scalarToVecPoint i).coeFn_compLpL (a i)
    have hproj := (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL
      (scalarToVecCoordL2 i (a i))
    filter_upwards [hsingle, hproj] with x hs hp
    change (((EuclideanSpace.proj (𝕜 := ℂ) j).compLp
      (scalarToVecCoordL2 i (a i)) : TransverseScalarL2) :
        TransverseTorus → ℂ) x = _
    change (((EuclideanSpace.proj (𝕜 := ℂ) j).compLp
      (scalarToVecCoordL2 i (a i)) : TransverseScalarL2) :
        TransverseTorus → ℂ) x = _ at hp
    change (((scalarToVecPoint i).compLp (a i) : TransverseVecL2 ι) :
      TransverseTorus → EuclideanSpace ℂ ι) x = _ at hs
    rw [hp]
    change (EuclideanSpace.proj (𝕜 := ℂ) j)
      ((((scalarToVecPoint i).compLp (a i) : TransverseVecL2 ι) :
        TransverseTorus → EuclideanSpace ℂ ι) x) = _
    rw [hs]
    simp [scalarToVecPoint, eq_comm]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : ι => transverseCoordL2 j (scalarToVecCoordL2 i (a i))),
      ae_all_iff.2 hterm] with x hx ht
  rw [hx, Finset.sum_apply]
  calc
    (∑ i : ι,
        ((transverseCoordL2 j (scalarToVecCoordL2 i (a i)) :
          TransverseScalarL2) : TransverseTorus → ℂ) x) =
        ∑ i : ι, if i = j then (a i : TransverseTorus → ℂ) x else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ht i
    _ = (a j : TransverseTorus → ℂ) x := by simp

/-- Coordinate extraction is a left inverse to coordinatewise assembly, at three components. -/
theorem transverseCoordL2_transverseC3OfCoordsL2
    (j : Fin 3) (a : TransverseC3CoordinateL2) :
    transverseCoordL2 j (transverseC3OfCoordsL2 a) = a j :=
  transverseCoordL2_transverseVecOfCoordsL2 j a

/-- Scalar transverse `L²` fields are determined by all their Fourier coefficients. -/
theorem transverseScalarL2_ext_of_coeff {f g : TransverseScalarL2}
    (h : ∀ n, transverseScalarCoeffCLM n f = transverseScalarCoeffCLM n g) :
    f = g := by
  apply transverseScalarFourierAnalysis.injective
  apply lp.ext
  funext n
  exact h n

/--
Vector-valued transverse `L²` fields are determined coordinatewise by all their Fourier
coefficients.  This is the fibre-generic form of `transverseC3L2_ext_coeff`
(`FastDynamo/Analysis/PeriodicWeakDerivative.lean`).
-/
theorem transverseVecL2_ext_coeff {f g : TransverseVecL2 ι}
    (h : ∀ n i, transverseCoeffCLM n i f = transverseCoeffCLM n i g) :
    f = g := by
  have hcoord : ∀ i : ι, transverseCoordL2 i f = transverseCoordL2 i g := by
    intro i
    apply transverseScalarL2_ext_of_coeff
    intro n
    exact h n i
  apply Lp.ext
  have hcoord_ae : ∀ i : ι,
      ((transverseCoordL2 i f : TransverseScalarL2) :
          TransverseTorus → ℂ) =ᵐ[transverseMeasure]
        ((transverseCoordL2 i g : TransverseScalarL2) :
          TransverseTorus → ℂ) := by
    intro i
    rw [hcoord i]
  have hf : ∀ i : ι,
      ((transverseCoordL2 i f : TransverseScalarL2) :
          TransverseTorus → ℂ) =ᵐ[transverseMeasure]
        fun x => (f x) i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f
  have hg : ∀ i : ι,
      ((transverseCoordL2 i g : TransverseScalarL2) :
          TransverseTorus → ℂ) =ᵐ[transverseMeasure]
        fun x => (g x) i := by
    intro i
    exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL g
  filter_upwards [ae_all_iff.2 hcoord_ae, ae_all_iff.2 hf,
    ae_all_iff.2 hg] with x hfg hfx hgx
  apply PiLp.ext
  intro i
  calc
    (f x) i = (transverseCoordL2 i f : TransverseScalarL2) x :=
      (hfx i).symm
    _ = (transverseCoordL2 i g : TransverseScalarL2) x := hfg i
    _ = (g x) i := hgx i

/-! ## The closed graph domain -/

/-- The graph equation `aᵢ(n) = (1 + 4π²|n|²) b̂ᵢ(n)`. -/
def transverseH2Constraint (n : TransverseFrequency) (i : ι) :
    (TransverseVecL2 ι × WeightedTransverseCoeffs ι) →L[ℂ] ℂ :=
  (weightedTransverseCoeffCLM n i).comp
      (ContinuousLinearMap.snd ℂ (TransverseVecL2 ι) (WeightedTransverseCoeffs ι)) -
    (transverseH2Weight n : ℂ) •
      (transverseCoeffCLM n i).comp
        (ContinuousLinearMap.fst ℂ (TransverseVecL2 ι) (WeightedTransverseCoeffs ι))

/-- Closed Fourier-graph realization of periodic `ℂ^ι`-valued `H²(T²)`. -/
def transverseH2Submodule :
    Submodule ℂ (TransverseVecL2 ι × WeightedTransverseCoeffs ι) :=
  ⨅ n, ⨅ i, (transverseH2Constraint n i).ker

/--
A pair `(b, a)` of a physical field and a coefficient array lies in the `H²` graph exactly when
the graph equation `aᵢ(n) = (1 + 4π²|n|²) b̂ᵢ(n)` holds at every frequency and component.
-/
theorem mem_transverseH2Submodule_iff (b : TransverseVecL2 ι)
    (a : WeightedTransverseCoeffs ι) :
    (b, a) ∈ transverseH2Submodule ↔
      ∀ n i, (a i) n =
        (transverseH2Weight n : ℂ) * transverseCoeffCLM n i b := by
  constructor
  · intro h n i
    have hker : (b, a) ∈ (transverseH2Constraint n i).ker :=
      (Submodule.mem_iInf _).mp
        ((Submodule.mem_iInf _).mp h n) i
    change (a i) n -
      (transverseH2Weight n : ℂ) * transverseCoeffCLM n i b = 0 at hker
    exact sub_eq_zero.mp hker
  · intro h
    rw [transverseH2Submodule, Submodule.mem_iInf]
    intro n
    rw [Submodule.mem_iInf]
    intro i
    change (a i) n -
      (transverseH2Weight n : ℂ) * transverseCoeffCLM n i b = 0
    exact sub_eq_zero.mpr (h n i)

/--
The `H²` graph is closed in `L² × ℓ²`, being an intersection of kernels of the continuous
constraint functionals `transverseH2Constraint`.
-/
lemma isClosed_transverseH2Submodule :
    IsClosed ((transverseH2Submodule (ι := ι) :
      Submodule ℂ (TransverseVecL2 ι × WeightedTransverseCoeffs ι)) :
      Set (TransverseVecL2 ι × WeightedTransverseCoeffs ι)) := by
  simpa only [transverseH2Submodule, Submodule.coe_iInf] using
    (isClosed_iInter fun n =>
      isClosed_iInter fun i => (transverseH2Constraint n i).isClosed_ker)

/--
The Fourier-graph model for periodic complex `ℂ^ι`-valued `H²` on the transverse torus.
-/
abbrev TransverseVecH2 (ι : Type*) [Fintype ι] :
    Submodule ℂ (TransverseVecL2 ι × WeightedTransverseCoeffs ι) :=
  transverseH2Submodule

/-- The Fourier-graph model for periodic complex three-component `H²` on the transverse torus. -/
abbrev TransverseC3H2 := TransverseVecH2 (Fin 3)

/-- The Fourier-graph model for periodic complex two-component `H²` on the transverse torus. -/
abbrev TransverseC2H2 := TransverseVecH2 (Fin 2)

/--
The transverse `H²` graph is a complete space, inherited from closedness inside the complete
product `TransverseVecL2 ι × WeightedTransverseCoeffs ι`. This is the point of the graph
realization: the subtype of `L²` fields with summable weighted coefficients would carry only the
incomplete `L²` norm.
-/
instance : CompleteSpace (TransverseVecH2 ι) :=
  (isClosed_transverseH2Submodule (ι := ι)).isComplete.completeSpace_coe

/-- Forget the weighted coefficient certificate. -/
def transverseH2Embedding : TransverseVecH2 ι →L[ℂ] TransverseVecL2 ι :=
  (ContinuousLinearMap.fst ℂ (TransverseVecL2 ι) (WeightedTransverseCoeffs ι)).domRestrict
    transverseH2Submodule

/--
The `H²`-to-`L²` embedding is the first projection: it returns the physical field stored in the
graph element.
-/
@[simp] theorem transverseH2Embedding_apply (b : TransverseVecH2 ι) :
    transverseH2Embedding b = b.1.1 :=
  rfl

/-- The physical `L²` field uniquely determines its weighted coefficient certificate. -/
theorem transverseH2Embedding_injective :
    Function.Injective (transverseH2Embedding (ι := ι)) := by
  intro x y hxy
  change x.1.1 = y.1.1 at hxy
  apply Subtype.ext
  apply Prod.ext
  · exact hxy
  · apply PiLp.ext
    intro i
    apply lp.ext
    funext n
    have hxker : x.1 ∈ (transverseH2Constraint n i).ker :=
      (Submodule.mem_iInf _).mp
        ((Submodule.mem_iInf _).mp x.2 n) i
    have hyker : y.1 ∈ (transverseH2Constraint n i).ker :=
      (Submodule.mem_iInf _).mp
        ((Submodule.mem_iInf _).mp y.2 n) i
    change (x.1.2 i) n -
      (transverseH2Weight n : ℂ) * transverseCoeffCLM n i x.1.1 = 0 at hxker
    change (y.1.2 i) n -
      (transverseH2Weight n : ℂ) * transverseCoeffCLM n i y.1.1 = 0 at hyker
    calc
      (x.1.2 i) n =
          (transverseH2Weight n : ℂ) * transverseCoeffCLM n i x.1.1 :=
        sub_eq_zero.mp hxker
      _ = (transverseH2Weight n : ℂ) * transverseCoeffCLM n i y.1.1 := by
        rw [hxy]
      _ = (y.1.2 i) n := (sub_eq_zero.mp hyker).symm

/-! ## Fourier derivative candidates by bounded multipliers -/

/-- The Fourier multiplier for the transverse Laplacian, acting on stored `H²` coefficients. -/
def transverseLaplacianFourierMultiplier (n : TransverseFrequency) : ℂ :=
  -(transverseFrequencyEnergy n : ℂ) / (transverseH2Weight n : ℂ)

/--
The Laplacian symbol divided by the order-two weight has modulus at most one, so the transverse
Laplacian is a contraction from the stored `H²` coefficients into `ℓ²`.
-/
lemma norm_transverseLaplacianFourierMultiplier_le_one
    (n : TransverseFrequency) :
    ‖transverseLaplacianFourierMultiplier n‖ ≤ 1 := by
  rw [transverseLaplacianFourierMultiplier, norm_div, norm_neg,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (transverseFrequencyEnergy_nonneg n),
    abs_of_pos (transverseH2Weight_pos n)]
  apply (div_le_one (transverseH2Weight_pos n)).2
  unfold transverseH2Weight
  linarith

/-- The Fourier multiplier for one transverse weak derivative. -/
def transverseDerivFourierMultiplier (j : Fin 2)
    (n : TransverseFrequency) : ℂ :=
  (2 * Real.pi * Complex.I * (n j : ℂ)) /
    (transverseH2Weight n : ℂ)

/--
The symbol `2π i n_j` of one transverse derivative, divided by the order-two weight, has modulus
at most one; the proof uses `2π|n_j| ≤ 1 + (2π n_j)² ≤ transverseH2Weight n`.
-/
lemma norm_transverseDerivFourierMultiplier_le_one
    (j : Fin 2) (n : TransverseFrequency) :
    ‖transverseDerivFourierMultiplier j n‖ ≤ 1 := by
  have hsum : (n j : ℝ) ^ 2 ≤ ∑ i, (n i : ℝ) ^ 2 := by
    exact Finset.single_le_sum (fun i _ => sq_nonneg (n i : ℝ))
      (Finset.mem_univ j)
  let x : ℝ := 2 * Real.pi * |(n j : ℝ)|
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx_sq : x ^ 2 ≤ transverseFrequencyEnergy n := by
    dsimp [x, transverseFrequencyEnergy]
    have hfac : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
    have hm := mul_le_mul_of_nonneg_left hsum hfac
    calc
      (2 * Real.pi * |(n j : ℝ)|) ^ 2 =
          (2 * Real.pi) ^ 2 * (n j : ℝ) ^ 2 := by
        rw [mul_pow, sq_abs]
      _ ≤ (2 * Real.pi) ^ 2 * ∑ i, (n i : ℝ) ^ 2 := hm
  have hx_weight : x ≤ transverseH2Weight n := by
    have hxx : x ≤ 1 + x ^ 2 := by
      nlinarith [sq_nonneg (x - 1)]
    unfold transverseH2Weight
    linarith
  rw [transverseDerivFourierMultiplier, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (transverseH2Weight_pos n)]
  have hnum :
      ‖(2 * Real.pi : ℂ) * Complex.I * (n j : ℂ)‖ = x := by
    calc
      ‖(2 * Real.pi : ℂ) * Complex.I * (n j : ℂ)‖ =
          ‖(2 * Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖(n j : ℂ)‖ := by
        rw [norm_mul, norm_mul]
      _ = 2 * Real.pi * |(n j : ℝ)| := by
        simp [abs_of_pos Real.pi_pos]
      _ = x := rfl
  rw [hnum]
  exact (div_le_one (transverseH2Weight_pos n)).2 hx_weight

/-- Bounded scalar coefficient map realizing the transverse Laplacian. -/
def transverseLaplacianCoeffMap :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (transverseLaplacianFourierMultiplier n))
    zero_le_one
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (transverseLaplacianFourierMultiplier n)).trans
        (norm_transverseLaplacianFourierMultiplier_le_one n))

/-- Bounded scalar coefficient map realizing one transverse weak derivative. -/
def transverseDerivCoeffMap (j : Fin 2) :
    TransverseScalarFourierL2 →L[ℂ] TransverseScalarFourierL2 :=
  lp.mapCLM 2
    (fun n => (ContinuousLinearMap.lsmul ℂ ℂ)
      (transverseDerivFourierMultiplier j n))
    zero_le_one
    (fun n => (ContinuousLinearMap.opNorm_lsmul_apply_le
      (E := ℂ) (transverseDerivFourierMultiplier j n)).trans
        (norm_transverseDerivFourierMultiplier_le_one j n))

/--
The Laplacian coefficient map acts diagonally, multiplying the `n`-th coefficient by
`transverseLaplacianFourierMultiplier n`.
-/
@[simp] theorem transverseLaplacianCoeffMap_apply
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    transverseLaplacianCoeffMap a n =
      transverseLaplacianFourierMultiplier n * a n :=
  rfl

/--
The `j`-th derivative coefficient map acts diagonally, multiplying the `n`-th coefficient by
`transverseDerivFourierMultiplier j n`.
-/
@[simp] theorem transverseDerivCoeffMap_apply (j : Fin 2)
    (a : TransverseScalarFourierL2) (n : TransverseFrequency) :
    transverseDerivCoeffMap j a n =
      transverseDerivFourierMultiplier j n * a n :=
  rfl

/-- Apply one scalar synthesis map to each stored fibre component. -/
def mapWeightedTransverseCoords
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarL2) :
    WeightedTransverseCoeffs ι →L[ℂ] TransverseVecCoordinateL2 ι :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : ι => TransverseScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp
      (PiLp.proj 2 (fun _ : ι => TransverseScalarFourierL2) i))

omit [Fintype ι] in
/-- `mapWeightedTransverseCoords T` applies `T` separately in each stored fibre
component. -/
@[simp] theorem mapWeightedTransverseCoords_apply
    (T : TransverseScalarFourierL2 →L[ℂ] TransverseScalarL2)
    (a : WeightedTransverseCoeffs ι) (i : ι) :
    mapWeightedTransverseCoords T a i = T (a i) :=
  rfl

/-- Coordinatewise synthesis has exactly the prescribed scalar coefficients. -/
theorem transverseCoeffCLM_transverseVecOfCoordsL2_synthesis [DecidableEq ι]
    (a : WeightedTransverseCoeffs ι) (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i
      (transverseVecOfCoordsL2
        (mapWeightedTransverseCoords transverseScalarFourierSynthesis a)) =
      (a i) n := by
  rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply,
    transverseCoordL2_transverseVecOfCoordsL2,
    mapWeightedTransverseCoords_apply,
    transverseScalarCoeffCLM_synthesis]

/-- Read the weighted coefficient certificate from a transverse `H²` field. -/
def transverseH2WeightedCoeffs :
    TransverseVecH2 ι →L[ℂ] WeightedTransverseCoeffs ι :=
  (ContinuousLinearMap.snd ℂ (TransverseVecL2 ι) (WeightedTransverseCoeffs ι)).domRestrict
    transverseH2Submodule

/--
The stored certificate of a transverse `H²` element is the weight times the physical Fourier
coefficient: `(transverseH2WeightedCoeffs b i) n = (1 + 4π²|n|²) * b̂ᵢ(n)`.
-/
theorem transverseH2WeightedCoeffs_apply
    (b : TransverseVecH2 ι) (n : TransverseFrequency) (i : ι) :
    (transverseH2WeightedCoeffs b i) n =
      (transverseH2Weight n : ℂ) *
        transverseCoeffCLM n i (transverseH2Embedding b) := by
  exact (mem_transverseH2Submodule_iff b.1.1 b.1.2).mp b.2 n i

/-- One Fourier-characterized transverse derivative candidate as a bounded map `H² → L²`. -/
def transverseVecDerivFromH2 (ι : Type*) [Fintype ι] [DecidableEq ι] (j : Fin 2) :
    TransverseVecH2 ι →L[ℂ] TransverseVecL2 ι :=
  transverseVecOfCoordsL2.comp
    ((mapWeightedTransverseCoords
      (transverseScalarFourierSynthesis.comp (transverseDerivCoeffMap j))).comp
        transverseH2WeightedCoeffs)

/-- One Fourier-characterized transverse derivative candidate on `ℂ³`-valued `H²`. -/
abbrev transverseDerivFromH2 (j : Fin 2) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  transverseVecDerivFromH2 (Fin 3) j

/-- The Fourier-characterized transverse Laplacian candidate as a bounded map `H² → L²`. -/
def transverseVecLaplacianFromH2 (ι : Type*) [Fintype ι] [DecidableEq ι] :
    TransverseVecH2 ι →L[ℂ] TransverseVecL2 ι :=
  transverseVecOfCoordsL2.comp
    ((mapWeightedTransverseCoords
      (transverseScalarFourierSynthesis.comp transverseLaplacianCoeffMap)).comp
        transverseH2WeightedCoeffs)

/-- The Fourier-characterized transverse Laplacian candidate on `ℂ³`-valued `H²`. -/
abbrev transverseLaplacianFromH2 :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  transverseVecLaplacianFromH2 (Fin 3)

/-- Fourier characterization of one transverse derivative candidate. -/
theorem transverseCoeffCLM_transverseDerivFromH2 [DecidableEq ι]
    (j : Fin 2) (b : TransverseVecH2 ι)
    (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i (transverseVecDerivFromH2 ι j b) =
      (2 * Real.pi * Complex.I * (n j : ℂ)) *
        transverseCoeffCLM n i (transverseH2Embedding b) := by
  change transverseCoeffCLM n i
    (transverseVecOfCoordsL2
      (mapWeightedTransverseCoords
        (transverseScalarFourierSynthesis.comp (transverseDerivCoeffMap j))
        (transverseH2WeightedCoeffs b))) = _
  rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply,
    transverseCoordL2_transverseVecOfCoordsL2,
    mapWeightedTransverseCoords_apply,
    ContinuousLinearMap.comp_apply,
    transverseScalarCoeffCLM_synthesis,
    transverseDerivCoeffMap_apply,
    transverseH2WeightedCoeffs_apply,
    transverseDerivFourierMultiplier]
  have hw : (transverseH2Weight n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (transverseH2Weight_pos n))
  field_simp [hw, transverseCoeffCLM]
  rfl

/-- Fourier characterization of the transverse Laplacian candidate. -/
theorem transverseCoeffCLM_transverseLaplacianFromH2 [DecidableEq ι]
    (b : TransverseVecH2 ι) (n : TransverseFrequency) (i : ι) :
    transverseCoeffCLM n i (transverseVecLaplacianFromH2 ι b) =
      -(transverseFrequencyEnergy n : ℂ) *
        transverseCoeffCLM n i (transverseH2Embedding b) := by
  change transverseCoeffCLM n i
    (transverseVecOfCoordsL2
      (mapWeightedTransverseCoords
        (transverseScalarFourierSynthesis.comp transverseLaplacianCoeffMap)
        (transverseH2WeightedCoeffs b))) = _
  rw [transverseCoeffCLM, ContinuousLinearMap.comp_apply,
    transverseCoordL2_transverseVecOfCoordsL2,
    mapWeightedTransverseCoords_apply,
    ContinuousLinearMap.comp_apply,
    transverseScalarCoeffCLM_synthesis,
    transverseLaplacianCoeffMap_apply,
    transverseH2WeightedCoeffs_apply,
    transverseLaplacianFourierMultiplier]
  have hw : (transverseH2Weight n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (transverseH2Weight_pos n))
  field_simp [hw, transverseCoeffCLM]
  rfl

end

end FastDynamo
