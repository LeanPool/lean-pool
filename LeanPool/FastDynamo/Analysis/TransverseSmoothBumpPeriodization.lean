/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.TransverseSmoothBumpH2CutoffConcrete
public import LeanPool.FastDynamo.Global.TorusChartFourierWeakTransfer
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Locally finite lattice periodization of compactly supported plane bumps

This file isolates the analytic bridge between compactly supported functions
on the transverse plane and functions on the unit transverse torus.  The
integer-lattice sum is defined directly on `WholePlane`; compact support makes
that sum pointwise finite.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set WithLp
open scoped ENNReal FourierTransform SchwartzMap

namespace TransverseSmoothBumpPeriodization

open TransverseSmoothBumpH2Cutoff
open TransverseSmoothBumpH2CutoffConcrete
open ScaleFamily.TorusCellPlacement
open ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate

/-- Translation of a whole-plane point by an integer transverse frequency. -/
def integerTranslate (n : TransverseFrequency) (x : WholePlane) : WholePlane :=
  frequencyPoint n + x

/-- Translating by an integer frequency adds its integer entries coordinatewise. -/
@[simp] theorem integerTranslate_apply
    (n : TransverseFrequency) (x : WholePlane) (j : Fin 2) :
    integerTranslate n x j = (n j : ℝ) + x j :=
  rfl

/-- Translating by the zero frequency is the identity. -/
@[simp] theorem integerTranslate_zero (x : WholePlane) :
    integerTranslate 0 x = x := by
  ext j
  simp [integerTranslate]

/-- Pointwise integer-lattice periodization. -/
def latticePeriodization
    {F : Type*} [AddCommMonoid F] [TopologicalSpace F]
    (f : WholePlane → F) (x : WholePlane) : F :=
  ∑' n : TransverseFrequency, f (integerTranslate n x)

/-- The canonical identification of coordinate functions with the transverse
whole plane. -/
def coordinatesToWholePlane (x : Fin 2 → ℝ) : WholePlane :=
  WithLp.toLp 2 x

/-- The identification of a raw coordinate tuple with a point of `WholePlane` does not
change the coordinates. -/
@[simp] theorem coordinatesToWholePlane_apply
    (x : Fin 2 → ℝ) (j : Fin 2) :
    coordinatesToWholePlane x j = x j :=
  rfl

/-- The half-open unit box, now regarded as a subset of `WholePlane`. -/
def wholePlaneIocFundamentalBox : Set WholePlane :=
  {x | ∀ j, x j ∈ Set.Ioc (0 : ℝ) (0 + 1)}

/-- A coordinate tuple lies in the half-open unit box `iocFundamentalBox` exactly when the
corresponding whole-plane point lies in `wholePlaneIocFundamentalBox`. -/
theorem coordinatesToWholePlane_mem_ioc_iff
    (x : Fin 2 → ℝ) :
    coordinatesToWholePlane x ∈ wholePlaneIocFundamentalBox ↔
      x ∈ iocFundamentalBox := by
  rfl

/-- A no-wrap support condition sufficient for a compactly supported function
to descend without overlapping copies on the half-open unit box. -/
def SupportedInIocFundamentalBox
    {F : Type*} [Zero F] (f : WholePlane → F) : Prop :=
  Function.support f ⊆ wholePlaneIocFundamentalBox

/-- Two representatives in the half-open box cannot differ by a nonzero
integer vector. -/
theorem integerTranslate_eq_zero_of_mem_ioc
    {n : TransverseFrequency} {x : WholePlane}
    (hx : x ∈ wholePlaneIocFundamentalBox)
    (hnx : integerTranslate n x ∈ wholePlaneIocFundamentalBox) :
    n = 0 := by
  funext j
  have hnlt : (n j : ℝ) < 1 := by
    have hxlo := (hx j).1
    have hyhi := (hnx j).2
    rw [integerTranslate_apply] at hyhi
    linarith
  have hnlo : (-1 : ℝ) < (n j : ℝ) := by
    have hxhi := (hx j).2
    have hylo := (hnx j).1
    rw [integerTranslate_apply] at hylo
    linarith
  have hnlt' : n j < (1 : ℤ) := by
    exact_mod_cast hnlt
  have hnlo' : (-1 : ℤ) < n j := by
    exact_mod_cast hnlo
  change n j = (0 : ℤ)
  omega

/-- On its no-wrap support box, periodization reproduces the original
function pointwise. -/
theorem latticePeriodization_eq_of_mem_ioc
    {F : Type*} [AddCommMonoid F] [TopologicalSpace F]
    (f : WholePlane → F) (hf : SupportedInIocFundamentalBox f)
    {x : WholePlane} (hx : x ∈ wholePlaneIocFundamentalBox) :
    latticePeriodization f x = f x := by
  unfold latticePeriodization
  rw [tsum_eq_single (0 : TransverseFrequency)]
  · exact congrArg f (integerTranslate_zero x)
  · intro n hn
    by_contra hne
    exact hn (integerTranslate_eq_zero_of_mem_ioc hx (hf hne))

/-! ## Descent to the quotient torus -/

/-- The canonical `(0,1]²` representative of a transverse-torus point,
viewed in `WholePlane`. -/
def wholePlaneIocRepresentative (q : TransverseTorus) : WholePlane :=
  WithLp.toLp 2 (fun j ↦
    ((AddCircle.equivIoc 1 0 (q j) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ))

/-- The canonical representative of a torus point has, in each coordinate, the `(0, 1]`
representative supplied by `AddCircle.equivIoc`. -/
@[simp] theorem wholePlaneIocRepresentative_apply
    (q : TransverseTorus) (j : Fin 2) :
    wholePlaneIocRepresentative q j =
      ((AddCircle.equivIoc 1 0 (q j) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) :=
  rfl

/-- Choosing the canonical `(0, 1]²` representative is a measurable section of the quotient
map, which is what lets periodizations be handled as torus `Lp` functions. -/
theorem measurable_wholePlaneIocRepresentative :
    Measurable wholePlaneIocRepresentative := by
  apply (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp
  refine Measurable.of_eval fun j ↦ ?_
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc 1 0).measurable.comp
      (measurable_pi_apply j))

/-- The canonical representative of a torus point lies in the half-open unit box. -/
theorem wholePlaneIocRepresentative_mem
    (q : TransverseTorus) :
    wholePlaneIocRepresentative q ∈ wholePlaneIocFundamentalBox := by
  intro j
  exact (AddCircle.equivIoc 1 0 (q j)).property

/-- A coordinate point already in the fundamental box is recovered exactly
after quotienting. -/
theorem wholePlaneIocRepresentative_mk_of_mem
    {x : Fin 2 → ℝ} (hx : x ∈ iocFundamentalBox) :
    wholePlaneIocRepresentative (fun j ↦ (x j : UnitAddCircle)) =
      coordinatesToWholePlane x := by
  ext j
  simpa [wholePlaneIocRepresentative, coordinatesToWholePlane] using
    (AddCircle.equivIoc_coe_of_mem (hx j))

/-- Quotient periodization obtained by evaluating the lattice sum at the
canonical representative. -/
def torusLatticePeriodization
    {F : Type*} [AddCommMonoid F] [TopologicalSpace F]
    (f : WholePlane → F) (q : TransverseTorus) : F :=
  latticePeriodization f (wholePlaneIocRepresentative q)

/-- On the fundamental box, quotient periodization pulls back to the original
no-wrap function pointwise. -/
theorem torusLatticePeriodization_mk_eq
    {F : Type*} [AddCommMonoid F] [TopologicalSpace F]
    (f : WholePlane → F) (hf : SupportedInIocFundamentalBox f)
    {x : Fin 2 → ℝ} (hx : x ∈ iocFundamentalBox) :
    torusLatticePeriodization f (fun j ↦ (x j : UnitAddCircle)) =
      f (coordinatesToWholePlane x) := by
  rw [torusLatticePeriodization, wholePlaneIocRepresentative_mk_of_mem hx]
  exact latticePeriodization_eq_of_mem_ioc f hf
    ((coordinatesToWholePlane_mem_ioc_iff x).2 hx)

/-! ## Fundamental-domain Fourier coefficients -/

/-- The Fourier coefficient of a no-wrap quotient periodization is the
corresponding whole-space integral in raw Euclidean coordinates. -/
theorem torusIntegral_mFourier_mul_periodization_eq_raw
    (f : WholePlane → ℂ) (hf : SupportedInIocFundamentalBox f)
    (frequency : TransverseFrequency) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          torusLatticePeriodization f q ∂transverseMeasure) =
      ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          f (coordinatesToWholePlane x) := by
  calc
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          torusLatticePeriodization f q ∂transverseMeasure) =
        ∫ x : Fin 2 → ℝ in iocFundamentalBox,
          UnitAddTorus.mFourier (-frequency)
              (fun k ↦ (x k : UnitAddCircle)) *
            torusLatticePeriodization f
              (fun k ↦ (x k : UnitAddCircle)) := by
      rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
        volume_unitAddTorus_eq_haar]
      have hpre := UnitAddTorus.integral_preimage
        (f := fun q : TransverseTorus ↦
          UnitAddTorus.mFourier (-frequency) q *
            torusLatticePeriodization f q)
        (fun _ : Fin 2 ↦ (0 : ℝ))
      change (∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q *
            torusLatticePeriodization f q
            ∂torusHaarMeasure (Fin 2)) = _ at hpre
      simpa [iocFundamentalBox] using hpre
    _ = ∫ x : Fin 2 → ℝ in iocFundamentalBox,
        euclideanMonomial (-frequency) x *
          f (coordinatesToWholePlane x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_iocFundamentalBox] with x hx
      rw [torusLatticePeriodization_mk_eq f hf hx]
      rw [euclideanMonomial_eq_mFourier]
    _ = ∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          f (coordinatesToWholePlane x) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hzero : f (coordinatesToWholePlane x) = 0 := by
        by_contra hne
        exact hx (hf hne)
      rw [hzero, mul_zero]

/-- The Euclidean Fourier monomial at frequency `-n` coincides with the additive character
`𝐞 (-⟪x, frequencyPoint n⟫)` used by Mathlib's Fourier transform, so periodic and
whole-plane conventions match on the integer lattice. -/
theorem euclideanMonomial_mul_eq_fourierKernel
    (frequency : TransverseFrequency) (x : Fin 2 → ℝ) (c : ℂ) :
    euclideanMonomial (-frequency) x * c =
      𝐞 (-inner ℝ (coordinatesToWholePlane x) (frequencyPoint frequency)) • c := by
  rw [Circle.smul_def, Real.fourierChar_apply]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
    coordinatesToWholePlane_apply, frequencyPoint_apply]
  rw [show -((x 0 * (frequency 0 : ℝ) + x 1 * (frequency 1 : ℝ))) =
      -(frequency 0 : ℝ) * x 0 + -(frequency 1 : ℝ) * x 1 by ring]
  simp only [euclideanMonomial, Pi.neg_apply, Int.cast_neg, smul_eq_mul]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Raw-coordinate integration of the pulled-back monomial is exactly the
Schwartz Fourier transform sampled at the integer lattice point. -/
theorem rawIntegral_euclideanMonomial_eq_fourier
    (F : SchwartzMap WholePlane ℂ) (frequency : TransverseFrequency) :
    (∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          F (coordinatesToWholePlane x)) =
      𝓕 F (frequencyPoint frequency) := by
  calc
    (∫ x : Fin 2 → ℝ,
        euclideanMonomial (-frequency) x *
          F (coordinatesToWholePlane x)) =
        ∫ x : Fin 2 → ℝ,
          𝐞 (-inner ℝ (coordinatesToWholePlane x)
              (frequencyPoint frequency)) •
            F (coordinatesToWholePlane x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact euclideanMonomial_mul_eq_fourierKernel frequency x _
    _ = ∫ y : WholePlane,
          𝐞 (-inner ℝ y (frequencyPoint frequency)) • F y := by
      exact (PiLp.volume_preserving_toLp (Fin 2)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding
        (fun y : WholePlane ↦
          𝐞 (-inner ℝ y (frequencyPoint frequency)) • F y)
    _ = 𝓕 F (frequencyPoint frequency) := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq]

/-- Generic coefficient identity for a compactly supported Schwartz function
whose support has no overlap across the chosen fundamental box. -/
theorem torusIntegral_mFourier_mul_periodization_eq_fourier
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ))
    (frequency : TransverseFrequency) :
    (∫ q : TransverseTorus,
        UnitAddTorus.mFourier (-frequency) q *
          torusLatticePeriodization (F : WholePlane → ℂ) q
          ∂transverseMeasure) =
      𝓕 F (frequencyPoint frequency) := by
  rw [torusIntegral_mFourier_mul_periodization_eq_raw (F : WholePlane → ℂ)
    hF frequency]
  exact rawIntegral_euclideanMonomial_eq_fourier F frequency

/-- For a Schwartz function supported without wrap-around in the fundamental box, the
lattice sum collapses to the single term at the canonical representative. -/
theorem torusLatticePeriodization_eq_representative
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ))
    (q : TransverseTorus) :
    torusLatticePeriodization (F : WholePlane → ℂ) q =
      F (wholePlaneIocRepresentative q) := by
  exact latticePeriodization_eq_of_mem_ioc (F : WholePlane → ℂ) hF
    (wholePlaneIocRepresentative_mem q)

/-- A no-wrap Schwartz periodization is measurable on the torus, being the continuous
function composed with the measurable representative section. -/
theorem measurable_torusLatticePeriodization
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ)) :
    Measurable (torusLatticePeriodization (F : WholePlane → ℂ)) := by
  have heq : torusLatticePeriodization (F : WholePlane → ℂ) =
      fun q ↦ F (wholePlaneIocRepresentative q) := by
    funext q
    exact torusLatticePeriodization_eq_representative F hF q
  rw [heq]
  exact F.continuous.measurable.comp measurable_wholePlaneIocRepresentative

/-- A no-wrap Schwartz periodization is bounded, hence belongs to every
finite torus `Lp`; the top-exponent form is the useful construction lemma. -/
theorem torusLatticePeriodization_memLp_top
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ)) :
    MemLp (torusLatticePeriodization (F : WholePlane → ℂ)) ∞
      transverseMeasure := by
  apply memLp_top_of_bound
    (measurable_torusLatticePeriodization F hF).aestronglyMeasurable
    ((SchwartzMap.seminorm ℝ 0 0) F)
  filter_upwards with q
  rw [torusLatticePeriodization_eq_representative F hF q]
  exact SchwartzMap.norm_le_seminorm ℝ F _

/-- A no-wrap Schwartz periodization is square integrable on the transverse torus, the
torus having finite measure. -/
theorem torusLatticePeriodization_memLp_two
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ)) :
    MemLp (torusLatticePeriodization (F : WholePlane → ℂ)) 2
      transverseMeasure :=
  (torusLatticePeriodization_memLp_top F hF).mono_exponent (by simp)

/-- The no-wrap periodization bundled as a scalar torus `L²` function. -/
def torusLatticePeriodizationL2
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ)) :
    TransverseScalarL2 :=
  (torusLatticePeriodization_memLp_two F hF).toLp
    (torusLatticePeriodization (F : WholePlane → ℂ))

/-- The `L²` bundling of a no-wrap periodization has the periodization itself as an almost
everywhere representative. -/
theorem torusLatticePeriodizationL2_coe_ae
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ)) :
    (torusLatticePeriodizationL2 F hF : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure]
        torusLatticePeriodization (F : WholePlane → ℂ) :=
  MemLp.coeFn_toLp _

/-- Fourier coefficients of the bundled quotient periodization are exactly
the integer samples of the whole-plane Schwartz Fourier transform. -/
theorem transverseScalarCoeff_torusLatticePeriodizationL2
    (F : SchwartzMap WholePlane ℂ)
    (hF : SupportedInIocFundamentalBox (F : WholePlane → ℂ))
    (frequency : TransverseFrequency) :
    transverseScalarCoeffCLM frequency
        (torusLatticePeriodizationL2 F hF) =
      𝓕 F (frequencyPoint frequency) := by
  rw [transverseScalarCoeffCLM_eq_inner, MeasureTheory.L2.inner_def]
  calc
    (∫ q : TransverseTorus,
        inner ℂ
          ((transverseMonomialL2 frequency : TransverseScalarL2) q)
          ((torusLatticePeriodizationL2 F hF : TransverseScalarL2) q)
          ∂transverseMeasure) =
        ∫ q : TransverseTorus,
          UnitAddTorus.mFourier (-frequency) q *
            torusLatticePeriodization (F : WholePlane → ℂ) q
            ∂transverseMeasure := by
      apply integral_congr_ae
      filter_upwards [transverseMonomialL2_coe_ae frequency,
        torusLatticePeriodizationL2_coe_ae F hF] with q hmono hperiod
      rw [hmono, hperiod, RCLike.inner_apply]
      rw [← UnitAddTorus.mFourier_neg (n := frequency) (x := q)]
      ring
    _ = 𝓕 F (frequencyPoint frequency) :=
      torusIntegral_mFourier_mul_periodization_eq_fourier F hF frequency

end TransverseSmoothBumpPeriodization

end

end FastDynamo
