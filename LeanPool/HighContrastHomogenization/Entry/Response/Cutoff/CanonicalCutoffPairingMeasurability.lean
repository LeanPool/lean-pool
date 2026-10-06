/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ResponseFieldSize
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateAssembly

/-!
# High-contrast homogenization: Entry.Response.Cutoff.CanonicalCutoffPairingMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of the canonical cutoff pairing

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the volume average
of the cutoff-weighted Euclidean pairing of the potential and flux defects of the doubled
canonical optimizer state; its integrand expands into one genuinely quadratic term and three
linear terms. This file proves the almost-sure strong measurability of that pairing and of its
absolute value, for both the recentred and adjoint canonical coefficients, together with the
square-integrability of the flux slots the expansion needs. It also shows that a coefficient
field agreeing almost everywhere on a Chapter-2 domain with a field uniformly elliptic there has
the same subcell averages, for every response maximizer, as the Chapter-2 canonical maximizer for
that field.
-/

section
/-!
## Measurability of the canonical cutoff pairing

The cutoff pairing of the response estimate `e.response.cutoff.estimate` is the volume average of
the cutoff-weighted Euclidean pairing of the potential defect and the flux defect of the doubled
canonical optimizer state.  Its integrand expands into one genuinely quadratic term and three
linear terms,

`φ · ⟨Z.1 - Y.1, Z.2 - Y.2⟩
  = φ · ⟨Z.1, Z.2⟩ - φ · ⟨Z.1, Y.2⟩ - φ · ⟨Y.1, Z.2⟩ + φ · ⟨Y.1, Y.2⟩`,

of which the last three are linear readouts of the canonical state against the fixed vector `Y`
and the constant `⟨Y.1, Y.2⟩`.

This file records the algebraic expansion and the measurability of the three linear readouts, for
the two recentred response coefficient families of `e.response.cutoff.estimate`.  The remaining
quadratic term is the volume average of the energy density of the canonical optimizer; it is not a
linear readout of the canonical optimizer state; it is carried below as an explicit hypothesis.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The algebraic expansion -/

/-- The Euclidean pairing of the potential defect `A - B` and the flux defect `C - D` expands into
one quadratic and three linear terms.  This is the pointwise expansion of the integrand of the
cutoff pairing `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem vecDot_sub_sub_expansion (A B C D : Vec d) :
    vecDot (A - B) (C - D) = vecDot A C - vecDot A D - vecDot B C + vecDot B D := by
  simp only [sub_eq_add_neg, vecDot_add_left, vecDot_add_right, vecDot_neg_left,
    vecDot_neg_right]
  ring

/-! ## Linear readouts of the canonical optimizer state -/

/-- The cutoff-weighted volume average of the potential component of the canonical optimizer state
paired against a fixed vector is measurable, on a family of Chapter-2 coefficient objects whose
weighted coordinate volume averages are measurable.  This is the potential linear term in the
expansion of the cutoff pairing of `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem measurable_volumeAverage_cutoff_vecDot_canonical_potential [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ)
    {aU : CoeffSpace d → Book.Ch02.CoeffOn (adaptedDomain q hq t)}
    (p r : Vec d) {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) (W : Vec d)
    (hcoord : ∀ α : BlockCoord d, Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x *
        toFullBlockVec (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x) α)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 W) := by
  classical
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hφL2 : MemScalarL2 (HighContrast.adaptedCell q t) φ := by
    refine MemLp.of_bound (hφ.contDiff.continuous.measurable.aestronglyMeasurable) 2 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  have hfun : (fun a : CoeffSpace d => volumeAverage (HighContrast.adaptedCell q t) (fun x =>
        φ x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 W))
      = fun a : CoeffSpace d => ∑ i : Fin d, W i *
          volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x *
            toFullBlockVec
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x)
              (Sum.inl i)) := by
    funext a
    have hZ1 : MemVectorL2 (HighContrast.adaptedCell q t)
        (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1) := by
      simpa only [canonicalOptimizerBlockState] using!
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain q hq t)
            (aU a)) p r).toSolution.toH1.grad_memVectorL2
    have hZi : ∀ i : Fin d, MemScalarL2 (HighContrast.adaptedCell q t) (fun x =>
        toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x) (Sum.inl i)) := by
      intro i
      simpa only [toFullBlockVec] using memScalarL2_coord_of_memVectorL2 hZ1 i
    have hInt : ∀ i : Fin d, Integrable (fun x => W i * (φ x *
        toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x) (Sum.inl i)))
        (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
      intro i
      exact (hφL2.integrable_mul (hZi i)).const_mul (W i)
    simp only [volumeAverage]
    rw [show (fun x => φ x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 W)
        = fun x => ∑ i : Fin d, W i * (φ x *
            toFullBlockVec
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x)
              (Sum.inl i)) by
      funext x
      simp only [vecDot, toFullBlockVec]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hInt i)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [MeasureTheory.integral_const_mul]
      ring)
  rw [hfun]
  exact Finset.measurable_sum Finset.univ (fun i _ => (hcoord (Sum.inl i)).const_mul (W i))

/-- The cutoff-weighted volume average of the flux component of the canonical optimizer state
paired against a fixed vector is measurable.  This is the flux linear term in the expansion of the
cutoff pairing of `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem measurable_volumeAverage_cutoff_vecDot_canonical_flux [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ)
    {aU : CoeffSpace d → Book.Ch02.CoeffOn (adaptedDomain q hq t)}
    (p r : Vec d) {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) (W : Vec d)
    (hcoord : ∀ α : BlockCoord d, Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x *
        toFullBlockVec (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x) α))
    (hZ2mem : ∀ a : CoeffSpace d, MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot W
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2) := by
  classical
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hφL2 : MemScalarL2 (HighContrast.adaptedCell q t) φ := by
    refine MemLp.of_bound (hφ.contDiff.continuous.measurable.aestronglyMeasurable) 2 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  have hfun : (fun a : CoeffSpace d => volumeAverage (HighContrast.adaptedCell q t) (fun x =>
        φ x * vecDot W
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2))
      = fun a : CoeffSpace d => ∑ i : Fin d, W i *
          volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x *
            toFullBlockVec
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x)
              (Sum.inr i)) := by
    funext a
    have hZi : ∀ i : Fin d, MemScalarL2 (HighContrast.adaptedCell q t) (fun x =>
        toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x) (Sum.inr i)) := by
      intro i
      simpa only [toFullBlockVec] using memScalarL2_coord_of_memVectorL2 (hZ2mem a) i
    have hInt : ∀ i : Fin d, Integrable (fun x => W i * (φ x *
        toFullBlockVec
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x) (Sum.inr i)))
        (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
      intro i
      exact (hφL2.integrable_mul (hZi i)).const_mul (W i)
    simp only [volumeAverage]
    rw [show (fun x => φ x * vecDot W
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)
        = fun x => ∑ i : Fin d, W i * (φ x *
            toFullBlockVec
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x)
              (Sum.inr i)) by
      funext x
      simp only [vecDot, toFullBlockVec]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hInt i)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [MeasureTheory.integral_const_mul]
      ring)
  rw [hfun]
  exact Finset.measurable_sum Finset.univ (fun i _ => (hcoord (Sum.inr i)).const_mul (W i))

/-! ## The two recentred response coefficient families -/

/-- The flux component of the canonical minus optimizer state is square integrable on the adapted
cell; the a.e. elliptic representative of the recentred coefficient controls it. -/
theorem memVectorL2_canonicalRespCoeffMinus_flux [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    (a : CoeffSpace d) :
    MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r x).2) := by
  classical
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have hZ1 : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r x).1) := by
    simpa only [canonicalOptimizerBlockState] using!
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a)) p r).toSolution.toH1.grad_memVectorL2
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) ((canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r x).1)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hZ1
  have hae : (fun x => matVecMul (f x) ((canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r x).1))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r x).2) := by
    filter_upwards [hbf.symm] with x hx
    simp only [canonicalOptimizerBlockState, canonicalRespCoeffMinusOn_toFun]
    rw [← hx]
  exact (memLp_congr_ae hae).mp hfluxf

/-- The flux component of the canonical plus optimizer state is square integrable on the adapted
cell. -/
theorem memVectorL2_canonicalRespCoeffPlus_flux [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    (a : CoeffSpace d) :
    MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r x).2) := by
  classical
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have hZ1 : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r x).1) := by
    simpa only [canonicalOptimizerBlockState] using!
      (Book.Ch02.canonicalMaximizer
        (Book.Ch02.responseExistenceTheory (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a)) p r).toSolution.toH1.grad_memVectorL2
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) ((canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r x).1)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hZ1
  have hae : (fun x => matVecMul (f x) ((canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r x).1))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r x).2) := by
    filter_upwards [hbf.symm] with x hx
    simp only [canonicalOptimizerBlockState, canonicalRespCoeffPlusOn_toFun]
    rw [← hx]
  exact (memLp_congr_ae hae).mp hfluxf

/-- The weighted coordinate volume averages of the canonical minus optimizer state are measurable,
so the potential linear term of the minus cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is measurable. -/
theorem measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_potential [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) (W : Vec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x).1 W) := by
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hsupp : (HighContrast.adaptedCell q t).indicator φ = φ := by
    funext x
    by_cases hx : x ∈ HighContrast.adaptedCell q t
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hφ.zero_of_notMem x hx]
  have hφL2 : MemScalarL2 (HighContrast.adaptedCell q t) φ := by
    refine MemLp.of_bound (hφ.contDiff.continuous.measurable.aestronglyMeasurable) 2 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  refine measurable_volumeAverage_cutoff_vecDot_canonical_potential q hq t p r hφ W ?_
  intro α
  exact measurable_volumeAverage_weighted_canonicalRespCoeffMinus q hq t F p r α
    hU.isOpen.measurableSet le_rfl (eta := φ) (by rw [hsupp]; exact hφL2)

/-- The potential linear term of the plus cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is measurable. -/
theorem measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_potential [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) (W : Vec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x).1 W) := by
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hsupp : (HighContrast.adaptedCell q t).indicator φ = φ := by
    funext x
    by_cases hx : x ∈ HighContrast.adaptedCell q t
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hφ.zero_of_notMem x hx]
  have hφL2 : MemScalarL2 (HighContrast.adaptedCell q t) φ := by
    refine MemLp.of_bound (hφ.contDiff.continuous.measurable.aestronglyMeasurable) 2 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  refine measurable_volumeAverage_cutoff_vecDot_canonical_potential q hq t p r hφ W ?_
  intro α
  exact measurable_volumeAverage_weighted_canonicalRespCoeffPlus q hq t F p r α
    hU.isOpen.measurableSet le_rfl (eta := φ) (by rw [hsupp]; exact hφL2)

/-- The flux linear term of the minus cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is measurable. -/
theorem measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_flux [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) (W : Vec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot W
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x).2) := by
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hsupp : (HighContrast.adaptedCell q t).indicator φ = φ := by
    funext x
    by_cases hx : x ∈ HighContrast.adaptedCell q t
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hφ.zero_of_notMem x hx]
  have hφL2 : MemScalarL2 (HighContrast.adaptedCell q t) φ := by
    refine MemLp.of_bound (hφ.contDiff.continuous.measurable.aestronglyMeasurable) 2 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  refine measurable_volumeAverage_cutoff_vecDot_canonical_flux q hq t p r hφ W ?_
    (fun a => memVectorL2_canonicalRespCoeffMinus_flux q hq t F p r a)
  intro α
  exact measurable_volumeAverage_weighted_canonicalRespCoeffMinus q hq t F p r α
    hU.isOpen.measurableSet le_rfl (eta := φ) (by rw [hsupp]; exact hφL2)

/-- The flux linear term of the plus cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is measurable. -/
theorem measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_flux [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) (W : Vec d) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot W
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x).2) := by
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hsupp : (HighContrast.adaptedCell q t).indicator φ = φ := by
    funext x
    by_cases hx : x ∈ HighContrast.adaptedCell q t
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hφ.zero_of_notMem x hx]
  have hφL2 : MemScalarL2 (HighContrast.adaptedCell q t) φ := by
    refine MemLp.of_bound (hφ.contDiff.continuous.measurable.aestronglyMeasurable) 2 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  refine measurable_volumeAverage_cutoff_vecDot_canonical_flux q hq t p r hφ W ?_
    (fun a => memVectorL2_canonicalRespCoeffPlus_flux q hq t F p r a)
  intro α
  exact measurable_volumeAverage_weighted_canonicalRespCoeffPlus q hq t F p r α
    hU.isOpen.measurableSet le_rfl (eta := φ) (by rw [hsupp]; exact hφL2)

/-! ## Reduction of the full pairing to its quadratic term -/

/-- If the cutoff-weighted volume average of the quadratic self-pairing of the canonical optimizer
state is almost-everywhere strongly measurable, then so is the full canonical cutoff pairing
itself.  The integrand expands into that quadratic term and the three linear readouts whose
measurability is recorded above; the expansion of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is applied pointwise and the four integrands are integrable, so the volume
average of the sum is the corresponding sum of volume averages. -/
theorem aestronglyMeasurable_pairing_canonical_of_quadratic [NeZero d]
    (P : Measure (CoeffSpace d)) (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (p r : Vec d) (Y : BlockVec d) {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ)
    {aU : CoeffSpace d → Book.Ch02.CoeffOn (adaptedDomain q hq t)}
    (hpot : ∀ W : Vec d, Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 W))
    (hflux : ∀ W : Vec d, Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot W
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2))
    (hZ2mem : ∀ a : CoeffSpace d, MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2))
    (hquad : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)) P) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 - Y.1)
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2 - Y.2))) P := by
  classical
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hφL2 : MemScalarL2 (HighContrast.adaptedCell q t) φ := by
    refine MemLp.of_bound (hφ.contDiff.continuous.measurable.aestronglyMeasurable) 2 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  have hφae : AEStronglyMeasurable φ (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hφL2.aestronglyMeasurable
  have hφbd : ∀ᵐ x ∂volumeMeasureOn (HighContrast.adaptedCell q t), ‖φ x‖ ≤ 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  have hY1mem : MemVectorL2 (HighContrast.adaptedCell q t) (fun _ : Vec d => Y.1) :=
    MeasureTheory.memLp_const Y.1
  have hY2mem : MemVectorL2 (HighContrast.adaptedCell q t) (fun _ : Vec d => Y.2) :=
    MeasureTheory.memLp_const Y.2
  have hpair : ∀ a : CoeffSpace d,
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2 - Y.2))
        = volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
            (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1
            (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)
          - volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
            (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 Y.2)
          - volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot Y.1
            (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)
          + volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot Y.1 Y.2) := by
    intro a
    have hZ1 : MemVectorL2 (HighContrast.adaptedCell q t)
        (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1) := by
      simpa only [canonicalOptimizerBlockState] using!
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain q hq t)
            (aU a)) p r).toSolution.toH1.grad_memVectorL2
    have hZ2 := hZ2mem a
    have hI1 : Integrable (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1)
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2))
        (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
      (integrableOn_vecDot_of_memVectorL2 hZ1 hZ2).bdd_mul hφae hφbd
    have hI2 : Integrable (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1) Y.2)
        (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
      (integrableOn_vecDot_of_memVectorL2 hZ1 hY2mem).bdd_mul hφae hφbd
    have hI3 : Integrable (fun x => φ x * vecDot Y.1
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2))
        (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
      (integrableOn_vecDot_of_memVectorL2 hY1mem hZ2).bdd_mul hφae hφbd
    have hI4 : Integrable (fun x => φ x * vecDot Y.1 Y.2)
        (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
      (MeasureTheory.integrable_const (vecDot Y.1 Y.2)).bdd_mul hφae hφbd
    simp only [volumeAverage]
    rw [show (fun x => φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2 - Y.2))
        = fun x => (φ x * vecDot
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2
            - φ x * vecDot
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 Y.2)
          - (φ x * vecDot Y.1
              (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2
            - φ x * vecDot Y.1 Y.2) by
      funext x
      rw [vecDot_sub_sub_expansion]
      ring]
    rw [MeasureTheory.integral_sub
      (f := fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2
        - φ x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 Y.2)
      (g := fun x => φ x * vecDot Y.1
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2
        - φ x * vecDot Y.1 Y.2)
      (hI1.sub hI2) (hI3.sub hI4)]
    rw [MeasureTheory.integral_sub hI1 hI2, MeasureTheory.integral_sub hI3 hI4]
    ring
  have hbase : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1
          (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)
        - volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
            (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 Y.2)
        - volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot Y.1
            (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)
        + volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot Y.1 Y.2)) P :=
    (((hquad.sub (hpot Y.2).aestronglyMeasurable).sub
      (hflux Y.1).aestronglyMeasurable).add aestronglyMeasurable_const)
  exact hbase.congr (Filter.Eventually.of_forall fun a => (hpair a).symm)

/-- The absolute value of the full canonical cutoff pairing of `e.response.cutoff.estimate`
(AK.HC Lemma A.1, (A.4)) is almost-everywhere strongly measurable as soon as the cutoff-weighted
quadratic self-pairing of the canonical optimizer state is: the modulus is a continuous function of
the pairing recorded by `aestronglyMeasurable_pairing_canonical_of_quadratic`. -/
theorem aestronglyMeasurable_abs_pairing_canonical_of_quadratic [NeZero d]
    (P : Measure (CoeffSpace d)) (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (p r : Vec d) (Y : BlockVec d) {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ)
    {aU : CoeffSpace d → Book.Ch02.CoeffOn (adaptedDomain q hq t)}
    (hpot : ∀ W : Vec d, Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 W))
    (hflux : ∀ W : Vec d, Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot W
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2))
    (hZ2mem : ∀ a : CoeffSpace d, MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2))
    (hquad : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1
        (canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2)) P) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      |volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).1 - Y.1)
        ((canonicalOptimizerBlockState (adaptedDomain q hq t) (aU a) p r x).2 - Y.2))|) P :=
  continuous_abs.comp_aestronglyMeasurable
    (aestronglyMeasurable_pairing_canonical_of_quadratic P q hq t p r Y hφ hpot hflux hZ2mem hquad)

/-- The canonical minus cutoff pairing of `e.response.cutoff.estimate` is almost-everywhere
strongly measurable, provided the cutoff-weighted volume average of the quadratic self-pairing of
the canonical minus optimizer state is.  This is the `hcanon_pairing` minus conjunct with the
quadratic term isolated as an explicit hypothesis. -/
theorem aestronglyMeasurable_abs_canonical_cutoff_pairing_minus_of_quadratic [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (hquad : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (respCell jStar F t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffMinusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1
        (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffMinusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2)) P) :
    AEStronglyMeasurable (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffMinusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffMinusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))|) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  refine aestronglyMeasurable_abs_pairing_canonical_of_quadratic P (respGrid jStar F) hq t
    p q' Y hφ ?_ ?_ ?_ ?_
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_potential
        (respGrid jStar F) hq t F p q' hφ W
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_flux
        (respGrid jStar F) hq t F p q' hφ W
  · intro a
    simpa only [respCell] using
      memVectorL2_canonicalRespCoeffMinus_flux (respGrid jStar F) hq t F p q' a
  · simpa only [respCell] using hquad

/-- The canonical plus cutoff pairing of `e.response.cutoff.estimate` is almost-everywhere
strongly measurable, provided the cutoff-weighted volume average of the quadratic self-pairing of
the canonical plus optimizer state is. -/
theorem aestronglyMeasurable_abs_canonical_cutoff_pairing_plus_of_quadratic [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (hquad : AEStronglyMeasurable (fun a : CoeffSpace d =>
      volumeAverage (respCell jStar F t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffPlusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1
        (canonicalOptimizerBlockState
            (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
            (canonicalRespCoeffPlusOn (respGrid jStar F)
              (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2)) P) :
    AEStronglyMeasurable (fun a : CoeffSpace d => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffPlusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffPlusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))|) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  refine aestronglyMeasurable_abs_pairing_canonical_of_quadratic P (respGrid jStar F) hq t
    p q' Y hφ ?_ ?_ ?_ ?_
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_potential
        (respGrid jStar F) hq t F p q' hφ W
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_flux
        (respGrid jStar F) hq t F p q' hφ W
  · intro a
    simpa only [respCell] using
      memVectorL2_canonicalRespCoeffPlus_flux (respGrid jStar F) hq t F p q' a
  · simpa only [respCell] using hquad

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Cell averages of an arbitrary response maximizer and the canonical selection

For a coefficient field `b` that agrees almost everywhere on a Chapter-2 domain `U` with a field
`f` that is uniformly elliptic there, every response maximizer for the loads `p`, `q` has the
subcell averages of the doubled optimizer state of the Chapter-2 canonical maximizer for `f`.

The argument is that a response maximizer may be normalized to have mean zero without changing its
gradient, so it is a scalar canonical maximizer; Chapter-2 a.e. gradient uniqueness for response
maximizers (AK.HC (2.9)) then identifies its doubled optimizer state with that of the canonical
choice.  This is the step that makes the doubled optimizer state `X_t^\pm` entering the weak
quantity `W^\pm` of `e.response.weak.estimate` a function of the sample through the measurable
canonical selection alone, independently of the choice of maximizer.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- If `b` agrees almost everywhere on a Chapter-2 domain `U` with a field `f` that is uniformly
elliptic on `U`, then the cell average over any `V ⊆ U` of the doubled optimizer state of an
arbitrary response maximizer of the response functional for loads `p`, `q` equals the cell average
of the doubled optimizer state of the Chapter-2 canonical maximizer for `f`.

A response maximizer may be normalized to have mean zero without changing its gradient, so it
becomes a scalar canonical maximizer; Chapter-2 a.e. gradient uniqueness for response maximizers
(AK.HC (2.9)) then identifies its doubled optimizer state with that of the canonical choice.  This
is the form in which the doubled optimizer state `X_t^\pm` entering the weak quantity `W^\pm` of
`e.response.weak.estimate` is seen to be determined by the measurable canonical selection,
independently of the choice of maximizer. -/
theorem cellAverage_optimizerField_eq_canonical {d : ℕ} {U : Book.Ch02.Domain d}
    {V : Set (Vec d)} (hVU : V ⊆ (U : Set (Vec d)))
    {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (hbf : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (u : AHarmonicFunction b (U : Set (Vec d)))
    (hu : IsResponseMaximizer (U : Set (Vec d)) p q b u) :
    cellAverage V (optimizerField b u)
      = cellAverage V (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q))
            := by
  classical
  let v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b :=
    ScalarCanonicalMaximizer.ofIsResponseMaximizer u hu
  have hcanon : cellAverage V
        (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q)) =
      cellAverage V (optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) :=
    cellAverage_scalarCanonicalMaximizer_eq_canonicalOfAEEq hVU hlam hle hEll hbf p q v
  have hgrad :
      v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad = u.toH1.grad := by
    funext x
    exact AHarmonicFunction.grad_normalizeMeanZero u x
  have hfield : ∀ x, optimizerField b u x
      = optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction x := by
    intro x
    simp only [optimizerField, hgrad]
  have htransport : cellAverage V (optimizerField b u)
      = cellAverage V (optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) :=
    cellAverage_congr_ae hVU (Filter.Eventually.of_forall hfield)
  exact htransport.trans hcanon.symm

end

end HCPolySupport.HighContrast.Multiscale
end
