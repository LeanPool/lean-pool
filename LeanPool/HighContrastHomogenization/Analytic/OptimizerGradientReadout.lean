/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DoubledMinimizerReadouts
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu

/-!
# High-contrast homogenization: Analytic.OptimizerGradientReadout

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weighted readouts of the response optimizer state

The response optimizer of the variational coarse block of `s.introduction` is a
chosen maximizer of a variational problem whose admissible class is the
`a`-harmonic functions of the domain, a class that moves with the coefficient
field.  Its gradient and flux are nevertheless recovered from the minimizer of
the doubled variational
problem, whose admissible class is fixed: the gradient is the sum of the
potential component of the doubled minimizer and the lower component of its
coefficient-operator image, and the flux is the sum of the flux component and
the upper component of that image.

This file turns that recovery into a formula for the weighted coordinate
readouts of the doubled optimizer state.  For a fixed square-integrable weight
and a fixed doubled coordinate, the weighted integral of the corresponding
component of the optimizer state over the domain is the sum of an ambient inner
product of the doubled minimizer against a fixed test state and a fixed multiple
of the doubled energy pairing of the minimizer against the swapped test state.
Both are readouts of the doubled minimizer of the kind the selection theorem
makes measurable.
-/

namespace HCPolySupport
namespace HighContrast
namespace Selection

open MeasureTheory
open scoped Topology

noncomputable section

variable {d : ℕ}

/-! ## The ambient inner product of two block fields -/

/-- The ambient inner product of two block `L²` fields is the integral of their
pointwise doubled pairing. -/
theorem inner_toHilbertBlockL2OfBlockField_eq_integral {U : Set (Vec d)}
    {F G : Vec d → BlockVec d} (hF : MemBlockL2 U F) (hG : MemBlockL2 U G) :
    inner ℝ (toHilbertBlockL2OfBlockField (U := U) hF)
        (toHilbertBlockL2OfBlockField (U := U) hG) =
      ∫ x in U, blockVecDot (F x) (G x) ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := U) hF,
    coeFn_toHilbertBlockL2OfBlockField (U := U) hG] with x hx hy
  rw [hx, hy]
  simp [hilbertifyBlockField]

/-! ## The fixed test states of a weighted coordinate readout -/

/-- The test state pairing a weight against the potential component. -/
@[expose]
def gradTestState (eta : Vec d → ℝ) (i : Fin d) : BlockState d where
  potential := fun x => eta x • basisVec i
  flux := fun _ => 0

/-- The test state pairing a weight against the flux component. -/
@[expose]
def fluxTestState (eta : Vec d → ℝ) (i : Fin d) : BlockState d where
  potential := fun _ => 0
  flux := fun x => eta x • basisVec i

theorem memVectorL2_smul_basisVec {U : Set (Vec d)} {eta : Vec d → ℝ}
    (heta : MemScalarL2 U eta) (i : Fin d) :
    MemVectorL2 U (fun x => eta x • basisVec i) := by
  have hcomp :=
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec (d := d) i)).lipschitzWith).comp_memLp
      (by simp) heta
  simpa [Function.comp_def] using hcomp

theorem gradTestState_memBlockL2 {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {eta : Vec d → ℝ} (heta : MemScalarL2 U eta) (i : Fin d) :
    MemBlockL2 U (gradTestState eta i).eval :=
  MeasureTheory.MemLp.of_fst_snd
    ⟨memVectorL2_smul_basisVec heta i, MeasureTheory.memLp_const (0 : Vec d)⟩

theorem fluxTestState_memBlockL2 {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {eta : Vec d → ℝ} (heta : MemScalarL2 U eta) (i : Fin d) :
    MemBlockL2 U (fluxTestState eta i).eval :=
  MeasureTheory.MemLp.of_fst_snd
    ⟨MeasureTheory.memLp_const (0 : Vec d), memVectorL2_smul_basisVec heta i⟩

theorem blockVecDot_gradTestState (eta : Vec d → ℝ) (i : Fin d) (Z : BlockVec d)
    (x : Vec d) :
    blockVecDot ((gradTestState eta i).eval x) Z = eta x * Z.1 i := by
  simp [blockVecDot, gradTestState, BlockState.eval, vecDot, basisVec, Pi.single_apply,
    mul_ite, Finset.sum_ite_eq']

theorem blockVecDot_fluxTestState (eta : Vec d → ℝ) (i : Fin d) (Z : BlockVec d)
    (x : Vec d) :
    blockVecDot ((fluxTestState eta i).eval x) Z = eta x * Z.2 i := by
  simp [blockVecDot, fluxTestState, BlockState.eval, vecDot, basisVec, Pi.single_apply,
    mul_ite, Finset.sum_ite_eq']

/-- The fixed test state selecting one doubled coordinate against a weight. -/
@[expose]
def blockTestState (eta : Vec d → ℝ) : BlockCoord d → BlockState d
  | Sum.inl i => gradTestState eta i
  | Sum.inr i => fluxTestState eta i

theorem blockTestState_memBlockL2 {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {eta : Vec d → ℝ} (heta : MemScalarL2 U eta) (alpha : BlockCoord d) :
    MemBlockL2 U (blockTestState eta alpha).eval := by
  cases alpha with
  | inl i => exact gradTestState_memBlockL2 heta i
  | inr i => exact fluxTestState_memBlockL2 heta i

theorem blockVecDot_blockTestState (eta : Vec d → ℝ) (alpha : BlockCoord d)
    (Z : BlockVec d) (x : Vec d) :
    blockVecDot ((blockTestState eta alpha).eval x) Z = eta x * toFullBlockVec Z alpha := by
  cases alpha with
  | inl i => exact blockVecDot_gradTestState eta i Z x
  | inr i => exact blockVecDot_fluxTestState eta i Z x

/-! ## The doubled optimizer state -/

/-- The doubled state of the response optimizer: its gradient paired with its
flux. -/
@[expose]
def optimizerBlockState (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) : Vec d → BlockVec d :=
  fun x =>
    ((Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
      q).toSolution.toH1.grad x,
      matVecMul (aU.toCoeffField x)
        ((Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
          q).toSolution.toH1.grad x))

/-! ## The doubled minimizer of the paper's domain layer -/

private theorem isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) :
    IsPotentialZeroTraceOn U f := by
  rcases hf with ⟨_, phi, hphi⟩
  exact IsPotentialZeroTraceOn.congr_ae hphi.symm phi.isPotentialZeroTraceOn

/-- A doubled admissible field of the paper's domain layer is a block admissible
state of the variational layer. -/
theorem isBlockMuAdmissible_of_isDoubledMuAdmissible {U : Book.Ch02.Domain d}
    {P0 : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P0 X) :
    IsBlockMuAdmissible (U : Set (Vec d)) P0
      ({ potential := X.potential, flux := X.flux } : BlockState d) :=
  ⟨hX.1.1, isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn hX.1, hX.2.1, hX.2.2⟩

/-- **A pointwise doubled minimizer represents the Hilbert minimizer** of the
cell's doubled problem. -/
theorem toHilbertBlockL2_eq_minimizerMap_of_isDoubledMuMinimizer
    {U : Book.Ch02.Domain d} [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {k : ℕ} (hvol : 0 < (volume (U : Set (Vec d))).toReal)
    {aU : Book.Ch02.CoeffOn U}
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k aU.toCoeffField)
    (P0 : BlockVec d) {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU P0 X)
    (hAdm : IsBlockMuAdmissible (U : Set (Vec d)) P0
      ({ potential := X.potential, flux := X.flux } : BlockState d)) :
    toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hAdm.memBlockL2_eval =
      (cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap P0 := by
  have hEnergy :
      blockEnergyAverage (U : Set (Vec d)) aU.toCoeffField
          ({ potential := X.potential, flux := X.flux } : BlockState d) =
        Mu (U : Set (Vec d)) P0 aU.toCoeffField := by
    calc
      blockEnergyAverage (U : Set (Vec d)) aU.toCoeffField
            ({ potential := X.potential, flux := X.flux } : BlockState d)
          = Book.Ch02.doubledMuValue U aU X := rfl
      _ = Book.Ch02.doubledMu U aU P0 := hX.doubledMuValue_eq_doubledMu
      _ = Mu (U : Set (Vec d)) P0 aU.toCoeffField := Book.Ch02.doubledMu_eq_Mu U aU P0
  have hcorr :
      toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hAdm.memBlockL2_eval -
          (cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).constantField P0 ∈
        (cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).correctionSpace.correctionSpace := by
    rw [correctionSpace_cellMuHilbert, constantField_cellMuHilbert,
      hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add,
      add_sub_cancel_left]
    exact hAdm.toCorrectionFieldData_mem_correctionSpace
  have hQuad :
      quadraticEnergy (cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energyBilin
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hAdm.memBlockL2_eval) =
        Mu (U : Set (Vec d)) P0 aU.toCoeffField := by
    rw [energyBilin_cellMuHilbert, ← hEnergy]
    exact (cellMuSystem hvol
      ⟨aU.toCoeffField,
        hk⟩).toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
      hAdm.memBlockL2_eval
  refine (cellMuHilbert hvol ⟨aU.toCoeffField,
    hk⟩).eq_minimizerMap_of_quadraticEnergy_le_muCandidate
    P0 _ hcorr (le_of_eq ?_)
  rw [hQuad]
  exact mu_eq_muCandidate_cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩ P0

/-- **The doubled optimizer state is recovered from a doubled minimizer**: in
every doubled coordinate it is the corresponding component of the minimizer plus
the swapped component of its coefficient-operator image. -/
theorem ae_toFullBlockVec_optimizerBlockState {U : Book.Ch02.Domain d}
    {aU : Book.Ch02.CoeffOn U} (p q : Vec d) (alpha : BlockCoord d)
    {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU (-p, q) X) :
    (fun x => toFullBlockVec (optimizerBlockState U aU p q x) alpha)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x => toFullBlockVec (X.eval x) alpha +
      toFullBlockVec (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x))
        alpha.swap := by
  cases alpha with
  | inl i =>
      filter_upwards
        [Book.Ch02.doubledMuMinimizer_negLeft_eq_canonicalGradient U aU p q hX]
        with x hx
      show (optimizerBlockState U aU p q x).1 i = _
      rw [optimizerBlockState, ← hx]
      rfl
  | inr i =>
      filter_upwards
        [Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux U aU p q hX]
        with x hx
      show (optimizerBlockState U aU p q x).2 i = _
      rw [optimizerBlockState, ← hx]
      rfl

/-! ## Integrability of the doubled pairing integrand -/

/-- The doubled pairing integrand of two block `L²` states is integrable on a
quantitative ellipticity slice of the cell. -/
theorem integrableOn_blockPairingIntegrand_of_slice {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ} {a : CoeffField d}
    (hSlice : AEEQuantitativeEllipticSlice U k a) {X Y : BlockState d}
    (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) :
    IntegrableOn (blockPairingIntegrand a X Y) U := by
  have hrw : blockPairingIntegrand a X Y =
      fun x => ∑ alpha, ∑ beta,
        blockPairingEntryWeight X Y alpha beta x *
          toFullBlockMat (blockCoeffField a x) alpha beta := by
    funext x
    exact blockPairingIntegrand_eq_sum_entryWeights a X Y x
  rw [hrw]
  exact integrable_finsetSum _ fun alpha _ =>
    integrable_finsetSum _ fun beta _ =>
      hSlice.integrableOn_pairingWeightedFullBlockCoeffEntry_of_memBlockL2 hX hY alpha beta

/-! ## The weighted coordinate readout -/

/-- **The weighted coordinate readout of the doubled optimizer state is a
readout of the doubled minimizer.**  The weight and the coordinate enter only
through two fixed test states, and the coefficient field only through the
doubled problem. -/
theorem integral_weighted_optimizerBlockState
    {U : Book.Ch02.Domain d} [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {k : ℕ} (hvol : 0 < (volume (U : Set (Vec d))).toReal)
    {aU : Book.Ch02.CoeffOn U}
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k aU.toCoeffField)
    (p q : Vec d) (alpha : BlockCoord d) {eta : Vec d → ℝ}
    (heta : MemScalarL2 (U : Set (Vec d)) eta) :
    ∫ x in (U : Set (Vec d)), eta x *
        toFullBlockVec (optimizerBlockState U aU p q x) alpha ∂volume =
      inner ℝ
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
            (blockTestState_memBlockL2 heta alpha))
          ((cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) +
        (volume (U : Set (Vec d))).toReal *
          (cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (blockTestState_memBlockL2 heta alpha.swap))
            ((cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) := by
  classical
  obtain ⟨X, hX⟩ := (Book.Ch02.doubledMuTheory U aU).minimizer_exists (-p, q)
  have hAdm : IsBlockMuAdmissible (U : Set (Vec d)) (-p, q)
      ({ potential := X.potential, flux := X.flux } : BlockState d) :=
    isBlockMuAdmissible_of_isDoubledMuAdmissible hX.1
  have hXmem : MemBlockL2 (U : Set (Vec d))
      ({ potential := X.potential, flux := X.flux } : BlockState d).eval :=
    hAdm.memBlockL2_eval
  have hMin := toHilbertBlockL2_eq_minimizerMap_of_isDoubledMuMinimizer hvol hk (-p, q) hX hAdm
  have hstate := ae_toFullBlockVec_optimizerBlockState (aU := aU) p q alpha hX
  have hcoord : MemScalarL2 (U : Set (Vec d))
      (fun x => toFullBlockVec
        (({ potential := X.potential, flux := X.flux } : BlockState d).eval x) alpha) :=
    memScalarL2_fullBlockCoord_of_memBlockL2 hXmem alpha
  have hint1 : IntegrableOn (fun x => eta x *
      toFullBlockVec (X.eval x) alpha) (U : Set (Vec d)) :=
    MeasureTheory.MemLp.integrable_mul heta hcoord
  have hpairing := integrableOn_blockPairingIntegrand_of_slice hk
    (blockTestState_memBlockL2 heta alpha.swap) hXmem
  have hpairrw : blockPairingIntegrand aU.toCoeffField (blockTestState eta alpha.swap)
        ({ potential := X.potential, flux := X.flux } : BlockState d) =
      fun x => eta x *
        toFullBlockVec (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x))
          alpha.swap := by
    funext x
    exact blockVecDot_blockTestState eta alpha.swap _ x
  have hint2 : IntegrableOn (fun x => eta x *
      toFullBlockVec (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x))
        alpha.swap) (U : Set (Vec d)) := by
    rw [hpairrw] at hpairing
    exact hpairing
  have hsplit :
      ∫ x in (U : Set (Vec d)), eta x *
          toFullBlockVec (optimizerBlockState U aU p q x) alpha ∂volume =
        (∫ x in (U : Set (Vec d)), eta x * toFullBlockVec (X.eval x) alpha ∂volume) +
          ∫ x in (U : Set (Vec d)), eta x *
            toFullBlockVec (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x))
              alpha.swap ∂volume := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards [hstate] with x hx
    rw [hx, mul_add]
  rw [hsplit]
  congr 1
  · rw [← hMin, inner_toHilbertBlockL2OfBlockField_eq_integral]
    refine integral_congr_ae (_root_.Filter.Eventually.of_forall fun x => ?_)
    exact (blockVecDot_blockTestState eta alpha
      (({ potential := X.potential, flux := X.flux } : BlockState d).eval x) x).symm
  · have hbil :
        (cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (blockTestState_memBlockL2 heta alpha.swap))
            ((cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) =
          blockPairingAverage (U : Set (Vec d)) aU.toCoeffField
            (blockTestState eta alpha.swap)
            ({ potential := X.potential, flux := X.flux } : BlockState d) := by
      rw [← hMin, (cellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energySymm,
        energyBilin_cellMuHilbert]
      exact (cellMuSystem hvol
        ⟨aU.toCoeffField,
          hk⟩).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
        (blockTestState_memBlockL2 heta alpha.swap) hXmem
    rw [hbil, blockPairingAverage, volumeAverage, hpairrw, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hvol), one_mul]

/-! ## Measurability of the weighted coordinate readout -/

/-- **The weighted coordinate readout of the doubled optimizer state is a
measurable function of the sample**, on one quantitative ellipticity slice of
the cell and for any parameter space whose localized smooth entry tests are
measurable. -/
theorem measurable_integral_weighted_optimizerBlockState
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))] {k : ℕ}
    (hUopen : IsOpen (U : Set (Vec d))) (hUfin : volume (U : Set (Vec d)) ≠ ⊤)
    (hvol : 0 < (volume (U : Set (Vec d))).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
      Measurable fun w => entryTestR i j φ (A w))
    (aU : Om → Book.Ch02.CoeffOn U)
    (haU : ∀ w : Om, (aU w).toCoeffField = (A w).toFun)
    (p q : Vec d) (alpha : BlockCoord d) {eta : Vec d → ℝ}
    (heta : MemScalarL2 (U : Set (Vec d)) eta) :
    Measurable fun w : Om =>
      ∫ x in (U : Set (Vec d)), eta x *
        toFullBlockVec (optimizerBlockState U (aU w) p q x) alpha ∂volume := by
  have hk : ∀ w : Om,
      AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (aU w).toCoeffField := by
    intro w
    rw [haU w]
    exact hSlice w
  have hEqSlice : ∀ w : Om,
      (⟨(aU w).toCoeffField, hk w⟩ :
        {b : CoeffField d // AEEQuantitativeEllipticSlice (U : Set (Vec d)) k b}) =
      sliceOf hSlice w := fun w => Subtype.ext (haU w)
  have hrw : (fun w : Om =>
      ∫ x in (U : Set (Vec d)), eta x *
        toFullBlockVec (optimizerBlockState U (aU w) p q x) alpha ∂volume) =
      fun w : Om =>
        inner ℝ
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (blockTestState_memBlockL2 heta alpha))
            ((cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap (-p, q)) +
          (volume (U : Set (Vec d))).toReal *
            (cellMuHilbert hvol (sliceOf hSlice w)).energyBilin
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
                (blockTestState_memBlockL2 heta alpha.swap))
              ((cellMuHilbert hvol (sliceOf hSlice w)).minimizerMap (-p, q)) := by
    funext w
    rw [integral_weighted_optimizerBlockState hvol (hk w) p q alpha heta, hEqSlice w]
  rw [hrw]
  exact (measurable_inner_cellMuMinimizer hUopen hUfin hvol hSlice hEntry (-p, q) _).add
    ((measurable_energyBilin_cellMuMinimizer hUopen hUfin hvol hSlice hEntry (-p, q)
      (blockTestState_memBlockL2 heta alpha.swap)).const_mul _)

end

end Selection
end HighContrast
end HCPolySupport
