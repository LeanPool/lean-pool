/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.PolynomialEntry
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.HomogenizedBlockIdentification
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastComparison
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop211Rebase
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCorrectedEndpointAssembly
public import LeanPool.HighContrastHomogenization.Provider.Quenched.ThresholdCalibration

/-!
# High-contrast homogenization: Provider.Quenched.AlgebraicConvergenceAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Algebraic convergence at a polynomial scale

This module assembles `t.algebraic.convergence` from the pieces the provider
layer already carries: the polynomial entry generation, the triadic rebase, the
small-contrast endgame on the rebased law, the annealed endpoint on the original
indexing, and the identification of the limiting doubled block.

The two constants stand outside the law.  The exponent of the geometric decay
`e.algebraic.contrast.decay` is the one the small-contrast endgame fixes as soon
as the coarse-growth exponent is known, and the constant in the logarithmic
bound on the entry generation is the product of the rebase exponent with one
plus the delay exponent, that being the exponent at which the two polynomial
length accounts absorb.

The limiting doubled block is self-dual, hence the constant doubled block of a
coefficient matrix.  The first section reads the Schur coefficients of such a
block in the parametrization `e.annealed.schur`: they are `σ_* = σ = ` the
symmetric part of the coefficient matrix and `k = ` its antisymmetric part.  The
limiting block therefore satisfies `s_bar_* = s_bar`, with `s_bar` positive definite and
`k_bar` antisymmetric.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The Schur coefficients of a constant doubled block -/

/-- **The constant doubled block of a coefficient matrix is the assembled block
of its Schur data**, in the parametrization `e.annealed.schur`: the symmetric
part plays both `σ` and `σ_*`, and the antisymmetric part plays `k`. -/
theorem constantBlockMatrix_eq_blockMatrixOfCoarseMatrices (a : Mat d) :
    Book.Ch02.constantBlockMatrix a =
      Book.Ch02.blockMatrixOfCoarseMatrices
        { sigma := symmPart a
          sigmaStarInv := (symmPart a)⁻¹
          kappa := skewPart a } := rfl

/-- **The Schur block `σ_*` of a constant doubled block** is the symmetric part
of the coefficient matrix. -/
theorem schurSigmaStar_constantBlockMatrix {a : Mat d} (ha : (symmPart a).PosDef) :
    schurSigmaStar (Book.Ch02.constantBlockMatrix a) = symmPart a := by
  change ((symmPart a)⁻¹)⁻¹ = symmPart a
  exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef ha)

/-- **The Schur block `k` of a constant doubled block** is the antisymmetric part
of the coefficient matrix. -/
theorem schurSkew_constantBlockMatrix {a : Mat d} (ha : (symmPart a).PosDef) :
    schurSkew (Book.Ch02.constantBlockMatrix a) = skewPart a := by
  rw [constantBlockMatrix_eq_blockMatrixOfCoarseMatrices]
  exact schurSkew_blockMatrixOfCoarseMatrices
    (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_of_posDef ha))

/-- **The Schur block `σ` of a constant doubled block** is the symmetric part of
the coefficient matrix.  Together with the reading of `σ_*` this says that a
constant doubled block is self-dual. -/
theorem schurSigma_constantBlockMatrix {a : Mat d} (ha : (symmPart a).PosDef) :
    schurSigma (Book.Ch02.constantBlockMatrix a) = symmPart a := by
  rw [constantBlockMatrix_eq_blockMatrixOfCoarseMatrices]
  exact schurSigma_blockMatrixOfCoarseMatrices
    (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_of_posDef ha))

/-! ## The logarithmic reading of a polynomial length bound -/

/-- A triadic length bounded by a power of a positive base bounds the generation
by the ceiling of the corresponding base-three logarithm.  This is the
equivalence between the two readings of `e.algebraic.entry`. -/
theorem natCast_le_ceil_mul_logb_of_three_pow_le {b C : ℝ} (hb : 0 < b) {n : ℕ}
    (hn : (3 : ℝ) ^ n ≤ b ^ C) :
    (n : ℤ) ≤ ⌈C * Real.logb 3 b⌉ := by
  have hcast : (3 : ℝ) ^ ((n : ℕ) : ℝ) = (3 : ℝ) ^ (n : ℕ) := Real.rpow_natCast 3 n
  have hbase : b ^ C = (3 : ℝ) ^ (C * Real.logb 3 b) := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_logb (by norm_num) (by norm_num) hb]
  have hle : (3 : ℝ) ^ ((n : ℕ) : ℝ) ≤ (3 : ℝ) ^ (C * Real.logb 3 b) := by
    rw [hcast, ← hbase]
    exact hn
  have hexp : ((n : ℕ) : ℝ) ≤ C * Real.logb 3 b :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).mp hle
  exact_mod_cast hexp.trans (Int.le_ceil (C * Real.logb 3 b))

/-! ## The assembled theorem -/

/-- **Theorem `t.algebraic.convergence`: algebraic convergence at a polynomial
scale.**  For a dimension at least two and a coarse-growth exponent below one
there are a finite constant and a positive exponent, both standing outside the
law, the reference block, the gauge, its growth witness and the source variable,
such that under the standing assumptions there is a deterministic generation
bounded as in `e.algebraic.entry`, at which the contrast decay
`e.algebraic.contrast.decay` starts, together with a deterministic symmetric
positive definite doubled block obeying the two-sided comparison
`e.algebraic.block.decay`.  Its Schur coefficients, in the parametrization
`e.annealed.schur`, satisfy `s_bar_* = s_bar` with `s_bar` positive definite and `k_bar`
antisymmetric. -/
theorem algebraic_convergence_assembly (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∃ (m₀ : ℕ) (Abar : BlockMat d),
          (m₀ : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
          (∀ j : ℕ,
            annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
              (3 : ℝ) ^ (-κ * (j : ℝ))) ∧
          IsSymmetricBlockMat Abar ∧
          Book.Ch02.BlockPosDef Abar ∧
          (∀ j : ℕ,
            BlockMatLoewnerLE Abar
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ))) ∧
            BlockMatLoewnerLE
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ)))
              (blockScale (1 + 6 * (3 : ℝ) ^ (-κ * (j : ℝ))) Abar)) ∧
          schurSigmaStar Abar = schurSigma Abar ∧
          (schurSigma Abar).PosDef ∧
          IsSkewMat (schurSkew Abar) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨cSc, hcSc, alpha, Cdelay, halpha, hCdelay, hcore⟩ :=
    endpoint_hcore_body_corrected d hd g hg
  obtain ⟨deltaEntry, cEnd, hdeltaEntry, hcEnd, hcalibration⟩ :=
    exists_threshold_calibration_below cSc hcSc
  obtain ⟨cStar, hcStar, hEntry⟩ :=
    HCPoly.Frozen.polynomial_entry_random_source d hd cSc deltaEntry cEnd hcSc
      hdeltaEntry hcEnd hcalibration
  obtain ⟨Centry, hCentry, hEntry⟩ := hEntry g hg
  have hfactor : 1 < (1 + deltaEntry) ^ 2 := by
    nlinarith only [hdeltaEntry.1]
  have hEndOne : 0 < 1 + cEnd := by linarith only [hcEnd]
  have hstrict := mul_lt_mul_of_pos_right hfactor hEndOne
  have hcEndSc : cEnd < cSc := by
    nlinarith only [hstrict, hcalibration]
  have hcStarSc : cStar ∈ Set.Ioo 0 cSc :=
    ⟨hcStar.1, (hcStar.2.trans (min_le_right _ _)).trans_lt hcEndSc⟩
  have hcStarIoc : cStar ∈ Set.Ioc 0 cSc := ⟨hcStarSc.1, hcStarSc.2.le⟩
  obtain ⟨Crebase, hCrebase, -, hRebase⟩ :=
    exists_prop211_rebase_provider d hd hcStarSc hg hCentry
  have hdelayOne : (0 : ℝ) < 1 + Cdelay := by linarith only [hCdelay]
  refine ⟨Crebase * (1 + Cdelay), alpha, mul_pos hCrebase hdelayOne, halpha, ?_⟩
  intro P E Ψ K S hP hstationary hunit hdagger
  let : IsProbabilityMeasure P := hP
  obtain ⟨nBase, Pbase, gBase, Ebase, ΨBase, Kbase, Sbase,
    hgBase, hPbase, hstationaryBase, hunitBase, hdaggerBase,
    hentryBase, hcontrastBase, hcontrastCovariance, hblockCovariance,
    hnBase, hbaseCost⟩ :=
    hRebase P E Ψ K S hP hstationary hunit hdagger
      (hEntry P E Ψ K S hP hstationary hunit hdagger)
  have hbase : (1 : ℝ) ≤ 2 + aspectRatio E * K := by
    have hAspect : 1 ≤ aspectRatio E :=
      one_le_aspectRatio_of_coarseEllipticityDagger hdagger
    have hK : 1 ≤ K := hdagger.one_lt_growthWitness.le
    have hproduct : 1 ≤ aspectRatio E * K :=
      one_le_mul_of_one_le_of_one_le hAspect hK
    exact one_le_two.trans (le_add_of_nonneg_right (zero_le_one.trans hproduct))
  obtain ⟨m0, hdelay, hcontrastBaseDecay⟩ :=
    hcore cStar gBase Pbase Ebase ΨBase Kbase Sbase hcStarIoc hgBase hPbase
      hstationaryBase hunitBase hdaggerBase hentryBase hcontrastBase
  obtain ⟨Abar, Nann, hAbarSymm, hAbarPos, hNann, hcontrast, hblocks, hAbarEq⟩ :=
    exists_annealed_endpoint_of_rebased_contrast_decay hstationaryBase
      hdaggerBase hcontrastCovariance hblockCovariance hbase hnBase hbaseCost
      hCdelay le_rfl hdelay hcontrastBaseDecay
  obtain ⟨hlowerLimit, hupperLimit⟩ :=
    annealedLimitBlock_sandwich_of_covariance hstationary hdagger
      hstationaryBase hdaggerBase hblockCovariance
  have hlower : ∀ m : ℕ,
      BlockMatLoewnerLE Abar (annealedBlock P (centeredCube d (m : ℤ))) := by
    simpa only [hAbarEq] using hlowerLimit
  have hupper : ∀ m : ℕ,
      BlockMatLoewnerLE
        (blockSharp (annealedBlock P (centeredCube d (m : ℤ)))) Abar := by
    simpa only [hAbarEq] using hupperLimit
  obtain ⟨abar, habarPos, habarEq⟩ :=
    exists_homogenizedCoeffMatrix_of_annealedBlock_sandwich hAbarSymm hAbarPos
      hlower hupper halpha hcontrast
  refine ⟨Nann, Abar,
    natCast_le_ceil_mul_logb_of_three_pow_le
      (lt_of_lt_of_le zero_lt_one hbase) hNann,
    hcontrast, hAbarSymm, hAbarPos, hblocks, ?_, ?_, ?_⟩
  · rw [← habarEq, schurSigmaStar_constantBlockMatrix habarPos,
      schurSigma_constantBlockMatrix habarPos]
  · rw [← habarEq, schurSigma_constantBlockMatrix habarPos]
    exact habarPos
  · rw [← habarEq, schurSkew_constantBlockMatrix habarPos]
    exact matTranspose_skewPart abar

end

end Quenched
end HighContrast
end HCPolySupport
