/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.PositiveSqrtCongruence
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Initial.GeometricMean
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.LoadMeanIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.RecenteredResponseIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CutoffDualityBoundInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.CutoffPairingCubeAverageIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.DualityBoundHypotheses
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.IntegratedWeakEnergyBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RandomToAnnealedRecentring
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback
public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure

/-!
# High-contrast homogenization: Entry.Response.Cutoff.PathwiseCutoffBoundReduction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pathwise cutoff bound, landed and reduced to integrability

This file proves the inequality half of the pathwise cutoff bound of
`e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)): pairing the centred pulled-back potential
against the pulled-back flux defect with the pulled-back cutoff weight field, it bounds the two
negative-Besov inputs by the scale-average seminorm of the `M_0^{1/2}`-transported, recentred
cell averages, and the four coefficients by the dimension and the grid data. It lands this
estimate as a single existential in the dimension: for every selected grid, response cutoff,
positive-definite block, and almost-everywhere elliptic coefficient, the pathwise cutoff pairing
bound holds on the adapted cell `respCell jStar F t`. It closes by reducing the resulting
pairing's integrability over the coefficient law to its measurability, since the bound dominates
the pairing, sample by sample, by a fixed multiple of the integrable scale-weighted squared
seminorm.
-/

section
/-!
## The inequality half of the pathwise cutoff bound

The negative-Besov duality bound of the cutoff argument (`AK.HC` Lemma A.1, (A.4)) pairs the
centred pulled-back potential against the pulled-back flux defect with the pulled-back cutoff
weight field.  Its two negative-Besov inputs are bounded by the scale-average seminorm of the
`M_0^{1/2}`-transported, recentred cell averages, and its four coefficients are bounded by the
cutoff class, the scale weights of the reference cube and the dimensional Frobenius product
`Frob₁ · Frob₂ ≤ 3 d²`.  The present file carries out the whole bookkeeping and concludes the
pathwise estimate `e.response.cutoff.estimate` in the exact shape consumed by the annealed
reduction: an explicit dimensional constant (depending only on the dimension and the universal
cutoff profile constant) times the scale weight `3^{-t}` times the square of the scale-average
seminorm of the recentred doubled optimizer state.

The constant is kept explicit and no existential is introduced.
-/

open HCPolySupport.HighContrast (matSqrt matSqrt_eq matSqrt_spec)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal

noncomputable section

/-- **The pathwise cutoff pairing bound in the shape of the annealed estimate.**  For a doubled
block `F` whose canonical metric is positive definite, a reference cube `Q = originCube d t`, a
cutoff `φ` in the response cutoff class, and a coefficient `b` that agrees almost everywhere on
the adapted cell with a uniformly elliptic field, the absolute cube average of the pulled-back
flux defect against the centred pulled-back potential times the pulled-back cutoff gradient is
bounded by an explicit dimensional constant times the scale weight `3^{-t}` times the square of
the scale-average seminorm of the recentred `M_0^{1/2}`-transported doubled optimizer state.  This
is the inequality half of the pathwise form of `e.response.cutoff.estimate`; it is the duality
bound `AK.HC` Lemma A.1, (A.4) with all four coefficient families and both negative-Besov inputs
discharged. -/
theorem abs_cubeAverage_pullback_pairing_le_besov_sq
    {d : ℕ} [NeZero d] {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {b : CoeffField d}
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff (respGrid jStar F) t φ) :
    |cubeAverage (originCube d t)
        (fun y => vecDot
          (matVecMul (respGrid jStar F)⁻¹
            ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
          (((respCenteredPullbackH1 hjStar hm t b u Y y
              - cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
            scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) y :
              Vec d)))| ≤
      (((2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          ((((d : ℝ) * HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)))) *
        (3 * (d : ℝ) ^ 2)) *
      ((3 : ℝ) ^ (-(t : ℝ)) *
        besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField b u) - Y)) ^ 2) := by
  classical
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ := hb
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  -- The pulled-back flux defect is square integrable on the reference cube.
  have hflux : MemLp (fun y => matVecMul (respGrid jStar F)⁻¹
      ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) 2
      (normalizedCubeMeasure (originCube d t)) :=
    memLp_two_pullback_flux_of_exists hq t ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ u Y
  -- The weight field and its three hypotheses.
  set ξ : Vec d → Vec d :=
    scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) with hξdef
  have hξcont : Continuous ξ := by
    rw [hξdef]
    exact continuous_pi (fun i => (contDiff_xi_of_isResponseCutoff hφ i).continuous)
  have hξLp : MemLp ξ ∞ (normalizedCubeMeasure (originCube d t)) := by
    rw [hξdef]
    exact memLp_top_normalizedCubeMeasure_of_norm_le (originCube d t)
      (by simpa only [hξdef] using hξcont.aestronglyMeasurable)
      (fun y => norm_xi_le_of_isResponseCutoff hφ y)
  have hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i) := by
    intro i
    rw [hξdef]
    exact contDiff_xi_of_isResponseCutoff hφ i
  set B : ℝ := 1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t)
    with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h3 : 0 < (3 : ℝ) ^ (-2 * t) := zpow_pos (by norm_num) _
    have hΘ : 0 ≤ responseCutoffProfileConst := responseCutoffProfileConst_pos.le
    positivity
  have hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet (originCube d t),
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B := by
    intro i z _
    rw [hξdef, hBdef]
    exact norm_fderiv_xi_le_of_isResponseCutoff hφ i z
  -- The scale-average seminorm of the recentred doubled optimizer state.
  set A : ℝ := besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField b u) - Y)) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact besovSeminorm_nonneg t _
  -- The two Frobenius factors of the metric pullback.
  set Frob₁ : ℝ := Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
      (matTranspose (respGrid jStar F) * (matSqrt (explicitCanonicalMetric F))⁻¹)) with hFrob1def
  set Frob₂ : ℝ := Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
      ((respGrid jStar F)⁻¹ * matSqrt (explicitCanonicalMetric F))) with hFrob2def
  have hFrob1nonneg : 0 ≤ Frob₁ := by rw [hFrob1def]; exact Real.sqrt_nonneg _
  have hFrob2nonneg : 0 ≤ Frob₂ := by rw [hFrob2def]; exact Real.sqrt_nonneg _
  -- `blockSqrt (respM0 F)` acts as the diagonal metric scaling.
  have hSS : matSqrt (explicitCanonicalMetric F) * matSqrt (explicitCanonicalMetric F) = explicitCanonicalMetric F :=
    (matSqrt_spec hm.posSemidef).2
  have hSmPD : (matSqrt (explicitCanonicalMetric F)).PosDef := HCPolySupport.HighContrast.posDef_matSqrt hm
  have hinv : (matSqrt (explicitCanonicalMetric F))⁻¹ * (matSqrt (explicitCanonicalMetric F))⁻¹ =
      (explicitCanonicalMetric F)⁻¹ := by
    rw [← Matrix.mul_inv_rev, hSS]
  have hdiag : toFullBlockMat (respM0 F) =
      Matrix.fromBlocks (explicitCanonicalMetric F) 0 0 (explicitCanonicalMetric F)⁻¹ := by
    ext (i | i) (j | j) <;> rfl
  have hBpsd : (Matrix.fromBlocks (matSqrt (explicitCanonicalMetric F)) 0 0
      (matSqrt (explicitCanonicalMetric F))⁻¹).PosSemidef := by
    let _ := hSmPD.isUnit.invertible
    exact (Matrix.PosDef.fromBlocks₁₁ (A := matSqrt (explicitCanonicalMetric F)) (0 : Mat d)
      ((matSqrt (explicitCanonicalMetric F))⁻¹) hSmPD).mpr (by simpa using hSmPD.inv.posSemidef)
  have hmat : matSqrt (toFullBlockMat (respM0 F)) =
      Matrix.fromBlocks (matSqrt (explicitCanonicalMetric F)) 0 0
        (matSqrt (explicitCanonicalMetric F))⁻¹ := by
    refine matSqrt_eq (respM0_full_posDef hm).posSemidef hBpsd ?_
    rw [hdiag, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hSS, hinv]
  have hsqrt_block : blockSqrt (respM0 F) =
      (⟨matSqrt (explicitCanonicalMetric F), 0, 0, (matSqrt (explicitCanonicalMetric F))⁻¹⟩ : BlockMat d) := by
    unfold blockSqrt
    rw [hmat]
    have hfull : toFullBlockMat (⟨matSqrt (explicitCanonicalMetric F), 0, 0,
        (matSqrt (explicitCanonicalMetric F))⁻¹⟩ : BlockMat d) =
        Matrix.fromBlocks (matSqrt (explicitCanonicalMetric F)) 0 0
          (matSqrt (explicitCanonicalMetric F))⁻¹ := by
      ext (i | i) (j | j) <;> rfl
    rw [← hfull, ofFullBlockMat_toFullBlockMat]
  have hscaled : ∀ Z : BlockVec d, blockMatVecMul (blockSqrt (respM0 F)) Z =
      (matVecMul (matSqrt (explicitCanonicalMetric F)) Z.1,
        matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ Z.2) := by
    intro Z
    rw [hsqrt_block]
    have hz1 : matVecMul (0 : Mat d) Z.2 = 0 := by funext i; simp [matVecMul]
    have hz2 : matVecMul (0 : Mat d) Z.1 = 0 := by funext i; simp [matVecMul]
    refine Prod.ext ?_ ?_
    · show matVecMul (matSqrt (explicitCanonicalMetric F)) Z.1 + matVecMul (0 : Mat d) Z.2 =
          matVecMul (matSqrt (explicitCanonicalMetric F)) Z.1
      rw [hz1, add_zero]
    · show matVecMul (0 : Mat d) Z.1 + matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ Z.2 =
          matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ Z.2
      rw [hz2, zero_add]
  -- The scale-average seminorm of the weak input is the target seminorm.
  have hfam : (fun x : Vec d =>
        (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
          matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2)) =
      fun x => blockMatVecMul (blockSqrt (respM0 F)) (optimizerField b u x - Y) := by
    funext x
    exact (hscaled (optimizerField b u x - Y)).symm
  have hAeq : besovSeminorm t (cellAverageFamily (respGrid jStar F) t (fun x =>
      (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
        matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2))) = A := by
    rw [hfam, hAdef]
    refine besovSeminorm_congr (fun n w hw => ?_)
    have hsub : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hfin : volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) ≠ ⊤ :=
      Geometry.volume_adaptedCellAtCenter_ne_top (respGrid jStar F) _ w
    have hvolr : (volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)).toReal =
        |(respGrid jStar F).det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
      rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (abs_nonneg _),
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
    have hvol : (volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)).toReal ≠ 0 := by
      rw [hvolr]
      have hdet : 0 < |(respGrid jStar F).det| :=
        abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp hq))
      positivity
    have : IsFiniteMeasure (volume.restrict (respCell jStar F t)) := by
      simpa [volumeMeasureOn] using!
        (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    obtain ⟨h1i, h2i⟩ :=
      memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u 0
    have h1i' : ∀ i, MemLp (fun x => (optimizerField b u x).1 i) 2
        (volume.restrict (respCell jStar F t)) := fun i => by
      simpa only [sub_zero] using! h1i i
    have h2i' : ∀ i, MemLp (fun x => (optimizerField b u x).2 i) 2
        (volume.restrict (respCell jStar F t)) := fun i => by
      simpa only [sub_zero] using! h2i i
    have hI1 : ∀ i, IntegrableOn (fun x => (optimizerField b u x).1 i)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun i => by
      have h : IntegrableOn (fun x => (optimizerField b u x).1 i) (respCell jStar F t) :=
        (h1i' i).integrable one_le_two
      exact h.mono_set hsub
    have hI2 : ∀ i, IntegrableOn (fun x => (optimizerField b u x).2 i)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun i => by
      have h : IntegrableOn (fun x => (optimizerField b u x).2 i) (respCell jStar F t) :=
        (h2i' i).integrable one_le_two
      exact h.mono_set hsub
    exact cellAverage_blockMatVecMul_sub_const hfin hvol (blockSqrt (respM0 F)) Y hI1 hI2
  -- The two negative-Besov inputs, rewritten with the target seminorm.
  have hgradWeak : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
      (respCenteredPullbackH1 hjStar hm t b u Y).grad ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A := by
    intro N
    have h := cubeBesov_respCenteredPullbackH1_grad_le hjStar hm t hEll hbf u Y N
    rw [hFrob1def]
    rwa [hAeq] at h
  have hfluxWeak : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
      (fun y => matVecMul (respGrid jStar F)⁻¹
        ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A := by
    intro N
    have h := cubeBesov_pullback_fluxDefect_le hjStar hm t hEll hbf u Y N
    rw [hFrob2def]
    rwa [hAeq] at h
  -- The duality bound at the pulled-back data.
  have hbridge := abs_cubeAverage_pullback_pairing_le (jStar := jStar) hjStar hm t b u Y
    (φ := φ) (B := B) (gradWeak := (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A)
    (fluxWeak := (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A)
    hB0 hξLp hξ hderiv hflux hgradWeak hfluxWeak
  -- The four coefficients of the duality bound.
  set gradCoeff : ℝ := 2 * cubeScaleFactor (originCube d t) * B + 3 *
      cubeLpNorm (originCube d t) ∞ ξ with hgcdef
  set fluxCoeff : ℝ :=
      ((Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) *
          (3 : ℝ) ^ ((d : ℝ) + 1)) * (Fintype.card (Fin d) : ℝ)) *
        ((Fintype.card (Fin d) : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + (1 - 1 / 2)) *
            cubeBesovScaleWeight (-(1 - 1 / 2 - 1 / 2)) (originCube d t))) with hfcdef
  set scaledGrad : ℝ := cubeBesovScaleWeight (-(1 / 2)) (originCube d t) *
      ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A) with hsgdef
  set scaledFlux : ℝ := cubeBesovScaleWeight (-(1 / 2)) (originCube d t) *
      ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A) with hsfdef
  set K : ℝ := 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
      96 * (d : ℝ) ^ 2 * responseCutoffProfileConst with hKdef
  set L : ℝ := ((((d : ℝ) * HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
      ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2))) with hLdef
  have hfluxCoeff_eq : fluxCoeff = L := by
    rw [hfcdef, hLdef]
    have hPc : Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) =
        (d : ℝ) * HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d := by
      simp only [Book.Ch01.Legacy.fullVectorPoincareConstant,
        HCPolySupport.fullVectorPoincareCubeConstant,
        HCPolySupport.cubeFullVectorPoincareUniformAnalyticConstant]
    rw [hPc]
    rw [show (Fintype.card (Fin d) : ℝ) = (d : ℝ) by simp]
    rw [show (-(1 - 1 / 2 - 1 / 2) : ℝ) = 0 by norm_num,
      cubeBesovScaleWeight_zero_originCube]
    rw [show (d : ℝ) + (1 - 1 / 2) = (d : ℝ) + 1 / 2 by norm_num]
    ring
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have hΘ : 0 < responseCutoffProfileConst := responseCutoffProfileConst_pos
    positivity
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    have hCZ : 0 ≤ HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d :=
      HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
    positivity
  have hgc0 : 0 ≤ gradCoeff := by
    rw [hgcdef]
    have hcs : 0 ≤ cubeScaleFactor (originCube d t) := by
      rw [cubeScaleFactor_originCube]
      exact Real.rpow_nonneg (by norm_num) _
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcs) hB0)
      (mul_nonneg (by norm_num) (cubeLpNorm_nonneg (originCube d t) ∞ ξ))
  have hfc0 : 0 ≤ fluxCoeff := hfluxCoeff_eq.symm ▸ hL0
  have hxiBound : cubeLpNorm (originCube d t) ∞ ξ ≤
      32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [hξdef]
    have hK0' : 0 ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by
      have hΘ : 0 < responseCutoffProfileConst := responseCutoffProfileConst_pos
      positivity
    have hpow : (3 : ℝ) ^ (-t) = (3 : ℝ) ^ (-(t : ℝ)) := by
      rw [← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    exact cubeLpNorm_top_le_of_norm_le (originCube d t) hK0'
      (fun y => by
        have h := norm_xi_le_of_isResponseCutoff hφ y
        rwa [hpow] at h)
  have hcancel : (3 : ℝ) ^ ((t : ℝ) / 2) * (3 : ℝ) ^ (-((t : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (t : ℝ) / 2 + -((t : ℝ) / 2) = 0 by ring, Real.rpow_zero]
  have hscaledGrad_eq : scaledGrad = Frob₁ * A := by
    rw [hsgdef, cubeBesovScaleWeight_neg_half_originCube]
    calc (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A)
        = ((3 : ℝ) ^ ((t : ℝ) / 2) * (3 : ℝ) ^ (-((t : ℝ) / 2))) * (Frob₁ * A) := by
          ring
      _ = Frob₁ * A := by rw [hcancel, one_mul]
  have hscaledFlux_eq : scaledFlux = Frob₂ * A := by
    rw [hsfdef, cubeBesovScaleWeight_neg_half_originCube]
    calc (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A)
        = ((3 : ℝ) ^ ((t : ℝ) / 2) * (3 : ℝ) ^ (-((t : ℝ) / 2))) * (Frob₂ * A) := by
          ring
      _ = Frob₂ * A := by rw [hcancel, one_mul]
  have hsg0 : 0 ≤ scaledGrad := hscaledGrad_eq.symm ▸ mul_nonneg hFrob1nonneg hA0
  have hsf0 : 0 ≤ scaledFlux := hscaledFlux_eq.symm ▸ mul_nonneg hFrob2nonneg hA0
  have hGf : Frob₁ * Frob₂ ≤ 3 * (d : ℝ) ^ 2 := by
    rw [hFrob1def, hFrob2def]
    exact explicitRoundedGrid_metricFrobenius_product_le jStar hjStar (explicitCanonicalMetric F) hm
  have hsplit : (3 : ℝ) ^ (t : ℝ) * (3 : ℝ) ^ (-2 * t) = (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hterm1 : 2 * (3 : ℝ) ^ (t : ℝ) * B =
      2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [hBdef]
    calc 2 * (3 : ℝ) ^ (t : ℝ) *
          (1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t))
        = 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 *
            ((3 : ℝ) ^ (t : ℝ) * (3 : ℝ) ^ (-2 * t)) := by ring
      _ = 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 *
            (3 : ℝ) ^ (-(t : ℝ)) := by rw [hsplit]
  have hterm2 : 3 * cubeLpNorm (originCube d t) ∞ ξ ≤
      96 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by
    calc 3 * cubeLpNorm (originCube d t) ∞ ξ
        ≤ 3 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ))) :=
          mul_le_mul_of_nonneg_left hxiBound (by norm_num)
      _ = 96 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by ring
  have hgradCoeffK : gradCoeff ≤ K * (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [hKdef]
    rw [hgcdef, cubeScaleFactor_originCube]
    calc 2 * (3 : ℝ) ^ (t : ℝ) * B + 3 * cubeLpNorm (originCube d t) ∞ ξ
        ≤ 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-(t : ℝ)) +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) :=
          add_le_add (le_of_eq hterm1) hterm2
      _ = (2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
            (3 : ℝ) ^ (-(t : ℝ)) := by ring
  -- Assemble: duality bound, then the constant arithmetic.
  have hbridge' : |cubeAverage (originCube d t)
      (fun y => vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (((respCenteredPullbackH1 hjStar hm t b u Y y
            - cubeAverage (originCube d t)
                (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
          scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) y :
            Vec d)))| ≤ (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) := by
    refine hbridge.trans_eq ?_
    simp only [hgcdef, hfcdef, hsgdef, hsfdef]
    ring
  have harith := mul_le_const_mul_rpow_mul_sq (d := d) t hA0 hFrob1nonneg hFrob2nonneg hK0 hL0
    hgc0 hfc0 hsg0 hsf0 hgradCoeffK hfluxCoeff_eq.le hscaledGrad_eq.le
    hscaledFlux_eq.le hGf
  have htarget : (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) =
      (((2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          ((((d : ℝ) * HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)))) *
        (3 * (d : ℝ) ^ 2)) *
      ((3 : ℝ) ^ (-(t : ℝ)) *
        besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField b u) - Y)) ^ 2) := by
    rw [hAdef, hKdef, hLdef]
  exact hbridge'.trans (harith.trans_eq htarget)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The pathwise cutoff pairing bound with every hypothesis discharged

The annealed cutoff bound `e.response.cutoff.estimate` is reduced by the frame theorems to the
deterministic pathwise estimate `hpath` on the adapted cell `respCell jStar F t`.  This file lands
that estimate as a single existential in the dimension: for every selected grid, every response
cutoff, every positive-definite block and every a.e.-elliptic representative of the coefficient,
the absolute volume average of the cutoff times the pairing of the centred doubled optimizer state
is at most a dimension-only constant times the scale weight `3 ^ (-t)` times the square of the
scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred state.

The volume average is first identified with the centred cube average on the reference cube by the
integration by parts of the cutoff pairing (`AK.HC` Lemma A.1, (A.4)), the change of variables
`x = (respGrid jStar F) y` and the vanishing of the flux defect against the cutoff gradient; the
resulting cube average is then bounded by the negative-Besov duality bound with all four
coefficient families discharged.  The integrability side conditions of the identification are
supplied here: the flux defect against the cutoff gradient is `L²` on the reference cube because
the flux defect is `L²` and the cutoff gradient is essentially bounded, the centred potential
multiplied by that pairing is integrable because the pulled-back potential is `L²`, and the
centred-potential pairing on the cell is its change of variables.  The constant is the explicit
dimension-only constant of `abs_cubeAverage_pullback_pairing_le_besov_sq`, so it depends on no
other datum.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The pathwise cutoff pairing bound `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4)) with
every hypothesis discharged, in the exact shape of the `hpath` hypothesis of
`exists_integral_abs_pairing_le_respWeak_of_pathwise`.  There is a dimension-only constant `C₀`
such that, for every grid depth `jStar`, block `F`, scale `t`, response cutoff `φ`, positive
definite canonical metric, coefficient `b` with an a.e.-elliptic representative on the adapted
cell and `b`-harmonic optimizer `u`, the absolute volume average on `respCell jStar F t` of the
cutoff times the pairing of the centred doubled optimizer state with `Y` is at most `C₀` times the
scale weight `3 ^ (-t)` times the square of the scale-average seminorm of the `M_0 ^ (1/2)`-scaled
recentred state. -/
theorem exists_pathwise_cutoff_pairing_bound (d : ℕ) [NeZero d] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ),
        2 * d ≤ 3 ^ jStar → IsResponseCutoff (respGrid jStar F) t φ →
        (explicitCanonicalMetric F).PosDef →
        ∀ (b : CoeffField d) (Y : BlockVec d)
          (u : AHarmonicFunction b (respCell jStar F t)),
          (∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
            IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
              b =ᵐ[volumeMeasureOn (respCell jStar F t)] f) →
          |volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))| ≤
            C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                  (optimizerField b u) - Y)) ^ 2) := by
  set C₀ : ℝ :=
    (((2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
        96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
      ((((d : ℝ) * HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
        ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)))) *
      (3 * (d : ℝ) ^ 2)) with hC₀def
  have hC₀ : 0 ≤ C₀ := by
    rw [hC₀def]
    have hΘ : 0 ≤ responseCutoffProfileConst := responseCutoffProfileConst_pos.le
    have hΘ2 : 0 ≤ responseCutoffProfileConst ^ 2 := sq_nonneg _
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hCZ : 0 ≤ HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d :=
      HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
    have hp1 : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
    have hp2 : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1 / 2) := Real.rpow_nonneg (by norm_num) _
    have hA : 0 ≤ 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
        96 * (d : ℝ) ^ 2 * responseCutoffProfileConst :=
      add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hd 4)) hΘ2)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hd 2)) hΘ)
    have hB : 0 ≤ (((d : ℝ) *
          HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
          ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hd hCZ) hp1) hd)
        (mul_nonneg hd hp2)
    exact mul_nonneg (mul_nonneg hA hB)
      (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ)))
  refine ⟨C₀, hC₀, ?_⟩
  intro jStar F t φ hjStar hφ hm b Y u hb
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  set fl : Vec d → Vec d := fun y => matVecMul (respGrid jStar F)⁻¹
    ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2) with hfl
  set ξ : Vec d → Vec d :=
    scalarCutoffGradientField (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) with hξdef
  set w : Vec d → ℝ := (respCenteredPullbackH1 hjStar hm t b u Y).toFun with hw
  set g : Vec d → ℝ := fun x =>
    (u.toH1.toFun x - vecDot Y.1 x) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j)) with hg
  -- Square integrability of the pulled-back flux and of the cutoff gradient.
  have hflux : MemLp fl 2 (normalizedCubeMeasure (originCube d t)) := by
    simpa only [hfl] using! memLp_two_pullback_flux_of_exists hq t hb u Y
  have hξLp : MemLp ξ ∞ (normalizedCubeMeasure (originCube d t)) := by
    simpa only [hξdef] using memLp_top_xi_of_isResponseCutoff (respGrid jStar F) hφ
  have hξ2 : MemLp ξ 2 (normalizedCubeMeasure (originCube d t)) :=
    hξLp.mono_exponent le_top
  -- The normalized cube measure is a finite nonzero multiple of the restricted volume.
  have hc0 : ENNReal.ofReal ((cubeVolume (originCube d t))⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos (originCube d t)))
  have hctop : ENNReal.ofReal ((cubeVolume (originCube d t))⁻¹) ≠ ∞ := ENNReal.ofReal_ne_top
  -- Integrability on the reference cube of the flux defect against the cutoff gradient.
  have hcube_mu : Integrable (fun y => vecDot (fl y) (ξ y))
      (normalizedCubeMeasure (originCube d t)) := by
    have hsum := integrable_finsetSum (Finset.univ)
      (fun i _ => (hflux.eval i).integrable_mul (hξ2.eval i))
    simpa only [vecDot] using! hsum
  have hcube : IntegrableOn (fun y => vecDot (fl y) (ξ y)) (cubeSet (originCube d t)) := by
    show Integrable (fun y => vecDot (fl y) (ξ y))
      (volume.restrict (cubeSet (originCube d t)))
    have h := hcube_mu
    rw [normalizedCubeMeasure, cubeMeasure] at h
    exact (integrable_smul_measure hc0 hctop).mp h
  -- The pulled-back centred potential is `L²` on the reference cube.
  have hw_open : MemLp w 2 (volume.restrict (openCubeSet (originCube d t))) := by
    simpa only [hw] using (respCenteredPullbackH1 hjStar hm t b u Y).memL2
  have hw_vol : MemLp w 2 (volume.restrict (cubeSet (originCube d t))) := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d t)]
    exact hw_open
  have hw_mu : MemLp w 2 (normalizedCubeMeasure (originCube d t)) := by
    rw [normalizedCubeMeasure, cubeMeasure]
    exact hw_vol.smul_measure ENNReal.ofReal_ne_top
  -- Integrability on the reference cube of the centred potential times the pairing.
  have hcubeProd_mu : Integrable (fun y => w y * vecDot (fl y) (ξ y))
      (normalizedCubeMeasure (originCube d t)) := by
    have hterm : ∀ i : Fin d, Integrable (fun y => ξ y i * (fl y i * w y))
        (normalizedCubeMeasure (originCube d t)) := by
      intro i
      exact ((hflux.eval i).integrable_mul hw_mu).mul_of_top_right (hξLp.eval i)
    have hsum := integrable_finsetSum (Finset.univ) (fun i _ => hterm i)
    refine hsum.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hcubeProd : IntegrableOn (fun y => w y * vecDot (fl y) (ξ y))
      (cubeSet (originCube d t)) := by
    show Integrable (fun y => w y * vecDot (fl y) (ξ y))
      (volume.restrict (cubeSet (originCube d t)))
    have h := hcubeProd_mu
    rw [normalizedCubeMeasure, cubeMeasure] at h
    exact (integrable_smul_measure hc0 hctop).mp h
  -- The two pairings on the cell are the change of variables of the cube pairings.
  have hgcomp : IntegrableOn (fun y => g (matVecMul (respGrid jStar F) y))
      (openCubeSet (originCube d t)) := by
    have hcp : Integrable (fun y => w y * vecDot (fl y) (ξ y))
        (volume.restrict (openCubeSet (originCube d t))) := by
      have h : Integrable (fun y => w y * vecDot (fl y) (ξ y))
          (volume.restrict (cubeSet (originCube d t))) := hcubeProd
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d t)] at h
      exact h
    refine hcp.congr (Filter.Eventually.of_forall (fun y => ?_))
    have hwv : w y = u.toH1.toFun (matVecMul (respGrid jStar F) y)
        - vecDot Y.1 (matVecMul (respGrid jStar F) y) := by
      rw [hw]
      exact congrFun (respCenteredPullbackH1_toFun hjStar hm t b u Y) y
    have hvd := vecDot_pullback_slots hq (φ := φ) hφ.contDiff
      (matVecMul (b (matVecMul (respGrid jStar F) y))
        (u.toH1.grad (matVecMul (respGrid jStar F) y)) - Y.2) y
    have hscg : (fun j : Fin d =>
          (fderiv ℝ φ (matVecMul (respGrid jStar F) y)) (basisVec j))
        = scalarCutoffGradientField φ (matVecMul (respGrid jStar F) y) := by
      funext j
      exact (scalarCutoffGradientField_apply φ (matVecMul (respGrid jStar F) y) j).symm
    simp only [hg, hfl, hξdef, hwv, hscg, optimizerField, Prod.snd_sub]
    exact congrArg (fun s => (u.toH1.toFun (matVecMul (respGrid jStar F) y)
      - vecDot Y.1 (matVecMul (respGrid jStar F) y)) * s) hvd
  have hint2 : IntegrableOn g (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have hemb := measurableEmbedding_matVecMul hq
    have hmap := map_matVecMul_volume_restrict hq (openCubeSet (originCube d t))
    have h1 : Integrable g
        (Measure.map (matVecMul (respGrid jStar F))
          (volume.restrict (openCubeSet (originCube d t)))) :=
      (hemb.integrable_map_iff).mpr hgcomp
    rw [hmap, image_openCubeSet_originCube_eq_adaptedCell (respGrid jStar F) t] at h1
    have hdet : 0 < |(respGrid jStar F).det|⁻¹ :=
      inv_pos.mpr (abs_pos.mpr
        ((Matrix.isUnit_iff_isUnit_det (A := respGrid jStar F)).mp hq |>.ne_zero))
    exact (integrable_smul_measure (c := ENNReal.ofReal |(respGrid jStar F).det|⁻¹)
      (ENNReal.ofReal_ne_zero_iff.mpr hdet) ENNReal.ofReal_ne_top).mp h1
  -- The remaining cell pairing and the flux integrability, from the elliptic representative.
  have hfluxCell : MemVectorL2 (respCell jStar F t)
      (fun x => matVecMul (b x) (u.toH1.grad x)) :=
    memVectorL2_flux_of_exists hq t hb u
  have hint1 : IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (HighContrast.adaptedCell (respGrid jStar F) t) :=
    cutoffPairingIntegrability_of_inputs hjStar hm hφ hb u Y
  -- The identity converting the volume average to the centred cube average.
  have hid := volumeAverage_cutoff_pairing_eq_neg_cubeAverage_centered
    (jStar := jStar) (F := F) hjStar hm t (b := b) u Y
    hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset hfluxCell hint1
    (by simpa only [hg] using hint2)
    (by simpa only [hfl, hξdef] using! hcube)
    (by simpa only [hw, hfl, hξdef] using! hcubeProd)
  -- The negative-Besov duality bound with all coefficients discharged.
  have hbnd := abs_cubeAverage_pullback_pairing_le_besov_sq
    (jStar := jStar) (F := F) hjStar hm t hb u Y hφ
  calc
    |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))|
        = |cubeAverage (originCube d t) (fun y => vecDot
            (matVecMul (respGrid jStar F)⁻¹
              ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
            (((respCenteredPullbackH1 hjStar hm t b u Y y -
                cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
              scalarCutoffGradientField
                (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y : Vec d)))| := by
          rw [show volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
              = _ from hid]
          exact abs_neg _
    _ ≤ C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField b u) - Y)) ^ 2) := by
          rw [hC₀def]
          exact hbnd

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Integrability of the cutoff pairing, reduced to its measurability

The pathwise cutoff pairing bound `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4)) dominates
the absolute cutoff pairing, sample by sample, by a fixed multiple of the scale-weighted squared
scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred optimizer state.  Consequently the
pairing is integrable over the law as soon as it is measurable and that seminorm square is
integrable, which isolates measurability as the only remaining obstruction to the integrability
premise of the cutoff rows.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing is `P`-integrable whenever it is `P`-a.e.-strongly measurable and the
scale-weighted squared scale-average seminorm of the `M_0 ^ (1/2)`-scaled recentred optimizer state
is `P`-integrable.  The pathwise bound `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4))
dominates the absolute pairing by a fixed multiple of that seminorm square, so the finite-integral
half of `Integrable` follows by domination, while the measurability half is supplied as the
hypothesis.  The elliptic-representative hypothesis on the coefficient family is exactly the
hypothesis consumed by the pathwise bound, and no further regularity of the pairing is required. -/
theorem integrable_abs_pairing_of_measurable_of_integrable_besov {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (hm : (explicitCanonicalMetric F).PosDef)
    (c : CoeffSpace d → CoeffField d)
    (hc : ∀ a, ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        c a =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (Y : BlockVec d) (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hmeas : AEStronglyMeasurable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P)
    (hbesov : Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField (c a) (u a)) - Y)) ^ 2) P) :
    Integrable (fun a => |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField (c a) (u a) x).1 - Y.1)
          ((optimizerField (c a) (u a) x).2 - Y.2))|) P := by
  obtain ⟨C₀, _, hpath⟩ := exists_pathwise_cutoff_pairing_bound d
  refine ⟨hmeas, HasFiniteIntegral.mono'
    (((hbesov.const_mul ((3 : ℝ) ^ (-(t : ℝ)))).const_mul C₀).hasFiniteIntegral) ?_⟩
  filter_upwards with a
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  exact hpath jStar F t φ hjStar hφ hm (c a) Y (u a) (hc a)

end

end HCPolySupport.HighContrast.Multiscale
end
