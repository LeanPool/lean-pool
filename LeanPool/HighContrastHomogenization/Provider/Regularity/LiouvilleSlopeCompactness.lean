/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineAverageSlopeGoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleExcessSlopeSelection
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLocalCauchy

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleSlopeCompactness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Compactness of finite affine slopes in the Liouville endgame

This module converts vanishing weighted affine residuals on one fixed cube
into vanishing residual-gradient averages. Combined with the small-tail
average-slope coercivity estimate, this is the local compactness input for
selecting a limiting Liouville slope.
-/

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem euclideanNorm_add_le_compactness
    {d : ℕ} (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 (x + y)‖ ≤
    ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

/-- Vanishing finite affine excess admits boundary slopes whose actual
weighted residuals vanish, without assuming attainment of the infimum. -/
theorem exists_boundarySlopeSequence_residual_tendsto_zero
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (n : ℤ) (m : ℕ → ℤ) (hm : ∀ q, n ≤ m q)
    (u : ∀ q, Book.Ch03.CubeSolution (originCube d (m q)) a)
    (hexcess : Tendsto
      (fun q => finiteAffineGradientExcess a n (m q) (u q))
      atTop (nhds 0)) :
    ∃ e : ℕ → Vec d,
      Tendsto
        (fun q => weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ (u q).toH1.grad x -
            (finiteAffineSolution a (m q) (e q)).toH1.grad x))
        atTop (nhds 0) := by
  let epsilon : ℕ → ℝ≥0∞ := fun q => ((q + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hchoose : ∀ q, ∃ eq : Vec d,
      weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ (u q).toH1.grad x -
            (finiteAffineSolution a (m q) eq).toH1.grad x) <
        finiteAffineGradientExcess a n (m q) (u q) + epsilon q := by
    intro q
    exact exists_finiteAffineGradientExcess_candidate_lt_add
      a (hm q) (u q) (epsilon q) (by simp [epsilon])
  let e : ℕ → Vec d := fun q => Classical.choose (hchoose q)
  have he : ∀ q, weightedGradNorm
          (a.coeffOn (originCube d n)).toCoeffField
          (openCubeSet (originCube d n))
          (fun x ↦ (u q).toH1.grad x -
            (finiteAffineSolution a (m q) (e q)).toH1.grad x) ≤
        finiteAffineGradientExcess a n (m q) (u q) + epsilon q :=
    fun q => (Classical.choose_spec (hchoose q)).le
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto
      (fun q => finiteAffineGradientExcess a n (m q) (u q) + epsilon q)
      atTop (nhds 0) := by
    simpa only [zero_add] using hexcess.add hepsilon
  refine ⟨e, tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_⟩
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall he

/-- Vanishing weighted finite-affine residuals on a fixed cube force their
local Hilbert-gradient classes to converge to zero. -/
theorem tendsto_finiteAffineGradientResidual_localGradient_zero
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (n : ℕ) (m : ℕ → ℤ) (hm : ∀ j, (n : ℤ) ≤ m j)
    (u : ∀ j, Book.Ch03.CubeSolution (originCube d (m j)) a)
    (e : ℕ → Vec d)
    (hresidual : Tendsto
      (fun j => weightedGradNorm
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        (openCubeSet (originCube d (n : ℤ)))
        (fun x ↦ (u j).toH1.grad x -
          (finiteAffineSolution a (m j) (e j)).toH1.grad x))
      atTop (nhds 0)) :
    Tendsto
      (fun j => (finiteAffineGradientResidual a (hm j) (u j) (e j)).toH1
        |>.gradToHilbertVectorL2)
      atTop (nhds 0) := by
  let r : ℕ → Book.Ch03.CubeSolution (originCube d (n : ℤ)) a :=
    fun j => finiteAffineGradientResidual a (hm j) (u j) (e j)
  let E : ℕ → ℝ := fun j =>
    Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a (r j).toH1
  have henergyENN : Tendsto (fun j => ENNReal.ofReal (E j))
      atTop (nhds 0) := by
    convert hresidual using 1
    funext j
    rw [weightedGradNorm_finiteAffineGradientResidual a (hm j) (u j) (e j)]
  have henergy : Tendsto E atTop (nhds 0) := by
    have htoReal :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp henergyENN
    have hconvert : (ENNReal.toReal ∘ fun j => ENNReal.ofReal (E j)) = E := by
      funext j
      change (ENNReal.ofReal (E j)).toReal = E j
      rw [ENNReal.toReal_ofReal]
      dsimp only [E, Book.Ch03.h1EnergyNormOnCube]
      positivity
    rw [hconvert, ENNReal.toReal_zero] at htoReal
    exact htoReal
  let K : ℝ := Real.sqrt
    (cubeVolume (originCube d (n : ℤ)) /
      (a.coeffOn (originCube d (n : ℤ))).lam)
  have hnormBound : ∀ j,
      ‖(r j).toH1.gradToHilbertVectorL2‖ ≤ K * E j := by
    intro j
    simpa only [K, E] using
      norm_gradToHilbertVectorL2_le_sqrt_cubeVolume_div_lam_mul_of_weightedGradNorm_le
        (originCube d (n : ℤ)) a (r j).toH1 (E j)
        (by dsimp only [E, Book.Ch03.h1EnergyNormOnCube]; positivity)
        (by rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube])
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Eventually.of_forall fun j => norm_nonneg
      (r j).toH1.gradToHilbertVectorL2)
    (Eventually.of_forall hnormBound)
  simpa only [mul_zero] using tendsto_const_nhds.mul henergy

/-- Vanishing weighted finite-affine residuals on a fixed cube force the
ordinary averages of their gradients to vanish. -/
theorem tendsto_finiteAffineGradientResidual_cubeAverageVec_zero
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (n : ℕ) (m : ℕ → ℤ) (hm : ∀ j, (n : ℤ) ≤ m j)
    (u : ∀ j, Book.Ch03.CubeSolution (originCube d (m j)) a)
    (e : ℕ → Vec d)
    (hresidual : Tendsto
      (fun j => weightedGradNorm
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        (openCubeSet (originCube d (n : ℤ)))
        (fun x ↦ (u j).toH1.grad x -
          (finiteAffineSolution a (m j) (e j)).toH1.grad x))
      atTop (nhds 0)) :
    Tendsto
      (fun j => cubeAverageVec (originCube d (n : ℤ))
        (finiteAffineGradientResidual a (hm j) (u j) (e j)).toH1.grad)
      atTop (nhds 0) := by
  let r : ℕ → Book.Ch03.CubeSolution (originCube d (n : ℤ)) a :=
    fun j => finiteAffineGradientResidual a (hm j) (u j) (e j)
  let E : ℕ → ℝ := fun j =>
    Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a (r j).toH1
  have henergyENN : Tendsto (fun j => ENNReal.ofReal (E j))
      atTop (nhds 0) := by
    convert hresidual using 1
    funext j
    rw [weightedGradNorm_finiteAffineGradientResidual a (hm j) (u j) (e j)]
  have henergy : Tendsto E atTop (nhds 0) := by
    have htoReal :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp henergyENN
    have hconvert : (ENNReal.toReal ∘ fun j => ENNReal.ofReal (E j)) = E := by
      funext j
      change (ENNReal.ofReal (E j)).toReal = E j
      rw [ENNReal.toReal_ofReal]
      dsimp only [E, Book.Ch03.h1EnergyNormOnCube]
      positivity
    rw [hconvert, ENNReal.toReal_zero] at htoReal
    exact htoReal
  let K : ℝ := Real.sqrt
    (cubeVolume (originCube d (n : ℤ)) /
      (a.coeffOn (originCube d (n : ℤ))).lam)
  have hnormBound : ∀ j,
      ‖(r j).toH1.gradToHilbertVectorL2‖ ≤ K * E j := by
    intro j
    simpa only [K, E] using
      norm_gradToHilbertVectorL2_le_sqrt_cubeVolume_div_lam_mul_of_weightedGradNorm_le
        (originCube d (n : ℤ)) a (r j).toH1 (E j)
        (by dsimp only [E, Book.Ch03.h1EnergyNormOnCube]; positivity)
        (by
          rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube])
  have hnorm : Tendsto (fun j => ‖(r j).toH1.gradToHilbertVectorL2‖)
      atTop (nhds 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun j => norm_nonneg
        (r j).toH1.gradToHilbertVectorL2)
      (Eventually.of_forall hnormBound)
    simpa only [mul_zero] using tendsto_const_nhds.mul henergy
  have hclass : Tendsto (fun j => (r j).toH1.gradToHilbertVectorL2)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hnorm
  have havg := (continuous_localGradientClassAverage.tendsto 0).comp hclass
  have havg' : Tendsto
      (fun j => cubeAverageVec (originCube d (n : ℤ)) (r j).toH1.grad)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, localGradientClassAverage_zero] using
      havg.congr' (Eventually.of_forall fun j => by
        change localGradientClassAverage (r j).toH1.gradToHilbertVectorL2 = _
        rw [localGradientClassAverage_eq_cubeAverageVec_of_ae
          (r j).toH1.gradToHilbertVectorL2 (r j).toH1.grad
          (r j).toH1.coeFn_gradToHilbertVectorL2])
  simpa only [r] using havg'

/-- If exact realizations of one global gradient admit finite-affine
approximants with vanishing residual on a fixed cube, then their boundary
slopes are uniformly bounded under the small good-tail threshold. -/
theorem exists_uniform_euclideanBound_finiteAffineSlopes_of_residual_tendsto_zero
    {d : ℕ} [NeZero d] {s : ℝ}
    {a : Book.Ch02.TriadicCoeffFamily d} {delta c : ℝ} {n₀ : ℤ}
    (hthreshold : c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c → ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm e ≤ 2 * euclideanNorm
            (cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad))
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodTail a s delta n₀)
    (n : ℕ) (hn : n₀ ≤ (n : ℤ))
    (u : ∀ j : ℕ,
      Book.Ch03.CubeSolution (originCube d ((n + j + 2 : ℕ) : ℤ)) a)
    (Dv : Vec d → Vec d) (huGrad : ∀ j, (u j).toH1.grad = Dv)
    (e : ℕ → Vec d)
    (hresidual : Tendsto
      (fun j => weightedGradNorm
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        (openCubeSet (originCube d (n : ℤ)))
        (fun x ↦ (u j).toH1.grad x -
          (finiteAffineSolution a ((n + j + 2 : ℕ) : ℤ) (e j)).toH1.grad x))
      atTop (nhds 0)) :
    ∃ R : ℝ, ∀ j, euclideanNorm (e j) ≤ R := by
  let m : ℕ → ℤ := fun j => ((n + j + 2 : ℕ) : ℤ)
  have hnm : ∀ j, (n : ℤ) ≤ m j := by
    intro j
    dsimp only [m]
    omega
  let r : ℕ → Book.Ch03.CubeSolution (originCube d (n : ℤ)) a :=
    fun j => finiteAffineGradientResidual a (hnm j) (u j) (e j)
  let A : Vec d := cubeAverageVec (originCube d (n : ℤ)) Dv
  let ravg : ℕ → Vec d := fun j =>
    cubeAverageVec (originCube d (n : ℤ)) (r j).toH1.grad
  have hravg : Tendsto ravg atTop (nhds 0) := by
    simpa only [ravg, r, m] using
      tendsto_finiteAffineGradientResidual_cubeAverageVec_zero
        a n m hnm u e (by simpa only [m] using hresidual)
  have hrange : Bornology.IsBounded (Set.range ravg) :=
    Metric.isBounded_range_of_tendsto ravg hravg
  obtain ⟨B, hB⟩ := Metric.isBounded_range_iff.mp hrange
  let B₀ : ℝ := B + ‖ravg 0‖
  let R : ℝ := 2 * (euclideanNorm A + (d : ℝ) * B₀)
  refine ⟨R, ?_⟩
  intro j
  have hdesc : originCube d (n : ℤ) ∈
      descendantsAtDepth (originCube d (m j))
        (Int.toNat (m j - (n : ℤ))) :=
    originCube_mem_descendantsAtDepth_of_le (hnm j)
  have huMem : MemVectorL2 (cubeSet (originCube d (n : ℤ)))
      (u j).toH1.grad :=
    Book.Ch03.publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet
      (u j).toH1 hdesc
  have hwMem : MemVectorL2 (cubeSet (originCube d (n : ℤ)))
      (finiteAffineSolution a (m j) (e j)).toH1.grad :=
    Book.Ch03.publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet
      (finiteAffineSolution a (m j) (e j)).toH1 hdesc
  have havgResidual : ravg j = A -
      cubeAverageVec (originCube d (n : ℤ))
        (finiteAffineSolution a (m j) (e j)).toH1.grad := by
    dsimp only [ravg, r, A]
    rw [finiteAffineGradientResidual_grad,
      cubeAverageVec_sub (originCube d (n : ℤ)) _ _ huMem hwMem,
      huGrad j]
  have hwavg : cubeAverageVec (originCube d (n : ℤ))
      (finiteAffineSolution a (m j) (e j)).toH1.grad = A - ravg j := by
    rw [havgResidual]
    abel
  have hcoercive : euclideanNorm (e j) ≤ 2 * euclideanNorm
      (cubeAverageVec (originCube d (n : ℤ))
        (finiteAffineSolution a (m j) (e j)).toH1.grad) := by
    simpa only [m] using hthreshold.2 a delta n₀ hdelta hgood n j hn (e j)
  have hravgSup : ‖ravg j‖ ≤ B₀ := by
    calc
      ‖ravg j‖ = ‖(ravg j - ravg 0) + ravg 0‖ := by congr 1; abel
      _ ≤ ‖ravg j - ravg 0‖ + ‖ravg 0‖ := norm_add_le _ _
      _ ≤ B + ‖ravg 0‖ := by
        rw [← dist_eq_norm]
        exact add_le_add (hB j 0) le_rfl
      _ = B₀ := rfl
  have hravgEuclidean : euclideanNorm (ravg j) ≤ (d : ℝ) * B₀ := by
    calc
      euclideanNorm (ravg j) = ‖HilbertVec.ofVec (ravg j)‖ :=
        euclideanNorm_eq_norm_ofVec _
      _ ≤ (d : ℝ) * ‖ravg j‖ := HilbertVec.norm_ofVec_le_mul_norm _
      _ ≤ (d : ℝ) * B₀ :=
        mul_le_mul_of_nonneg_left hravgSup (by positivity)
  calc
    euclideanNorm (e j) ≤ 2 * euclideanNorm
        (cubeAverageVec (originCube d (n : ℤ))
          (finiteAffineSolution a (m j) (e j)).toH1.grad) := hcoercive
    _ = 2 * euclideanNorm (A - ravg j) := by rw [hwavg]
    _ ≤ 2 * (euclideanNorm A + euclideanNorm (ravg j)) := by
      have htri := euclideanNorm_add_le_compactness A (-ravg j)
      rw [euclideanNorm_neg] at htri
      exact mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ 2 * (euclideanNorm A + (d : ℝ) * B₀) := by gcongr
    _ = R := rfl

/-- A sequence of project vectors with a uniform explicit Euclidean bound
has a convergent subsequence in the native project-vector topology. -/
theorem exists_tendsto_subsequence_of_uniform_euclideanBound
    {d : ℕ} [NeZero d] (e : ℕ → Vec d)
    (hbound : ∃ R : ℝ, ∀ j, euclideanNorm (e j) ≤ R) :
    ∃ eLim : Vec d, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (e ∘ φ) atTop (nhds eLim) := by
  obtain ⟨R, hR⟩ := hbound
  have hmem : ∀ j, e j ∈ Metric.closedBall (0 : Vec d) R := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖e j‖ ≤ ‖HilbertVec.ofVec (e j)‖ :=
        HilbertVec.norm_le_norm_ofVec (e j)
      _ = euclideanNorm (e j) := (euclideanNorm_eq_norm_ofVec _).symm
      _ ≤ R := hR j
  obtain ⟨eLim, _heLim, φ, hφ, htendsto⟩ :=
    (isCompact_closedBall (0 : Vec d) R).tendsto_subseq hmem
  exact ⟨eLim, φ, hφ, htendsto⟩

end

end HighContrast
end HCPolySupport
