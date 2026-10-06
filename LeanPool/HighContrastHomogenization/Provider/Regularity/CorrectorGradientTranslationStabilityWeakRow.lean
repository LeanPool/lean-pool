/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeTranslationDualTest
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGradientCubeIntegralTranslationStability
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.CaccioppoliBridge
public import LeanPool.HighContrastHomogenization.Support.Deterministic.HomogenizationBlackBoxes.DualityExponentLoss
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorGradientTranslationStabilityWeakRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Corrector-gradient translation stability from the weak corrector row

The average of a corrector gradient over a centered triadic cube and its average
over a fixed displacement of that cube are compared by pairing the field against
the displaced-cube test on the parent cube.  The pairing is exactly the
difference of the two averages, and it is bounded by the field's scale
normalized negative Besov norm times the test's positive Besov norm.  The latter
is proportional to the square root of the relative displacement, which tends to
zero along the centered exhaustion, so one scale-uniform bound for the weak row
already gives translation stability of the averages.

The row is read on the affine-plus-corrector field rather than on the corrector
gradient alone; the two differ by a constant, which cancels in the difference of
averages.
-/

namespace HCPolySupport
namespace HighContrast

open _root_.Filter MeasureTheory Set

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- For an integrable vector field, the coordinatewise cube average is its
Bochner integral against normalized cube measure. -/
theorem cubeAverageVec_eq_integral_normalizedCubeMeasure_of_integrable
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : Integrable F (normalizedCubeMeasure Q)) :
    cubeAverageVec Q F = ∫ x, F x ∂normalizedCubeMeasure Q := by
  funext i
  rw [cubeAverageVec, cubeAverage_eq_integral_normalizedCubeMeasure]
  simpa only [ContinuousLinearMap.proj_apply] using
    (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).integral_comp_comm hF

/-! ## The pairing identity -/

theorem integrableOn_cubeSet_of_memLp_two (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn f (cubeSet Q) volume := by
  have hint : Integrable f (normalizedCubeMeasure Q) := hf.integrable (by norm_num)
  rw [normalizedCubeMeasure, cubeMeasure] at hint
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 (cubeVolume_pos Q)
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hint

/-- Pairing a field against the displaced-cube test on the parent cube returns
exactly the difference between its average over the cube and its average over
the displaced cube. -/
theorem cubeBesovPairing_cubeTranslationTest (d n : ℕ) (t : Vec d)
    (f : Vec d → ℝ)
    (hf : IntegrableOn f (cubeSet (originCube d ((n + 1 : ℕ) : ℤ))) volume)
    (hsubT : translatedCubeSet (originCube d (n : ℤ)) t ⊆
      cubeSet (originCube d ((n + 1 : ℕ) : ℤ))) :
    cubeBesovPairing (originCube d ((n + 1 : ℕ) : ℤ)) f (cubeTranslationTest d n t) =
      cubeAverage (originCube d (n : ℤ)) f -
        cubeAverage (originCube d (n : ℤ)) (fun y => f (y + t)) := by
  have hsubA : cubeSet (originCube d (n : ℤ)) ⊆
      cubeSet (originCube d ((n + 1 : ℕ) : ℤ)) := cubeSet_originCube_subset_succ d n
  have hprod : ∀ x, f x * cubeTranslationTest d n t x =
      (3 : ℝ) ^ d * ((cubeSet (originCube d (n : ℤ))).indicator f x -
        (translatedCubeSet (originCube d (n : ℤ)) t).indicator f x) := by
    intro x
    have hval : ∀ S : Set (Vec d),
        f x * S.indicator (fun _ => (1 : ℝ)) x = S.indicator f x := by
      intro S
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    simp only [cubeTranslationTest, cubeIndicatorDifference]
    calc
      f x * ((3 : ℝ) ^ d *
          ((cubeSet (originCube d (n : ℤ))).indicator (fun _ => (1 : ℝ)) x -
            (translatedCubeSet (originCube d (n : ℤ)) t).indicator
              (fun _ => (1 : ℝ)) x))
          = (3 : ℝ) ^ d *
            (f x * (cubeSet (originCube d (n : ℤ))).indicator (fun _ => (1 : ℝ)) x -
              f x * (translatedCubeSet (originCube d (n : ℤ)) t).indicator
                (fun _ => (1 : ℝ)) x) := by ring
      _ = (3 : ℝ) ^ d *
            ((cubeSet (originCube d (n : ℤ))).indicator f x -
              (translatedCubeSet (originCube d (n : ℤ)) t).indicator f x) := by
            rw [hval, hval]
  have hI1 : IntegrableOn ((cubeSet (originCube d (n : ℤ))).indicator f)
      (cubeSet (originCube d ((n + 1 : ℕ) : ℤ))) volume :=
    hf.indicator (measurableSet_cubeSet _)
  have hI2 : IntegrableOn
      ((translatedCubeSet (originCube d (n : ℤ)) t).indicator f)
      (cubeSet (originCube d ((n + 1 : ℕ) : ℤ))) volume :=
    hf.indicator (measurableSet_translatedCubeSet _ _)
  have hsplit : ∫ x in cubeSet (originCube d ((n + 1 : ℕ) : ℤ)),
        f x * cubeTranslationTest d n t x ∂volume =
      (3 : ℝ) ^ d *
        ((∫ x in cubeSet (originCube d (n : ℤ)), f x ∂volume) -
          ∫ x in translatedCubeSet (originCube d (n : ℤ)) t, f x ∂volume) := by
    rw [setIntegral_congr_fun (measurableSet_cubeSet _) fun x _ => hprod x,
      integral_const_mul, integral_sub hI1 hI2,
      setIntegral_indicator (measurableSet_cubeSet _),
      setIntegral_indicator (measurableSet_translatedCubeSet _ _),
      Set.inter_eq_self_of_subset_right hsubA,
      Set.inter_eq_self_of_subset_right hsubT]
  have htrans : ∫ x in translatedCubeSet (originCube d (n : ℤ)) t, f x ∂volume =
      ∫ y in cubeSet (originCube d (n : ℤ)), f (y + t) ∂volume :=
    (setIntegral_comp_addRight_translateSet t (cubeSet (originCube d (n : ℤ))) f).symm
  have hvolQ : cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)) =
      ((3 : ℝ) ^ (n + 1)) ^ d := by
    rw [cubeVolume, cubeScaleFactor_originCube, zpow_natCast]
  have hvolA : cubeVolume (originCube d (n : ℤ)) = ((3 : ℝ) ^ n) ^ d := by
    rw [cubeVolume, cubeScaleFactor_originCube, zpow_natCast]
  have hratio : (3 : ℝ) ^ d * (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)))⁻¹ =
      (cubeVolume (originCube d (n : ℤ)))⁻¹ := by
    rw [hvolQ, hvolA, pow_succ, mul_pow]
    have h1 : ((3 : ℝ) ^ n) ^ d ≠ 0 := by positivity
    have h2 : ((3 : ℝ) ^ d) ≠ 0 := by positivity
    field_simp
  rw [cubeBesovPairing, cubeAverage, hsplit, htrans, cubeAverage, cubeAverage,
    ← hratio]
  ring

/-! ## The pairing bound -/

private theorem memLp_component (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) (i : Fin d) :
    MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  refine MemLp.mono hF
    ((continuous_apply i).comp_aestronglyMeasurable hF.aestronglyMeasurable) ?_
  filter_upwards with x
  exact norm_le_pi_norm (F x) i

private theorem dualLocalMemLpGlobal_cubeTranslationTest (d n : ℕ) (t : Vec d)
    (Q : TriadicCube d) :
    CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (cubeTranslationTest d n t) := by
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  intro _j R _hR
  have hfluct : cubeFluctuation R (cubeTranslationTest d n t) =
      fun x => cubeTranslationTest d n t x -
        cubeAverage R (cubeTranslationTest d n t) := rfl
  rw [hconj, hfluct]
  exact (memLp_cubeTranslationTest d n t R (2 : ℝ≥0∞)).sub (memLp_const _)

/-- One scale-uniform bound for the weak corrector row controls the difference
between the average of a field over a centered cube and its average over a fixed
displacement of that cube. -/
theorem norm_cubeAverageVec_translate_sub_le_of_weakRow (d : ℕ) [NeZero d]
    (n : ℕ) (F : Vec d → Vec d) (t : Vec d) {s : ℝ} (hs : 0 < s) (hs2 : s < 1 / 2)
    {W : ℝ} (hW : 0 ≤ W) (hWle : W ≤ (3 : ℝ) ^ n) (htW : ∀ i, |t i| ≤ W)
    {J : ℕ} (hJ : 1 ≤ J) {N : ℝ}
    (hmem : MemLp F (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d ((n + 1 : ℕ) : ℤ))))
    (hrow : cubeScaleNormalizedDualNegativeBesovVectorNormTwo
      (originCube d ((n + 1 : ℕ) : ℤ)) s F ≤ N) :
    ‖cubeAverageVec (originCube d (n : ℤ)) (fun x => F (x + t)) -
        cubeAverageVec (originCube d (n : ℤ)) F‖ ≤
      N * cubeTranslationTestBound d n s W J := by
  set Q : TriadicCube d := originCube d ((n + 1 : ℕ) : ℤ) with hQ
  set A : TriadicCube d := originCube d (n : ℤ) with hA
  set g : Vec d → ℝ := cubeTranslationTest d n t with hg
  set B : ℝ := cubeBesovScaleWeight s Q * cubeTranslationTestBound d n s W J with hB
  have hboundPos : 0 < cubeTranslationTestBound d n s W J :=
    cubeTranslationTestBound_pos d n hs2 J
  have hwpos : 0 < cubeBesovScaleWeight s Q := by
    rw [cubeBesovScaleWeight]
    exact Real.rpow_pos_of_pos (zpow_pos (by norm_num) _) _
  have hBpos : 0 < B := by rw [hB]; positivity
  have hsubT : translatedCubeSet A t ⊆ cubeSet Q :=
    translatedCubeSet_originCube_subset_succ d n t hWle htW
  have hnorm : ∀ M : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) M g ≤ B :=
    fun M => cubeTranslationTest_dualTestNorm_le_bound d n t hs2 hW hWle htW hJ M
  have hlocal := dualLocalMemLpGlobal_cubeTranslationTest d n t Q
  have hi : ∀ i : Fin d,
      |cubeAverageVec A (fun x => F (x + t)) i - cubeAverageVec A F i| ≤
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) * B := by
    intro i
    have hpair : cubeBesovPairing Q (fun x => F x i) g =
        cubeAverage A (fun x => F x i) -
          cubeAverage A (fun y => F (y + t) i) :=
      cubeBesovPairing_cubeTranslationTest d n t (fun x => F x i)
        (integrableOn_cubeSet_of_memLp_two Q (memLp_component Q hmem i)) hsubT
    have hbound : |cubeBesovPairing Q (fun x => F x i) g| ≤
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) * B :=
      abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two
        Q s (fun x => F x i) g hs (memLp_component Q hmem i) hBpos hnorm hlocal
    have hrewrite : cubeAverageVec A (fun x => F (x + t)) i - cubeAverageVec A F i =
        -(cubeBesovPairing Q (fun x => F x i) g) := by
      rw [hpair, cubeAverageVec, cubeAverageVec]
      ring
    rw [hrewrite, abs_neg]
    exact hbound
  have hDnn : ∀ i : Fin d,
      0 ≤ cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) * B := by
    intro i
    have hconj0 : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 :=
      cubeBesovConjExponent_ne_zero (2 : ℝ≥0∞)
    have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
    have hconjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by rw [hconj]; norm_num
    exact mul_nonneg
      (cubeBesovDualFullNorm_nonneg Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) _ hconj0 hconjTop)
      hBpos.le
  have hsum : ‖cubeAverageVec A (fun x => F (x + t)) - cubeAverageVec A F‖ ≤
      ∑ i : Fin d,
        cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i) * B := by
    refine (pi_norm_le_iff_of_nonneg
      (Finset.sum_nonneg fun i _ => hDnn i)).2 fun i => ?_
    refine le_trans ?_ (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hDnn j)
      (Finset.mem_univ i))
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi i
  refine hsum.trans ?_
  rw [← Finset.sum_mul, hB]
  have hrowSum : cubeBesovScaleWeight s Q *
      ∑ i : Fin d, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i)
        ≤ N := hrow
  calc
    (∑ i : Fin d, cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i)) *
        (cubeBesovScaleWeight s Q * cubeTranslationTestBound d n s W J)
        = (cubeBesovScaleWeight s Q *
            ∑ i : Fin d,
              cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fun x => F x i)) *
          cubeTranslationTestBound d n s W J := by ring
    _ ≤ N * cubeTranslationTestBound d n s W J :=
        mul_le_mul_of_nonneg_right hrowSum hboundPos.le

/-! ## Translation stability -/

private theorem integrableOn_const_cubeSet (Q : TriadicCube d) (c : ℝ) :
    IntegrableOn (fun _ : Vec d => c) (cubeSet Q) volume := by
  have : IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_cubeSet_lt_top Q⟩
  exact integrable_const c

private theorem cubeAverageVec_const_add (Q : TriadicCube d) (c : Vec d)
    {G : Vec d → Vec d}
    (hG : ∀ i, IntegrableOn (fun x => G x i) (cubeSet Q) volume) :
    cubeAverageVec Q (fun x => c + G x) = c + cubeAverageVec Q G := by
  funext i
  show cubeAverage Q (fun x => c i + G x i) = c i + cubeAverage Q (fun x => G x i)
  have hvol : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  rw [cubeAverage, cubeAverage,
    integral_add (integrableOn_const_cubeSet Q (c i)) (hG i), setIntegral_const,
    smul_eq_mul, Measure.real, volume_cubeSet_toReal]
  field_simp

/-- **Translation stability of corrector-gradient cube averages.**  One
scale-uniform bound for the weak corrector row of the affine-plus-corrector
field makes the centered normalized cube averages of the corrector gradient and
of its fixed translate asymptotically equal. -/
theorem NormalizedLocalH1Carrier.tendsto_norm_integral_globalGradient_translate_sub_zero_of_weakRow
    [NeZero d] (Phi : NormalizedLocalH1Carrier d) (e t : Vec d) {s : ℝ}
    (hs : 0 < s) (hs2 : s < 1 / 2) (q0 : ℕ) (N : ℝ)
    (hN : ∀ q : ℕ, q0 ≤ q →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (q : ℤ)) s
        (fun x => e + Phi.globalGradientRepresentative x) ≤ N) :
    Tendsto
      (fun n : ℕ =>
        ‖(∫ x, Phi.globalGradientRepresentative (x + t)
            ∂normalizedCubeMeasure (originCube d (n : ℤ))) -
          ∫ x, Phi.globalGradientRepresentative x
            ∂normalizedCubeMeasure (originCube d (n : ℤ))‖)
      atTop (nhds 0) := by
  set F : Vec d → Vec d := fun x => e + Phi.globalGradientRepresentative x with hF
  have hNnn : 0 ≤ N :=
    le_trans
      (cubeScaleNormalizedDualNegativeBesovVectorNormTwo_nonneg
        (originCube d (q0 : ℤ)) s F) (hN q0 le_rfl)
  have htnorm : ∀ i, |t i| ≤ ‖t‖ := fun i => norm_le_pi_norm t i
  have hkey : ∀ n : ℕ, q0 ≤ n + 1 → ‖t‖ ≤ (3 : ℝ) ^ n → ∀ J : ℕ, 1 ≤ J →
      ‖(∫ x, Phi.globalGradientRepresentative (x + t)
            ∂normalizedCubeMeasure (originCube d (n : ℤ))) -
          ∫ x, Phi.globalGradientRepresentative x
            ∂normalizedCubeMeasure (originCube d (n : ℤ))‖ ≤
        N * cubeTranslationTestBound d n s ‖t‖ J := by
    intro n hq ht J hJ
    have hmemT := Phi.memLp_globalGradientRepresentative_translate_normalizedCubeMeasure t n
    have hmemP := Phi.memLp_globalGradientRepresentative_normalizedCubeMeasure n
    rw [← cubeAverageVec_eq_integral_normalizedCubeMeasure_of_integrable _ _
        (hmemT.integrable (by norm_num)),
      ← cubeAverageVec_eq_integral_normalizedCubeMeasure_of_integrable _ _
        (hmemP.integrable (by norm_num))]
    have hgT : ∀ i, IntegrableOn
        (fun x => Phi.globalGradientRepresentative (x + t) i)
        (cubeSet (originCube d (n : ℤ))) volume := fun i =>
      integrableOn_cubeSet_of_memLp_two _ (memLp_component _ hmemT i)
    have hgP : ∀ i, IntegrableOn
        (fun x => Phi.globalGradientRepresentative x i)
        (cubeSet (originCube d (n : ℤ))) volume := fun i =>
      integrableOn_cubeSet_of_memLp_two _ (memLp_component _ hmemP i)
    have hshift : cubeAverageVec (originCube d (n : ℤ)) (fun x => F (x + t)) -
        cubeAverageVec (originCube d (n : ℤ)) F =
        cubeAverageVec (originCube d (n : ℤ))
            (fun x => Phi.globalGradientRepresentative (x + t)) -
          cubeAverageVec (originCube d (n : ℤ))
            Phi.globalGradientRepresentative := by
      rw [hF, cubeAverageVec_const_add _ e hgT, cubeAverageVec_const_add _ e hgP]
      abel
    rw [← hshift]
    refine norm_cubeAverageVec_translate_sub_le_of_weakRow d n F t hs hs2
      (norm_nonneg t) ht htnorm hJ ?_ (hN (n + 1) hq)
    exact (memLp_const e).add
      (Phi.memLp_globalGradientRepresentative_normalizedCubeMeasure (n + 1))
  have hd : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast this
  set rho : ℝ := (3 : ℝ) ^ (s - 1 / 2) with hrhodef
  have hrho0 : 0 < rho := Real.rpow_pos_of_pos (by norm_num) _
  have hrho1 : rho < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs2])
  set cD : ℝ := Real.sqrt (24 * (d : ℝ) * (3 : ℝ) ^ d) with hcDdef
  have htail : Tendsto (fun J : ℕ => N * (cD * (rho ^ J / (1 - rho)))) atTop
      (nhds 0) := by
    have hbase : Tendsto (fun J : ℕ => rho ^ J) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hrho0.le hrho1
    have := (hbase.const_mul (N * cD * (1 - rho)⁻¹))
    rw [mul_zero] at this
    refine this.congr fun J => ?_
    rw [div_eq_mul_inv]
    ring
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨J0, hJ0⟩ := Metric.tendsto_atTop.mp htail (eps / 2) (by linarith only [heps])
  set J : ℕ := max J0 1 with hJdef
  have hJ1 : 1 ≤ J := le_max_right _ _
  have hJtail : N * (cD * (rho ^ J / (1 - rho))) < eps / 2 := by
    have := hJ0 J (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  set SJ : ℝ := ∑ j ∈ Finset.range J, ((3 : ℝ) ^ s) ^ j with hSJdef
  have hhead : Tendsto
      (fun n : ℕ =>
        N * (Real.sqrt (8 * (d : ℝ) * (3 : ℝ) ^ d * (‖t‖ / (3 : ℝ) ^ n)) * SJ))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ‖t‖ / (3 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3))
    have h2 : Tendsto
        (fun n : ℕ => 8 * (d : ℝ) * (3 : ℝ) ^ d * (‖t‖ / (3 : ℝ) ^ n)) atTop
        (nhds 0) := by
      have := h1.const_mul (8 * (d : ℝ) * (3 : ℝ) ^ d)
      rwa [mul_zero] at this
    have h3 : Tendsto
        (fun n : ℕ =>
          Real.sqrt (8 * (d : ℝ) * (3 : ℝ) ^ d * (‖t‖ / (3 : ℝ) ^ n))) atTop
        (nhds 0) := by
      have := h2.sqrt
      rwa [Real.sqrt_zero] at this
    have := (h3.mul_const SJ).const_mul N
    rwa [zero_mul, mul_zero] at this
  obtain ⟨n1, hn1⟩ := Metric.tendsto_atTop.mp hhead (eps / 2) (by linarith only [heps])
  have hgrow : ∀ᶠ n : ℕ in atTop, ‖t‖ ≤ (3 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3)).eventually_ge_atTop ‖t‖
  obtain ⟨n2, hn2⟩ := eventually_atTop.mp hgrow
  refine ⟨max (max n1 n2) q0, fun n hn => ?_⟩
  have hn1' : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2' : n2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hq0' : q0 ≤ n + 1 := le_trans (le_trans (le_max_right _ _) hn) (Nat.le_succ n)
  have hbound := hkey n hq0' (hn2 n hn2') J hJ1
  have hhead' : N * (Real.sqrt (8 * (d : ℝ) * (3 : ℝ) ^ d * (‖t‖ / (3 : ℝ) ^ n)) * SJ)
      < eps / 2 := by
    have := hn1 n hn1'
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hsplit : N * cubeTranslationTestBound d n s ‖t‖ J =
      N * (Real.sqrt (8 * (d : ℝ) * (3 : ℝ) ^ d * (‖t‖ / (3 : ℝ) ^ n)) * SJ) +
        N * (cD * (rho ^ J / (1 - rho))) := by
    rw [cubeTranslationTestBound, ← hSJdef, ← hcDdef, ← hrhodef]
    ring
  rw [hsplit] at hbound
  linarith only [hbound, hhead', hJtail]

end

end HighContrast
end HCPolySupport
