/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NegativeSobolevCubeDuality
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.EuclideanWspExactOverlapFullControl
public import LeanPool.HighContrastHomogenization.Support.Besov.Negative.ExactAggregationBridge
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.CaccioppoliVectorization
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NegativeBesovLocalize

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalDualToBesovBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fractional dual to componentwise full Besov dual

Below the trace threshold the physical negative fractional norm on a triadic
cube is controlled by the sum of the scalar full Besov dual norms of its
components, with a finite dimension-only coefficient.  Both sides keep the
physical cube scale.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- A finite dimension-only coefficient comparing the exact fractional smooth
dual with the componentwise full Besov dual. -/
@[expose]
def fractionalDualToBesovConstant (d : ℕ) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) ^ ((d : ℝ) / 2) *
    cubeEuclideanWspExactOverlapFullControlConstant d

theorem fractionalDualToBesovConstant_lt_top (d : ℕ) :
    fractionalDualToBesovConstant d < ∞ := by
  unfold fractionalDualToBesovConstant
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by norm_num))
    (cubeEuclideanWspExactOverlapFullControlConstant_lt_top d)

/-- Below the trace threshold, the physical negative fractional norm on a
triadic cube is controlled by the sum of its scalar full Besov dual norms.
Both sides retain the physical cube scale. -/
theorem negSobolevNorm_le_fractionalDualToBesovConstant_mul_fullDualSum
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    negSobolevNorm (openCubeSet Q) s F.toField ≤
      fractionalDualToBesovConstant d *
        ENNReal.ofReal
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F.toField x i)) := by
  let sF : FractionalOrder := ⟨s, hs, hsHalf.trans (by norm_num)⟩
  rw [negSobolevNorm_eq_cubeEuclideanNegativeWspSmoothDualENorm
    Q hs hsHalf F]
  change cubeEuclideanNegativeWspSmoothDualENorm Q sF
      FiniteLpExponent.two F ≤ _
  unfold cubeEuclideanNegativeWspSmoothDualENorm
  apply iSup_le
  rintro ⟨h, hunit⟩
  let K : ℝ≥0∞ := fractionalDualToBesovConstant d
  let B : ℝ := K.toReal
  have hKtop : K ≠ ∞ := (fractionalDualToBesovConstant_lt_top d).ne
  have hBnonneg : 0 ≤ B := ENNReal.toReal_nonneg
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hpConjTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    rw [hpConj]
    norm_num
  let h2 : CubeEuclideanWspSmoothTest Q sF FiniteLpExponent.two :=
    { toField := h.toField
      contDiff := h.contDiff }
  have hunit2 :
      cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two h2.toField ≤ 1 := by
    simpa [h2, FiniteLpExponent.conjugate_two] using hunit
  have hcoordMem : ∀ i : Fin d,
      MemLp (fun x => h.toField x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    let hWsp := h2.toCubeEuclideanWspField
    simpa [hWsp, h2] using
      cubeEuclideanLp_coordinate_memLp hWsp.toCubeEuclideanLpField i
  have hcoordMemReal : ∀ i : Fin d,
      MemLp (fun x => h.toField x i) (ENNReal.ofReal 2)
        (normalizedCubeMeasure Q) := by
    intro i
    norm_num
    exact hcoordMem i
  have hcoordLocal : ∀ i : Fin d,
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
        (fun x => h.toField x i) := by
    intro i
    exact CubeBesovDualLocalMemLpGlobal.of_memLp_parent
      (p := (2 : ℝ≥0∞)) (by simpa [hpConj] using hcoordMem i)
  have hcoordBound : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => h.toField x i) ≤ B := by
    intro i N
    let hWsp := h2.toCubeEuclideanWspField
    have hover : ENNReal.ofReal
        (cubeBesovOverlapPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
          N (fun x => h.toField x i)) ≤
        exactOverlapFiniteNorm (exactOverlapScalarPParameters sF FiniteLpExponent.two)
          Q (fun x => h.toField x i)
          (exactDualOverlapIntegrable Q 2 (by norm_num) (hcoordMemReal i)) := by
      simpa [exactOverlapScalarPParameters, sF] using
        exactAggregation_overlapPartialNorm_le_exactOverlapFiniteNorm
          (exactOverlapScalarPParameters sF FiniteLpExponent.two) Q
          (fun x => h.toField x i) (hcoordMemReal i) N
    have hfull :=
      exactOverlapScalarPFullNorm_le_dimensionConstant_mul_cubeEuclideanWspFull
        Q sF FiniteLpExponent.two hWsp i
    have hfull' :
        exactOverlapFiniteNorm (exactOverlapScalarPParameters sF FiniteLpExponent.two)
            Q (fun x => h.toField x i)
            (exactDualOverlapIntegrable Q 2 (by norm_num) (hcoordMemReal i)) ≤
          cubeEuclideanWspExactOverlapFullControlConstant d := by
      calc
        exactOverlapFiniteNorm
              (exactOverlapScalarPParameters sF FiniteLpExponent.two)
              Q (fun x => h.toField x i)
              (exactDualOverlapIntegrable Q 2 (by norm_num) (hcoordMemReal i)) ≤
            cubeEuclideanWspExactOverlapFullControlConstant d *
              cubeEuclideanWspFullENorm Q sF FiniteLpExponent.two h.toField := by
                simpa [hWsp, FiniteLpExponent.conjugate_two] using hfull
        _ ≤ cubeEuclideanWspExactOverlapFullControlConstant d * 1 := by
              gcongr
        _ = cubeEuclideanWspExactOverlapFullControlConstant d := by rw [mul_one]
    have hpartial :
        cubeBesovPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => h.toField x i) ≤
          (3 : ℝ) ^ ((d : ℝ) / 2) *
            cubeBesovOverlapPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              N (fun x => h.toField x i) := by
      exact cubeBesovPartialNorm_le_three_rpow_mul_overlapPartialNorm
        Q s (by norm_num) (by norm_num) N _
    have hpartialENN : ENNReal.ofReal
        (cubeBesovPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (fun x => h.toField x i)) ≤ K := by
      calc
        ENNReal.ofReal
            (cubeBesovPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
              (fun x => h.toField x i)) ≤
            ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) / 2) *
              cubeBesovOverlapPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                N (fun x => h.toField x i)) := ENNReal.ofReal_le_ofReal hpartial
        _ = (3 : ℝ≥0∞) ^ ((d : ℝ) / 2) *
              ENNReal.ofReal
                (cubeBesovOverlapPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
                  N (fun x => h.toField x i)) := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
              ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))
                (by positivity : 0 ≤ (d : ℝ) / 2)]
            norm_num
        _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) / 2) *
              exactOverlapFiniteNorm
                (exactOverlapScalarPParameters sF FiniteLpExponent.two)
                Q (fun x => h.toField x i)
                (exactDualOverlapIntegrable Q 2 (by norm_num) (hcoordMemReal i)) := by
            gcongr
        _ ≤ (3 : ℝ≥0∞) ^ ((d : ℝ) / 2) *
              cubeEuclideanWspExactOverlapFullControlConstant d := by
            gcongr
        _ = K := rfl
    have hpartialReal :
        cubeBesovPartialNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
            (fun x => h.toField x i) ≤ B := by
      exact (ENNReal.ofReal_le_iff_le_toReal hKtop).mp hpartialENN
    rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q s
      (2 : ℝ≥0∞) (2 : ℝ≥0∞) N (fun x => h.toField x i) hpConjTop]
    simpa [hpConj] using hpartialReal
  have hFcoord : ∀ i : Fin d,
      MemLp (fun x => F.toField x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    exact cubeEuclideanLp_coordinate_memLp F i
  have hInt : ∀ i : Fin d,
      Integrable (fun x => F.toField x i * h.toField x i)
        (normalizedCubeMeasure Q) := by
    intro i
    exact (hFcoord i).integrable_mul (hcoordMem i)
  have hpair :
      |cubeEuclideanNormalizedSmoothPairing F h| ≤
        B * ∑ i : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F.toField x i) := by
    calc
      |cubeEuclideanNormalizedSmoothPairing F h| =
          |cubeAverage Q (fun x => vecDot (F.toField x) (h.toField x))| := by
            unfold cubeEuclideanNormalizedSmoothPairing
            rw [cubeAverage_eq_integral_normalizedCubeMeasure]
      _ ≤ ∑ i : Fin d,
          |cubeBesovPairing Q (fun x => F.toField x i)
            (fun x => h.toField x i)| :=
        abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing
          Q F.toField h.toField hInt
      _ ≤ ∑ i : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
              (fun x => F.toField x i) * B := by
        apply Finset.sum_le_sum
        intro i _hi
        exact Book.Ch01.Legacy.abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two_of_nonneg
          Q s (fun x => F.toField x i) (fun x => h.toField x i)
          hs (hFcoord i) hBnonneg (hcoordBound i) (hcoordLocal i)
      _ = B * ∑ i : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F.toField x i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [mul_comm]
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
        ENNReal.ofReal (B * ∑ i : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F.toField x i)) := ENNReal.ofReal_le_ofReal hpair
    _ = K * ENNReal.ofReal (∑ i : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F.toField x i)) := by
      rw [ENNReal.ofReal_mul hBnonneg, ENNReal.ofReal_toReal hKtop]
    _ = fractionalDualToBesovConstant d *
        ENNReal.ofReal (∑ i : Fin d,
          cubeBesovDualFullNorm Q s (2 : ℝ≥0∞) (2 : ℝ≥0∞)
            (fun x => F.toField x i)) := rfl

end

end HighContrast
end HCPolySupport
