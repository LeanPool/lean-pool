/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanCore
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanGaussVectorIntegrable

/-!
# The Gaussian Carleman estimate with its explicit constant

The shared commutator estimate, Gaussian weight identities, and componentwise
energy bounds give `prop:carleman-gauss` with the constant
`c₀ = e^{4/3}(9 + 2√6)`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

local instance gaussExplicitMeasureSpace : MeasureSpace ParabolicPoint :=
  Measure.prod.measureSpace

local instance gaussExplicitNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance gaussExplicitNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- Gaussian Carleman inequality on the positive-time cylinder with the
explicit constant `c₀ = e^{4/3}(9 + 2√6)` (`prop:carleman-gauss`). -/
theorem carlemanGaussian_explicit (a : ℝ) (ha : 0 < a) (w : ParabolicPoint → Vec3)
    (hwtest : w ∈ spaceTimeTestFunction (V := Vec3) univ (Ioo 0 2)) :
      ∫ z in spaceTimeSet univ (Ioo 0 2),
        (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
          (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
            spatialGradientSq w (spatialGradient w) z) ≤
      (Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6)) * ∫ z in spaceTimeSet univ (Ioo 0 2),
        (z.2 * Real.exp ((1 - z.2) / 3)) ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) *
          vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 := by
  let c₀ : ℝ := Real.exp (4 / 3) * (9 + 2 * Real.sqrt 6)
  show _ ≤ c₀ * _
  let q : ℝ := a + 1
  let φ : ParabolicPoint → ℝ := CKN.gaussCarlemanPhase q
  let v (i : Fin 3) : ParabolicPoint → ℝ :=
    fun z => Real.exp (φ z) * w z i
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hq : 1 ≤ q := by dsimp [q]; linarith only [ha]
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U :=
    CKN.gaussCarlemanPhase_contDiffOn q
  obtain ⟨hw, hwc, hwU⟩ := hwtest
  have hvi (i : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (v i) ∧
      HasCompactSupport (v i) ∧ tsupport (v i) ⊆ U :=
    ESS.gauss_conjugated_component_properties q w hw hwc hwU i
  have hPi (i : Fin 3) : Integrable (fun z : ParabolicPoint =>
      z.2 ^ 2 * CKN.carlemanConj φ (v i) z ^ 2) volume :=
    ESS.gauss_component_conjugated_heat_integrable q w hw hwc hwU i
  have hscalar (i : Fin 3) :
      q * (∫ z : ParabolicPoint, z.2 * v i z ^ 2 ∂volume) +
        2 * ((∫ z : ParabolicPoint,
          z.2 ^ 2 * CKN.scalarGradSq (v i) z ∂volume) +
          (∫ z : ParabolicPoint, z.2 ^ 2 * v i z ^ 2 *
            CKN.scalarGradSq φ z ∂volume)) ≤
        (9 + 2 * Real.sqrt 6) *
          (∫ z : ParabolicPoint,
            z.2 ^ 2 * CKN.carlemanConj φ (v i) z ^ 2 ∂volume) := by
    obtain ⟨hvis, hvic, hviU⟩ := hvi i
    have hcore := ESS.carleman_commutator_le hU hφ hvis hvic hviU
    have hIP : (∫ z : ParabolicPoint,
        q / 3 * z.2 * v i z ^ 2 ∂volume) ≤
          ∫ z : ParabolicPoint,
            z.2 ^ 2 * CKN.carlemanConj φ (v i) z ^ 2 ∂volume := by
      calc
        _ = ∫ z : ParabolicPoint,
            CKN.carlemanCommutatorDensity φ (v i) z ∂volume :=
              (ESS.gauss_commutator_integral_eq q (v i) hviU).symm
        _ ≤ _ := hcore
    have hE := ESS.gauss_scalar_energy_le_of_commutator q hq (v i)
      hvis hvic hviU (hPi i) hIP
    have hJ :
        q * (∫ z : ParabolicPoint, z.2 * v i z ^ 2 ∂volume) =
          3 * (∫ z : ParabolicPoint,
            q / 3 * z.2 * v i z ^ 2 ∂volume) := by
      calc
        _ = ∫ z : ParabolicPoint, q * (z.2 * v i z ^ 2) ∂volume := by
              rw [integral_const_mul]
        _ = ∫ z : ParabolicPoint,
            3 * (q / 3 * z.2 * v i z ^ 2) ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with z
              ring
        _ = _ := by rw [integral_const_mul]
    exact CKN.gaussCarleman_final_absorb hJ hIP hE
  let A : ℝ := ∫ z : ParabolicPoint,
    (CKN.gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
          spatialGradientSq w (spatialGradient w) z) ∂volume
  let B : ℝ := ∫ z : ParabolicPoint,
    q * z.2 * vec3EuclideanNorm (fun i => v i z) ^ 2 +
      2 * z.2 ^ 2 *
        ((∑ i : Fin 3, CKN.scalarGradSq (v i) z) +
          vec3EuclideanNorm (fun i => v i z) ^ 2 * CKN.scalarGradSq φ z) ∂volume
  let P : ℝ := ∫ z : ParabolicPoint,
    z.2 ^ 2 * (∑ i : Fin 3, CKN.carlemanConj φ (v i) z ^ 2) ∂volume
  let D : ℝ := ∫ z : ParabolicPoint,
    (CKN.gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 ∂volume
  have hAintegrable := ESS.gauss_original_energy_integrable a w hw hwc hwU
  have hBintegrable := ESS.gauss_vector_upper_integrable q w hw hwc hwU
  have hPintegrable := ESS.gauss_conjugated_heat_integrable q w hw hwc hwU
  have hDintegrable := ESS.gauss_original_heat_integrable a w hw hwc hwU
  have hAB : A ≤ Real.exp (2 / 3 : ℝ) * B := by
    calc
      A ≤ ∫ z : ParabolicPoint,
          Real.exp (2 / 3 : ℝ) *
            (q * z.2 * vec3EuclideanNorm (fun i => v i z) ^ 2 +
              2 * z.2 ^ 2 *
                ((∑ i : Fin 3, CKN.scalarGradSq (v i) z) +
                  vec3EuclideanNorm (fun i => v i z) ^ 2 *
                    CKN.scalarGradSq φ z)) ∂volume := by
        apply integral_mono hAintegrable (hBintegrable.const_mul _)
        intro z
        exact ESS.gauss_vector_weighted_energy_le_global a w ha hw hwU z
      _ = Real.exp (2 / 3 : ℝ) * B := by rw [integral_const_mul]
  have hBP : B ≤ (9 + 2 * Real.sqrt 6) * P := by
    have hBeq : B = ∑ i : Fin 3,
        (q * (∫ z : ParabolicPoint, z.2 * v i z ^ 2 ∂volume) +
          2 * ((∫ z : ParabolicPoint,
            z.2 ^ 2 * CKN.scalarGradSq (v i) z ∂volume) +
            (∫ z : ParabolicPoint, z.2 ^ 2 * v i z ^ 2 *
              CKN.scalarGradSq φ z ∂volume))) :=
      ESS.gauss_vector_upper_integral_eq_sum q w hw hwc hwU
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => hscalar i)
    calc
      B = ∑ i : Fin 3,
          (q * (∫ z : ParabolicPoint, z.2 * v i z ^ 2 ∂volume) +
            2 * ((∫ z : ParabolicPoint,
              z.2 ^ 2 * CKN.scalarGradSq (v i) z ∂volume) +
              (∫ z : ParabolicPoint, z.2 ^ 2 * v i z ^ 2 *
                CKN.scalarGradSq φ z ∂volume))) := hBeq
      _ ≤ ∑ i : Fin 3, (9 + 2 * Real.sqrt 6) *
          (∫ z : ParabolicPoint,
            z.2 ^ 2 * CKN.carlemanConj φ (v i) z ^ 2 ∂volume) := hsum
      _ = (9 + 2 * Real.sqrt 6) *
          (∑ i : Fin 3, ∫ z : ParabolicPoint,
            z.2 ^ 2 * CKN.carlemanConj φ (v i) z ^ 2 ∂volume) := by
              rw [Finset.mul_sum]
      _ = (9 + 2 * Real.sqrt 6) * P := by
        congr 1
        exact (ESS.gauss_vector_conjugated_heat_integral_eq_sum q w hw hwc hwU).symm
  have hPD : P ≤ Real.exp (2 / 3 : ℝ) * D := by
    calc
      P ≤ ∫ z : ParabolicPoint,
          Real.exp (2 / 3 : ℝ) *
            ((CKN.gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
              Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
              vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
                ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) ∂volume := by
        apply integral_mono hPintegrable (hDintegrable.const_mul _)
        intro z
        exact ESS.gauss_vector_operator_energy_le_global a w hw hwU z
      _ = Real.exp (2 / 3 : ℝ) * D := by rw [integral_const_mul]
  have hAD : A ≤ c₀ * D := by
    have hexp : Real.exp (2 / 3 : ℝ) * Real.exp (2 / 3 : ℝ) =
        Real.exp (4 / 3 : ℝ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hk : 0 ≤ 9 + 2 * Real.sqrt 6 := by positivity
    have he : 0 ≤ Real.exp (2 / 3 : ℝ) := le_of_lt (Real.exp_pos _)
    calc
      A ≤ Real.exp (2 / 3 : ℝ) * B := hAB
      _ ≤ Real.exp (2 / 3 : ℝ) * ((9 + 2 * Real.sqrt 6) * P) :=
        mul_le_mul_of_nonneg_left hBP he
      _ ≤ Real.exp (2 / 3 : ℝ) *
          ((9 + 2 * Real.sqrt 6) * (Real.exp (2 / 3 : ℝ) * D)) := by
            apply mul_le_mul_of_nonneg_left _ he
            exact mul_le_mul_of_nonneg_left hPD hk
      _ = c₀ * D := by
        dsimp [c₀]
        calc
          _ = (Real.exp (2 / 3 : ℝ) * Real.exp (2 / 3 : ℝ)) *
              (9 + 2 * Real.sqrt 6) * D := by ring
          _ = _ := by rw [hexp]
  have hAset := ESS.gauss_original_energy_setIntegral_eq_integral a w hwU
  have hDset := ESS.gauss_original_heat_setIntegral_eq_integral a w hwU
  change (∫ z in spaceTimeSet univ (Ioo 0 2),
      (CKN.gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
            spatialGradientSq w (spatialGradient w) z)) ≤
    c₀ * (∫ z in spaceTimeSet univ (Ioo 0 2),
      (CKN.gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2)
  calc
    _ = A := hAset
    _ ≤ c₀ * D := hAD
    _ = c₀ * (∫ z in spaceTimeSet univ (Ioo 0 2),
      (CKN.gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) :=
        congrArg (fun x : ℝ => c₀ * x) hDset.symm

end ESS
