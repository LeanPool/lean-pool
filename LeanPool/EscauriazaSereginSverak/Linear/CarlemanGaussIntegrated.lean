/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanGaussIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreGradient

/-!
# Integrated Gaussian gradient estimate

The Gaussian phase specializes `eq:carleman-gradient-integrated` to the
coefficient bound used in `eq:carleman-E`.
-/

public section


open CKN CKN.Foundation.Parabolic Set MeasureTheory

noncomputable section

namespace ESS

/-- Product Lebesgue measure on parabolic space-time. -/
local instance gaussIntegratedMeasureSpace : MeasureSpace ParabolicPoint :=
  Measure.prod.measureSpace

/-- The product norm on parabolic space-time used in this identity. -/
local instance gaussIntegratedNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The real scalar action compatible with the product norm on parabolic space-time. -/
local instance gaussIntegratedNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The integrated gradient and phase-gradient energy is bounded by three
times the Gaussian commutator mass and the cross integral. -/
theorem gauss_scalar_gradient_energy_le (q : ℝ) (hq : 1 ≤ q)
    (v : ParabolicPoint → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v)
    (hvU : tsupport v ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (∫ z : ParabolicPoint, z.2 ^ 2 * scalarGradSq v z ∂volume) +
      (∫ z : ParabolicPoint, z.2 ^ 2 * v z ^ 2 *
        scalarGradSq (gaussCarlemanPhase q) z ∂volume) ≤
      3 * (∫ z : ParabolicPoint, q / 3 * z.2 * v z ^ 2 ∂volume) +
        |∫ z : ParabolicPoint, z.2 ^ 2 * v z *
          carlemanConj (gaussCarlemanPhase q) v z ∂volume| := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  let φ := gaussCarlemanPhase q
  let C : ℝ := ∫ z : ParabolicPoint, z.2 ^ 2 * v z * carlemanConj φ v z ∂volume
  let I : ℝ := ∫ z : ParabolicPoint, q / 3 * z.2 * v z ^ 2 ∂volume
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U := gaussCarlemanPhase_contDiffOn q
  have hGrad := carleman_gradient_identity 2 hU hφ hv hvc hvU
  have hRpoint (z : ParabolicPoint) :
      q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 =
        z.2 ^ 2 * v z ^ 2 * (scalarGradSq φ z - timePartial φ z) +
          z.2 ^ 2 * v z ^ 2 * scalarGradSq φ z := by
    have hp := gauss_potential_times_field_global q v hvU z
    calc
      q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 =
          z.2 ^ 2 * (v z ^ 2 *
            (-scalarGradSq φ z + q * (1 / z.2 - 1 / 3)) +
            v z ^ 2 * scalarGradSq φ z) := by ring
      _ = z.2 ^ 2 * (v z ^ 2 *
            (scalarGradSq φ z - timePartial φ z) +
            v z ^ 2 * scalarGradSq φ z) := by rw [hp]
      _ = _ := by ring
  have hD : Integrable (fun z : ParabolicPoint => z.2 ^ 2 * v z ^ 2 *
      (scalarGradSq φ z - timePartial φ z)) volume :=
    gauss_potential_integrable q v hv hvc hvU
  have hF : Integrable (fun z : ParabolicPoint => z.2 ^ 2 * v z ^ 2 *
      scalarGradSq φ z) volume :=
    gauss_phase_gradient_mass_integrable q v hv hvc hvU
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hvcProd : HasCompactSupport (show Vec3 × ℝ → ℝ from v) := by
    exact hvc
  have hI : Integrable (fun z : ParabolicPoint => q / 3 * z.2 * v z ^ 2) volume :=
    gauss_mass_integrable q v hv hvcProd
  have hMass : Integrable (fun z : ParabolicPoint => z.2 * v z ^ 2) volume := by
    have heq : (fun z : ParabolicPoint => z.2 * v z ^ 2) =
        fun z => (3 / q) * (q / 3 * z.2 * v z ^ 2) := by
      funext z
      field_simp [ne_of_gt hqpos]
    rw [heq]
    exact hI.const_mul _
  have hR : Integrable (fun z : ParabolicPoint =>
      q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2) volume := by
    have heq : (fun z : ParabolicPoint =>
        q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2) =
        fun z => z.2 ^ 2 * v z ^ 2 *
          (scalarGradSq φ z - timePartial φ z) +
          z.2 ^ 2 * v z ^ 2 * scalarGradSq φ z := by
      funext z
      exact hRpoint z
    rw [heq]
    exact hD.add hF
  have hCoeff : Integrable (fun z : ParabolicPoint =>
      (-z.2 + q * z.2 ^ 2 * (1 / z.2 - 1 / 3)) * v z ^ 2) volume := by
    have heq : (fun z : ParabolicPoint =>
        (-z.2 + q * z.2 ^ 2 * (1 / z.2 - 1 / 3)) * v z ^ 2) =
        fun z => -(z.2 * v z ^ 2) +
          q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 := by
      funext z
      ring
    rw [heq]
    exact hMass.neg.add hR
  have hMassQ : Integrable (fun z : ParabolicPoint => q * z.2 * v z ^ 2) volume := by
    have heq : (fun z : ParabolicPoint => q * z.2 * v z ^ 2) =
        fun z => 3 * (q / 3 * z.2 * v z ^ 2) := by funext z; ring
    rw [heq]
    exact hI.const_mul _
  have hRint : (∫ z : ParabolicPoint,
      q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 ∂volume) =
      (∫ z : ParabolicPoint, z.2 ^ 2 * v z ^ 2 *
        (scalarGradSq φ z - timePartial φ z) ∂volume) +
      (∫ z : ParabolicPoint, z.2 ^ 2 * v z ^ 2 * scalarGradSq φ z ∂volume) := by
    have heq : (fun z : ParabolicPoint =>
        q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2) =
        fun z => z.2 ^ 2 * v z ^ 2 *
          (scalarGradSq φ z - timePartial φ z) +
          z.2 ^ 2 * v z ^ 2 * scalarGradSq φ z := by
      funext z
      exact hRpoint z
    rw [heq, integral_add hD hF]
  have hCoeffInt : (∫ z : ParabolicPoint,
      (-z.2 + q * z.2 ^ 2 * (1 / z.2 - 1 / 3)) * v z ^ 2 ∂volume) =
      -(∫ z : ParabolicPoint, z.2 * v z ^ 2 ∂volume) +
        (∫ z : ParabolicPoint,
          q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 ∂volume) := by
    calc
      (∫ z : ParabolicPoint,
        (-z.2 + q * z.2 ^ 2 * (1 / z.2 - 1 / 3)) * v z ^ 2 ∂volume) =
          ∫ z : ParabolicPoint,
            -(z.2 * v z ^ 2) +
              q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = _ := by
        have hadd :
            (∫ z : ParabolicPoint,
              -(z.2 * v z ^ 2) +
                q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 ∂volume) =
              (∫ z : ParabolicPoint, -(z.2 * v z ^ 2) ∂volume) +
                (∫ z : ParabolicPoint,
                  q * z.2 ^ 2 * (1 / z.2 - 1 / 3) * v z ^ 2 ∂volume) := by
          exact integral_add hMass.neg hR
        simpa only [integral_neg] using hadd
  have hCoeffLe : (∫ z : ParabolicPoint,
      (-z.2 + q * z.2 ^ 2 * (1 / z.2 - 1 / 3)) * v z ^ 2 ∂volume) ≤
      ∫ z : ParabolicPoint, q * z.2 * v z ^ 2 ∂volume := by
    apply integral_mono hCoeff hMassQ
    intro z
    exact gauss_coefficient_times_field_le q (le_trans (by norm_num) hq) v hvU z
  have hMassQint : (∫ z : ParabolicPoint, q * z.2 * v z ^ 2 ∂volume) =
      3 * I := by
    calc
      (∫ z : ParabolicPoint, q * z.2 * v z ^ 2 ∂volume) =
          ∫ z : ParabolicPoint, 3 * (q / 3 * z.2 * v z ^ 2) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = 3 * I := by rw [integral_const_mul]
  have hGrad' :
      (∫ z : ParabolicPoint, z.2 ^ 2 * scalarGradSq v z ∂volume) =
        -(∫ z : ParabolicPoint, z.2 * v z ^ 2 ∂volume) - C +
          (∫ z : ParabolicPoint, z.2 ^ 2 * v z ^ 2 *
            (scalarGradSq φ z - timePartial φ z) ∂volume) := by
    dsimp [C]
    simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat,
      div_self (by norm_num : (2 : ℝ) ≠ 0), neg_mul, one_mul] using hGrad
  have hEeq :
      (∫ z : ParabolicPoint, z.2 ^ 2 * scalarGradSq v z ∂volume) +
        (∫ z : ParabolicPoint, z.2 ^ 2 * v z ^ 2 * scalarGradSq φ z ∂volume) =
      (∫ z : ParabolicPoint,
        (-z.2 + q * z.2 ^ 2 * (1 / z.2 - 1 / 3)) * v z ^ 2 ∂volume) - C := by
    rw [hGrad', hCoeffInt, hRint]
    dsimp [C]
    ring
  rw [hEeq]
  have hCabs : -C ≤ |C| := neg_le_abs C
  rw [hMassQint] at hCoeffLe
  dsimp [I] at hCoeffLe ⊢
  linarith only [hCoeffLe, hCabs]

/-- The Gaussian commutator inequality and the cross estimate control the
scalar gradient and phase-gradient energy. -/
theorem gauss_scalar_energy_le_of_commutator (q : ℝ) (hq : 1 ≤ q)
    (v : ParabolicPoint → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v)
    (hvU : tsupport v ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (hP : Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 *
      carlemanConj (gaussCarlemanPhase q) v z ^ 2) volume)
    (hIP : (∫ z : ParabolicPoint, q / 3 * z.2 * v z ^ 2 ∂volume) ≤
      ∫ z : ParabolicPoint,
        z.2 ^ 2 * carlemanConj (gaussCarlemanPhase q) v z ^ 2 ∂volume) :
    (∫ z : ParabolicPoint, z.2 ^ 2 * scalarGradSq v z ∂volume) +
      (∫ z : ParabolicPoint, z.2 ^ 2 * v z ^ 2 *
        scalarGradSq (gaussCarlemanPhase q) z ∂volume) ≤
      (3 + Real.sqrt 6) *
        (∫ z : ParabolicPoint,
          z.2 ^ 2 * carlemanConj (gaussCarlemanPhase q) v z ^ 2 ∂volume) := by
  let I : ℝ := ∫ z : ParabolicPoint, q / 3 * z.2 * v z ^ 2 ∂volume
  let P : ℝ := ∫ z : ParabolicPoint,
    z.2 ^ 2 * carlemanConj (gaussCarlemanPhase q) v z ^ 2 ∂volume
  let C : ℝ := ∫ z : ParabolicPoint,
    z.2 ^ 2 * v z * carlemanConj (gaussCarlemanPhase q) v z ∂volume
  let E : ℝ :=
    (∫ z : ParabolicPoint, z.2 ^ 2 * scalarGradSq v z ∂volume) +
      (∫ z : ParabolicPoint, z.2 ^ 2 * v z ^ 2 *
        scalarGradSq (gaussCarlemanPhase q) z ∂volume)
  have hvcProd : HasCompactSupport (show Vec3 × ℝ → ℝ from v) := by
    exact hvc
  have hIintegrable : Integrable
      (fun z : Vec3 × ℝ => q / 3 * z.2 * v z ^ 2) volume :=
    gauss_mass_integrable q v hv hvcProd
  have hCintegrable : Integrable
      (fun z : Vec3 × ℝ => z.2 ^ 2 * v z *
        carlemanConj (gaussCarlemanPhase q) v z) volume :=
    gauss_cross_integrable q v hv hvc hvU
  have hC : |C| ≤ Real.sqrt 6 / 2 * (I + P) :=
    gauss_cross_integral_le q hq v
      (carlemanConj (gaussCarlemanPhase q) v) hvU
      hCintegrable hIintegrable hP
  have hE : E ≤ 3 * I + |C| :=
    gauss_scalar_gradient_energy_le q hq v hv hvc hvU
  exact gaussCarleman_absorb_young hIP hE hC

end ESS
