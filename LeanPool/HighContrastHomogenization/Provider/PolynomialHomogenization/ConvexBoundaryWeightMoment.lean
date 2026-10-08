/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryDistanceLayer
public import LeanPool.HighContrastHomogenization.Analytic.TestNorms
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaIntegration
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexBoundaryWeightMoment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Negative moments of Euclidean boundary distance

The weak `L¹` tail of inverse boundary distance is integrated to control all
negative moments of order below one on a ball-sandwiched convex domain.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem lintegral_Ioi_ofReal_rpow_eq {a c : ℝ}
    (ha : a < -1) (hc : 0 < c) :
    ∫⁻ t in Set.Ioi c, ENNReal.ofReal (t ^ a) ∂volume =
      ENNReal.ofReal (c ^ (a + 1) / (-(a + 1))) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ a) (Set.Ioi c) :=
    integrableOn_Ioi_rpow_of_lt ha hc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi c)] (fun t : ℝ => t ^ a) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hc.trans ht).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_Ioi_rpow_of_lt ha hc]
  congr 1
  field_simp [show a + 1 ≠ 0 by linarith only [ha]]

/-- A nonnegative measurable function with a weak `L¹` tail has every moment
of order strictly between zero and one. -/
theorem lintegral_rpow_le_of_weakL1_tail
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {f : α → ℝ} {p A : ℝ}
    (hνtop : ν Set.univ ≠ ⊤) (hp0 : 0 < p) (hp1 : p < 1) (hA : 0 < A)
    (hf0 : 0 ≤ᵐ[ν] f) (hfmeas : AEMeasurable f ν)
    (htail : ∀ {t : ℝ}, 0 < t →
      ν {x : α | t < f x} ≤ ENNReal.ofReal (A * t⁻¹) * ν Set.univ) :
    ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂ν ≤
      ν Set.univ * ENNReal.ofReal (A ^ p / (1 - p)) := by
  have hp2 : 2 < p + 2 := by linarith only [hp0]
  have hpow_shift : p + 2 - 3 = p - 1 := by ring
  have hlow0 :=
    CubeCalderonZygmund.low_weighted_layercake_le
      ν (u := f) (p := p + 2) (M := 1) (lambda0 := A) hp2 hA.le
  rw [show p + 2 - 2 = p by ring, hpow_shift] at hlow0
  have hlow :
      ENNReal.ofReal p *
          ∫⁻ t in Set.Ioc (0 : ℝ) A,
            ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume ≤
        ν Set.univ * ENNReal.ofReal (A ^ p) := by
    have hrestrict :
        volume.restrict (Set.Ioc (0 : ℝ) A) =
          volume.restrict (Set.Ioo (0 : ℝ) A) :=
      Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
    rw [hrestrict]
    simpa only [one_mul] using hlow0
  have htail_majorant : ∀ t ∈ Set.Ioi A,
      ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
        (ν Set.univ * ENNReal.ofReal A) * ENNReal.ofReal (t ^ (p - 2)) := by
    intro t ht
    have ht0 : 0 < t := hA.trans ht
    have hreal : (A * t⁻¹) * t ^ (p - 1) = A * t ^ (p - 2) := by
      calc
        (A * t⁻¹) * t ^ (p - 1) = A * (t ^ (-1 : ℝ) * t ^ (p - 1)) := by
          rw [Real.rpow_neg_one]
          ring
        _ = A * t ^ ((-1 : ℝ) + (p - 1)) := by
          rw [Real.rpow_add ht0]
        _ = A * t ^ (p - 2) := by ring_nf
    calc
      ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ≤
          (ENNReal.ofReal (A * t⁻¹) * ν Set.univ) *
            ENNReal.ofReal (t ^ (p - 1)) := by
        simpa only [mul_comm] using
          mul_le_mul_right (htail ht0) (ENNReal.ofReal (t ^ (p - 1)))
      _ = ν Set.univ *
          ENNReal.ofReal ((A * t⁻¹) * t ^ (p - 1)) := by
        calc
          (ENNReal.ofReal (A * t⁻¹) * ν Set.univ) *
              ENNReal.ofReal (t ^ (p - 1)) =
              ν Set.univ * (ENNReal.ofReal (A * t⁻¹) *
                ENNReal.ofReal (t ^ (p - 1))) := by ac_rfl
          _ = ν Set.univ *
              ENNReal.ofReal ((A * t⁻¹) * t ^ (p - 1)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hA.le (inv_nonneg.mpr ht0.le))]
      _ = ν Set.univ * ENNReal.ofReal (A * t ^ (p - 2)) := by rw [hreal]
      _ = (ν Set.univ * ENNReal.ofReal A) * ENNReal.ofReal (t ^ (p - 2)) := by
        rw [ENNReal.ofReal_mul hA.le]
        ac_rfl
  have hconsttop : ν Set.univ * ENNReal.ofReal A ≠ ⊤ :=
    ENNReal.mul_ne_top hνtop ENNReal.ofReal_ne_top
  have hpower_int :
      ∫⁻ t in Set.Ioi A, ENNReal.ofReal (t ^ (p - 2)) ∂volume =
        ENNReal.ofReal (A ^ (p - 1) / (1 - p)) := by
    convert lintegral_Ioi_ofReal_rpow_eq (a := p - 2) (c := A)
      (by linarith only [hp1]) hA using 1
    ring_nf
  have hhigh_int :
      ∫⁻ t in Set.Ioi A,
          ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume ≤
        (ν Set.univ * ENNReal.ofReal A) *
          ENNReal.ofReal (A ^ (p - 1) / (1 - p)) := by
    calc
      ∫⁻ t in Set.Ioi A,
          ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume ≤
          ∫⁻ t in Set.Ioi A,
            (ν Set.univ * ENNReal.ofReal A) *
              ENNReal.ofReal (t ^ (p - 2)) ∂volume := by
        exact setLIntegral_mono' measurableSet_Ioi htail_majorant
      _ = (ν Set.univ * ENNReal.ofReal A) *
          ∫⁻ t in Set.Ioi A, ENNReal.ofReal (t ^ (p - 2)) ∂volume := by
        exact lintegral_const_mul' _ _ hconsttop
      _ = _ := by rw [hpower_int]
  have hhigh :
      ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi A,
            ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume ≤
        ν Set.univ * ENNReal.ofReal (p * A ^ p / (1 - p)) := by
    calc
      ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi A,
            ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume ≤
          ENNReal.ofReal p * ((ν Set.univ * ENNReal.ofReal A) *
            ENNReal.ofReal (A ^ (p - 1) / (1 - p))) := by
        simpa only [mul_comm] using
          mul_le_mul_right hhigh_int (ENNReal.ofReal p)
      _ = ν Set.univ * ENNReal.ofReal
          (p * (A * (A ^ (p - 1) / (1 - p)))) := by
        calc
          ENNReal.ofReal p * ((ν Set.univ * ENNReal.ofReal A) *
              ENNReal.ofReal (A ^ (p - 1) / (1 - p))) =
              ν Set.univ * (ENNReal.ofReal p * ENNReal.ofReal A *
                ENNReal.ofReal (A ^ (p - 1) / (1 - p))) := by ac_rfl
          _ = ν Set.univ * ENNReal.ofReal
              ((p * A) * (A ^ (p - 1) / (1 - p))) := by
            rw [← ENNReal.ofReal_mul hp0.le,
              ← ENNReal.ofReal_mul (mul_nonneg hp0.le hA.le)]
          _ = _ := by ring_nf
      _ = ν Set.univ * ENNReal.ofReal (p * A ^ p / (1 - p)) := by
        congr 2
        have hApow : A * A ^ (p - 1) = A ^ p := by
          calc
            A * A ^ (p - 1) = A ^ (1 : ℝ) * A ^ (p - 1) := by
              rw [Real.rpow_one]
            _ = A ^ ((1 : ℝ) + (p - 1)) := (Real.rpow_add hA _ _).symm
            _ = A ^ p := by ring_nf
        rw [← hApow]
        ring
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul
    ν hf0 hfmeas hp0
  have hsplit :
      ∫⁻ t in Set.Ioi (0 : ℝ),
          ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume =
        (∫⁻ t in Set.Ioc (0 : ℝ) A,
          ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume) +
        ∫⁻ t in Set.Ioi A,
          ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume := by
    rw [← lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same,
      Set.Ioc_union_Ioi_eq_Ioi hA.le]
  rw [hlayer, hsplit, mul_add]
  calc
    ENNReal.ofReal p *
          ∫⁻ t in Set.Ioc (0 : ℝ) A,
            ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume +
        ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi A,
            ν {x : α | t < f x} * ENNReal.ofReal (t ^ (p - 1)) ∂volume ≤
        ν Set.univ * ENNReal.ofReal (A ^ p) +
          ν Set.univ * ENNReal.ofReal (p * A ^ p / (1 - p)) :=
      add_le_add hlow hhigh
    _ = ν Set.univ *
        (ENNReal.ofReal (A ^ p) + ENNReal.ofReal (p * A ^ p / (1 - p))) := by
      ring
    _ = ν Set.univ * ENNReal.ofReal
        (A ^ p + p * A ^ p / (1 - p)) := by
      rw [ENNReal.ofReal_add (Real.rpow_nonneg hA.le _)
        (div_nonneg (mul_nonneg hp0.le (Real.rpow_nonneg hA.le _))
          (sub_nonneg.mpr hp1.le))]
    _ = ν Set.univ * ENNReal.ofReal (A ^ p / (1 - p)) := by
      congr 2
      field_simp [show 1 - p ≠ 0 by linarith only [hp1]]
      ring

/-- The negative power of Euclidean boundary distance. -/
@[expose]
noncomputable def euclideanBoundaryWeight
    (U : Set (Vec d)) (p : ℝ) (x : Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (euclideanBoundaryDistance U x ^ (-p))

theorem measurable_euclideanBoundaryWeight (U : Set (Vec d)) (p : ℝ) :
    Measurable (euclideanBoundaryWeight U p) := by
  exact ((measurable_euclideanBoundaryDistance U).pow measurable_const).ennreal_ofReal

/-- The normalized negative boundary-distance moment. -/
@[expose]
noncomputable def euclideanBoundaryWeightMoment
    (U : Set (Vec d)) (p : ℝ) : ℝ≥0∞ :=
  eVolumeAverage U (euclideanBoundaryWeight U p)

/-- Every boundary-distance moment below order one has an explicit bound. -/
theorem lintegral_euclideanBoundaryWeight_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {rho Rad p : ℝ}
    (hsand : HasBallSandwich U rho Rad) (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ x in U, euclideanBoundaryWeight U p x ∂volume ≤
      volume U * ENNReal.ofReal (((d : ℝ) / rho) ^ p / (1 - p)) := by
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hA : 0 < (d : ℝ) / rho := div_pos hdreal hsand.1
  have hνtop : (volume.restrict U) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact hU.volume_lt_top.ne
  have hf0 :
      0 ≤ᵐ[volume.restrict U]
        (fun x : Vec d => (euclideanBoundaryDistance U x)⁻¹) :=
    ae_of_all _ fun x => inv_nonneg.mpr (euclideanBoundaryDistance_nonneg U x)
  have hfmeas : AEMeasurable
      (fun x : Vec d => (euclideanBoundaryDistance U x)⁻¹)
      (volume.restrict U) :=
    (measurable_euclideanBoundaryDistance U).inv.aemeasurable
  have htail : ∀ {t : ℝ}, 0 < t →
      (volume.restrict U)
          {x : Vec d | t < (euclideanBoundaryDistance U x)⁻¹} ≤
        ENNReal.ofReal (((d : ℝ) / rho) * t⁻¹) *
          (volume.restrict U) Set.univ := by
    intro t ht
    have h := measure_inverse_euclideanBoundaryDistance_gt_le hd hU hsand ht
    rw [Measure.restrict_apply_univ]
    convert h using 1
    congr 2
    ring
  have hmoment := lintegral_rpow_le_of_weakL1_tail
    (volume.restrict U) hνtop hp0 hp1 hA hf0 hfmeas htail
  rw [Measure.restrict_apply_univ] at hmoment
  calc
    ∫⁻ x in U, euclideanBoundaryWeight U p x ∂volume =
        ∫⁻ x in U,
          ENNReal.ofReal ((euclideanBoundaryDistance U x)⁻¹ ^ p) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
      have hdist := (euclideanBoundaryDistance_pos hd hU hx).le
      simp only [euclideanBoundaryWeight, Real.inv_rpow hdist,
        Real.rpow_neg hdist]
    _ ≤ volume U * ENNReal.ofReal (((d : ℝ) / rho) ^ p / (1 - p)) := hmoment

theorem euclideanBoundaryWeightMoment_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {rho Rad p : ℝ}
    (hsand : HasBallSandwich U rho Rad) (hp0 : 0 < p) (hp1 : p < 1) :
    euclideanBoundaryWeightMoment U p ≤
      ENNReal.ofReal (((d : ℝ) / rho) ^ p / (1 - p)) := by
  obtain ⟨hrho, _hRad, c, hball, _hout⟩ := hsand
  have hUne : U.Nonempty :=
    ⟨c, hball (center_mem_euclideanBallAt c hrho)⟩
  have hV0 : volume U ≠ 0 :=
    volume_ne_zero_of_isOpenBoundedConvexDomain hU hUne
  have hVtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  rw [euclideanBoundaryWeightMoment, eVolumeAverage]
  apply (ENNReal.div_le_iff hV0 hVtop).mpr
  simpa only [mul_comm] using
    lintegral_euclideanBoundaryWeight_le hd hU
      ⟨hrho, _hRad, c, hball, _hout⟩ hp0 hp1

/-- Boundary-distance moment at the fractional Hardy exponent `2s`. -/
theorem euclideanBoundaryWeightMoment_two_mul_le (hd : 1 ≤ d)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {rho Rad s : ℝ}
    (hsand : HasBallSandwich U rho Rad)
    (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    euclideanBoundaryWeightMoment U (2 * s) ≤
      ENNReal.ofReal (((d : ℝ) / rho) ^ (2 * s) / (1 - 2 * s)) := by
  exact euclideanBoundaryWeightMoment_le hd hU hsand
    (by linarith only [hs.1]) (by linarith only [hs.2])

end

end HighContrast
end HCPolySupport
