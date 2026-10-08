/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleExcessRigidityPrep
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineRegularityJointAssembly

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleFixedCubeExcess

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Vanishing finite affine excess on a fixed cube

This module aligns the two-scale Caccioppoli output with the outer scale of
finite-excess decay by restricting the exact realization on `Q_(q+2)` to
`Q_q`.  The restricted solutions still represent the frozen global pair
exactly, and their excess on every fixed cube tends to zero.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set _root_.Filter
open scoped ENNReal Topology

noncomputable section

/-- Restricting the exact realization on `Q_q` to `Q_(q-2)` converts the
two-scale Caccioppoli growth estimate into a top-scale energy estimate. -/
theorem exists_scalarIdentityLiouvilleFiniteTopEnergyGrowth
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ)
    (hdelta : delta ≤ 1) (hgood : ScalarIdentityGoodTail a s delta n)
    {b : CoeffField d} {theta : ℝ} (hb : IsAELocallyUniformlyElliptic b)
    (hcoeff : ∀ q : ℕ,
      Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))] b)
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemLiouvilleClass b theta v Dv) :
    ∃ u : ∀ q : ℕ,
        Book.Ch03.CubeSolution (originCube d ((q : ℤ) - 2)) a,
      (∀ q, (u q).toH1.toFun = v ∧ (u q).toH1.grad = Dv) ∧
        Tendsto
          (fun q : ℕ => ENNReal.ofReal
            (Real.rpow 3 (-theta * (q : ℝ)) *
              Book.Ch03.h1EnergyNormOnCube
                (originCube d ((q : ℤ) - 2)) a (u q).toH1))
          atTop (nhds 0) := by
  obtain ⟨C, hC, z, hz, hgrowth⟩ :=
    exists_scalarIdentityLiouvilleFiniteGradientGrowth
      d s hs hs_lt a delta n hdelta hgood hb hcoeff hv
  let u : ∀ q : ℕ,
      Book.Ch03.CubeSolution (originCube d ((q : ℤ) - 2)) a :=
    fun q => finiteCubeSolutionRestriction a (by omega : (q : ℤ) - 2 ≤ (q : ℤ))
      (z q)
  have hu : ∀ q, (u q).toH1.toFun = v ∧ (u q).toH1.grad = Dv := by
    intro q
    constructor
    · simpa only [u, finiteCubeSolutionRestriction_toFun] using (hz q).1
    · simpa only [u, finiteCubeSolutionRestriction_grad] using (hz q).2
  refine ⟨u, hu, ?_⟩
  have hbase : Tendsto
      (fun q : ℕ => ENNReal.ofReal
        ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-theta) *
          Book.Ch03.h1EnergyNormOnCube
            (originCube d ((q : ℤ) - 2)) a (u q).toH1))
      atTop (nhds 0) := by
    convert hgrowth using 1
    funext q
    rw [finiteCenteredCubeSolutionEnergy_eq_of_le a (q : ℤ) (z q)
      ((q : ℤ) - 2) (by omega)]
  have hmul := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal (Real.rpow (Real.sqrt d) theta)) hbase
    (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hmul
  convert hmul using 1
  funext q
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  symm
  calc
    ENNReal.ofReal (Real.rpow (Real.sqrt d) theta) *
        ENNReal.ofReal
          ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-theta) *
            Book.Ch03.h1EnergyNormOnCube
              (originCube d ((q : ℤ) - 2)) a (u q).toH1) =
      ENNReal.ofReal (Real.rpow (Real.sqrt d) theta *
        ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-theta) *
          Book.Ch03.h1EnergyNormOnCube
            (originCube d ((q : ℤ) - 2)) a (u q).toH1)) :=
      (ENNReal.ofReal_mul (Real.rpow_nonneg hsqrt.le theta)).symm
    _ = ENNReal.ofReal (Real.rpow 3 (-theta * (q : ℝ)) *
          Book.Ch03.h1EnergyNormOnCube
            (originCube d ((q : ℤ) - 2)) a (u q).toH1) := by
      congr 1
      rw [Real.mul_rpow hsqrt.le (by positivity : (0 : ℝ) ≤ 3 ^ q)]
      calc
        Real.rpow (Real.sqrt d) theta *
            (Real.rpow (Real.sqrt d) (-theta) *
              Real.rpow ((3 : ℝ) ^ q) (-theta) *
                Book.Ch03.h1EnergyNormOnCube
                  (originCube d ((q : ℤ) - 2)) a (u q).toH1) =
          (Real.rpow (Real.sqrt d) theta *
            Real.rpow (Real.sqrt d) (-theta)) *
              (Real.rpow ((3 : ℝ) ^ q) (-theta) *
                Book.Ch03.h1EnergyNormOnCube
                  (originCube d ((q : ℤ) - 2)) a (u q).toH1) := by ring
        _ = Real.rpow 3 (-theta * (q : ℝ)) *
              Book.Ch03.h1EnergyNormOnCube
                (originCube d ((q : ℤ) - 2)) a (u q).toH1 := by
          have hcancel : Real.rpow (Real.sqrt d) theta *
              Real.rpow (Real.sqrt d) (-theta) = 1 := by
            simpa only [add_neg_cancel, Real.rpow_zero, Real.rpow_eq_pow] using
              (Real.rpow_add hsqrt theta (-theta)).symm
          have hthree : Real.rpow ((3 : ℝ) ^ q) (-theta) =
              Real.rpow 3 (-theta * (q : ℝ)) := by
            calc
              Real.rpow ((3 : ℝ) ^ q) (-theta) =
                  Real.rpow (Real.rpow 3 (q : ℝ)) (-theta) := by
                    apply congrArg (fun x : ℝ => Real.rpow x (-theta))
                    exact (Real.rpow_natCast 3 q).symm
              _ = Real.rpow 3 ((q : ℝ) * (-theta)) :=
                (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)
                  (q : ℝ) (-theta)).symm
              _ = Real.rpow 3 (-theta * (q : ℝ)) := by ring_nf
          rw [hcancel, one_mul, hthree]

/-- A real-rate excess estimate with exponent strictly above the energy-growth
exponent forces the excess on a fixed cube to vanish. -/
theorem tendsto_fixedFiniteAffineGradientExcess_of_realRate
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {theta eta Cdec : ℝ} (hCdec : 0 ≤ Cdec) (heta : theta < eta)
    (k : ℤ)
    (u : ∀ q : ℕ,
      Book.Ch03.CubeSolution (originCube d ((q : ℤ) - 2)) a)
    (hgrowth : Tendsto
      (fun q : ℕ => ENNReal.ofReal
        (Real.rpow 3 (-theta * (q : ℝ)) *
          Book.Ch03.h1EnergyNormOnCube
            (originCube d ((q : ℤ) - 2)) a (u q).toH1))
      atTop (nhds 0))
    (hrate : ∀ᶠ q : ℕ in atTop,
      finiteAffineGradientExcess a k ((q : ℤ) - 2) (u q) ≤
        ENNReal.ofReal
            (Cdec * Real.rpow 3
              (-eta * ((((q : ℤ) - 2) - k : ℤ) : ℝ))) *
          finiteAffineGradientExcess a ((q : ℤ) - 2) ((q : ℤ) - 2) (u q)) :
    Tendsto
      (fun q : ℕ => finiteAffineGradientExcess a k ((q : ℤ) - 2) (u q))
      atTop (nhds 0) := by
  have hgap : 0 < eta - theta := sub_pos.mpr heta
  obtain ⟨Q, hQ⟩ := exists_nat_gt
    (eta * (2 + (k : ℝ)) / (eta - theta))
  have hthreshold : eta * (2 + (k : ℝ)) <
      (eta - theta) * (Q : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hgap).mp hQ
  have hcoef : ∀ᶠ q : ℕ in atTop,
      Cdec * Real.rpow 3
          (-eta * ((((q : ℤ) - 2) - k : ℤ) : ℝ)) ≤
        Cdec * Real.rpow 3 (-theta * (q : ℝ)) := by
    filter_upwards [eventually_ge_atTop Q] with q hq
    have hQq : (Q : ℝ) ≤ q := by exact_mod_cast hq
    have hlinear : eta * (2 + (k : ℝ)) ≤
        (eta - theta) * (q : ℝ) :=
      hthreshold.le.trans
        (mul_le_mul_of_nonneg_left hQq hgap.le)
    have hexp : -eta * ((((q : ℤ) - 2) - k : ℤ) : ℝ) ≤
        -theta * (q : ℝ) := by
      push_cast
      linarith only [hlinear]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp)
      hCdec
  have hupper : Tendsto
      (fun q : ℕ => ENNReal.ofReal Cdec *
        ENNReal.ofReal
          (Real.rpow 3 (-theta * (q : ℝ)) *
            Book.Ch03.h1EnergyNormOnCube
              (originCube d ((q : ℤ) - 2)) a (u q).toH1))
      atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal Cdec) hgrowth (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ => bot_le
  filter_upwards [hrate, hcoef] with q hrateq hcoefq
  let E : ℝ := Book.Ch03.h1EnergyNormOnCube
    (originCube d ((q : ℤ) - 2)) a (u q).toH1
  have htop := finiteAffineGradientExcess_self_le_solutionEnergy
    a ((q : ℤ) - 2) (u q)
  have hcoefENN : ENNReal.ofReal
      (Cdec * Real.rpow 3
        (-eta * ((((q : ℤ) - 2) - k : ℤ) : ℝ))) ≤
      ENNReal.ofReal (Cdec * Real.rpow 3 (-theta * (q : ℝ))) :=
    ENNReal.ofReal_mono hcoefq
  calc
    finiteAffineGradientExcess a k ((q : ℤ) - 2) (u q) ≤
        ENNReal.ofReal
            (Cdec * Real.rpow 3
              (-eta * ((((q : ℤ) - 2) - k : ℤ) : ℝ))) *
          finiteAffineGradientExcess a ((q : ℤ) - 2) ((q : ℤ) - 2) (u q) :=
      hrateq
    _ ≤ ENNReal.ofReal
            (Cdec * Real.rpow 3
              (-eta * ((((q : ℤ) - 2) - k : ℤ) : ℝ))) *
          ENNReal.ofReal E := mul_le_mul_right htop _
    _ ≤ ENNReal.ofReal (Cdec * Real.rpow 3 (-theta * (q : ℝ))) *
          ENNReal.ofReal E := mul_le_mul_left hcoefENN _
    _ = ENNReal.ofReal Cdec * ENNReal.ofReal
          (Real.rpow 3 (-theta * (q : ℝ)) * E) := by
      rw [ENNReal.ofReal_mul hCdec, mul_assoc]
      congr 1
      exact (ENNReal.ofReal_mul
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)).symm

/-- Good-tail finite regularity and Liouville growth jointly produce exact
finite realizations whose affine-gradient excess vanishes on every fixed
centered cube beyond the good-tail base. -/
theorem exists_scalarIdentityLiouvilleFixedCubeExcessVanishingConstants
    (d : ℕ) [NeZero d] (s theta : ℝ) (hs : 0 < s)
    (hs_lt : s < 1 / 2) (htheta : theta < 1) :
    ∃ eta Cfamily c Cdec : ℝ,
      max theta (1 / 2 : ℝ) < eta ∧ eta < 1 ∧
      1 ≤ Cfamily ∧ c ∈ Ioo (0 : ℝ) 1 ∧ 0 < Cdec ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        (∃! Phi : Vec d → NormalizedLocalH1Carrier d,
          IsFiniteAffineCorrectionJointLocalEquation a Phi) ∧
        ∀ {b : CoeffField d}, IsAELocallyUniformlyElliptic b →
          (∀ q : ℕ,
            Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a
              =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))] b) →
          ∀ {v : Vec d → ℝ} {Dv : Vec d → Vec d},
            MemLiouvilleClass b theta v Dv →
            ∃ u : ∀ q : ℕ,
                Book.Ch03.CubeSolution (originCube d ((q : ℤ) - 2)) a,
              (∀ q, (u q).toH1.toFun = v ∧ (u q).toH1.grad = Dv) ∧
              ∀ k : ℤ, n ≤ k →
                Tendsto
                  (fun q : ℕ =>
                    finiteAffineGradientExcess a k ((q : ℤ) - 2) (u q))
                  atTop (nhds 0) := by
  obtain ⟨eta, hetaMax, heta1⟩ :=
    exists_excessDecayExponent_gt_max_half htheta
  have heta0 : 0 ≤ eta := by
    have : (0 : ℝ) < eta := (by norm_num : (0 : ℝ) < 1 / 2).trans
      ((le_max_right theta (1 / 2 : ℝ)).trans_lt hetaMax)
    exact this.le
  have hthetaEta : theta < eta :=
    (le_max_left theta (1 / 2 : ℝ)).trans_lt hetaMax
  obtain ⟨Cfamily, c, Cdec, hCfamily, hc, hCdec, hall⟩ :=
    exists_scalarIdentityFiniteExcessDecayAndJointLocalEquationConstants
      d s eta hs hs_lt heta0 heta1
  refine ⟨eta, Cfamily, c, Cdec, hetaMax, heta1, hCfamily, hc, hCdec, ?_⟩
  intro a delta n hdelta hgood
  have hdeltaOne : delta ≤ 1 :=
    hdelta.2.trans (le_of_lt hc.2)
  have hbaseAssembly := hall a delta n hdelta hgood
  refine ⟨hbaseAssembly.1, ?_⟩
  intro b hb hcoeff v Dv hv
  obtain ⟨u, hu, hgrowth⟩ :=
    exists_scalarIdentityLiouvilleFiniteTopEnergyGrowth
      d s hs hs_lt a delta n hdeltaOne hgood hb hcoeff hv
  refine ⟨u, hu, ?_⟩
  intro k hnk
  have hgoodk : ScalarIdentityGoodTail a s delta k :=
    hgood.mono_start hnk
  have hkAssembly := hall a delta k hdelta hgoodk
  have hrate : ∀ᶠ q : ℕ in atTop,
      finiteAffineGradientExcess a k ((q : ℤ) - 2) (u q) ≤
        ENNReal.ofReal
            (Cdec * Real.rpow 3
              (-eta * ((((q : ℤ) - 2) - k : ℤ) : ℝ))) *
          finiteAffineGradientExcess a ((q : ℤ) - 2) ((q : ℤ) - 2) (u q) := by
    filter_upwards [eventually_ge_atTop (k + 3).toNat] with q hq
    have hkq : k < (q : ℤ) - 2 := by
      have hkbase : k + 3 ≤ ((k + 3).toNat : ℤ) := Int.self_le_toNat _
      have hcast : ((k + 3).toNat : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
      omega
    obtain ⟨Q, hQ, hdecay⟩ := hkAssembly.2 ((q : ℤ) - 2) hkq
    exact hdecay (u q)
  exact tendsto_fixedFiniteAffineGradientExcess_of_realRate
    a hCdec.le hthetaEta k u hgrowth hrate

end

end HighContrast
end HCPolySupport
