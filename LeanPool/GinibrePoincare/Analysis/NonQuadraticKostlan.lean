/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticKostlan.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPotential
public import LeanPool.GinibrePoincare.Analysis.KostlanProductLaw
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticProductDensity

/-! # Kostlan's diagonal identity for unbounded radial tilts
Monotone convergence extends the Gaussian angular calculation to arbitrary
continuous nonnegative symmetric radial density ratios. No integrability
hypothesis is imposed on the tilt in the extended nonnegative identity.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
namespace GinibrePoincare
noncomputable section

private theorem kostlanWeight_nonneg' (n : ℕ) (z : Configuration n) :
    0 ≤ kostlanWeight n z :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (Complex.normSq_nonneg _) _

private theorem integrable_kostlanWeight' (n : ℕ) :
    Integrable (kostlanWeight n) (complexGaussianMeasure n) := by
  have he : kostlanWeight n = fun z : Configuration n => ∏ i, ‖z i‖ ^ (2*i.val) := by
    funext z
    unfold kostlanWeight
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Complex.sq_norm, ← pow_mul]
  rw [he]
  exact integrable_prod_norm_pow_complexGaussianMeasure n _

private theorem bounded_radial_weight_integrable (n : ℕ)
    (w : Configuration n → ℝ) (hw : Continuous w)
    (hi : Integrable w (complexGaussianMeasure n)) (hnn : ∀ z, 0 ≤ w z)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (C : ℝ)
    (hbound : ∀ r, ‖F r‖ ≤ C) :
    Integrable (fun z => w z * F (fun i => Complex.normSq (z i)))
      (complexGaussianMeasure n) := by
  apply (hi.mul_const C).mono'
  · apply Continuous.aestronglyMeasurable
    apply hw.mul
    exact hF.comp (continuous_pi fun i => Complex.continuous_normSq.comp (continuous_apply i))
  · filter_upwards with z
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hnn z)]
    exact mul_le_mul_of_nonneg_left (hbound _) (hnn z)

/-- Nonnegative version of the exact angular identity for bounded tests. -/
theorem lintegral_radial_vandermonde_eq_factorial_bounded (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hS : IsSymmetricRadiusTest n F)
    (hpos : ∀ r, 0 ≤ F r) (C : ℝ) (hC : ∀ r, ‖F r‖ ≤ C) :
    (∫⁻ z, ENNReal.ofReal (vandermondeWeight z * F (fun i => Complex.normSq (z i)))
      ∂complexGaussianMeasure n) =
    (n.factorial : ℝ≥0∞) * ∫⁻ z,
      ENNReal.ofReal (kostlanWeight n z * F (fun i => Complex.normSq (z i)))
      ∂complexGaussianMeasure n := by
  have hiv := bounded_radial_weight_integrable n vandermondeWeight
    (Complex.continuous_normSq.comp continuous_vandermonde)
    (integrable_vandermondeWeight_complexGaussianMeasure n)
    vandermondeWeight_nonneg F hF C hC
  have hik := bounded_radial_weight_integrable n (kostlanWeight n)
    (by unfold kostlanWeight; fun_prop) (integrable_kostlanWeight' n)
    (kostlanWeight_nonneg' n) F hF C hC
  rw [← ofReal_integral_eq_lintegral_ofReal hiv
    (ae_of_all _ fun z => mul_nonneg (vandermondeWeight_nonneg z) (hpos _)),
    ← ofReal_integral_eq_lintegral_ofReal hik
    (ae_of_all _ fun z => mul_nonneg (kostlanWeight_nonneg' n z) (hpos _))]
  rw [integral_radial_vandermonde_eq_factorial n hn F hF hS C hC,
    ENNReal.ofReal_mul (by positivity)]
  simp

private theorem ofReal_min_iSup (r : ℝ) :
    (⨆ k : ℕ, ENNReal.ofReal (min r (k : ℝ))) = ENNReal.ofReal r := by
  apply le_antisymm
  · exact iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · obtain ⟨k, hk⟩ := exists_nat_ge r
    exact le_iSup_of_le k (by rw [min_eq_left hk])

private theorem lintegral_min_radial_weight (n : ℕ)
    (w : Configuration n → ℝ) (hw : Measurable w) (hnn : ∀ z, 0 ≤ w z)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫⁻ z, ENNReal.ofReal (w z * F (fun i => Complex.normSq (z i)))
      ∂complexGaussianMeasure n) =
    ⨆ k : ℕ, ∫⁻ z,
      ENNReal.ofReal (w z * min (F (fun i => Complex.normSq (z i))) (k : ℝ))
      ∂complexGaussianMeasure n := by
  have hpoint : ∀ z, ENNReal.ofReal (w z * F (fun i => Complex.normSq (z i))) =
      ⨆ k : ℕ, ENNReal.ofReal (w z * min (F (fun i => Complex.normSq (z i))) (k : ℝ)) := by
    intro z
    simp_rw [ENNReal.ofReal_mul (hnn z)]
    rw [← ENNReal.mul_iSup, ofReal_min_iSup]
  simp_rw [hpoint]
  apply lintegral_iSup
  · intro k
    apply Measurable.ennreal_ofReal
    apply hw.mul
    apply Continuous.measurable
    apply Continuous.min _ continuous_const
    exact hF.comp (continuous_pi fun i => Complex.continuous_normSq.comp (continuous_apply i))
  · intro j k hjk z
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (min_le_min_left _ (Nat.cast_le.mpr hjk)) (hnn z))

/-- General Kostlan angular identity for arbitrary nonnegative continuous
symmetric radial tilts. Infinite partition integrals are allowed here. -/
theorem lintegral_radial_vandermonde_eq_factorial (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hS : IsSymmetricRadiusTest n F)
    (hpos : ∀ r, 0 ≤ F r) :
    (∫⁻ z, ENNReal.ofReal (vandermondeWeight z * F (fun i => Complex.normSq (z i)))
      ∂complexGaussianMeasure n) =
    (n.factorial : ℝ≥0∞) * ∫⁻ z,
      ENNReal.ofReal (kostlanWeight n z * F (fun i => Complex.normSq (z i)))
      ∂complexGaussianMeasure n := by
  rw [lintegral_min_radial_weight n vandermondeWeight
    (Complex.continuous_normSq.comp continuous_vandermonde).measurable vandermondeWeight_nonneg F
        hF,
    lintegral_min_radial_weight n (kostlanWeight n)
      (by unfold kostlanWeight; fun_prop) (kostlanWeight_nonneg' n) F hF,
    ENNReal.mul_iSup]
  apply iSup_congr
  intro k
  have hsk : IsSymmetricRadiusTest n (fun r => min (F r) (k : ℝ)) := by
    intro σ r
    exact congrArg (fun t : ℝ => min t (k : ℝ)) (hS σ r)
  have hpk : ∀ r, 0 ≤ min (F r) (k : ℝ) := fun r =>
    le_min (hpos r) (Nat.cast_nonneg k)
  have hck : ∀ r, ‖min (F r) (k : ℝ)‖ ≤ (k : ℝ) := by
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (hpk r)]
    exact min_le_right _ _
  exact lintegral_radial_vandermonde_eq_factorial_bounded n hn (fun r => min (F r) (k : ℝ))
    (hF.min continuous_const) hsk hpk (k : ℝ) hck

/-- A continuous scalar profile for the squared-radius representation of V. -/
def potentialSquaredRadiusProfile (V : Potential) (r : ℝ) : ℝ := V (Real.sqrt r : ℂ)

/-- Rotation invariance identifies the planar potential with its scalar profile. -/
theorem potential_eq_squaredRadiusProfile {V : Potential}
    (hV : IsRotationalPotential V) (z : ℂ) :
    V z = potentialSquaredRadiusProfile V (Complex.normSq z) := by
  unfold potentialSquaredRadiusProfile
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  by_cases hz : z = 0
  · simp [hz]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnC : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hu : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn]
  have he := hV (z / (‖z‖ : ℂ)) (‖z‖ : ℂ) hu
  rwa [div_mul_cancel₀ z hnC] at he

/-- Density ratio of the general confinement relative to the quadratic one. -/
def potentialRadialTilt (n : ℕ) (V : Potential) (r : Fin n → ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * ∑ i, (potentialSquaredRadiusProfile V (r i) - r i))

theorem continuous_potentialRadialTilt (n : ℕ) {V : Potential} (hV : Continuous V) :
    Continuous (potentialRadialTilt n V) := by
  unfold potentialRadialTilt potentialSquaredRadiusProfile
  apply Real.continuous_exp.comp
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro i hi
  apply Continuous.sub _ (continuous_apply i)
  exact hV.comp (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_apply i)))

theorem potentialRadialTilt_pos (n : ℕ) (V : Potential) (r : Fin n → ℝ) :
    0 < potentialRadialTilt n V r := Real.exp_pos _

theorem potentialRadialTilt_symmetric (n : ℕ) (V : Potential) :
    IsSymmetricRadiusTest n (potentialRadialTilt n V) := by
  intro σ r
  unfold potentialRadialTilt
  congr 2
  exact Equiv.sum_comp σ (fun i => potentialSquaredRadiusProfile V (r i) - r i)

/-- Pointwise multiplication by the radial tilt recovers the exact density. -/
theorem gaussianWeight_mul_potentialRadialTilt (n : ℕ) {V : Potential}
    (hV : IsRotationalPotential V) (z : Configuration n) :
    gaussianWeight n z * potentialRadialTilt n V (fun i => Complex.normSq (z i)) =
      Real.exp (-(n : ℝ) * ∑ i, V (z i)) := by
  unfold gaussianWeight potentialRadialTilt configurationNormSq
  rw [← Real.exp_add, Finset.sum_sub_distrib]
  simp_rw [← potential_eq_squaredRadiusProfile hV]
  congr 1
  ring

/-- The exact general density ratio identity retains the Vandermonde factor. -/
theorem ginibreWeight_mul_potentialRadialTilt (n : ℕ) {V : Potential}
    (hV : IsRotationalPotential V) (z : Configuration n) :
    ginibreWeight n z * potentialRadialTilt n V (fun i => Complex.normSq (z i)) =
      potentialWeight n V z := by
  unfold ginibreWeight potentialWeight
  rw [mul_right_comm, gaussianWeight_mul_potentialRadialTilt n hV]

/-- The arbitrary radial potential has the same angular diagonal identity,
without any Gaussian-polynomial integrability assumption on its density ratio. -/
theorem potentialRadialTilt_diagonal (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) :
    (∫⁻ z, ENNReal.ofReal (vandermondeWeight z *
      potentialRadialTilt n V (fun i => Complex.normSq (z i))) ∂complexGaussianMeasure n) =
    (n.factorial : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (kostlanWeight n z *
      potentialRadialTilt n V (fun i => Complex.normSq (z i))) ∂complexGaussianMeasure n :=
  lintegral_radial_vandermonde_eq_factorial n hn _ (continuous_potentialRadialTilt n hV)
    (potentialRadialTilt_symmetric n V) (fun r => (potentialRadialTilt_pos n V r).le)

/-- The general radial tilt integral is the actual Lebesgue partition integral
multiplied by the explicit Gaussian-reference scalar. -/
theorem potentialPartition_radialTilt (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) :
    (∫⁻ z, ENNReal.ofReal (vandermondeWeight z *
      potentialRadialTilt n V (fun i => Complex.normSq (z i))) ∂complexGaussianMeasure n) =
    ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) * potentialPartition n V := by
  rw [complexGaussianDensityIdentification n hn]
  unfold complexGaussianDensityMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_complexGaussianDensity n)
    (by apply Measurable.ennreal_ofReal; apply Continuous.measurable;
        exact (Complex.continuous_normSq.comp continuous_vandermonde).mul
          ((continuous_potentialRadialTilt n hVc).comp
            (continuous_pi fun i => Complex.continuous_normSq.comp (continuous_apply i))))]
  have he : ∀ z : Configuration n,
      (complexGaussianDensity n * (fun z => ENNReal.ofReal (vandermondeWeight z *
        potentialRadialTilt n V (fun i => Complex.normSq (z i))))) z =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) * ENNReal.ofReal (potentialWeight n V z) := by
    intro z
    simp only [Pi.mul_apply, complexGaussianDensity]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (gaussianWeight_nonneg n z)),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    calc
      (((n : ℝ) / Real.pi) ^ n * gaussianWeight n z) *
          (vandermondeWeight z * potentialRadialTilt n V (fun i => Complex.normSq (z i))) =
        ((n : ℝ) / Real.pi) ^ n *
          ((gaussianWeight n z * potentialRadialTilt n V (fun i => Complex.normSq (z i))) *
            vandermondeWeight z) := by ring
      _ = _ := by rw [gaussianWeight_mul_potentialRadialTilt n hVr]; rfl
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, potentialPartition_eq_lintegral]

/-- The concrete separable tilted measure used by the nonquadratic Kostlan law. -/
def rawPotentialKostlanReference (n : ℕ) (V : Potential) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity (fun z => ENNReal.ofReal (kostlanWeight n z *
    potentialRadialTilt n V (fun i => Complex.normSq (z i))))

/-- Its actual mass is fixed by the original finite partition integral. -/
theorem rawPotentialKostlanReference_mass (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) :
    (n.factorial : ℝ≥0∞) * rawPotentialKostlanReference n V Set.univ =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) * potentialPartition n V := by
  unfold rawPotentialKostlanReference
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← potentialRadialTilt_diagonal n hn hVc]
  exact potentialPartition_radialTilt n hn hVc hVr

/-- Unnormalized coordinate tilt for the general radial Kostlan law. -/
def potentialKostlanCoordinateWeight (n k : ℕ) (V : Potential) (z : ℂ) : ℝ :=
  Complex.normSq z ^ k * Real.exp (-(n : ℝ) * (V z - Complex.normSq z))

/-- The complex Gaussian coordinate law `complexCoordinateGaussianProbability n` reweighted by
the unnormalised density `potentialKostlanCoordinateWeight n k V`. -/
def rawPotentialKostlanCoordinateLaw (n k : ℕ) (V : Potential) : Measure ℂ :=
  (complexCoordinateGaussianProbability n : Measure ℂ).withDensity
    (fun z => ENNReal.ofReal (potentialKostlanCoordinateWeight n k V z))

instance rawPotentialKostlanCoordinateLaw_sigmaFinite (n k : ℕ) (V : Potential) :
    SigmaFinite (rawPotentialKostlanCoordinateLaw n k V) := by
  unfold rawPotentialKostlanCoordinateLaw
  infer_instance

theorem potentialKostlanCoordinateWeight_nonneg (n k : ℕ) (V : Potential) (z : ℂ) :
    0 ≤ potentialKostlanCoordinateWeight n k V z :=
  mul_nonneg (pow_nonneg (Complex.normSq_nonneg _) _) (Real.exp_pos _).le

theorem potentialKostlanCoordinateWeight_prod (n : ℕ) {V : Potential}
    (hV : IsRotationalPotential V) (z : Configuration n) :
    (∏ i : Fin n, potentialKostlanCoordinateWeight n i.val V (z i)) =
      kostlanWeight n z * potentialRadialTilt n V (fun i => Complex.normSq (z i)) := by
  unfold potentialKostlanCoordinateWeight kostlanWeight potentialRadialTilt
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  simp_rw [← potential_eq_squaredRadiusProfile hV]
  congr 2
  rw [Finset.mul_sum]

/-- The general separable reference is a genuine finite product of explicit
coordinate laws, before any normalization. -/
theorem rawPotentialKostlanReference_eq_product (n : ℕ) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) :
    rawPotentialKostlanReference n V =
      Measure.pi (fun i : Fin n => rawPotentialKostlanCoordinateLaw n i.val V) := by
  unfold rawPotentialKostlanCoordinateLaw
  rw [pi_withDensity_ofReal_eq_unconditional _ _
    (by intro i; unfold potentialKostlanCoordinateWeight;
        exact ((Complex.continuous_normSq.pow i.val).mul
          (Real.continuous_exp.comp (continuous_const.mul
            (hVc.sub Complex.continuous_normSq)))).measurable)
    (fun i z => potentialKostlanCoordinateWeight_nonneg n i.val V z)]
  unfold rawPotentialKostlanReference complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  congr 1
  funext z
  rw [potentialKostlanCoordinateWeight_prod n hVr]

/-- Exact finite-product factorization of the arbitrary radial partition
integral. The coordinate masses are their actual density integrals. -/
theorem potentialPartition_eq_coordinate_product (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) :
    ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) * potentialPartition n V =
      (n.factorial : ℝ≥0∞) *
        ∏ i : Fin n, rawPotentialKostlanCoordinateLaw n i.val V Set.univ := by
  rw [← rawPotentialKostlanReference_mass n hn hVc hVr,
    rawPotentialKostlanReference_eq_product n hVc hVr, Measure.pi_univ]

/-- Finite original partition implies positive finite total mass of the
separable reference, without separate moment assumptions. -/
theorem rawPotentialKostlanReference_mass_valid (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    0 < rawPotentialKostlanReference n V Set.univ ∧
      rawPotentialKostlanReference n V Set.univ < ⊤ := by
  have he := rawPotentialKostlanReference_mass n hn hVc hVr
  have hc : 0 < ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hpos : 0 < (n.factorial : ℝ≥0∞) * rawPotentialKostlanReference n V Set.univ := by
    rw [he]
    exact ENNReal.mul_pos_iff.mpr ⟨hc, potentialPartition_pos n hn hVc⟩
  have hlt : (n.factorial : ℝ≥0∞) * rawPotentialKostlanReference n V Set.univ < ⊤ := by
    rw [he]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  exact ⟨(ENNReal.mul_pos_iff.mp hpos).2,
    ENNReal.lt_top_of_mul_ne_top_right hlt.ne (ne_of_gt (ENNReal.mul_pos_iff.mp hpos).1)⟩

private theorem factor_mass_valid {n : ℕ} (m : Fin n → ℝ≥0∞)
    (hp : 0 < ∏ i, m i) (hf : (∏ i, m i) < ⊤) (i : Fin n) :
    0 < m i ∧ m i < ⊤ := by
  classical
  have hm : ∀ i : Fin n, m i ≠ 0 :=
    fun j => (Finset.prod_ne_zero_iff.mp (ne_of_gt hp)) j (Finset.mem_univ j)
  have hrest : (∏ j ∈ Finset.univ.erase i, m j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hm j
  have he : (∏ j : Fin n, m j) = m i * ∏ j ∈ Finset.univ.erase i, m j :=
    (Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)).symm
  exact ⟨pos_iff_ne_zero.mpr (hm i),
    ENNReal.lt_top_of_mul_ne_top_left (he ▸ hf.ne) hrest⟩

/-- All required one-coordinate moments are positive and finite as a
consequence of the original partition condition. -/
theorem rawPotentialKostlanCoordinateLaw_mass_valid (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (i : Fin n) :
    0 < rawPotentialKostlanCoordinateLaw n i.val V Set.univ ∧
      rawPotentialKostlanCoordinateLaw n i.val V Set.univ < ⊤ := by
  have hv := rawPotentialKostlanReference_mass_valid n hn hVc hVr hfin
  rw [rawPotentialKostlanReference_eq_product n hVc hVr, Measure.pi_univ] at hv
  exact factor_mass_valid _ hv.1 hv.2 i

/-- Normalized general Kostlan coordinate laws use their actual moments. -/
def potentialKostlanCoordinateLaw (n k : ℕ) (V : Potential) : Measure ℂ :=
  (rawPotentialKostlanCoordinateLaw n k V Set.univ)⁻¹ • rawPotentialKostlanCoordinateLaw n k V

/-- The concrete normalized general separable reference. -/
def potentialKostlanReference (n : ℕ) (V : Potential) : Measure (Configuration n) :=
  (rawPotentialKostlanReference n V Set.univ)⁻¹ • rawPotentialKostlanReference n V

theorem potentialKostlanCoordinateLaw_isProbabilityMeasure (n : ℕ) (hn : 0 < n)
    {V : Potential} (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (i : Fin n) :
    IsProbabilityMeasure (potentialKostlanCoordinateLaw n i.val V) := by
  have hv := rawPotentialKostlanCoordinateLaw_mass_valid n hn hVc hVr hfin i
  constructor
  change (rawPotentialKostlanCoordinateLaw n i.val V Set.univ)⁻¹ *
    rawPotentialKostlanCoordinateLaw n i.val V Set.univ = 1
  exact ENNReal.inv_mul_cancel (ne_of_gt hv.1) hv.2.ne

/-- The normalized nonquadratic reference is a product of independent
normalized coordinate laws. -/
theorem potentialKostlanReference_eq_product (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    potentialKostlanReference n V =
      Measure.pi (fun i : Fin n => potentialKostlanCoordinateLaw n i.val V) := by
  classical
  have hprob : ∀ i : Fin n, IsProbabilityMeasure (potentialKostlanCoordinateLaw n i.val V) :=
    fun i => potentialKostlanCoordinateLaw_isProbabilityMeasure n hn hVc hVr hfin i
  let := hprob
  symm
  apply Measure.pi_eq
  intro s hs
  unfold potentialKostlanReference
  rw [rawPotentialKostlanReference_eq_product n hVc hVr, Measure.smul_apply, Measure.pi_pi,
    Measure.pi_univ]
  unfold potentialKostlanCoordinateLaw
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.prod_inv_distrib, Finset.prod_mul_distrib]
  intro i hi j hj hij
  exact Or.inl (ne_of_gt (rawPotentialKostlanCoordinateLaw_mass_valid n hn hVc hVr hfin i).1)

/-- Pointwise Gaussian-density cancellation for the general potential. -/
theorem potentialRadialTilt_gaussianDensity (n : ℕ) {V : Potential}
    (hVr : IsRotationalPotential V) (z : Configuration n) :
    complexGaussianDensity n z * ENNReal.ofReal (vandermondeWeight z *
      potentialRadialTilt n V (fun i => Complex.normSq (z i))) =
    ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) * ENNReal.ofReal (potentialWeight n V z) := by
  simp only [complexGaussianDensity]
  rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity) (gaussianWeight_nonneg n z)),
      ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    (((n : ℝ) / Real.pi) ^ n * gaussianWeight n z) *
        (vandermondeWeight z * potentialRadialTilt n V (fun i => Complex.normSq (z i))) =
      ((n : ℝ) / Real.pi) ^ n *
        ((gaussianWeight n z * potentialRadialTilt n V (fun i => Complex.normSq (z i))) *
          vandermondeWeight z) := by ring
    _ = _ := by rw [gaussianWeight_mul_potentialRadialTilt n hVr]; rfl

/-- Unnormalized radial test integrals agree with the general independent
reference, with the exact original partition scalar. -/
theorem potential_radial_raw_lintegral (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V)
    (G : (Fin n → ℝ) → ℝ) (hG : Continuous G) (hGS : IsSymmetricRadiusTest n G)
    (hGp : ∀ r, 0 ≤ G r) :
    ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) *
      (∫⁻ z, ENNReal.ofReal (G (fun i => Complex.normSq (z i))) ∂rawPotentialMeasure n V) =
    (n.factorial : ℝ≥0∞) *
      (∫⁻ z, ENNReal.ofReal (G (fun i => Complex.normSq (z i)))
        ∂rawPotentialKostlanReference n V) := by
  let H : (Fin n → ℝ) → ℝ := fun r => potentialRadialTilt n V r * G r
  have hH : Continuous H := (continuous_potentialRadialTilt n hVc).mul hG
  have hHS : IsSymmetricRadiusTest n H := by
    intro σ r
    dsimp [H]
    rw [potentialRadialTilt_symmetric n V σ r, hGS σ r]
  have hHp : ∀ r, 0 ≤ H r := fun r => mul_nonneg (potentialRadialTilt_pos n V r).le (hGp r)
  have htest : Measurable (fun z : Configuration n => ENNReal.ofReal (G (fun i => Complex.normSq (z
      i)))) :=
    (hG.comp (continuous_pi fun i => Complex.continuous_normSq.comp (continuous_apply
        i))).measurable.ennreal_ofReal
  have hdiag := lintegral_radial_vandermonde_eq_factorial n hn H hH hHS hHp
  have hleft :
      (∫⁻ z, ENNReal.ofReal (vandermondeWeight z * H (fun i => Complex.normSq (z i)))
        ∂complexGaussianMeasure n) =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) *
        (∫⁻ z, ENNReal.ofReal (G (fun i => Complex.normSq (z i))) ∂rawPotentialMeasure n V) := by
    rw [complexGaussianDensityIdentification n hn]
    unfold complexGaussianDensityMeasure rawPotentialMeasure
    rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_complexGaussianDensity n)
      (by apply Measurable.ennreal_ofReal; apply Continuous.measurable;
          exact (Complex.continuous_normSq.comp continuous_vandermonde).mul
            (hH.comp (continuous_pi fun i => Complex.continuous_normSq.comp (continuous_apply i)))),
      lintegral_withDensity_eq_lintegral_mul _ (measurable_potentialDensity n hVc) htest,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    dsimp only [Pi.mul_apply, H]
    rw [← mul_assoc (vandermondeWeight z), ENNReal.ofReal_mul
      (mul_nonneg (vandermondeWeight_nonneg z) (potentialRadialTilt_pos n V _).le)]
    rw [← mul_assoc, potentialRadialTilt_gaussianDensity n hVr]
    exact mul_assoc _ _ _
  have hkw : Continuous (kostlanWeight n) := by unfold kostlanWeight; fun_prop
  have hright :
      (∫⁻ z, ENNReal.ofReal (kostlanWeight n z * H (fun i => Complex.normSq (z i)))
        ∂complexGaussianMeasure n) =
      (∫⁻ z, ENNReal.ofReal (G (fun i => Complex.normSq (z i)))
        ∂rawPotentialKostlanReference n V) := by
    unfold rawPotentialKostlanReference
    rw [lintegral_withDensity_eq_lintegral_mul _
      (by apply Measurable.ennreal_ofReal; apply Continuous.measurable;
          exact hkw.mul
            ((continuous_potentialRadialTilt n hVc).comp
              (continuous_pi fun i => Complex.continuous_normSq.comp (continuous_apply i)))) htest]
    apply lintegral_congr
    intro z
    dsimp only [Pi.mul_apply, H]
    rw [← mul_assoc, ENNReal.ofReal_mul
      (mul_nonneg (kostlanWeight_nonneg' n z) (potentialRadialTilt_pos n V _).le)]
  rw [hleft, hright] at hdiag
  exact hdiag

/-- General nonquadratic Kostlan factorization: every continuous nonnegative
symmetric radial observable has the same expectation under the actual gas
and the independent normalized coordinate laws. Unbounded tests are allowed. -/
theorem potential_radial_lintegral_eq_product (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (G : (Fin n → ℝ) → ℝ) (hG : Continuous G) (hGS : IsSymmetricRadiusTest n G)
    (hGp : ∀ r, 0 ≤ G r) :
    (∫⁻ z, ENNReal.ofReal (G (fun i => Complex.normSq (z i))) ∂potentialMeasure n V) =
      ∫⁻ z, ENNReal.ofReal (G (fun i => Complex.normSq (z i)))
        ∂Measure.pi (fun i : Fin n => potentialKostlanCoordinateLaw n i.val V) := by
  rw [← potentialKostlanReference_eq_product n hn hVc hVr hfin]
  unfold potentialMeasure potentialKostlanReference
  rw [lintegral_smul_measure, lintegral_smul_measure]
  let c := ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n)
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (by positivity)
  have hZ := potentialPartition_pos n hn hVc
  have hM := rawPotentialKostlanReference_mass_valid n hn hVc hVr hfin
  have he := rawPotentialKostlanReference_mass n hn hVc hVr
  have ht := potential_radial_raw_lintegral n hn hVc hVr G hG hGS hGp
  apply (ENNReal.mul_left_inj (ne_of_gt (ENNReal.mul_pos_iff.mpr ⟨hc, hZ⟩))
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne).mp
  simp only [smul_eq_mul]
  conv_lhs => rw [mul_comm]
  conv_rhs => rw [mul_comm]
  change (c * potentialPartition n V) * (_ * _) = (c * potentialPartition n V) * (_ * _)
  rw [mul_assoc c, ENNReal.mul_inv_cancel_left hZ.ne' hfin.ne, ← he,
    mul_assoc (n.factorial : ℝ≥0∞), ENNReal.mul_inv_cancel_left hM.1.ne' hM.2.ne]
  exact ht

private theorem bounded_radiusTest_integrable (n : ℕ) (μ : Measure (Configuration n))
    [IsProbabilityMeasure μ] (G : (Fin n → ℝ) → ℝ) (hG : Continuous G)
    (C : ℝ) (hC : ∀ r, ‖G r‖ ≤ C) :
    Integrable (fun z => G (fun i => Complex.normSq (z i))) μ := by
  apply (integrable_const C).mono'
  · exact (hG.comp (continuous_pi fun i =>
      Complex.continuous_normSq.comp (continuous_apply i))).aestronglyMeasurable
  · exact ae_of_all _ fun z => hC _

/-- Signed bounded continuous radial expectations transfer to the actual
independent coordinate product for arbitrary continuous radial confinement. -/
theorem potential_radial_integral_eq_product (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (G : (Fin n → ℝ) → ℝ) (hG : Continuous G) (hGS : IsSymmetricRadiusTest n G)
    (C : ℝ) (hC : ∀ r, ‖G r‖ ≤ C) :
    (∫ z, G (fun i => Complex.normSq (z i)) ∂potentialMeasure n V) =
      ∫ z, G (fun i => Complex.normSq (z i))
        ∂Measure.pi (fun i : Fin n => potentialKostlanCoordinateLaw n i.val V) := by
  let := potentialMeasure_isProbabilityMeasure n hn hVc hfin
  have hp : ∀ i : Fin n, IsProbabilityMeasure (potentialKostlanCoordinateLaw n i.val V) :=
    fun i => potentialKostlanCoordinateLaw_isProbabilityMeasure n hn hVc hVr hfin i
  let := hp
  let ν := Measure.pi (fun i : Fin n => potentialKostlanCoordinateLaw n i.val V)
  have hCpos : 0 ≤ C := (norm_nonneg (G (fun _ => 0))).trans (hC _)
  have htransfer : ∀ (H : (Fin n → ℝ) → ℝ), Continuous H → IsSymmetricRadiusTest n H →
      (∀ r, 0 ≤ H r) → (∀ r, ‖H r‖ ≤ C) →
      (∫ z, H (fun i => Complex.normSq (z i)) ∂potentialMeasure n V) =
        ∫ z, H (fun i => Complex.normSq (z i)) ∂ν := by
    intro H hH hHS hHp hHC
    have he := potential_radial_lintegral_eq_product n hn hVc hVr hfin H hH hHS hHp
    rw [← ofReal_integral_eq_lintegral_ofReal
      (bounded_radiusTest_integrable n _ H hH C hHC) (ae_of_all _ fun z => hHp _),
      ← ofReal_integral_eq_lintegral_ofReal
      (bounded_radiusTest_integrable n _ H hH C hHC) (ae_of_all _ fun z => hHp _)] at he
    have hre := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun z => hHp _))] using hre
  let P := fun r => max (G r) 0
  let N := fun r => max (-G r) 0
  have hP : Continuous P := hG.max continuous_const
  have hN : Continuous N := hG.neg.max continuous_const
  have hPS : IsSymmetricRadiusTest n P := by
    intro σ r; exact congrArg (fun x => max x 0) (hGS σ r)
  have hNS : IsSymmetricRadiusTest n N := by
    intro σ r; exact congrArg (fun x => max (-x) 0) (hGS σ r)
  have hPp : ∀ r, 0 ≤ P r := fun r => le_max_right _ _
  have hNp : ∀ r, 0 ≤ N r := fun r => le_max_right _ _
  have hPC : ∀ r, ‖P r‖ ≤ C := by
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (hPp r)]
    exact max_le ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC r)) hCpos
  have hNC : ∀ r, ‖N r‖ ≤ C := by
    intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (hNp r)]
    exact max_le ((neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using hC r)) hCpos
  have hsplit : G = fun r => P r - N r := by
    funext r
    dsimp [P, N]
    by_cases hg : 0 ≤ G r
    · rw [max_eq_left hg, max_eq_right (neg_nonpos.mpr hg), sub_zero]
    · have hg' := le_of_not_ge hg
      rw [max_eq_right hg', max_eq_left (neg_nonneg.mpr hg')]
      ring
  have hPeq := htransfer P hP hPS hPp hPC
  have hNeq := htransfer N hN hNS hNp hNC
  rw [hsplit]
  rw [integral_sub (bounded_radiusTest_integrable n _ P hP C hPC)
    (bounded_radiusTest_integrable n _ N hN C hNC),
    integral_sub (bounded_radiusTest_integrable n _ P hP C hPC)
    (bounded_radiusTest_integrable n _ N hN C hNC), hPeq, hNeq]

/-- Square entropy transfers exactly to the arbitrary-potential independent
product. This is an actual entropy identity, without an LSI premise. -/
theorem potential_radial_entropy_eq_product (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hc : HasCompactSupport F)
    (hS : IsSymmetricRadiusTest n F) :
    squareEntropy (potentialMeasure n V) (fun z => F (fun i => Complex.normSq (z i))) =
      squareEntropy (Measure.pi (fun i : Fin n => potentialKostlanCoordinateLaw n i.val V))
        (fun z => F (fun i => Complex.normSq (z i))) := by
  apply squareEntropy_eq_of_moments
  · have hs : HasCompactSupport (fun r => F r ^ 2) := by
      apply hc.mono
      intro r hr hz
      exact hr (by simp [hz])
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous (hF.pow 2)
    exact potential_radial_integral_eq_product n hn hVc hVr hfin (fun r => F r ^ 2)
      (hF.pow 2) (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2) (hS σ r)) C hC
  · obtain ⟨C, hC⟩ := (compactSupport_square_mul_log hc).exists_bound_of_continuous
      (continuous_square_mul_log hF)
    exact potential_radial_integral_eq_product n hn hVc hVr hfin
      (fun r => F r ^ 2 * Real.log (F r ^ 2)) (continuous_square_mul_log hF)
      (by intro σ r; exact congrArg (fun x : ℝ => x ^ 2 * Real.log (x ^ 2)) (hS σ r)) C hC

end
end GinibrePoincare
