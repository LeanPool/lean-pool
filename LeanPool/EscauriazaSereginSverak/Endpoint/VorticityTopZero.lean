/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopZeroTools

/-!
# The terminal value of the vorticity

If the velocity has zero weak trace at time zero, the continuous representative of the vorticity
below an exterior top point vanishes at the top time (`lem:vorticity-top-extension`, trace
identification): the pairing of the representative with a spatial test is continuous up to the
top time, agrees on almost every slice with the pairing of the velocity with the curl of the
test, and the latter tends to zero.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak curl identity on almost every slice below an exterior top point. -/
theorem vorticityTopZero_ae_slice {U : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {q : ParabolicPoint → ℝ} {R₂ M E : ℝ}
    (hfam : ∀ (x₁ : Vec3) (t₁ : ℝ), R₂ < vec3EuclideanNorm x₁ →
      t₁ ∈ Ioo (-2 : ℝ) 0 →
      ∃ (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω ∧ IsOpen I ∧
        closure (parabolicCylinder x₁ t₁ 1) ⊆ spaceTimeSet Ω I ∧
        IsSuitableWeakSolution Ω I 3 U DU q
          (0 : ParabolicPoint → Vec3) ∧
        (∀ᵐ z ∂(volume.restrict (parabolicCylinder x₁ t₁ 1)),
          vec3EuclideanNorm (U z) ≤ M) ∧
        (∫⁻ z in parabolicCylinder x₁ t₁ 1,
          ‖DU z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (E ^ 2))
    {x₁ : Vec3} (hx₁ : R₂ < vec3EuclideanNorm x₁) {φ : Vec3 → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφB : tsupport φ ⊆ vec3Ball x₁ 1) :
    ∀ᵐ t, t ∈ Iio (0 : ℝ) → t ∈ Ioi (-1 : ℝ) →
      ∫ x, ∑ i : Fin 3, weakVorticity DU (x, t) i * φ x i =
        ∫ x, ∑ i : Fin 3, U (x, t) i * spatialTestCurl φ x i := by
  have key : ∀ n : ℕ, ∀ᵐ t, t ∈ Ioo (-(1 / ((n : ℝ) + 8)) - 1) (-(1 / ((n : ℝ) + 8))) →
      ∫ x, ∑ i : Fin 3, weakVorticity DU (x, t) i * φ x i =
        ∫ x, ∑ i : Fin 3, U (x, t) i * spatialTestCurl φ x i := by
    intro n
    have hn8 : (0 : ℝ) < (n : ℝ) + 8 := by positivity
    have hpos : 0 < 1 / ((n : ℝ) + 8) := by positivity
    have hle : 1 / ((n : ℝ) + 8) ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [Nat.cast_nonneg (α := ℝ) n])
    obtain ⟨Ω, I, hΩ, hI, hcl, hsws, -, -⟩ :=
      hfam x₁ (-(1 / ((n : ℝ) + 8))) hx₁ ⟨by linarith only [hle], by linarith only [hpos]⟩
    obtain ⟨Ω', J, hbox, hsub⟩ := vorticity_exists_localBox_of_closure hΩ hI hsws.2.2.1 hcl
    have hmid : -(1 / ((n : ℝ) + 8)) - 1 / 2 ∈
        Ioo (-(1 / ((n : ℝ) + 8)) - 1) (-(1 / ((n : ℝ) + 8))) :=
      ⟨by linarith only [], by linarith only []⟩
    have hball : vec3Ball x₁ 1 ⊆ Ω' := fun y hy =>
      (@hsub (y, -(1 / ((n : ℝ) + 8)) - 1 / 2) ⟨hy, hmid⟩).1
    have hx₁mem : x₁ ∈ vec3Ball x₁ 1 := by
      change vec3EuclideanNorm (x₁ - x₁) < 1
      rw [sub_self, vec3EuclideanNorm_zero]
      norm_num
    have hJ : Ioo (-(1 / ((n : ℝ) + 8)) - 1) (-(1 / ((n : ℝ) + 8))) ⊆ J := fun s hs =>
      (@hsub (x₁, s) ⟨hx₁mem, hs⟩).2
    have hfin : volume Ω' ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono subset_closure) hbox.2.1.measure_lt_top).ne
    have hInt := CKN.isSuitableWeakSolution_iff_integrable.mp hsws
    have hmem := CKN.slice_memLp_ae_of_sws hInt hbox
    have hweak : ∀ᵐ s ∂(volume.restrict J), ∀ i : Fin 3,
        CKN.HasWeakGradientOn Ω' (fun x => U (x, s) i) (fun x => DU (x, s) i) :=
      ae_all_iff.2 (suitableWeakGradientOnSlices hsws Ω' J hbox)
    filter_upwards [ae_imp_of_ae_restrict (hmem.and hweak)] with s hs hsI
    obtain ⟨⟨hu, hDu⟩, hw⟩ := hs (hJ hsI)
    exact vorticityTopZero_slice_pairing hfin hu hDu hw hφ hφc (hφB.trans hball)
  filter_upwards [ae_all_iff.2 key] with t ht htneg htgt
  have ha : 0 < -t := neg_pos.2 htneg
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / -t)
  have hn8 : (0 : ℝ) < (n : ℝ) + 8 := by positivity
  have h1 : 1 / -t < (n : ℝ) + 8 := by linarith only [hn]
  have h2 : 1 / ((n : ℝ) + 8) < -t := by
    rw [div_lt_iff₀ hn8]
    rw [div_lt_iff₀ ha] at h1
    linarith only [h1]
  have hpos : 0 < 1 / ((n : ℝ) + 8) := by positivity
  have hle : 1 / ((n : ℝ) + 8) ≤ 1 / 8 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have htgt' : -1 < t := htgt
  exact ht n ⟨by linarith only [hpos, htgt'], by linarith only [h2]⟩

/-- The continuous representative of the vorticity below an exterior top point vanishes at the
top time. -/
theorem vorticityTop_zero {U : ParabolicPoint → Vec3}
    {DU : ParabolicPoint → Fin 3 → Vec3} {q : ParabolicPoint → ℝ} {R₂ M E : ℝ}
    (hfam : ∀ (x₁ : Vec3) (t₁ : ℝ), R₂ < vec3EuclideanNorm x₁ →
      t₁ ∈ Ioo (-2 : ℝ) 0 →
      ∃ (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω ∧ IsOpen I ∧
        closure (parabolicCylinder x₁ t₁ 1) ⊆ spaceTimeSet Ω I ∧
        IsSuitableWeakSolution Ω I 3 U DU q
          (0 : ParabolicPoint → Vec3) ∧
        (∀ᵐ z ∂(volume.restrict (parabolicCylinder x₁ t₁ 1)),
          vec3EuclideanNorm (U z) ≤ M) ∧
        (∫⁻ z in parabolicCylinder x₁ t₁ 1,
          ‖DU z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (E ^ 2))
    (htrace : HasZeroDistributionalVelocityTrace U)
    {x₁ : Vec3} (hx₁ : R₂ < vec3EuclideanNorm x₁) {ω : Fin 3 → Vec3 × ℝ → ℝ} {C : ℝ}
    (hωc : ∀ i, ContinuousOn (ω i)
      ({x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ 1 / 2} ×ˢ Icc ((0 : ℝ) - 1 / 4) 0))
    (hωb : ∀ i, ∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₁) ≤ 1 / 2} ×ˢ
      Icc ((0 : ℝ) - 1 / 4) 0 : Set (Vec3 × ℝ)), |ω i z| ≤ C)
    (hωae : ∀ i, ω i =ᵐ[volume.restrict (vec3Ball x₁ (1 / 2) ×ˢ Ioo ((0 : ℝ) - 1 / 4) 0)]
      vorticityCurl (fun i j z => DU z i j) i) :
    ∀ y : Vec3, vec3EuclideanNorm (y - x₁) < 1 / 2 → ∀ i, ω i (y, 0) = 0 := by
  have ha : (0 : ℝ) - 1 / 4 < 0 := by norm_num
  have hBsub : vec3Ball x₁ (1 / 2) ⊆ vec3Ball x₁ 1 := vec3Ball_mono (by norm_num)
  -- the pairing with every test supported in the ball vanishes at the top time
  have hpair : ∀ φ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ vec3Ball x₁ (1 / 2) → ∫ x, ∑ k : Fin 3, ω k (x, 0) * φ x k = 0 := by
    intro φ hφ hφc hφB
    have hA := vorticityTopZero_ae_slice hfam hx₁ hφ hφc (hφB.trans hBsub)
    have hB := vorticityTopZero_ae_rep (w := weakVorticity DU) hωae hφB
    have hC := vorticityTopZero_tendsto ha hωc hωb hφ.continuous hφc hφB
    have hD := (htrace (spatialTestCurl φ) (spatialVorticityTestCurl_contDiff hφ)
      (spatialVorticityTestCurl_hasCompactSupport hφc)).2
    refine vorticityTopZero_limit_eq ha hC hD ?_
    filter_upwards [hA, hB] with t h1 h2 ht
    rw [h2 ht, h1 ht.2 (lt_of_le_of_lt (by norm_num) ht.1)]
  intro y hy i
  have hcont : ContinuousOn (fun x => ω i (x, 0)) (vec3Ball x₁ (1 / 2)) :=
    (hωc i).comp (continuous_id.prodMk continuous_const).continuousOn fun x hx =>
      ⟨show vec3EuclideanNorm (x - x₁) ≤ 1 / 2 from le_of_lt hx, ha.le, le_rfl⟩
  have hopen := isOpen_vec3Ball x₁ (1 / 2)
  have hzero := hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hopen.measurableSet) fun θ hθ hθc hθB => by
      set φ : Vec3 → Vec3 := fun x k => if k = i then θ x else 0 with hφdef
      have hφs : ContDiff ℝ (⊤ : ℕ∞) φ := by
        refine contDiff_pi.2 fun k => ?_
        by_cases hk : k = i
        · simpa [hφdef, hk] using hθ
        · simpa [hφdef, hk] using (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Vec3 => (0 : ℝ))
      have hsupp : support φ ⊆ support θ := fun x hx h0 => hx (by
        funext k
        simp [hφdef, h0])
      have hφc : HasCompactSupport φ := hθc.mono' (hsupp.trans (subset_tsupport θ))
      have hφB : tsupport φ ⊆ vec3Ball x₁ (1 / 2) := (closure_mono hsupp).trans hθB
      have h := hpair φ hφs hφc hφB
      refine (integral_congr_ae (Eventually.of_forall fun x => ?_)).trans h
      simp [hφdef, smul_eq_mul, mul_comm]
  have hae : (fun x => ω i (x, 0)) =ᵐ[volume.restrict (vec3Ball x₁ (1 / 2))] fun _ => 0 :=
    (ae_restrict_iff' hopen.measurableSet).2 hzero
  exact Measure.eqOn_open_of_ae_eq hae hopen hcont continuousOn_const hy

end ESS
