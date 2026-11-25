/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.MeasureLocality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PositiveDistributionMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlots
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# The unweighted induction step

If the weighted and unweighted convergence claims hold with `q` varying slots,
then the unweighted claim holds with `q + 1`. For a smooth test `φ`, integrating
by parts moves `φ` into slot `q` and the varying sequence of that slot into the
weight; writing `φ = (φ + C‖z‖²) - C‖z‖²` makes the new slot plurisubharmonic.
The limiting functional is positive and linear on smooth tests, hence given by a
measure, and uniform approximation extends convergence to continuous tests.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open MeasureLocality (integrable_of_tsupport_subset)

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

theorem mixedDensity_update_eq_zero_of_notMem_tsupport {f : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) {a : ComplexModel n → ℝ} {z : ComplexModel n} (hz : z ∉ tsupport a) :
    mixedDensity (Function.update f i₀ a) z = 0 := by
  cases n with
  | zero => exact i₀.elim0
  | succ m =>
    rw [mixedDensity_update_eq_cons, mixedDensity_cons_eq,
      MixedHessian.mixedC_eq_zero_of_notMem_tsupport hz]
    simp

theorem update_apply_seq {F : Fin n → ℕ → ComplexModel n → ℝ} (i₀ : Fin n)
    (c : ComplexModel n → ℝ) (k : ℕ) :
    (fun i ↦ Function.update F i₀ (fun _ ↦ c) i k) = Function.update (fun i ↦ F i k) i₀ c := by
  funext i
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem isSmoothPsdOn_norm_sq (U : Opens (ComplexModel n)) :
    IsSmoothPsdOn U (fun z : ComplexModel n ↦ ‖z‖ ^ 2) :=
  ⟨(contDiff_norm_sq ℝ).contDiffOn, fun z _ ↦ by
    rw [complexHessian_norm_sq]; exact Matrix.PosSemidef.one⟩

theorem IsAdmissible.update_const {q : ℕ} {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible (q + 1) U u F) (hq : q < n) {a : ComplexModel n → ℝ}
    (ha : IsSmoothPsdOn U a) :
    IsAdmissible q U (Function.update u ⟨q, hq⟩ a) (Function.update F ⟨q, hq⟩ fun _ ↦ a) := by
  refine ⟨fun i ↦ ?_, fun i hi k ↦ ?_⟩
  · by_cases h : i = ⟨q, hq⟩
    · subst h; simpa using isDecApprox_const ha
    · simpa [Function.update_of_ne h] using hF.1 i
  · by_cases h : i = ⟨q, hq⟩
    · subst h; simp [EqOn]
    · have hi' : q + 1 ≤ i.val := by
        rcases Nat.lt_or_ge q i.val with h' | h'
        · exact h'
        · exact absurd (Fin.ext (le_antisymm h' hi)) h
      simpa [Function.update_of_ne h] using hF.2 i hi' k

open scoped Distributions in
/-- **Integration by parts against a smooth test.** The integrals of `φ` against
the mixed densities of a level-`(q+1)` admissible family converge to the pairing
of the slot-`q` limit function with the mixed limits carrying `φ + C‖z‖²` and
`‖z‖²` in that slot. Neither limit measure depends on the slot-`q` function, so
the identity compares two tuples differing only in that slot. This is the
Bedford–Taylor form of `∫ φ ddᶜu ∧ T = ∫ u ddᶜφ ∧ T`. -/
theorem tendsto_smoothTest_ibp {q : ℕ} (hW : WClaim n q) (hq : q < n)
    {U : Opens (ComplexModel n)} (u : Fin n → ComplexModel n → ℝ) {φ : ComplexModel n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    {C : ℝ} (hC : IsSmoothPsdOn ⊤ fun z ↦ φ z + C * ‖z‖ ^ 2)
    (χ : 𝓓(U, ℝ)) (hχ1 : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1)
    {μ₁ μ₂ : Measure (ComplexModel n)}
    (h1c : μ₁ (U : Set (ComplexModel n))ᶜ = 0)
    (h1f : ∀ K, IsCompact K → K ⊆ U → μ₁ K < ⊤)
    (h1P : ∀ F, IsAdmissible q U
      (Function.update u ⟨q, hq⟩ fun z ↦ φ z + C * ‖z‖ ^ 2) F → TendstoMixed U F μ₁)
    (h2c : μ₂ (U : Set (ComplexModel n))ᶜ = 0)
    (h2f : ∀ K, IsCompact K → K ⊆ U → μ₂ K < ⊤)
    (h2P : ∀ F, IsAdmissible q U
      (Function.update u ⟨q, hq⟩ fun z : ComplexModel n ↦ ‖z‖ ^ 2) F → TendstoMixed U F μ₂)
    (F : Fin n → ℕ → ComplexModel n → ℝ) (hF : IsAdmissible (q + 1) U u F) :
    Tendsto (fun k ↦ ∫ z, φ z * mixedDensity (fun i ↦ F i k) z) atTop
      (𝓝 ((∫ z, χ z * u ⟨q, hq⟩ z ∂μ₁) - C * ∫ z, χ z * u ⟨q, hq⟩ z ∂μ₂)) := by
  set i₀ : Fin n := ⟨q, hq⟩
  set a : ComplexModel n → ℝ := fun z ↦ φ z + C * ‖z‖ ^ 2 with ha_def
  set ψ : ComplexModel n → ℝ := fun z ↦ ‖z‖ ^ 2 with hψ_def
  have ha : IsSmoothPsdOn U a := ⟨hC.1.mono (subset_univ _), fun z _ ↦ hC.2 z trivial⟩
  have hψ : IsSmoothPsdOn U ψ := isSmoothPsdOn_norm_sq U
  have hW1 := hW U _ μ₁ h1c h1f h1P _ (hF.update_const hq ha) (u i₀) (F i₀) (hF.1 i₀) χ
    χ.continuous χ.hasCompactSupport χ.tsupport_subset
  have hW2 := hW U _ μ₂ h2c h2f h2P _ (hF.update_const hq hψ) (u i₀) (F i₀) (hF.1 i₀) χ
    χ.continuous χ.hasCompactSupport χ.tsupport_subset
  simp only [update_apply_seq] at hW1 hW2
  refine (hW1.sub (hW2.const_mul C)).congr fun k ↦ ?_
  set f : Fin n → ComplexModel n → ℝ := fun i ↦ F i k with hf_def
  have hfs : ∀ i, ContDiffOn ℝ ∞ (f i) U := fun i ↦ ((hF.1 i).1 k).1
  have hupd (c : ComplexModel n → ℝ) (hc : ContDiffOn ℝ ∞ c U) :
      ∀ i, ContDiffOn ℝ ∞ (Function.update f i₀ c i) U := fun i ↦ by
    by_cases h : i = i₀
    · subst h; simpa using hc
    · simpa [Function.update_of_ne h] using hfs i
  have step1 : ∫ z, φ z * mixedDensity f z =
      ∫ z, F i₀ k z * mixedDensity (Function.update f i₀ φ) z := by
    conv_lhs => rw [← Function.update_eq_self i₀ f]
    exact integral_mul_mixedDensity_update_swap hfs i₀ hφ.contDiffOn (hfs i₀) hφc hφU
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hlin (z : ComplexModel n) : mixedDensity (Function.update f i₀ φ) z =
      mixedDensity (Function.update f i₀ a) z - C * mixedDensity (Function.update f i₀ ψ) z := by
    have hfun : (fun y ↦ a y + (-C) * ψ y) = φ := by
      funext y; simp only [ha_def, hψ_def]; ring
    have h := mixedDensity_update_add_smul (f := f) i₀
      (hC.1.contDiffAt (by simp) |>.of_le h2)
      ((contDiff_norm_sq ℝ).contDiffAt.of_le h2 : ContDiffAt ℝ 2 ψ z) (-C)
    rw [hfun] at h
    rw [h]; ring
  have hχφ (z : ComplexModel n) :
      mixedDensity (Function.update f i₀ φ) z = χ z * mixedDensity (Function.update f i₀ φ) z := by
    by_cases hz : z ∈ tsupport φ
    · rw [(hχ1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds, one_mul]
    · rw [mixedDensity_update_eq_zero_of_notMem_tsupport i₀ hz, mul_zero]
  have hint (c : ComplexModel n → ℝ) (hc : ContDiffOn ℝ ∞ c U) :
      Integrable fun z ↦ χ z * F i₀ k z * mixedDensity (Function.update f i₀ c) z := by
    have hcont : Continuous fun z ↦ χ z * F i₀ k z * mixedDensity (Function.update f i₀ c) z :=
      continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport χ) χ.tsupport_subset
        ((χ.continuous.continuousOn.mul (hfs i₀).continuousOn).mul
          (continuousOn_mixedDensity (hupd c hc)))
        fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]
    exact hcont.integrable_of_hasCompactSupport (χ.hasCompactSupport.mul_right.mul_right)
  have step2 : ∫ z, F i₀ k z * mixedDensity (Function.update f i₀ φ) z =
      (∫ z, χ z * F i₀ k z * mixedDensity (Function.update f i₀ a) z) -
        C * ∫ z, χ z * F i₀ k z * mixedDensity (Function.update f i₀ ψ) z := by
    rw [← integral_const_mul, ← integral_sub (hint a ha.1) ((hint ψ hψ.1).const_mul C)]
    congr 1
    funext z
    rw [hχφ, hlin]
    ring
  simp only [hf_def] at step1 step2
  rw [step1, step2]

open scoped Distributions in
/-- The data for the integration-by-parts identity always exist. -/
theorem exists_tendsto_smoothTest_ibp {q : ℕ} (hP : PClaim n q) (hq : q < n)
    (U : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ) {φ : ComplexModel n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∃ (C : ℝ) (χ : 𝓓(U, ℝ)) (μ₁ μ₂ : Measure (ComplexModel n)),
      IsSmoothPsdOn ⊤ (fun z ↦ φ z + C * ‖z‖ ^ 2) ∧ (∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) ∧
        μ₁ (U : Set (ComplexModel n))ᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ U → μ₁ K < ⊤) ∧
        (∀ F, IsAdmissible q U
          (Function.update u ⟨q, hq⟩ fun z ↦ φ z + C * ‖z‖ ^ 2) F → TendstoMixed U F μ₁) ∧
        μ₂ (U : Set (ComplexModel n))ᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ U → μ₂ K < ⊤) ∧
        ∀ F, IsAdmissible q U
          (Function.update u ⟨q, hq⟩ fun z : ComplexModel n ↦ ‖z‖ ^ 2) F →
            TendstoMixed U F μ₂ := by
  obtain ⟨C, -, hCpsd⟩ := exists_isSmoothPsdOn_add_norm_sq hφ hφc
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact hφc hφU
  obtain ⟨μ₁, h1c, h1f, h1P⟩ := hP U (Function.update u ⟨q, hq⟩ fun z ↦ φ z + C * ‖z‖ ^ 2)
  obtain ⟨μ₂, h2c, h2f, h2P⟩ := hP U (Function.update u ⟨q, hq⟩ fun z : ComplexModel n ↦ ‖z‖ ^ 2)
  exact ⟨C, χ, μ₁, μ₂, hCpsd, hχ1, h1c, h1f, h1P, h2c, h2f, h2P⟩

/-- **Smooth tests.** Under the level-`q` claims, the integrals of a smooth test
against the mixed densities of any level-`(q+1)` admissible family converge to a
common limit. -/
theorem exists_tendsto_smoothTest {q : ℕ} (hP : PClaim n q) (hW : WClaim n q) (hq : q < n)
    (U : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ) {φ : ComplexModel n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∃ L : ℝ, ∀ F, IsAdmissible (q + 1) U u F →
      Tendsto (fun k ↦ ∫ z, φ z * mixedDensity (fun i ↦ F i k) z) atTop (𝓝 L) := by
  obtain ⟨C, χ, μ₁, μ₂, hC, hχ1, h1c, h1f, h1P, h2c, h2f, h2P⟩ :=
    exists_tendsto_smoothTest_ibp hP hq U u hφ hφc hφU
  exact ⟨_, fun F hF ↦ tendsto_smoothTest_ibp hW hq u hφ hφc hφU hC χ hχ1 h1c h1f h1P
    h2c h2f h2P F hF⟩

/-- Uniform approximation of a compactly supported continuous function by smooth
functions supported in a prescribed open neighbourhood of its support. -/
theorem exists_contDiff_approx {φ : ComplexModel n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) {V : Opens (ComplexModel n)} (hV : tsupport φ ⊆ V) {η : ℝ}
    (hη : 0 < η) :
    ∃ ψ : ComplexModel n → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ V ∧
      ∀ x, |φ x - ψ x| ≤ η := by
  obtain ⟨g, hg, hgφ⟩ := (hc.uniformContinuous_of_continuous hφ).exists_contDiff_dist_le hη
  obtain ⟨χ, hχ1, hχ01⟩ := exists_testFunction_eq_one_nhds_compact hc hV
  refine ⟨fun x ↦ χ x * g x, χ.contDiff.mul hg, χ.hasCompactSupport.mul_right,
    (tsupport_mul_subset_left).trans χ.tsupport_subset, fun x ↦ ?_⟩
  have hφχ : φ x = χ x * φ x := by
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  rw [hφχ, ← mul_sub, abs_mul, abs_of_nonneg (hχ01 x).1]
  have h1 : |φ x - g x| ≤ η := by
    rw [← Real.dist_eq, dist_comm]; exact (hgφ x).le
  calc χ x * |φ x - g x| ≤ 1 * η := mul_le_mul (hχ01 x).2 h1 (abs_nonneg _) zero_le_one
    _ = η := one_mul η

theorem integrable_mul_of_continuousOn {U : Opens (ComplexModel n)} {D : ComplexModel n → ℝ}
    (hD : ContinuousOn D U) {f : ComplexModel n → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hU : tsupport f ⊆ U) :
    Integrable fun z ↦ f z * D z := by
  have hcont : Continuous fun z ↦ f z * D z :=
    continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport f) hU
      (hf.continuousOn.mul hD) fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]
  exact hcont.integrable_of_hasCompactSupport hc.mul_right

/-- **From smooth to continuous tests, for measures.** Convergence of the integrals of
all smooth tests with compact support in `U` implies convergence for continuous tests. -/
theorem tendsto_integral_of_tendsto_contDiff_tests {U : Opens (ComplexModel n)}
    {μs : ℕ → Measure (ComplexModel n)} {μ : Measure (ComplexModel n)}
    (hμsf : ∀ k K, IsCompact K → K ⊆ U → μs k K < ⊤)
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hsm : ∀ ψ : ComplexModel n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      Tendsto (fun k ↦ ∫ z, ψ z ∂(μs k)) atTop (𝓝 (∫ z, ψ z ∂μ)))
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    Tendsto (fun k ↦ ∫ z, φ z ∂(μs k)) atTop (𝓝 (∫ z, φ z ∂μ)) := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφc U.isOpen hφU
  obtain ⟨ρ, hρ0, hρ1⟩ := exists_nonneg_testFunction_one_le_on_compact hVc hVU
  set R := ∫ z, ρ z ∂μ
  have hR0 : 0 ≤ R := integral_nonneg hρ0
  have hρlim := hsm ρ ρ.contDiff ρ.hasCompactSupport ρ.tsupport_subset
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (6 * R + 6) with hη_def
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨ψ, hψ, hψc, hψV, hφψ⟩ :=
    exists_contDiff_approx hφ hφc (V := ⟨V, hVo⟩) hKV hη
  have hψU : tsupport ψ ⊆ U := hψV.trans (subset_closure.trans hVU)
  have hψlim := hsm ψ hψ hψc hψU
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hψlim (ε / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hρlim 1 one_pos
  refine ⟨max N₁ N₂, fun k hk ↦ ?_⟩
  have hk₁ := hN₁ k (le_of_max_le_left hk)
  have hk₂ := hN₂ k (le_of_max_le_right hk)
  rw [Real.dist_eq] at hk₁ hk₂ ⊢
  have hpt (z : ComplexModel n) : |φ z - ψ z| ≤ η * ρ z := by
    by_cases hz : z ∈ closure V
    · exact (hφψ z).trans (le_mul_of_one_le_right hη.le (hρ1 z hz))
    · have hzV : z ∉ V := fun h ↦ hz (subset_closure h)
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hzV (hKV h),
        image_eq_zero_of_notMem_tsupport fun h ↦ hzV (hψV h), sub_zero, abs_zero]
      exact mul_nonneg hη.le (hρ0 z)
  have hbound : ∀ ν : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ U → ν K < ⊤) →
      |(∫ z, φ z ∂ν) - ∫ z, ψ z ∂ν| ≤ η * ∫ z, ρ z ∂ν := by
    intro ν hν
    have hνφ := integrable_of_tsupport_subset hν hφ hφc hφU
    have hνψ := integrable_of_tsupport_subset hν hψ.continuous hψc hψU
    have hνρ := integrable_of_tsupport_subset hν ρ.continuous ρ.hasCompactSupport
      ρ.tsupport_subset
    rw [← integral_sub hνφ hνψ, ← integral_const_mul, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hνρ.const_mul η)
      (Eventually.of_forall fun z ↦ by simpa [Real.norm_eq_abs] using hpt z)
  have hbound1 := hbound (μs k) (hμsf k)
  have hbound2 := hbound μ hμf
  have hρk : ∫ z, ρ z ∂(μs k) ≤ R + 1 := by
    have := (abs_lt.mp hk₂).2; linarith
  have hsum : η * (R + 1) + η * R < 2 * ε / 3 := by
    have : η * (6 * R + 6) = ε := by
      rw [hη_def]; field_simp
    nlinarith
  calc |(∫ z, φ z ∂(μs k)) - ∫ z, φ z ∂μ|
      ≤ |(∫ z, φ z ∂(μs k)) - ∫ z, ψ z ∂(μs k)| + |(∫ z, ψ z ∂(μs k)) - ∫ z, ψ z ∂μ| +
          |(∫ z, φ z ∂μ) - ∫ z, ψ z ∂μ| := by
        have := abs_sub_le (∫ z, φ z ∂(μs k)) (∫ z, ψ z ∂(μs k)) (∫ z, φ z ∂μ)
        have h2 := abs_sub_le (∫ z, ψ z ∂(μs k)) (∫ z, ψ z ∂μ) (∫ z, φ z ∂μ)
        rw [abs_sub_comm (∫ z, ψ z ∂μ) (∫ z, φ z ∂μ)] at h2
        linarith
    _ ≤ η * (R + 1) + ε / 3 + η * R := by
        have := hbound1.trans (mul_le_mul_of_nonneg_left hρk hη.le)
        linarith [hk₁.le]
    _ < ε := by linarith

/-- **From smooth to continuous tests.** Weak convergence of nonnegative
continuous densities on `U` against smooth tests implies convergence against
all continuous compactly supported tests in `U`. -/
theorem tendsto_of_tendsto_contDiff_tests {U : Opens (ComplexModel n)}
    {D : ℕ → ComplexModel n → ℝ} (hD : ∀ k, ContinuousOn (D k) U)
    (hD0 : ∀ k, ∀ z ∈ U, 0 ≤ D k z) {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hsm : ∀ ψ : ComplexModel n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      Tendsto (fun k ↦ ∫ z, ψ z * D k z) atTop (𝓝 (∫ z, ψ z ∂μ)))
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    Tendsto (fun k ↦ ∫ z, φ z * D k z) atTop (𝓝 (∫ z, φ z ∂μ)) := by
  let μs := fun k => (volume.restrict (U : Set (ComplexModel n))).withDensity
    fun z => ENNReal.ofReal (D k z)
  have e (k : ℕ) {f : ComplexModel n → ℝ} (hf : tsupport f ⊆ U) :
      ∫ z, f z ∂(μs k) = ∫ z, f z * D k z :=
    integral_ofReal_density (hD k) (hD0 k) hf
  have ht : Tendsto (fun k => ∫ z, φ z ∂(μs k)) atTop (𝓝 (∫ z, φ z ∂μ)) :=
    tendsto_integral_of_tendsto_contDiff_tests
      (fun k K hK hKU => ofReal_density_lt_top (hD k) hK hKU) hμf
      (fun ψ hψ hψc hψU => by
        change Tendsto (fun k => ∫ z, ψ z ∂(μs k)) atTop (𝓝 (∫ z, ψ z ∂μ))
        simp_rw [e _ hψU]
        exact hsm ψ hψ hψc hψU)
      hφ hφc hφU
  simpa only [e _ hφU] using ht

open scoped Distributions in
/-- **The unweighted induction step.** -/
theorem pClaim_succ {q : ℕ} (hP : PClaim n q) (hW : WClaim n q) : PClaim n (q + 1) := by
  intro U u
  by_cases hq : q < n
  swap
  · obtain ⟨μ, h1, h2, h3⟩ := hP U u
    exact ⟨μ, h1, h2, fun F hF ↦ h3 F ⟨hF.1, fun i hi ↦ absurd i.isLt (by omega)⟩⟩
  classical
  by_cases hex : ∃ F, IsAdmissible (q + 1) U u F
  swap
  · exact ⟨0, by simp, fun _ _ _ ↦ by simp, fun F hF ↦ absurd ⟨F, hF⟩ hex⟩
  obtain ⟨F₀, hF₀⟩ := hex
  have hL (φ : 𝓓(U, ℝ)) := exists_tendsto_smoothTest hP hW hq U u φ.contDiff
    φ.hasCompactSupport φ.tsupport_subset
  choose L hL using hL
  have hDc (F : Fin n → ℕ → ComplexModel n → ℝ) (hF : IsAdmissible (q + 1) U u F) (k : ℕ) :
      ContinuousOn (mixedDensity fun i ↦ F i k) U :=
    continuousOn_mixedDensity fun i ↦ ((hF.1 i).1 k).1
  have hD0 (F : Fin n → ℕ → ComplexModel n → ℝ) (hF : IsAdmissible (q + 1) U u F) (k : ℕ) :
      ∀ z ∈ U, 0 ≤ mixedDensity (fun i ↦ F i k) z := fun z hz ↦
    mixedDensity_nonneg fun i ↦ ((hF.1 i).1 k).2 z hz
  have hIntT (φ : 𝓓(U, ℝ)) (k : ℕ) :
      Integrable fun z ↦ φ z * mixedDensity (fun i ↦ F₀ i k) z :=
    integrable_mul_of_continuousOn (hDc F₀ hF₀ k) φ.continuous φ.hasCompactSupport
      φ.tsupport_subset
  let T : 𝓓(U, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := fun φ ψ ↦ by
        refine tendsto_nhds_unique (hL (φ + ψ) F₀ hF₀) ?_
        refine ((hL φ F₀ hF₀).add (hL ψ F₀ hF₀)).congr fun k ↦ ?_
        rw [← integral_add (hIntT φ k) (hIntT ψ k)]
        congr 1; funext z; simp [add_mul]
      map_smul' := fun c φ ↦ by
        refine tendsto_nhds_unique (hL (c • φ) F₀ hF₀) ?_
        refine ((hL φ F₀ hF₀).const_mul c).congr fun k ↦ ?_
        rw [← integral_const_mul]
        congr 1; funext z; simp [mul_assoc] }
  have hTpos : ∀ φ : 𝓓(U, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ T φ := fun φ hφ ↦ by
    refine ge_of_tendsto (hL φ F₀ hF₀) (Eventually.of_forall fun k ↦ ?_)
    refine integral_nonneg fun z ↦ ?_
    by_cases hz : z ∈ U
    · exact mul_nonneg (hφ z) (hD0 F₀ hF₀ k z hz)
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (φ.tsupport_subset h)]
  obtain ⟨ν, -, hνlf, hν⟩ := exists_regular_measure_of_nonneg_testFunctional T hTpos
  have hval : MeasurableEmbedding (Subtype.val : U → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  refine ⟨ν.map Subtype.val, ?_, fun K hK hKU ↦ ?_, fun F hF φ hφ hφc hφU ↦ ?_⟩
  · rw [hval.map_apply]
    have : (Subtype.val : U → ComplexModel n) ⁻¹' (U : Set (ComplexModel n))ᶜ = ∅ := by
      ext x; simp
    simp [this]
  · rw [hval.map_apply]
    have hKc : IsCompact ((Subtype.val : U → ComplexModel n) ⁻¹' K) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (by
        intro x hx; exact ⟨⟨x, hKU hx⟩, rfl⟩)
    exact hKc.measure_lt_top
  · refine tendsto_of_tendsto_contDiff_tests (hDc F hF) (hD0 F hF) (fun K hK hKU ↦ ?_) ?_
      hφ hφc hφU
    · rw [hval.map_apply]
      have hKc : IsCompact ((Subtype.val : U → ComplexModel n) ⁻¹' K) :=
        Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (by
          intro x hx; exact ⟨⟨x, hKU hx⟩, rfl⟩)
      exact hKc.measure_lt_top
    · intro ψ hψ hψc hψU
      let ψ' : 𝓓(U, ℝ) := ⟨ψ, hψ, hψc, hψU⟩
      have h := hL ψ' F hF
      have hint : ∫ z, ψ z ∂(ν.map Subtype.val) = L ψ' := by
        rw [hval.integral_map]
        exact hν ψ'
      rw [hint]
      exact h

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
