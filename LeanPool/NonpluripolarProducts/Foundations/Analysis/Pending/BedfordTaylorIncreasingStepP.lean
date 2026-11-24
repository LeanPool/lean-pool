/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingClaims

/-!
# Increasing Bedford–Taylor convergence: base cases and the unweighted step

This file starts Cegrell's induction for the convergence of mixed Monge–Ampère
measures along increasing sequences of locally bounded plurisubharmonic functions
(Błocki, *The complex Monge–Ampère operator in pluripotential theory*, lecture notes,
Thm 2.2.5; Cegrell). The claims `IncPClaim n q`, `IncWClaim n q` are those of
`BedfordTaylorIncreasingClaims`: slots of index at least `q` are fixed smooth
functions with positive semidefinite complex Hessian.

* `incPClaim_zero`: if every slot is fixed, every `μ_k` is the Bedford–Taylor limit of
  the limiting tuple, hence equals `μ` by uniqueness.
* `incWClaim_zero`: if every slot is fixed and smooth, `μ` is the smooth density measure,
  absolutely continuous with respect to Lebesgue measure. The weights `G_k` increase to
  `w` Lebesgue-almost everywhere on `Ω`, hence `μ`-almost everywhere, and are squeezed
  between `G_0` and `w`; dominated convergence applies.
* `incPClaim_succ`: for a smooth test `φ` and `p = C‖z‖²` with `φ + p` plurisubharmonic,
  integration by parts in slot `q` against the regularized slot defect gives
  `∫ φ dμ_k - ∫ φ dμ(p, R_k) = ∫ η (F_q^k - p) dμ(φ + p, R_k) - ∫ η (F_q^k - p) dμ(p, R_k)`
  for a fixed cutoff `η ≡ 1` near `supp φ`. The tuples with `p`, `φ + p` in slot `q` are
  admissible at level `q`, so every term converges by the level-`q` claims, with weights
  `F_q^k` in the weighted claim. The cutoff may be chosen once for all `k`: the two
  defect measures agree off `supp φ` by locality of Bedford–Taylor limits.
  Convergence against continuous tests follows by uniform approximation.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- A locally bounded plurisubharmonic function times a continuous test supported in `Ω`
is integrable against any measure finite on the compact subsets of `Ω`. -/
theorem integrable_mul_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {c : ComplexModel n → ℝ} (hc : IsLocallyBoundedPshOn Ω c) {ρ : Measure (ComplexModel n)}
    (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) {ψ : ComplexModel n → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ (Ω : Set (ComplexModel n))) :
    Integrable (fun z ↦ ψ z * c z) ρ := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hψc Ω.isOpen hψΩ
  set U : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hU : RelativelyCompactIn U Ω := ⟨hVc, hVΩ⟩
  have hUΩ : U ≤ Ω := subset_closure.trans hVΩ
  obtain ⟨f, hf⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hc hU
  exact (isDecApprox_of_isDecreasingApproximation hc hUΩ hf).integrable_mul
    (fun K hK hKU ↦ hρ K hK (hKU.trans hUΩ)) hψ hψc hKV

/-- **Locality of Bedford–Taylor limits.** Tuples agreeing on an open subset have limits
agreeing there. -/
theorem IsBTLimit.restrict_eq_of_eqOn {Ω W : Opens (ComplexModel n)}
    {u v : Fin n → ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω u μ) (hν : IsBTLimit Ω v ν) (hWΩ : W ≤ Ω)
    (h : ∀ i, EqOn (u i) (v i) W) :
    μ.restrict (W : Set (ComplexModel n)) = ν.restrict (W : Set (ComplexModel n)) :=
  ((hμ.restrict_opens hWΩ).congr h).unique (hν.restrict_opens hWΩ)

/-- **Integration by parts against a regularized slot defect, with any cutoff.** The
identity of `exists_integral_sub_eq_slotDefect` holds for every continuous compactly
supported cutoff `χ` in `Ω` equal to one near `supp φ`: two such cutoffs differ off
`supp φ`, where the two defect measures agree. -/
theorem integral_sub_eq_slotDefect_of_eventuallyEq_one {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    {a b φ p : ComplexModel n → ℝ} {μa μb ν₁ ν₂ : Measure (ComplexModel n)}
    (ha : IsLocallyBoundedPshOn Ω a) (hb : IsLocallyBoundedPshOn Ω b)
    (hμa : IsBTLimit Ω (Function.update v i₀ a) μa)
    (hμb : IsBTLimit Ω (Function.update v i₀ b) μb)
    (hν₁ : IsBTLimit Ω (Function.update v i₀ fun z ↦ φ z + p z) ν₁)
    (hν₂ : IsBTLimit Ω (Function.update v i₀ p) ν₂)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ (Ω : Set (ComplexModel n)))
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ (Ω : Set (ComplexModel n))) (hχ1 : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) :
    (∫ z, φ z ∂μa) - ∫ z, φ z ∂μb =
      (∫ z, χ z * (a z - b z) ∂ν₁) - ∫ z, χ z * (a z - b z) ∂ν₂ := by
  obtain ⟨χ₀, hχ₀, hχ₀c, hχ₀Ω, hχ₀1, hid⟩ :=
    exists_integral_sub_eq_slotDefect i₀ hμa hμb hν₁ hν₂ hφ hφc hφΩ
  rw [hid]
  have hint : ∀ {ψ : ComplexModel n → ℝ}, Continuous ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Ω : Set (ComplexModel n)) → ∀ ν : Measure (ComplexModel n),
      (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) → Integrable (fun z ↦ ψ z * (a z - b z)) ν := by
    intro ψ hψ hψc hψΩ ν hν
    refine ((integrable_mul_of_isLocallyBoundedPshOn ha hν hψ hψc hψΩ).sub
      (integrable_mul_of_isLocallyBoundedPshOn hb hν hψ hψc hψΩ)).congr
      (Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.sub_apply]; ring
  set d : ComplexModel n → ℝ := fun z ↦ χ z - χ₀ z with hd_def
  have hd : Continuous d := hχ.sub hχ₀.continuous
  have hdc : HasCompactSupport d := hχc.sub hχ₀c
  have hdΩ : tsupport d ⊆ (Ω : Set (ComplexModel n)) :=
    (tsupport_sub _ _).trans (union_subset hχΩ hχ₀Ω)
  have hsplit : ∀ ν : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) →
      ∫ z, χ z * (a z - b z) ∂ν =
        (∫ z, χ₀ z * (a z - b z) ∂ν) + ∫ z, d z * (a z - b z) ∂ν := by
    intro ν hν
    rw [← integral_add (hint hχ₀.continuous hχ₀c hχ₀Ω ν hν) (hint hd hdc hdΩ ν hν)]
    congr 1; funext z; simp only [hd_def]; ring
  set W : Opens (ComplexModel n) :=
    ⟨(Ω : Set (ComplexModel n)) ∩ (tsupport φ)ᶜ, Ω.isOpen.inter (isClosed_tsupport φ).isOpen_compl⟩
  have hWΩ : W ≤ Ω := fun z hz ↦ hz.1
  have hres := hν₁.restrict_eq_of_eqOn hν₂ hWΩ fun i z hz ↦ by
    by_cases h : i = i₀
    · subst h; simp [image_eq_zero_of_notMem_tsupport hz.2]
    · simp [Function.update_of_ne h]
  have hzero : ∀ z ∉ (W : Set (ComplexModel n)), d z * (a z - b z) = 0 := by
    intro z hz
    by_cases hzΩ : z ∈ (Ω : Set (ComplexModel n))
    · have hzφ : z ∈ tsupport φ := by
        by_contra h; exact hz ⟨hzΩ, h⟩
      have h1 := (hχ1.filter_mono (nhds_le_nhdsSet hzφ)).self_of_nhds
      have h2 := (hχ₀1.filter_mono (nhds_le_nhdsSet hzφ)).self_of_nhds
      simp [hd_def, h1, h2]
    · have h1 : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzΩ (hχΩ h)
      have h2 : χ₀ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzΩ (hχ₀Ω h)
      simp [hd_def, h1, h2]
  have hdeq : ∫ z, d z * (a z - b z) ∂ν₁ = ∫ z, d z * (a z - b z) ∂ν₂ := by
    have e1 := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν₁) hzero
    have e2 := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := ν₂) hzero
    rw [← e1, ← e2, hres]
  rw [hsplit ν₁ hν₁.2.1, hsplit ν₂ hν₂.2.1, hdeq]
  ring

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

/-- The Bedford–Taylor limit of a tuple of smooth functions with positive semidefinite
complex Hessian is the smooth density measure. -/
theorem IsBTLimit.eq_densityMeasure {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    (hu : ∀ i, IsSmoothPsdOn Ω (u i)) : μ = densityMeasure Ω u := by
  have hfin : ∀ K, IsCompact K → K ⊆ Ω → densityMeasure Ω u K < ⊤ := fun K hK hKΩ ↦
    densityMeasure_lt_top (fun i ↦ (hu i).1) hK hKΩ
  have hres : μ.restrict (Ω : Set (ComplexModel n)) =
      (densityMeasure Ω u).restrict (Ω : Set (ComplexModel n)) := by
    refine restrict_eq_of_testFunction_integral_eq hμ.2.1 hfin fun φ ↦ ?_
    obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
    set U : Opens (ComplexModel n) := ⟨V, hVo⟩
    have hU : RelativelyCompactIn U Ω := ⟨hVc, hVΩ⟩
    have hUΩ : U ≤ Ω := subset_closure.trans hVΩ
    have hadm : IsAdmissible n U u fun i _ ↦ u i :=
      ⟨fun i ↦ isDecApprox_const ⟨(hu i).1.mono hUΩ, fun z hz ↦ (hu i).2 z (hUΩ hz)⟩,
        fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    have h := hμ.tendstoMixed hU hadm φ φ.continuous φ.hasCompactSupport hKV
    rw [integral_densityMeasure hu φ.tsupport_subset]
    exact tendsto_nhds_unique h tendsto_const_nhds
  calc μ = μ.restrict (Ω : Set (ComplexModel n)) :=
        (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμ.1)).symm
    _ = (densityMeasure Ω u).restrict (Ω : Set (ComplexModel n)) := hres
    _ = densityMeasure Ω u :=
        Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (densityMeasure_compl Ω u))

/-- At level `0` all slots are fixed, so the approximating measures are the limit. -/
theorem IsIncAdmissible.eq_of_isBTLimit_zero {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    {μs : ℕ → Measure (ComplexModel n)} {μ : Measure (ComplexModel n)}
    (hF : IsIncAdmissible 0 Ω u F) (hμs : ∀ k, IsBTLimit Ω (fun i ↦ F i k) (μs k))
    (hμ : IsBTLimit Ω u μ) (k : ℕ) : μs k = μ :=
  ((hμs k).congr fun i ↦ (hF.2.2 i (Nat.zero_le _)).2 k).unique hμ

/-- **Base case of the unweighted claim.** -/
theorem incPClaim_zero : IncPClaim n 0 := by
  intro Ω u F μs μ hF hμs hμ χ _ _ _
  simp only [hF.eq_of_isBTLimit_zero hμs hμ]
  exact tendsto_const_nhds

/-- **Base case of the weighted claim.** The limit measure is a smooth density, so
Lebesgue-almost-everywhere convergence of the weights suffices. -/
theorem incWClaim_zero : IncWClaim n 0 := by
  intro Ω u F μs μ hF hμs hμ w G hw hG χ hχ hχc hχΩ
  simp only [hF.eq_of_isBTLimit_zero hμs hμ]
  have hu : ∀ i, IsSmoothPsdOn Ω (u i) := fun i ↦ (hF.2.2 i (Nat.zero_le _)).1
  have hac : μ ≪ volume := by
    rw [hμ.eq_densityMeasure hu, densityMeasure]
    exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hI : ∀ {c : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω c →
      Integrable (fun z ↦ χ z * c z) μ := fun hc ↦
        integrable_mul_of_isLocallyBoundedPshOn hc hμ.2.1 hχ hχc hχΩ
  have hχ0 : ∀ z, z ∉ (Ω : Set (ComplexModel n)) → χ z = 0 := fun z hz ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (hχΩ h)
  refine tendsto_integral_of_dominated_convergence (fun z ↦ |χ z * G 0 z| + |χ z * w z|)
    (fun k ↦ (hI (hG.1 k)).aestronglyMeasurable) ((hI (hG.1 0)).abs.add (hI hw).abs)
    (fun k ↦ Eventually.of_forall fun z ↦ ?_) ?_
  · by_cases hz : z ∈ (Ω : Set (ComplexModel n))
    · have h0 : G 0 z ≤ G k z := hG.2.1 z hz (Nat.zero_le k)
      have h1 : G k z ≤ w z := hG.2.2.1 k z hz
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, ← mul_add]
      refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_, ?_⟩) (abs_nonneg _)
      · linarith [neg_abs_le (G 0 z), abs_nonneg (w z)]
      · linarith [le_abs_self (w z), abs_nonneg (G 0 z)]
    · simp [hχ0 z hz]
  · filter_upwards [hac.ae_le hG.2.2.2] with z hz
    by_cases hzΩ : z ∈ (Ω : Set (ComplexModel n))
    · exact (hz hzΩ).const_mul _
    · simp only [hχ0 z hzΩ, zero_mul]
      exact tendsto_const_nhds

/-- Putting a fixed smooth plurisubharmonic function in slot `q` of a level-`(q+1)`
admissible increasing family gives a level-`q` family. -/
theorem IsIncAdmissible.update_const {q : ℕ} {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsIncAdmissible (q + 1) Ω u F) (hq : q < n) {a : ComplexModel n → ℝ}
    (ha : IsSmoothPsdOn Ω a) :
    IsIncAdmissible q Ω (Function.update u ⟨q, hq⟩ a) (Function.update F ⟨q, hq⟩ fun _ ↦ a) := by
  refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · by_cases h : i = ⟨q, hq⟩
    · subst h; simpa using ha.isLocallyBoundedPshOn
    · simpa [Function.update_of_ne h] using hF.1 i
  · by_cases h : i = ⟨q, hq⟩
    · subst h; simpa using isIncApprox_const ha.isLocallyBoundedPshOn
    · simpa [Function.update_of_ne h] using hF.2.1 i
  · by_cases h : i = ⟨q, hq⟩
    · subst h; simpa [EqOn] using ha
    · have hi' : q + 1 ≤ i.val := by
        rcases Nat.lt_or_ge q i.val with h' | h'
        · exact h'
        · exact absurd (Fin.ext (le_antisymm h' hi)) h
      simpa [Function.update_of_ne h] using hF.2.2 i hi'

/-- **Smooth tests in the unweighted step.** -/
theorem tendsto_integral_smoothTest_of_incClaims {q : ℕ} (hq : q < n) (hP : IncPClaim n q)
    (hW : IncWClaim n q) {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {F : Fin n → ℕ → ComplexModel n → ℝ} {μs : ℕ → Measure (ComplexModel n)}
    {μ : Measure (ComplexModel n)} (hF : IsIncAdmissible (q + 1) Ω u F)
    (hμs : ∀ k, IsBTLimit Ω (fun i ↦ F i k) (μs k)) (hμ : IsBTLimit Ω u μ)
    {φ : ComplexModel n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ (Ω : Set (ComplexModel n))) :
    Tendsto (fun k ↦ ∫ z, φ z ∂(μs k)) atTop (𝓝 (∫ z, φ z ∂μ)) := by
  classical
  set i₀ : Fin n := ⟨q, hq⟩ with hi₀
  obtain ⟨C, hC0, hCpsd⟩ := exists_isSmoothPsdOn_add_norm_sq hφ hφc
  set p : ComplexModel n → ℝ := fun z ↦ C * ‖z‖ ^ 2 with hp_def
  have hp : IsSmoothPsdOn Ω p := by
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    refine ⟨(contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffOn, fun z _ ↦ ?_⟩
    have hsplit : p = C • fun z : ComplexModel n ↦ ‖z‖ ^ 2 := by
      funext y; simp [hp_def]
    rw [hsplit, complexHessian_smul ((contDiff_norm_sq ℝ).contDiffAt.of_le h2),
      complexHessian_norm_sq]
    exact Matrix.PosSemidef.one.smul (by exact_mod_cast hC0)
  have hφp : IsSmoothPsdOn Ω fun z ↦ φ z + p z :=
    ⟨hCpsd.1.mono (subset_univ _), fun z _ ↦ hCpsd.2 z trivial⟩
  have hpb := hp.isLocallyBoundedPshOn
  obtain ⟨η, hη1, -⟩ := exists_testFunction_eq_one_nhds_compact hφc hφΩ
  -- the Bedford–Taylor limits
  have hμs' : ∀ k, IsBTLimit Ω (Function.update (fun i ↦ F i k) i₀ (F i₀ k)) (μs k) := fun k ↦ by
    rw [Function.update_eq_self]; exact hμs k
  have hμ' : IsBTLimit Ω (Function.update u i₀ (u i₀)) μ := by
    rw [Function.update_eq_self]; exact hμ
  choose ρs hρs using fun k ↦ (hμs' k).exists_update_smoothPsd i₀ hp
  choose σs hσs using fun k ↦ (hμs' k).exists_update_smoothPsd i₀ hφp
  obtain ⟨ρ, hρ⟩ := hμ'.exists_update_smoothPsd i₀ hp
  obtain ⟨σ, hσ⟩ := hμ'.exists_update_smoothPsd i₀ hφp
  have hFk : ∀ k, IsLocallyBoundedPshOn Ω (F i₀ k) := fun k ↦ (hF.2.1 i₀).1 k
  -- the integration by parts identities, with the common cutoff `η`
  have hid : ∀ k, (∫ z, φ z ∂(μs k)) - ∫ z, φ z ∂(ρs k) =
      (∫ z, η z * (F i₀ k z - p z) ∂(σs k)) - ∫ z, η z * (F i₀ k z - p z) ∂(ρs k) := fun k ↦
    integral_sub_eq_slotDefect_of_eventuallyEq_one i₀ (hFk k) hpb (hμs' k) (hρs k) (hσs k)
      (hρs k) hφ hφc hφΩ η.continuous η.hasCompactSupport η.tsupport_subset hη1
  have hidlim : (∫ z, φ z ∂μ) - ∫ z, φ z ∂ρ =
      (∫ z, η z * (u i₀ z - p z) ∂σ) - ∫ z, η z * (u i₀ z - p z) ∂ρ :=
    integral_sub_eq_slotDefect_of_eventuallyEq_one i₀ (hF.1 i₀) hpb hμ' hρ hσ hρ hφ hφc hφΩ
      η.continuous η.hasCompactSupport η.tsupport_subset hη1
  have hsplit : ∀ {c : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω c →
      ∀ ν : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) →
        ∫ z, η z * (c z - p z) ∂ν = (∫ z, η z * c z ∂ν) - ∫ z, η z * p z ∂ν := by
    intro c hc ν hν
    rw [← integral_sub
      (integrable_mul_of_isLocallyBoundedPshOn hc hν η.continuous η.hasCompactSupport
        η.tsupport_subset)
      (integrable_mul_of_isLocallyBoundedPshOn hpb hν η.continuous η.hasCompactSupport
        η.tsupport_subset)]
    congr 1; funext z; ring
  -- the level-`q` families
  have hadmρ := hF.update_const hq hp
  have hadmσ := hF.update_const hq hφp
  have hρs' : ∀ k, IsBTLimit Ω (fun i ↦ Function.update F i₀ (fun _ ↦ p) i k) (ρs k) :=
    fun k ↦ by rw [update_apply_seq]; exact hρs k
  have hσs' : ∀ k, IsBTLimit Ω (fun i ↦ Function.update F i₀ (fun _ ↦ fun z ↦ φ z + p z) i k)
      (σs k) := fun k ↦ by rw [update_apply_seq]; exact hσs k
  have hηp : Continuous fun z ↦ η z * p z :=
    η.continuous.mul (continuous_const.mul (continuous_norm.pow 2))
  have hηpc : HasCompactSupport fun z ↦ η z * p z := η.hasCompactSupport.mul_right
  have hηpΩ : tsupport (fun z ↦ η z * p z) ⊆ (Ω : Set (ComplexModel n)) :=
    tsupport_mul_subset_left.trans η.tsupport_subset
  have t1 := hP Ω _ _ ρs ρ hadmρ hρs' hρ φ hφ.continuous hφc hφΩ
  have t2 := hW Ω _ _ σs σ hadmσ hσs' hσ (u i₀) (F i₀) (hF.1 i₀) (hF.2.1 i₀) η η.continuous
    η.hasCompactSupport η.tsupport_subset
  have t3 := hP Ω _ _ σs σ hadmσ hσs' hσ _ hηp hηpc hηpΩ
  have t4 := hW Ω _ _ ρs ρ hadmρ hρs' hρ (u i₀) (F i₀) (hF.1 i₀) (hF.2.1 i₀) η η.continuous
    η.hasCompactSupport η.tsupport_subset
  have t5 := hP Ω _ _ ρs ρ hadmρ hρs' hρ _ hηp hηpc hηpΩ
  have hlim := t1.add ((t2.sub t3).sub (t4.sub t5))
  have hval : (∫ z, φ z ∂ρ) + (((∫ z, η z * u i₀ z ∂σ) - ∫ z, η z * p z ∂σ) -
      ((∫ z, η z * u i₀ z ∂ρ) - ∫ z, η z * p z ∂ρ)) = ∫ z, φ z ∂μ := by
    rw [← hsplit (hF.1 i₀) σ hσ.2.1, ← hsplit (hF.1 i₀) ρ hρ.2.1]
    linarith
  rw [hval] at hlim
  refine hlim.congr fun k ↦ ?_
  have h := hid k
  rw [hsplit (hFk k) _ (hσs k).2.1, hsplit (hFk k) _ (hρs k).2.1] at h
  linarith

/-- **The unweighted induction step** for increasing sequences (Błocki, Thm 2.2.5). -/
theorem incPClaim_succ {q : ℕ} (hq : q < n) (hP : IncPClaim n q) (hW : IncWClaim n q) :
    IncPClaim n (q + 1) := by
  intro Ω u F μs μ hF hμs hμ χ hχ hχc hχΩ
  exact tendsto_integral_of_tendsto_contDiff_tests (fun k ↦ (hμs k).2.1) hμ.2.1
    (fun ψ hψ hψc hψΩ ↦ tendsto_integral_smoothTest_of_incClaims hq hP hW hF hμs hμ hψ hψc hψΩ)
    hχ hχc hχΩ

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
