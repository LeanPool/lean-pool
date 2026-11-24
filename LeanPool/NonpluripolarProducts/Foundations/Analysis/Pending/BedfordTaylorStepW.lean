/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorStepP

/-!
# The weighted induction step

Upper bound: decreasing continuous weights integrated against weakly converging
positive densities are eventually at most the limit weighted integral plus
`ε` (upper semicontinuous weight argument).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

theorem IsDecApprox.le_of_mem {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) {z : ComplexModel n} (hz : z ∈ U)
    (k : ℕ) : w z ≤ G k z :=
  (hG.2.1 z hz).le_of_tendsto (hG.2.2.1 z hz) k

theorem IsDecApprox.exists_abs_le {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ C, ∀ k, ∀ z ∈ K, |G k z| ≤ C := by
  obtain ⟨m, hm⟩ := hG.2.2.2 K hK hKU
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn ((hG.1 0).1.continuousOn.mono hKU)).bddAbove
  refine ⟨max M (-m), fun k z hz ↦ abs_le.2 ⟨?_, ?_⟩⟩
  · have h1 := hm ⟨z, hz, rfl⟩
    have h2 := hG.le_of_mem (hKU hz) k
    have : -max M (-m) ≤ m := by simp only [neg_le]; exact le_max_right _ _
    linarith
  · exact ((hG.2.1 z (hKU hz) (Nat.zero_le k)).trans (hM ⟨z, hz, rfl⟩)).trans (le_max_left _ _)

theorem integral_withDensity_ofReal {μ : Measure (ComplexModel n)} {d : ComplexModel n → ℝ}
    (hd : Measurable d) (hd0 : ∀ z, 0 ≤ d z) (g : ComplexModel n → ℝ) :
    ∫ z, g z ∂(μ.withDensity fun z ↦ ENNReal.ofReal (d z)) = ∫ z, d z * g z ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp [ENNReal.toReal_ofReal (hd0 _)]

/-- **Upper bound for weighted integrals.** -/
theorem eventually_weighted_integral_le {U : Opens (ComplexModel n)}
    {F : Fin n → ℕ → ComplexModel n → ℝ} (hFs : ∀ i k, IsSmoothPsdOn U (F i k))
    {μ : Measure (ComplexModel n)} (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hT : TendstoMixed U F μ) {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ}
    (hG : IsDecApprox U w G) {χ : ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) (hχ0 : ∀ z, 0 ≤ χ z) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z ≤
      ∫ z, χ z * w z ∂μ + ε := by
  set K := tsupport χ
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · have hχz : ∀ z, χ z = 0 := fun z ↦ image_eq_zero_of_notMem_tsupport (by simp [K, hKe] at *)
    exact Eventually.of_forall fun k ↦ by simp [hχz, hε.le]
  obtain ⟨ρ, hρ1, hρ01⟩ := exists_testFunction_eq_one_nhds_compact hχc hχU
  have hρK : ∀ z ∈ K, ρ z = 1 := fun z hz ↦ (hρ1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  set D : ℕ → ComplexModel n → ℝ := fun k z ↦ ρ z * mixedDensity (fun i ↦ F i k) z with hD
  have hDc (k : ℕ) : Continuous (D k) :=
    continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport ρ) ρ.tsupport_subset
      (ρ.continuous.continuousOn.mul (continuousOn_mixedDensity fun i ↦ (hFs i k).1))
      fun z hz ↦ by simp [hD, image_eq_zero_of_notMem_tsupport hz]
  have hD0 (k : ℕ) (z : ComplexModel n) : 0 ≤ D k z := by
    by_cases hz : z ∈ U
    · exact mul_nonneg (hρ01 z).1 (mixedDensity_nonneg fun i ↦ (hFs i k).2 z hz)
    · simp [hD, image_eq_zero_of_notMem_tsupport fun h ↦ hz (ρ.tsupport_subset h)]
  set μs : ℕ → Measure (ComplexModel n) := fun k ↦
    volume.withDensity fun z ↦ ENNReal.ofReal (D k z)
  set μ' : Measure (ComplexModel n) := μ.withDensity fun z ↦ ENNReal.ofReal (ρ z)
  have hμsfin (k : ℕ) : IsFiniteMeasure (μs k) :=
    isFiniteMeasure_withDensity_ofReal
      ((hDc k).integrable_of_hasCompactSupport (ρ.hasCompactSupport.mul_right)).2
  have hμ'fin : IsFiniteMeasure μ' :=
    isFiniteMeasure_withDensity_ofReal
      (integrable_of_tsupport_subset hμf ρ.continuous ρ.hasCompactSupport ρ.tsupport_subset).2
  -- continuous weights agreeing with `G k` on `K`
  obtain ⟨C, hC⟩ := hG.exists_abs_le hχc hχU
  set f : ℕ → ComplexModel n → ℝ := fun k z ↦ ρ z * G k z with hf
  have hfc (k : ℕ) : Continuous (f k) :=
    continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport ρ) ρ.tsupport_subset
      (ρ.continuous.continuousOn.mul (hG.1 k).1.continuousOn)
      fun z hz ↦ by simp [hf, image_eq_zero_of_notMem_tsupport hz]
  have hweak : ∀ g : ComplexModel n → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun k ↦ ∫ x, g x ∂(μs k)) atTop (𝓝 (∫ x, g x ∂μ')) := by
    intro g hg hgc
    have hconv := hT (fun z ↦ g z * ρ z) (hg.mul ρ.continuous) hgc.mul_right
      ((tsupport_mul_subset_right).trans ρ.tsupport_subset)
    simp only [μs, μ', integral_withDensity_ofReal (hDc _).measurable (hD0 _),
      integral_withDensity_ofReal ρ.continuous.measurable fun z ↦ (hρ01 z).1]
    refine (hconv.congr fun k ↦ ?_).trans ?_
    · congr 1; funext z; simp only [hD]; ring
    · simp only [mul_comm]; exact le_rfl
  have hmain := uscWeight_eventually_integral_le μs μ' K hχc hKne f (fun z ↦ ρ z * w z) χ C
    (fun k ↦ (hfc k).upperSemicontinuous)
    (fun z hz ↦ by simpa [hf, hρK z hz] using hG.2.1 z (hχU hz))
    (fun z hz ↦ by simpa [hf, hρK z hz] using hG.2.2.1 z (hχU hz))
    (fun k z hz ↦ by simpa [hf, hρK z hz] using hC k z hz)
    hχ hχc (subset_tsupport χ) hχ0 hweak hε
  refine hmain.mono fun k hk ↦ ?_
  have hL : ∫ x, χ x * f k x ∂(μs k) = ∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z := by
    rw [integral_withDensity_ofReal (hDc _).measurable (hD0 _)]
    congr 1; funext z
    by_cases hz : z ∈ K
    · simp [hD, hf, hρK z hz]; ring
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hR : ∫ x, χ x * (ρ x * w x) ∂μ' = ∫ z, χ z * w z ∂μ := by
    rw [integral_withDensity_ofReal ρ.continuous.measurable fun z ↦ (hρ01 z).1]
    congr 1; funext z
    by_cases hz : z ∈ K
    · simp [hρK z hz]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hL, hR] at hk
  exact hk

/-- One-slot compact raise for the mixed density against a PSD weight. -/
theorem setIntegral_mul_mixedDensity_update_le_of_compact {a : ComplexModel n → ℝ}
    (ha : ContDiff ℝ ∞ a) {f : Fin n → ComplexModel n → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (j : Fin n) {c c' : ComplexModel n → ℝ} (hc : ContDiff ℝ ∞ c) (hc' : ContDiff ℝ ∞ c')
    {K W : Set (ComplexModel n)} (hK : IsCompact K) (hKW : K ⊆ W) (hWm : MeasurableSet W)
    (hWc : IsCompact (closure W)) (hcc' : ∀ z ∉ K, c z = c' z)
    (hapsd : ∀ z ∈ W, (complexHessian a z).PosSemidef)
    (hfpsd : ∀ i, ∀ z ∈ W, (complexHessian (f i) z).PosSemidef) (hle : ∀ z ∈ W, c z ≤ c' z) :
    ∫ z in W, a z * mixedDensity (Function.update f j c) z ≤
      ∫ z in W, a z * mixedDensity (Function.update f j c') z := by
  cases n with
  | zero => exact j.elim0
  | succ m =>
    simp only [mixedDensity_update_eq_cons, mixedDensity_cons_eq, ← mul_div_assoc]
    rw [integral_div, integral_div]
    refine div_le_div_of_nonneg_right ?_ (pow_nonneg Real.pi_pos.le _)
    exact MixedHessian.setIntegral_mul_mixedC_re_mono_of_compact (fun i ↦ hf _) ha hc hc' hK hKW
      hWm hWc hcc' hapsd (fun i z hz ↦ hfpsd _ z hz) hle

/-- **Compact raise in several slots.** Raising the slots in `S`, each by a
function supported in `K`, raises the integral against a PSD weight over `W`. -/
theorem setIntegral_mul_mixedDensity_le_of_compact {a : ComplexModel n → ℝ}
    (ha : ContDiff ℝ ∞ a) {K W : Set (ComplexModel n)} (hK : IsCompact K)
    (hKW : K ⊆ W) (hWm : MeasurableSet W) (hWc : IsCompact (closure W))
    (hapsd : ∀ z ∈ W, (complexHessian a z).PosSemidef) (S : Finset (Fin n)) :
    ∀ (b b' : Fin n → ComplexModel n → ℝ), (∀ i, ContDiff ℝ ∞ (b i)) →
      (∀ i, ContDiff ℝ ∞ (b' i)) → (∀ i ∉ S, b i = b' i) →
      (∀ i ∈ S, ∀ z ∉ K, b i z = b' i z) →
      (∀ i, ∀ z ∈ W, (complexHessian (b i) z).PosSemidef) →
      (∀ i, ∀ z ∈ W, (complexHessian (b' i) z).PosSemidef) →
      (∀ i ∈ S, ∀ z ∈ W, b i z ≤ b' i z) →
      ∫ z in W, a z * mixedDensity b z ≤ ∫ z in W, a z * mixedDensity b' z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro b b' _ _ hS _ _ _ _
    have : b = b' := funext fun i ↦ hS i (Finset.notMem_empty i)
    rw [this]
  | insert j S hjS ih =>
    intro b b' hb hb' hS hbb' hbpsd hb'psd hle
    set b'' := Function.update b j (b' j) with hb''
    have hstep : ∫ z in W, a z * mixedDensity b z ≤ ∫ z in W, a z * mixedDensity b'' z := by
      conv_lhs => rw [← Function.update_eq_self j b]
      exact setIntegral_mul_mixedDensity_update_le_of_compact ha hb j (hb j) (hb' j) hK hKW hWm
        hWc (hbb' j (Finset.mem_insert_self j S)) hapsd hbpsd
        (hle j (Finset.mem_insert_self j S))
    refine hstep.trans (ih b'' b' (fun i ↦ ?_) hb' (fun i hi ↦ ?_) (fun i hi z hz ↦ ?_)
      (fun i z hz ↦ ?_) hb'psd (fun i hi z hz ↦ ?_))
    · by_cases h' : i = j
      · subst h'; simpa [hb''] using hb' i
      · simpa [hb'', Function.update_of_ne h'] using hb i
    · by_cases h' : i = j
      · subst h'; simp [hb'']
      · simpa [hb'', Function.update_of_ne h'] using
          hS i (by simp [Finset.mem_insert, h', hi])
    · have h' : i ≠ j := fun h ↦ hjS (h ▸ hi)
      simpa [hb'', Function.update_of_ne h'] using hbb' i (Finset.mem_insert_of_mem hi) z hz
    · by_cases h' : i = j
      · subst h'; simpa [hb''] using hb'psd i z hz
      · simpa [hb'', Function.update_of_ne h'] using hbpsd i z hz
    · have h' : i ≠ j := fun h ↦ hjS (h ▸ hi)
      simpa [hb'', Function.update_of_ne h'] using hle i (Finset.mem_insert_of_mem hi) z hz

/-- **Collar comparison in several slots.** Raising the slots in `S`, all equal
to `h` off `K`, raises the weighted integral over `W`. -/
theorem setIntegral_mul_mixedDensity_le_of_le {a h : ComplexModel n → ℝ}
    (ha : ContDiff ℝ ∞ a) {K W : Set (ComplexModel n)} (hK : IsCompact K)
    (hKW : K ⊆ W) (hWm : MeasurableSet W) (hWc : IsCompact (closure W))
    (hapsd : ∀ z ∈ W, (complexHessian a z).PosSemidef)
    (S : Finset (Fin n)) :
    ∀ (b b' : Fin n → ComplexModel n → ℝ), (∀ i, ContDiff ℝ ∞ (b i)) →
      (∀ i, ContDiff ℝ ∞ (b' i)) → (∀ i ∉ S, b i = b' i) →
      (∀ i ∈ S, ∀ z ∉ K, b i z = h z) → (∀ i ∈ S, ∀ z ∉ K, b' i z = h z) →
      (∀ i, ∀ z ∈ W, (complexHessian (b i) z).PosSemidef) →
      (∀ i, ∀ z ∈ W, (complexHessian (b' i) z).PosSemidef) →
      (∀ i ∈ S, ∀ z ∈ W, b i z ≤ b' i z) →
      ∫ z in W, a z * mixedDensity b z ≤ ∫ z in W, a z * mixedDensity b' z := by
  intro b b' hb hb' hS hbh hb'h hbpsd hb'psd hle
  exact setIntegral_mul_mixedDensity_le_of_compact ha hK hKW hWm hWc hapsd S
    b b' hb hb' hS (fun i hi z hz => (hbh i hi z hz).trans (hb'h i hi z hz).symm)
    hbpsd hb'psd hle

section Collar

open SmoothMax

theorem le_smoothMax_right {E : Type*} (f g : E → ℝ) (z : E) : g z ≤ smoothMax f g z := by
  simp only [smoothMax]; linarith [SmoothMax.posPart_nonneg (f z - g z)]

theorem contDiffOn_smoothMax {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) :
    ContDiffOn ℝ ∞ (smoothMax f g) s :=
  hg.add (contDiff_posPart.comp_contDiffOn (hf.sub hg))

theorem complexHessian_sub_const (f : ComplexModel n → ℝ) (c : ℝ) (z : ComplexModel n) :
    complexHessian (fun y ↦ f y - c) z = complexHessian f z := by
  have hd : fderiv ℝ (fun y ↦ f y - c) = fderiv ℝ f := funext fun x ↦ fderiv_sub_const c
  have h : realHessian (fun y ↦ f y - c) z = realHessian f z := by
    funext a b
    simp only [realHessian_eq_fderiv, hd]
  ext j k
  simp [complexHessian, h]

/-- The collar potential `A(‖z - z₀‖² - R²)`. -/
abbrev collar (z₀ : ComplexModel n) (A R : ℝ) (z : ComplexModel n) : ℝ :=
  SmoothMax.quadraticCollar z₀ A R z

theorem contDiff_collar (z₀ : ComplexModel n) (A R : ℝ) : ContDiff ℝ ∞ (collar z₀ A R) :=
  SmoothMax.contDiff_quadraticCollar z₀ A R

theorem complexHessian_collar (z₀ : ComplexModel n) (A R : ℝ) (z : ComplexModel n) :
    complexHessian (collar z₀ A R) z = (A : ℂ) • 1 := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hq : ContDiff ℝ 2 (fun y : ComplexModel n ↦ ‖y‖ ^ 2) := (contDiff_norm_sq ℝ).of_le h2
  have hsplit : collar z₀ A R = A • ((fun y ↦ ‖(-z₀) + ContinuousLinearMap.id ℝ _ y‖ ^ 2) +
      fun _ ↦ -R ^ 2) := by
    funext y; simp [SmoothMax.quadraticCollar, sub_eq_add_neg, add_comm]
  have hsh : ContDiff ℝ 2
      (fun y : ComplexModel n ↦ ‖(-z₀) + ContinuousLinearMap.id ℝ _ y‖ ^ 2) :=
    hq.comp (contDiff_const.add (ContinuousLinearMap.id ℝ _).contDiff)
  have hR : realHessian (fun y : ComplexModel n ↦ ‖(-z₀) + ContinuousLinearMap.id ℝ _ y‖ ^ 2) z =
      realHessian (fun y : ComplexModel n ↦ ‖y‖ ^ 2) ((-z₀) + z) := by
    funext a b
    simpa using realHessian_comp_affine hq (ContinuousLinearMap.id ℝ (ComplexModel n)) (-z₀) z a b
  have hH : complexHessian (fun y : ComplexModel n ↦ ‖(-z₀) + ContinuousLinearMap.id ℝ _ y‖ ^ 2) z
      = complexHessian (fun y : ComplexModel n ↦ ‖y‖ ^ 2) ((-z₀) + z) := by
    ext j k; simp only [complexHessian, hR]
  set q : ComplexModel n → ℝ := fun y ↦ ‖(-z₀) + ContinuousLinearMap.id ℝ _ y‖ ^ 2 with hq_def
  have hqc : ContDiffAt ℝ 2 (q + fun _ ↦ -R ^ 2) z := (hsh.add contDiff_const).contDiffAt
  rw [hsplit, complexHessian_smul hqc, complexHessian_add (u := q) (v := fun _ ↦ -R ^ 2)
    hsh.contDiffAt contDiffAt_const, hH, complexHessian_norm_sq]
  have hc : complexHessian (fun _ : ComplexModel n ↦ -R ^ 2) z = 0 := by
    ext j k; simp [complexHessian]
  rw [hc, add_zero]

theorem isSmoothPsdOn_collar (U : Opens (ComplexModel n)) (z₀ : ComplexModel n) {A : ℝ}
    (hA : 0 ≤ A) (R : ℝ) : IsSmoothPsdOn U (collar z₀ A R) :=
  ⟨(contDiff_collar z₀ A R).contDiffOn, fun z _ ↦ by
    rw [complexHessian_collar]
    exact Matrix.PosSemidef.one.smul (by exact_mod_cast hA)⟩

/-- The collar modification of a decreasing approximation is again one. -/
theorem IsDecApprox.smoothMax_sub {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (c : ℝ) {h : ComplexModel n → ℝ}
    (hh : IsSmoothPsdOn U h) :
    IsDecApprox U (smoothMax (fun y ↦ w y - c) h) (fun k ↦ smoothMax (fun y ↦ G k y - c) h) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun k ↦ ⟨contDiffOn_smoothMax (((hG.1 k).1).sub contDiffOn_const) hh.1, fun z hz ↦ ?_⟩,
    fun z hz k l hkl ↦ smoothMax_mono (by simpa using hG.2.1 z hz hkl) le_rfl,
    fun z hz ↦ ?_, fun K hK hKU ↦ ?_⟩
  · refine complexHessian_smoothMax_posSemidef
      ((((hG.1 k).1.sub contDiffOn_const).contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
      ((hh.1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2) ?_ (hh.2 z hz)
    rw [complexHessian_sub_const]; exact (hG.1 k).2 z hz
  · have hc : Continuous fun t : ℝ ↦ h z + SmoothMax.posPart (t - c - h z) :=
      continuous_const.add (contDiff_posPart.continuous.comp
        ((continuous_id.sub continuous_const).sub continuous_const))
    exact (hc.tendsto _).comp (hG.2.2.1 z hz)
  · obtain ⟨m, hm⟩ := (hK.image_of_continuousOn (hh.1.continuousOn.mono hKU)).bddBelow
    exact ⟨m, by rintro _ ⟨z, hz, rfl⟩; exact (hm ⟨z, hz, rfl⟩).trans (le_smoothMax_right _ _ z)⟩

end Collar

section BallEstimate

theorem eventuallyEq_smul_of_eq_one {θ : ComplexModel n → ℝ}
    {s : Set (ComplexModel n)} (hθ : ∀ᶠ x in 𝓝ˢ s, θ x = 1) {z : ComplexModel n} (hz : z ∈ s)
    (f : ComplexModel n → ℝ) : (fun y ↦ θ y • f y) =ᶠ[𝓝 z] f := by
  filter_upwards [hθ.filter_mono (nhds_le_nhdsSet hz)] with y hy
  simp [hy]

theorem integrableOn_of_continuousOn_closure {U : Opens (ComplexModel n)} {W : Set (ComplexModel
    n)}
    (hWc : IsCompact (closure W)) (hWU : closure W ⊆ U) {f : ComplexModel n → ℝ}
    (hf : ContinuousOn f U) : IntegrableOn f W :=
  ((hf.mono hWU).integrableOn_compact hWc).mono_set subset_closure

/-- **The collar estimate.** For a family equal to the collar potential off a
compact set `K` inside the ball `W`, the limit weighted integral of a cutoff
`ζ` equal to one on `K` is at most every approximating weighted integral. -/
theorem integral_cutoff_weight_le {q : ℕ} {V : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible q V u F) {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ}
    (hG : IsDecApprox V w G) {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ V → μ K < ⊤) (hT : TendstoMixed V F μ)
    {h : ComplexModel n → ℝ} (hh : IsSmoothPsdOn V h) {K W : Set (ComplexModel n)}
    (hK : IsCompact K) (hKW : K ⊆ W) (hWo : IsOpen W) (hWc : IsCompact (closure W))
    (hWV : closure W ⊆ V)
    (hGh : ∀ k, ∀ z ∈ (V : Set (ComplexModel n)), z ∉ K → G k z = h z)
    (hFh : ∀ i : Fin n, i.val < q → ∀ k, ∀ z ∈ (V : Set (ComplexModel n)), z ∉ K → F i k z = h z)
    {ζ : ComplexModel n → ℝ} (hζ : Continuous ζ) (hζ01 : ∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1)
    (hζK : ∀ z ∈ K, ζ z = 1) (hζW : tsupport ζ ⊆ W) (l : ℕ) :
    ∫ z, ζ z * w z ∂μ ≤ ∫ z, ζ z * G l z * mixedDensity (fun i ↦ F i l) z := by
  classical
  have hWV' : W ⊆ V := subset_closure.trans hWV
  have hζc : HasCompactSupport ζ := hWc.of_isClosed_subset (isClosed_tsupport ζ)
    (hζW.trans subset_closure)
  have hζV : tsupport ζ ⊆ V := hζW.trans hWV'
  -- (i) collar comparison over `W`
  obtain ⟨θ, hθ1, -⟩ := exists_testFunction_eq_one_nhds_compact hWc hWV
  have hθs : ContDiff ℝ ∞ (θ : ComplexModel n → ℝ) := θ.contDiff
  have hglob {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f V) :
      ContDiff ℝ ∞ (fun y ↦ θ y • f y) :=
    _root_.SGPT.Foundations.Analysis.SmoothCutoff.contDiff_smul_of_tsupport_subset
      V.isOpen hθs θ.tsupport_subset hf
  have hθW (z : ComplexModel n) (hz : z ∈ W) (f : ComplexModel n → ℝ) :
      (fun y ↦ θ y • f y) =ᶠ[𝓝 z] f :=
    eventuallyEq_smul_of_eq_one hθ1 (subset_closure hz) f
  have hθ0 (z : ComplexModel n) (hz : z ∉ (V : Set (ComplexModel n))) : θ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (θ.tsupport_subset h)
  have hcomp (k : ℕ) (hlk : l ≤ k) :
      ∫ z in W, G l z * mixedDensity (fun i ↦ F i k) z ≤
        ∫ z in W, G l z * mixedDensity (fun i ↦ F i l) z := by
    have hmain := setIntegral_mul_mixedDensity_le_of_le (a := fun y ↦ θ y • G l y)
      (h := fun y ↦ θ y • h y) (hglob (hG.1 l).1) hK hKW hWo.measurableSet hWc
      (fun z hz ↦ by
        rw [MixedHessian.complexHessian_congr (hθW z hz _)]; exact (hG.1 l).2 z (hWV' hz))
      (Finset.univ.filter fun i : Fin n ↦ i.val < q)
      (fun i y ↦ θ y • F i k y) (fun i y ↦ θ y • F i l y)
      (fun i ↦ hglob ((hF.1 i).1 k).1) (fun i ↦ hglob ((hF.1 i).1 l).1)
      (fun i hi ↦ by
        have hi' : q ≤ i.val := by simpa using hi
        funext y
        by_cases hyV : y ∈ (V : Set (ComplexModel n))
        · simp [hF.2 i hi' k hyV, hF.2 i hi' l hyV]
        · simp [hθ0 y hyV])
      (fun i hi z hz ↦ by
        have hi' : i.val < q := by simpa using hi
        by_cases hzV : z ∈ (V : Set (ComplexModel n))
        · simp [hFh i hi' k z hzV hz]
        · simp [hθ0 z hzV])
      (fun i hi z hz ↦ by
        have hi' : i.val < q := by simpa using hi
        by_cases hzV : z ∈ (V : Set (ComplexModel n))
        · simp [hFh i hi' l z hzV hz]
        · simp [hθ0 z hzV])
      (fun i z hz ↦ by
        rw [MixedHessian.complexHessian_congr (hθW z hz _)]; exact ((hF.1 i).1 k).2 z (hWV' hz))
      (fun i z hz ↦ by
        rw [MixedHessian.complexHessian_congr (hθW z hz _)]; exact ((hF.1 i).1 l).2 z (hWV' hz))
      (fun i hi z hz ↦ by
        have hθz : θ z = 1 :=
          (hθ1.filter_mono (nhds_le_nhdsSet (subset_closure hz))).self_of_nhds
        simp only [hθz, one_smul]
        exact (hF.1 i).2.1 z (hWV' hz) hlk)
    refine (setIntegral_congr_fun hWo.measurableSet fun z hz ↦ ?_).trans_le
      (hmain.trans_eq (setIntegral_congr_fun hWo.measurableSet fun z hz ↦ ?_))
    · have hθz : θ z = 1 := (hθ1.filter_mono (nhds_le_nhdsSet (subset_closure hz))).self_of_nhds
      rw [hθz, one_smul, mixedDensity_congr fun i ↦ hθW z hz (F i k)]
    · have hθz : θ z = 1 := (hθ1.filter_mono (nhds_le_nhdsSet (subset_closure hz))).self_of_nhds
      rw [hθz, one_smul, mixedDensity_congr fun i ↦ hθW z hz (F i l)]
  -- (ii) splitting off the collar
  set H : Fin n → ComplexModel n → ℝ := fun i ↦ if i.val < q then h else F i 0 with hH
  have hHs : ∀ i, ContDiffOn ℝ ∞ (H i) V := fun i ↦ by
    by_cases hi : i.val < q
    · simpa [hH, hi] using hh.1
    · simpa [hH, hi] using ((hF.1 i).1 0).1
  have hζ0 (z : ComplexModel n) (hz : z ∉ W) : ζ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (hζW h)
  have hsplit (k : ℕ) : ∀ z ∈ W, G l z * mixedDensity (fun i ↦ F i k) z =
      ζ z * G l z * mixedDensity (fun i ↦ F i k) z + (1 - ζ z) * (h z * mixedDensity H z) := by
    intro z hz
    by_cases hzK : z ∈ K
    · rw [hζK z hzK]; ring
    · have hzV := hWV' hz
      have hnbhd : (V : Set (ComplexModel n)) \ K ∈ 𝓝 z :=
        (V.isOpen.sdiff hK.isClosed).mem_nhds ⟨hzV, hzK⟩
      have hMD : mixedDensity (fun i ↦ F i k) z = mixedDensity H z := by
        refine mixedDensity_congr fun i ↦ ?_
        filter_upwards [hnbhd] with y hy
        by_cases hi : i.val < q
        · simp [hH, hi, hFh i hi k y hy.1 hy.2]
        · simp [hH, hi, hF.2 i (not_lt.mp hi) k hy.1]
      rw [hGh l z hzV hzK, hMD]; ring
  have hcont1 (k : ℕ) : ContinuousOn (fun z ↦ ζ z * G l z * mixedDensity (fun i ↦ F i k) z) V :=
    (hζ.continuousOn.mul (hG.1 l).1.continuousOn).mul
      (continuousOn_mixedDensity fun i ↦ ((hF.1 i).1 k).1)
  have hcont2 : ContinuousOn (fun z ↦ (1 - ζ z) * (h z * mixedDensity H z)) V :=
    (continuousOn_const.sub hζ.continuousOn).mul (hh.1.continuousOn.mul
      (continuousOn_mixedDensity hHs))
  set c := ∫ z in W, (1 - ζ z) * (h z * mixedDensity H z)
  have heq (k : ℕ) : ∫ z in W, G l z * mixedDensity (fun i ↦ F i k) z =
      (∫ z, ζ z * G l z * mixedDensity (fun i ↦ F i k) z) + c := by
    rw [setIntegral_congr_fun hWo.measurableSet (hsplit k),
      integral_add (integrableOn_of_continuousOn_closure hWc hWV (hcont1 k))
        (integrableOn_of_continuousOn_closure hWc hWV hcont2),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by simp [hζ0 z hz]]
  -- (iii) passing to the limit in `k`
  have hζG : Continuous fun z ↦ ζ z * G l z :=
    continuous_of_continuousOn_of_eq_zero V.isOpen (isClosed_tsupport ζ) hζV
      (hζ.continuousOn.mul (hG.1 l).1.continuousOn)
      fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]
  have hlim := hT (fun z ↦ ζ z * G l z) hζG hζc.mul_right
    ((tsupport_mul_subset_left).trans hζV)
  have hle1 : ∫ z, ζ z * G l z ∂μ ≤ ∫ z, ζ z * G l z * mixedDensity (fun i ↦ F i l) z := by
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨l, fun k hk ↦ ?_⟩)
    have := hcomp k hk
    rw [heq k, heq l] at this
    linarith
  -- (iv) comparing the limit weight
  obtain ⟨C, hC⟩ := hG.exists_abs_le hζc hζV
  have hmeas : Measurable fun z ↦ ζ z * w z := by
    refine measurable_of_tendsto_metrizable (f := fun m z ↦ ζ z * G m z)
      (fun m ↦ (continuous_of_continuousOn_of_eq_zero V.isOpen (isClosed_tsupport ζ) hζV
        (hζ.continuousOn.mul (hG.1 m).1.continuousOn)
        fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]).measurable) ?_
    rw [tendsto_pi_nhds]
    intro z
    by_cases hzV : z ∈ (V : Set (ComplexModel n))
    · exact (hG.2.2.1 z hzV).const_mul _
    · have : ζ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzV (hζV h)
      simp [this]
  have hbdd : ∀ z, |ζ z * w z| ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ tsupport ζ
    · have hwC : |w z| ≤ C := by
        have hlimz := hG.2.2.1 z (hζV hz)
        exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlimz) fun m ↦ hC m z hz
      rw [abs_mul, abs_of_nonneg (hζ01 z).1]
      exact ((mul_le_of_le_one_left (abs_nonneg _) (hζ01 z).2).trans hwC).trans (le_max_left _ _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hIw : Integrable (fun z ↦ ζ z * w z) μ := by
    rw [← integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left _ _).trans (subset_tsupport ζ))]
    exact Measure.integrableOn_of_bounded (M := max C 0) (hμf _ hζc hζV).ne
      hmeas.aestronglyMeasurable (Eventually.of_forall hbdd)
  have hIG : Integrable (fun z ↦ ζ z * G l z) μ :=
    integrable_of_tsupport_subset hμf hζG hζc.mul_right ((tsupport_mul_subset_left).trans hζV)
  refine (integral_mono hIw hIG fun z ↦ ?_).trans hle1
  by_cases hzV : z ∈ (V : Set (ComplexModel n))
  · exact mul_le_mul_of_nonneg_left (hG.le_of_mem hzV l) (hζ01 z).1
  · have : ζ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzV (hζV h)
    simp [this]

theorem IsDecApprox.integrable_mul {V : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox V w G) {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ V → μ K < ⊤) {ψ : ComplexModel n → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψV : tsupport ψ ⊆ V) :
    Integrable (fun z ↦ ψ z * w z) μ := by
  obtain ⟨C, hC⟩ := hG.exists_abs_le hψc hψV
  obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ
  have hmeas : Measurable fun z ↦ ψ z * w z := by
    refine measurable_of_tendsto_metrizable (f := fun m z ↦ ψ z * G m z)
      (fun m ↦ (continuous_of_continuousOn_of_eq_zero V.isOpen (isClosed_tsupport ψ) hψV
        (hψ.continuousOn.mul (hG.1 m).1.continuousOn)
        fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]).measurable) ?_
    rw [tendsto_pi_nhds]
    intro z
    by_cases hzV : z ∈ (V : Set (ComplexModel n))
    · exact (hG.2.2.1 z hzV).const_mul _
    · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzV (hψV h)
      simp [this]
  have hbdd : ∀ z, ‖ψ z * w z‖ ≤ B * max C 0 := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · have hwC : |w z| ≤ C :=
        le_of_tendsto' ((continuous_abs.tendsto _).comp (hG.2.2.1 z (hψV hz))) fun m ↦ hC m z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hB z) (hwC.trans (le_max_left _ _))
        (abs_nonneg _) ((norm_nonneg _).trans (hB z))
    · simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hB z)) (le_max_right _ _)
  rw [← integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left _ _).trans (subset_tsupport ψ))]
  exact Measure.integrableOn_of_bounded (M := B * max C 0) (hμf _ hψc hψV).ne
    hmeas.aestronglyMeasurable (Eventually.of_forall hbdd)

/-- **Convergence for a modified family.** With the collar estimate, the upper
bound applied to `χ` and to `ζ - χ` squeezes the weighted integrals of `χ`. -/
theorem tendsto_weighted_of_collar {q : ℕ} {V : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible q V u F) {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ}
    (hG : IsDecApprox V w G) {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ V → μ K < ⊤) (hT : TendstoMixed V F μ)
    {h : ComplexModel n → ℝ} (hh : IsSmoothPsdOn V h) {K W : Set (ComplexModel n)}
    (hK : IsCompact K) (hKW : K ⊆ W) (hWo : IsOpen W) (hWc : IsCompact (closure W))
    (hWV : closure W ⊆ V)
    (hGh : ∀ k, ∀ z ∈ (V : Set (ComplexModel n)), z ∉ K → G k z = h z)
    (hFh : ∀ i : Fin n, i.val < q → ∀ k, ∀ z ∈ (V : Set (ComplexModel n)), z ∉ K → F i k z = h z)
    {ζ : ComplexModel n → ℝ} (hζ : Continuous ζ) (hζ01 : ∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1)
    (hζK : ∀ z ∈ K, ζ z = 1) (hζW : tsupport ζ ⊆ W) {χ : ComplexModel n → ℝ}
    (hχ : Continuous χ) (hχ0 : ∀ z, 0 ≤ χ z) (hχζ : ∀ z, χ z ≤ ζ z) :
    Tendsto (fun k ↦ ∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z) atTop
      (𝓝 (∫ z, χ z * w z ∂μ)) := by
  have hWV' : W ⊆ V := subset_closure.trans hWV
  have hζc : HasCompactSupport ζ := hWc.of_isClosed_subset (isClosed_tsupport ζ)
    (hζW.trans subset_closure)
  have hζV : tsupport ζ ⊆ V := hζW.trans hWV'
  have hχζs : tsupport χ ⊆ tsupport ζ := closure_mono fun z hz ↦ by
    have h1 : χ z ≠ 0 := hz
    have h2 := hχζ z
    have h3 := hχ0 z
    exact fun h0 ↦ h1 (le_antisymm (h0 ▸ h2) h3)
  have hχc : HasCompactSupport χ := hζc.mono' ((subset_tsupport χ).trans hχζs)
  have hχV : tsupport χ ⊆ V := hχζs.trans hζV
  have hFs : ∀ i k, IsSmoothPsdOn V (F i k) := fun i k ↦ (hF.1 i).1 k
  set L := ∫ z, χ z * w z ∂μ
  have hDc (k : ℕ) := continuousOn_mixedDensity fun i ↦ (hFs i k).1
  have hIk (ψ : ComplexModel n → ℝ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
      (hψV : tsupport ψ ⊆ V) (k : ℕ) :
      Integrable fun z ↦ ψ z * G k z * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn (D := fun z ↦ G k z * mixedDensity (fun i ↦ F i k) z)
      ((hG.1 k).1.continuousOn.mul (hDc k)) hψ hψc hψV
    simpa only [mul_assoc] using this
  have hζχ : Continuous fun z ↦ ζ z - χ z := hζ.sub hχ
  have hζχc : HasCompactSupport fun z ↦ ζ z - χ z := hζc.sub hχc
  have hζχV : tsupport (fun z ↦ ζ z - χ z) ⊆ V :=
    (tsupport_sub _ _).trans (union_subset hζV hχV)
  rw [tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · have hε : 0 < (L - a) / 2 := by linarith
    filter_upwards [eventually_weighted_integral_le hFs hμf hT hG hζχ hζχc hζχV
      (fun z ↦ sub_nonneg.2 (hχζ z)) hε] with k hk
    have hcol := integral_cutoff_weight_le hF hG hμf hT hh hK hKW hWo hWc hWV hGh hFh hζ hζ01
      hζK hζW k
    have hsplitL : ∫ z, (ζ z - χ z) * G k z * mixedDensity (fun i ↦ F i k) z =
        (∫ z, ζ z * G k z * mixedDensity (fun i ↦ F i k) z) -
          ∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z := by
      rw [← integral_sub (hIk ζ hζ hζc hζV k) (hIk χ hχ hχc hχV k)]
      congr 1; funext z; ring
    have hsplitR : ∫ z, (ζ z - χ z) * w z ∂μ = (∫ z, ζ z * w z ∂μ) - L := by
      rw [← integral_sub (hG.integrable_mul hμf hζ hζc hζV) (hG.integrable_mul hμf hχ hχc hχV)]
      congr 1; funext z; ring
    rw [hsplitL, hsplitR] at hk
    linarith
  · have hε : 0 < (b - L) / 2 := by linarith
    filter_upwards [eventually_weighted_integral_le hFs hμf hT hG hχ hχc hχV hχ0 hε] with k hk
    linarith

theorem IsDecApprox.mono {U V : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (hVU : V ≤ U) : IsDecApprox V w G :=
  ⟨fun k ↦ ⟨(hG.1 k).1.mono hVU, fun z hz ↦ (hG.1 k).2 z (hVU hz)⟩,
    fun z hz ↦ hG.2.1 z (hVU hz), fun z hz ↦ hG.2.2.1 z (hVU hz),
    fun K hK hKV ↦ hG.2.2.2 K hK (hKV.trans hVU)⟩

theorem IsAdmissible.mono {q : ℕ} {U V : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {F : Fin n → ℕ → ComplexModel n → ℝ} (hF : IsAdmissible q U u F) (hVU : V ≤ U) :
    IsAdmissible q V u F :=
  ⟨fun i ↦ (hF.1 i).mono hVU, fun i hi k _ hz ↦ hF.2 i hi k (hVU hz)⟩

end BallEstimate

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
