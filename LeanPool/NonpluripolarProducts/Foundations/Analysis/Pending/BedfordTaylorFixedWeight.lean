/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorQuasiContinuity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorExistence
public import Mathlib.Topology.TietzeExtension

/-!
# Weak convergence against a fixed quasi-continuous weight

Let `μₖ = ddᶜvₖ₁ ∧ ⋯ ∧ ddᶜvₖₙ` and `μ = ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ` be Bedford–Taylor limits of
tuples of locally bounded plurisubharmonic functions on `Ω ⊆ ℂⁿ`, with the `vₖᵢ` locally
uniformly bounded in `k`, and suppose `μₖ → μ` vaguely on `Ω`. Then for every locally
bounded plurisubharmonic `f` on `Ω` and every continuous compactly supported `χ` in `Ω`

  `∫ χ f dμₖ → ∫ χ f dμ`

This local version extends the fixed-weight argument in
[Błocki, equation (2.2.2)](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=45),
which treats monotone bounded data agreeing on a common boundary collar of a ball.

Proof. Choose an open `U` with `supp χ ⊆ U ⋐ Ω`; on `U` all slots are bounded by one
constant `M`, so after shifting the slots by `-M` (gauge invariance) the domination by the
relative capacity gives `μₖ(E), μ(E) ≤ C · c(E, U)` for `E ⊆ U`, uniformly in `k`.
By quasi-continuity there is an open `G` with `c(G, U) < δ` and `f` continuous on
`supp χ \ G`; by Tietze's theorem (clamped to the bound `B` of `f` on `supp χ`) there is a
continuous `φ` with `|φ| ≤ B` and `φ = f` on `supp χ \ G`. Then

  `|∫ χ f dν - ∫ χ φ dν| ≤ ‖χ‖∞ · 2B · ν(supp χ ∩ G) ≤ ‖χ‖∞ · 2B · C · δ`

for `ν = μₖ` and `ν = μ`, while `∫ χ φ dμₖ → ∫ χ φ dμ` by vague convergence.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- A real sequence converges if it is, up to every `ε`, uniformly close to a convergent
sequence whose limit is `ε`-close to the proposed limit. -/
theorem tendsto_of_forall_abs_sub_le {a : ℕ → ℝ} {a₀ : ℝ}
    (h : ∀ ε > 0, ∃ b : ℕ → ℝ, ∃ b₀ : ℝ, Tendsto b atTop (𝓝 b₀) ∧
      (∀ k, |a k - b k| ≤ ε) ∧ |a₀ - b₀| ≤ ε) :
    Tendsto a atTop (𝓝 a₀) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨b, b₀, hb, hab, hab₀⟩ := h (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hb (ε / 4) (by positivity)
  refine ⟨N, fun k hk ↦ ?_⟩
  have h1 := abs_lt.1 (by simpa [Real.dist_eq] using hN k hk)
  have h2 := abs_le.1 (hab k)
  have h3 := abs_le.1 hab₀
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem IsLocallyBoundedPshOn.mono_opens {Ω U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hUΩ : U ≤ Ω) : IsLocallyBoundedPshOn U u := by
  refine ⟨hu.1.mono hUΩ, fun z hz ↦ ?_⟩
  obtain ⟨V, hzV, -, C, hC⟩ := hu.2 z (hUΩ hz)
  exact ⟨V ⊓ U, ⟨hzV, hz⟩, inf_le_right, C, fun w hw ↦ hC w hw.1⟩

/-- Strict sublevel sets of a plurisubharmonic function, intersected with its domain,
are open (upper semicontinuity). -/
theorem isOpen_setOf_mem_and_lt_of_plurisubharmonicOn {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) Ω) (c : ℝ) :
    IsOpen {z | z ∈ Ω ∧ f z < c} := by
  refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
  have h := (hf z hz.1).upperSemicontinuousAt (c : EReal) (EReal.coe_lt_coe_iff.2 hz.2)
  filter_upwards [Ω.isOpen.mem_nhds hz.1, h] with x hx hxc
  exact ⟨hx, EReal.coe_lt_coe_iff.1 hxc⟩

theorem measurable_indicator_of_plurisubharmonicOn {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) Ω) :
    Measurable ((Ω : Set (ComplexModel n)).indicator f) := by
  refine measurable_of_Iio fun c ↦ ?_
  have hset : (Ω : Set (ComplexModel n)).indicator f ⁻¹' Iio c =
      {z | z ∈ Ω ∧ f z < c} ∪ ((Ω : Set (ComplexModel n))ᶜ ∩ {_z | (0 : ℝ) < c}) := by
    ext z
    by_cases hz : z ∈ Ω
    · simp [hz, show z ∈ (Ω : Set (ComplexModel n)) from hz]
    · simp [hz, show z ∉ (Ω : Set (ComplexModel n)) from hz]
  rw [hset]
  exact (isOpen_setOf_mem_and_lt_of_plurisubharmonicOn hf c).measurableSet.union
    (Ω.isOpen.measurableSet.compl.inter (MeasurableSet.const _))

theorem measurable_mul_of_plurisubharmonicOn {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : PlurisubharmonicOn (fun z ↦ (f z : EReal)) Ω)
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχΩ : tsupport χ ⊆ (Ω : Set (ComplexModel n))) :
    Measurable fun z ↦ χ z * f z := by
  have hfun : (fun z ↦ χ z * f z) = fun z ↦ χ z * (Ω : Set (ComplexModel n)).indicator f z := by
    funext z
    by_cases hz : z ∈ (Ω : Set (ComplexModel n))
    · rw [indicator_of_mem hz]
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hχΩ h), zero_mul, zero_mul]
  rw [hfun]
  exact hχ.measurable.mul (measurable_indicator_of_plurisubharmonicOn hf)

theorem integrable_mul_of_abs_le {ν : Measure (ComplexModel n)} {χ g : ComplexModel n → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hν : ν (tsupport χ) < ⊤)
    (hg : Measurable fun z ↦ χ z * g z) {B : ℝ} (hB : ∀ z ∈ tsupport χ, |g z| ≤ B) :
    Integrable (fun z ↦ χ z * g z) ν := by
  obtain ⟨S, hS⟩ := hχc.exists_bound_of_continuous hχ
  rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport χ)
    fun z hz ↦ subset_tsupport χ (left_ne_zero_of_mul hz)]
  refine Measure.integrableOn_of_bounded (M := S * B) hν.ne hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (isClosed_tsupport χ).measurableSet] with z hz
  rw [norm_mul, Real.norm_eq_abs (g z)]
  exact mul_le_mul (hS z) (hB z hz) (abs_nonneg _) ((norm_nonneg _).trans (hS z))

/-- Changing the weight on `supp χ ∩ G` changes the integral by at most
`‖χ‖∞ · 2B · ν(supp χ ∩ G)`. -/
theorem abs_integral_mul_sub_integral_mul_le {ν : Measure (ComplexModel n)}
    {χ f φ : ComplexModel n → ℝ} {G : Set (ComplexModel n)} (hG : MeasurableSet G)
    (hfi : Integrable (fun z ↦ χ z * f z) ν) (hφi : Integrable (fun z ↦ χ z * φ z) ν)
    (hνG : ν (tsupport χ ∩ G) < ⊤) {S B : ℝ} (hS : ∀ z, |χ z| ≤ S)
    (hf : ∀ z ∈ tsupport χ, |f z| ≤ B) (hφ : ∀ z, |φ z| ≤ B)
    (heq : ∀ z ∈ tsupport χ \ G, φ z = f z) :
    |∫ z, χ z * f z ∂ν - ∫ z, χ z * φ z ∂ν| ≤ S * (2 * B) * (ν (tsupport χ ∩ G)).toReal := by
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hφ 0)
  have hs : MeasurableSet (tsupport χ ∩ G) := (isClosed_tsupport χ).measurableSet.inter hG
  have hint : Integrable ((tsupport χ ∩ G).indicator fun _ ↦ S * (2 * B)) ν :=
    (integrable_indicator_iff hs).2 (integrableOn_const hνG.ne)
  rw [← integral_sub hfi hφi, ← Real.norm_eq_abs]
  calc ‖∫ z, (χ z * f z - χ z * φ z) ∂ν‖
      ≤ ∫ z, (tsupport χ ∩ G).indicator (fun _ ↦ S * (2 * B)) z ∂ν := by
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun z ↦ ?_)
        have hnn : 0 ≤ (tsupport χ ∩ G).indicator (fun _ ↦ S * (2 * B)) z :=
          indicator_nonneg (fun _ _ ↦ by positivity) z
        by_cases hz1 : z ∈ tsupport χ
        · by_cases hz2 : z ∈ G
          · rw [indicator_of_mem (show z ∈ tsupport χ ∩ G from ⟨hz1, hz2⟩), Real.norm_eq_abs,
            ← mul_sub, abs_mul]
            have hfz := abs_le.1 (hf z hz1)
            have hφz := abs_le.1 (hφ z)
            refine mul_le_mul (hS z) (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _) hS0
          · rw [heq z ⟨hz1, hz2⟩, sub_self, norm_zero]
            exact hnn
        · rw [image_eq_zero_of_notMem_tsupport hz1, zero_mul, zero_mul, sub_self, norm_zero]
          exact hnn
    _ = S * (2 * B) * (ν (tsupport χ ∩ G)).toReal := by
        rw [integral_indicator_const _ hs, smul_eq_mul, measureReal_def, mul_comm]

/-- **Uniform capacity domination on a subdomain.** If the slots of a Bedford–Taylor limit
are bounded by `M` on `U ⊆ Ω`, then `ν(E) ≤ (2nM)ⁿ · c(E, U)` for `E ⊆ U`. -/
theorem IsBTLimit.le_relCapacity_of_abs_le {Ω U : Opens (ComplexModel n)}
    {w : Fin n → ComplexModel n → ℝ} {ν : Measure (ComplexModel n)} (hν : IsBTLimit Ω w ν)
    (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) (hUΩ : U ≤ Ω) {M : ℝ} (hM : 0 < M)
    (hwM : ∀ i, ∀ z ∈ U, |w i z| ≤ M) {E : Set (ComplexModel n)}
    (hEU : E ⊆ (U : Set (ComplexModel n))) :
    ν E ≤ ENNReal.ofReal ((n * (2 * M)) ^ n) * relCapacity U E := by
  have hconst : IsSmoothPluriharmonicOn U (fun _ ↦ -M) :=
    ⟨contDiffOn_const, fun z _ ↦ by ext j k; simp [complexHessian]⟩
  have h1 := (hν.restrict_opens hUΩ).add_pluriharmonic (h := fun _ _ ↦ -M) fun _ ↦ hconst
  have hcpsh : PlurisubharmonicOn (fun _ : ComplexModel n ↦ ((-M : ℝ) : EReal)) U :=
    fun x _ ↦ plurisubharmonicAt_const ((-M : ℝ) : EReal) (by simp) x
  have hpsh (i : Fin n) : IsLocallyBoundedPshOn U (fun z ↦ w i z + -M) := by
    refine isLocallyBoundedPshOn_of_abs_le (C := 2 * M) ?_ fun z hz ↦ ?_
    · have := ((IsLocallyBoundedPshOn.mono_opens (hw i) hUΩ).1).add hcpsh
      simpa only [EReal.coe_add] using this
    · have := abs_le.1 (hwM i z hz)
      rw [abs_le]; constructor <;> linarith
  have h2 := h1.le_relCapacity hpsh (by positivity : (0 : ℝ) < 2 * M)
    (fun i z hz ↦ by have := abs_le.1 (hwM i z hz); constructor <;> linarith) E
  rwa [Measure.restrict_eq_self _ hEU] at h2

/-- Local convergence against a fixed plurisubharmonic weight under vague convergence. -/
theorem tendsto_integral_mul_of_isBTLimit
    {Ω : Opens (ComplexModel n)} {v : ℕ → Fin n → ComplexModel n → ℝ}
    {μs : ℕ → Measure (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)}
    (hv : ∀ k i, IsLocallyBoundedPshOn Ω (v k i)) (hμs : ∀ k, IsBTLimit Ω (v k) (μs k))
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) (hμ : IsBTLimit Ω u μ)
    (hbd : ∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
      ∃ M : ℝ, ∀ k i, ∀ z ∈ K, |v k i z| ≤ M)
    (hconv : ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
      tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
      Tendsto (fun k => ∫ z, χ z ∂(μs k)) atTop (𝓝 (∫ z, χ z ∂μ)))
    {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f)
    {χ : ComplexModel n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ (Ω : Set (ComplexModel n))) :
    Tendsto (fun k => ∫ z, χ z * f z ∂(μs k)) atTop (𝓝 (∫ z, χ z * f z ∂μ)) := by
  classical
  have hKc : IsCompact (tsupport χ) := hχc
  obtain ⟨U₀, hU₀o, hKU₀, hU₀Ω, hU₀c⟩ :=
    exists_open_between_and_isCompact_closure hKc Ω.isOpen hχΩ
  set U : Opens (ComplexModel n) := ⟨U₀, hU₀o⟩ with hU_def
  have hUΩ : U ≤ Ω := subset_closure.trans hU₀Ω
  -- one bound for all slots on `U`
  obtain ⟨M₁, hM₁⟩ := hbd _ hU₀c hU₀Ω
  choose Cu hCu using fun i ↦ IsLocallyBoundedPshOn.exists_abs_le (hu i) hU₀c hU₀Ω
  set M : ℝ := max 1 (max M₁ (∑ i, |Cu i|)) with hM_def
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hvM : ∀ k i, ∀ z ∈ U, |v k i z| ≤ M := fun k i z hz ↦
    (hM₁ k i z (subset_closure hz)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have huM : ∀ i, ∀ z ∈ U, |u i z| ≤ M := fun i z hz ↦
    (hCu i z (subset_closure hz)).trans ((le_abs_self _).trans
      ((Finset.single_le_sum (f := fun i ↦ |Cu i|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ i)).trans ((le_max_right _ _).trans (le_max_right _ _))))
  set C : ℝ := (n * (2 * M)) ^ n with hC_def
  have hC0 : 0 ≤ C := by positivity
  -- the weight
  obtain ⟨B₀, hB₀⟩ := IsLocallyBoundedPshOn.exists_abs_le hf hKc hχΩ
  set B : ℝ := max B₀ 0 with hB_def
  have hB0 : 0 ≤ B := le_max_right _ _
  have hfB : ∀ z ∈ tsupport χ, |f z| ≤ B := fun z hz ↦ (hB₀ z hz).trans (le_max_left _ _)
  obtain ⟨S, hS⟩ := hχc.exists_bound_of_continuous hχ
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have hSabs : ∀ z, |χ z| ≤ S := fun z ↦ by simpa [Real.norm_eq_abs] using hS z
  have hmeas := measurable_mul_of_plurisubharmonicOn hf.1 hχ hχΩ
  have hfU : IsLocallyBoundedPshOn U f := IsLocallyBoundedPshOn.mono_opens hf hUΩ
  refine tendsto_of_forall_abs_sub_le fun ε hε ↦ ?_
  set δ : ℝ := ε / (S * (2 * B) * C + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨G, hGo, hGcap, hGcont⟩ :=
    IsLocallyBoundedPshOn.exists_isOpen_relCapacity_lt_continuousOn hfU hKc hKU₀ hδ
  -- Tietze extension of `f` from `supp χ \ G`, clamped to `[-B, B]`
  have hclosed : IsClosed (tsupport χ \ G) := (isClosed_tsupport χ).sdiff hGo
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hclosed
    ⟨(tsupport χ \ G).domRestrict f, hGcont.domRestrict⟩
  set φ : ComplexModel n → ℝ := fun z ↦ max (-B) (min B (g z)) with hφ_def
  have hφc : Continuous φ := continuous_const.max (continuous_const.min g.continuous)
  have hφB : ∀ z, |φ z| ≤ B := fun z ↦
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hφeq : ∀ z ∈ tsupport χ \ G, φ z = f z := by
    intro z hz
    have hgz : g z = f z := congrArg (fun h : C(↥(tsupport χ \ G), ℝ) ↦ h ⟨z, hz⟩) hg
    have hb := abs_le.1 (hfB z hz.1)
    simp only [hφ_def, hgz]
    rw [min_eq_right hb.2, max_eq_right hb.1]
  have hφmeas : Measurable fun z ↦ χ z * φ z := (hχ.mul hφc).measurable
  have hkey : ∀ ν : Measure (ComplexModel n),
      (∀ E, E ⊆ (U : Set (ComplexModel n)) → ν E ≤ ENNReal.ofReal C * relCapacity U E) →
      ν (tsupport χ) < ⊤ → |∫ z, χ z * f z ∂ν - ∫ z, χ z * φ z ∂ν| ≤ ε := by
    intro ν hνE hνK
    have hfinG : ν (tsupport χ ∩ G) < ⊤ := (measure_mono inter_subset_left).trans_lt hνK
    have hKG : ν (tsupport χ ∩ G) ≤ ENNReal.ofReal (C * δ) := by
      rw [ENNReal.ofReal_mul hC0]
      refine (hνE _ (inter_subset_left.trans hKU₀)).trans ?_
      gcongr
      exact ((relCapacity_mono inter_subset_right).trans hGcap.le)
    have hreal : (ν (tsupport χ ∩ G)).toReal ≤ C * δ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hKG
    calc |∫ z, χ z * f z ∂ν - ∫ z, χ z * φ z ∂ν|
        ≤ S * (2 * B) * (ν (tsupport χ ∩ G)).toReal :=
          abs_integral_mul_sub_integral_mul_le hGo.measurableSet
            (integrable_mul_of_abs_le hχ hχc hνK hmeas hfB)
            (integrable_mul_of_abs_le hχ hχc hνK hφmeas fun z _ ↦ hφB z) hfinG hSabs hfB hφB hφeq
      _ ≤ S * (2 * B) * (C * δ) := by gcongr
      _ ≤ ε := by
          have hpos : 0 < S * (2 * B) * C + 1 := by positivity
          rw [hδ_def, ← mul_assoc, mul_div_assoc', div_le_iff₀ hpos]
          nlinarith [mul_nonneg (mul_nonneg hS0 (mul_nonneg zero_le_two hB0)) hC0]
  refine ⟨fun k ↦ ∫ z, χ z * φ z ∂(μs k), ∫ z, χ z * φ z ∂μ,
    hconv _ (hχ.mul hφc) hχc.mul_right (tsupport_mul_subset_left.trans hχΩ),
    fun k ↦ hkey _ (fun E hE ↦ ?_) ((hμs k).2.1 _ hKc hχΩ), hkey _ (fun E hE ↦ ?_)
      (hμ.2.1 _ hKc hχΩ)⟩
  · exact (hμs k).le_relCapacity_of_abs_le (hv k) hUΩ hM (hvM k) hE
  · exact hμ.le_relCapacity_of_abs_le hu hUΩ hM huM hE

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
