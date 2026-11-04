/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

public import LeanPool.LCAnalysis.IntegralExistence

/-!
# Calculus with weak integrals: algebra, change of variables, fundamental theorem

For curves in a locally convex space `F` (Glöckner–Neeb, §1.1):

* Algebraic rules: weak integrals are additive in the integrand and in the interval, and
  commute with continuous linear maps.
* Change of variables: for a `C^1` real function `φ`,
  `∫_a^b φ'(t) • γ(φ t) dt = ∫_{φ a}^{φ b} γ`, as an equivalence of the two existence statements.
* Fundamental theorem of calculus, first part (Glöckner–Neeb, Prop. 1.1.5): if `γ` has a
  continuous derivative `γ'`, then `γ b - γ a` is the weak integral of `γ'` over `[a, b]`; no
  completeness assumption on `F` is needed. The same holds for `t ↦ df(x + t h)(h)` when `f` is
  `C^1` on a set containing the segment (the mean value theorem, Glöckner–Neeb, Prop. 1.2.6).
* Fundamental theorem of calculus, second part (Glöckner–Neeb, Prop. 1.1.12): if the weak
  integrals `η s = ∫_a^s γ` of a continuous curve exist, then `η` is differentiable with
  derivative `γ`. In a sequentially complete space they always exist.
-/

@[expose] public section

open Set Filter Function
open scoped Topology Pointwise

noncomputable section

namespace LCAnalysis

universe u v w

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {γ η : ℝ → F} {a b c : ℝ} {y z : F}

/-! ### Algebraic rules -/

theorem HasWeakIntegral.neg (hy : HasWeakIntegral γ a b y) :
    HasWeakIntegral (fun t ↦ -γ t) a b (-y) := by
  intro φ
  simp only [map_neg]
  rw [intervalIntegral.integral_neg, hy φ]

theorem HasWeakIntegral.add (hγ : ContinuousOn γ (uIcc a b)) (hη : ContinuousOn η (uIcc a b))
    (hy : HasWeakIntegral γ a b y) (hz : HasWeakIntegral η a b z) :
    HasWeakIntegral (fun t ↦ γ t + η t) a b (y + z) := by
  intro φ
  have i₁ : IntervalIntegrable (fun t ↦ φ (γ t)) MeasureTheory.volume a b :=
    (φ.continuous.comp_continuousOn hγ).intervalIntegrable
  have i₂ : IntervalIntegrable (fun t ↦ φ (η t)) MeasureTheory.volume a b :=
    (φ.continuous.comp_continuousOn hη).intervalIntegrable
  simp only [map_add]
  rw [intervalIntegral.integral_add i₁ i₂, hy φ, hz φ]

theorem hasWeakIntegral_const (v : F) (a b : ℝ) :
    HasWeakIntegral (fun _ ↦ v) a b ((b - a) • v) := by
  intro φ
  simp [map_smul, smul_eq_mul]

/-- Weak integrals commute with continuous linear maps. -/
theorem HasWeakIntegral.map (hy : HasWeakIntegral γ a b y) (L : F →L[ℝ] G) :
    HasWeakIntegral (fun t ↦ L (γ t)) a b (L y) :=
  fun φ ↦ hy (φ.comp L)

/-- Additivity in the interval. -/
theorem HasWeakIntegral.add_adjacent (hγab : ContinuousOn γ (uIcc a b))
    (hγbc : ContinuousOn γ (uIcc b c)) (hy : HasWeakIntegral γ a b y)
    (hz : HasWeakIntegral γ b c z) : HasWeakIntegral γ a c (y + z) := by
  intro φ
  have i₁ : IntervalIntegrable (fun t ↦ φ (γ t)) MeasureTheory.volume a b :=
    (φ.continuous.comp_continuousOn hγab).intervalIntegrable
  have i₂ : IntervalIntegrable (fun t ↦ φ (γ t)) MeasureTheory.volume b c :=
    (φ.continuous.comp_continuousOn hγbc).intervalIntegrable
  rw [map_add, hy φ, hz φ, intervalIntegral.integral_add_adjacent_intervals i₁ i₂]

/-! ### Change of variables -/

/-- Change of variables in weak integrals: if `φ` is `C^1` on `[a, b]` and `γ` is continuous on
`φ '' [a, b]`, then `y` is a weak integral of `γ` over `[φ a, φ b]` if and only if it is a weak
integral of `t ↦ φ' t • γ (φ t)` over `[a, b]`. -/
theorem hasWeakIntegral_comp_smul_deriv_iff {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ uIcc a b, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (uIcc a b))
    (hγ : ContinuousOn γ (φ '' uIcc a b)) :
    HasWeakIntegral (fun t ↦ φ' t • γ (φ t)) a b y ↔ HasWeakIntegral γ (φ a) (φ b) y := by
  have key : ∀ ψ : F →L[ℝ] ℝ,
      ∫ t in a..b, ψ (φ' t • γ (φ t)) = ∫ t in φ a..φ b, ψ (γ t) := fun ψ ↦ by
    rw [← intervalIntegral.integral_comp_mul_deriv' (g := fun x ↦ ψ (γ x)) hφ hφ'
      (ψ.continuous.comp_continuousOn hγ)]
    simp [map_smul, smul_eq_mul, mul_comm]
  exact forall_congr' fun ψ ↦ by rw [key]

/-- The affine case: `∫_t^{t+s} γ = s • ∫_0^1 γ(t + s r) dr`. -/
theorem hasWeakIntegral_affine_iff {t s : ℝ} (hγ : ContinuousOn γ (uIcc t (t + s))) :
    HasWeakIntegral (fun r ↦ s • γ (t + s * r)) 0 1 y ↔ HasWeakIntegral γ t (t + s) y := by
  have hmaps : (fun r ↦ t + s * r) '' uIcc 0 1 ⊆ uIcc t (t + s) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [uIcc_of_le zero_le_one] at hr
    rcases le_total 0 s with hs | hs
    · rw [uIcc_of_le (by linarith)]
      constructor <;> nlinarith [hr.1, hr.2]
    · rw [uIcc_of_ge (by linarith)]
      constructor <;> nlinarith [hr.1, hr.2]
  have := hasWeakIntegral_comp_smul_deriv_iff (y := y) (a := 0) (b := 1)
    (φ := fun r ↦ t + s * r) (φ' := fun _ ↦ s)
    (fun r _ ↦ by simpa using ((hasDerivAt_id r).const_mul s).const_add t)
    continuousOn_const (hγ.mono hmaps)
  simpa using this

/-! ### The fundamental theorem of calculus -/

/-- Fundamental theorem of calculus, first part: if `γ` has a continuous derivative `γ'` on
`[a, b]`, then `γ b - γ a` is the weak integral of `γ'` over `[a, b]`. No completeness of `F` is
needed. -/
theorem hasWeakIntegral_sub_of_hasDirDerivAt {γ' : ℝ → F}
    (hγ : ∀ t ∈ uIcc a b, HasDirDerivAt γ t 1 (γ' t)) (hγ' : ContinuousOn γ' (uIcc a b)) :
    HasWeakIntegral γ' a b (γ b - γ a) := by
  intro φ
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s ↦ φ (γ s)) (φ (γ' t)) t := fun t ht ↦ by
    have := (show HasDirDerivAt γ (0 + t • (1 : ℝ)) 1 (γ' t) by simpa using hγ t ht)
      |>.hasDerivAt_clm φ
    simpa using this
  rw [map_sub, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (φ.continuous.comp_continuousOn hγ').intervalIntegrable]

/-- Fundamental theorem of calculus along a segment: if `f` is `C^1` on a set containing the
segment `[x, x + h]`, then `f (x + h) - f x = ∫₀¹ df(x + t h)(h) dt`, the weak integral existing
in `F` (no completeness assumption). -/
theorem ContDiffMBOn.hasWeakIntegral_dMB {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
     {f : E → F} {U : Set E} (hf : ContDiffMBOn 1 f U) {x h : E}
    (hxh : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    HasWeakIntegral (fun t ↦ dMB f (x + t • h, h)) 0 1 (f (x + h) - f x) := fun φ ↦ by
  rw [map_sub, hf.integral_dMB hxh φ]

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- For a neighborhood `N` of `0` there is a closed convex neighborhood `W` of `0` with
`2 • W ⊆ N`. -/
theorem exists_closed_convex_two_smul_subset {N : Set F} (hN : N ∈ 𝓝 (0 : F)) :
    ∃ W ∈ 𝓝 (0 : F), IsClosed W ∧ Convex ℝ W ∧ (2 : ℝ) • W ⊆ N := by
  have h2 : (2 : ℝ)⁻¹ • N ∈ 𝓝 (0 : F) := (set_smul_mem_nhds_zero_iff (by norm_num)).mpr hN
  obtain ⟨W, hW, hWc, hWconv, hWN⟩ := exists_closed_convex_nhds_subset h2
  refine ⟨W, hW, hWc, hWconv, ?_⟩
  calc (2 : ℝ) • W ⊆ (2 : ℝ) • (2 : ℝ)⁻¹ • N := smul_set_mono hWN
    _ = N := by rw [smul_smul, mul_inv_cancel₀ (by norm_num), one_smul]

variable [T2Space F]

theorem weakIntegral_eq_sub_of_hasDirDerivAt {γ' : ℝ → F}
    (hγ : ∀ t ∈ uIcc a b, HasDirDerivAt γ t 1 (γ' t)) (hγ' : ContinuousOn γ' (uIcc a b)) :
    weakIntegral γ' a b = γ b - γ a :=
  (hasWeakIntegral_sub_of_hasDirDerivAt hγ hγ').weakIntegral_eq

/-- Fundamental theorem of calculus, second part: if `γ` is continuous on an open interval `I`
and the weak integrals `∫_a^s γ` exist for `s ∈ I`, then `s ↦ ∫_a^s γ` is differentiable on `I`,
with derivative `γ`. -/
theorem hasDirDerivAt_weakIntegral_right_of_exists {I : Set ℝ} (hI : IsOpen I)
    (hIc : I.OrdConnected) (hγ : ContinuousOn γ I) (ha : a ∈ I)
    (hex : ∀ s ∈ I, ∃ y, HasWeakIntegral γ a s y) {t : ℝ} (ht : t ∈ I) :
    HasDirDerivAt (fun s ↦ weakIntegral γ a s) t 1 (γ t) := by
  have hex : ∀ s ∈ I, HasWeakIntegral γ a s (weakIntegral γ a s) := fun s hs ↦
    hasWeakIntegral_weakIntegral (hex s hs)
  unfold HasDirDerivAt
  rw [← tendsto_sub_nhds_zero_iff]
  intro N hN
  rw [Filter.mem_map]
  obtain ⟨W, hW, hWc, hWconv, hWN⟩ := exists_closed_convex_two_smul_subset hN
  obtain ⟨ε, hε, hεI, hεW⟩ : ∃ ε > 0, Metric.ball t ε ⊆ I ∧
      ∀ u ∈ Metric.ball t ε, γ u - γ t ∈ W := by
    have hcont : ContinuousAt (fun u ↦ γ u - γ t) t :=
      ((hγ.continuousAt (hI.mem_nhds ht)).sub continuousAt_const)
    have h1 : ∀ᶠ u in 𝓝 t, γ u - γ t ∈ W :=
      hcont.eventually_mem (by simpa using hW)
    obtain ⟨ε₁, hε₁, h₁⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds ht)
    obtain ⟨ε₂, hε₂, h₂⟩ := Metric.mem_nhds_iff.mp h1
    exact ⟨min ε₁ ε₂, lt_min hε₁ hε₂,
      (Metric.ball_subset_ball (min_le_left _ _)).trans h₁,
      fun u hu ↦ h₂ (Metric.ball_subset_ball (min_le_right _ _) hu)⟩
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hε)]
    with s (hs0 : s ≠ 0) hsε
  simp only [smul_eq_mul, mul_one, Set.mem_preimage]
  have hsε' : |s| < ε := by simpa using hsε
  -- the segment `[t, t + s]` lies in the ball
  have hseg : uIcc t (t + s) ⊆ Metric.ball t ε := fun u hu ↦ by
    rw [Metric.mem_ball, Real.dist_eq]
    rcases le_total 0 s with h | h
    · rw [uIcc_of_le (by linarith)] at hu
      rw [abs_lt]; constructor <;> linarith [hu.1, hu.2, abs_of_nonneg h]
    · rw [uIcc_of_ge (by linarith)] at hu
      rw [abs_lt]; constructor <;> linarith [hu.1, hu.2, abs_of_nonpos h]
  have hγseg : ContinuousOn γ (uIcc t (t + s)) := hγ.mono (hseg.trans hεI)
  have hts : t + s ∈ I := hεI (hseg right_mem_uIcc)
  -- `∫_a^{t+s} γ - ∫_a^t γ` is a weak integral of `γ` over `[t, t + s]`
  set z := weakIntegral γ a (t + s) - weakIntegral γ a t
  have hz : HasWeakIntegral γ t (t + s) z := fun φ ↦ by
    have i : ∀ u ∈ I, IntervalIntegrable (fun r ↦ φ (γ r)) MeasureTheory.volume a u := fun u hu ↦
      (φ.continuous.comp_continuousOn (hγ.mono (hIc.uIcc_subset ha hu))).intervalIntegrable
    rw [map_sub, hex _ hts φ, hex t ht φ,
      intervalIntegral.integral_interval_sub_left (i _ hts) (i t ht)]
  -- `s⁻¹ • ∫_t^{t+s} γ - γ t = ∫₀¹ (γ (t + s r) - γ t) dr`
  have hcurve : ContinuousOn (fun r ↦ γ (t + s * r)) (Icc 0 1) := by
    refine hγseg.comp (by fun_prop) fun r hr ↦ ?_
    rcases le_total 0 s with h | h
    · rw [uIcc_of_le (by linarith)]; constructor <;> nlinarith [hr.1, hr.2]
    · rw [uIcc_of_ge (by linarith)]; constructor <;> nlinarith [hr.1, hr.2]
  have hz' : HasWeakIntegral (fun r ↦ γ (t + s * r)) 0 1 (s⁻¹ • z) := by
    have := ((hasWeakIntegral_affine_iff hγseg).mpr hz).const_smul s⁻¹
    simpa [smul_smul, inv_mul_cancel₀ hs0] using this
  have hdiff : HasWeakIntegral (fun r ↦ γ (t + s * r) - γ t) 0 1 (s⁻¹ • z - γ t) := by
    have := hz'.sub zero_le_one hcurve continuousOn_const (hasWeakIntegral_const (γ t) 0 1)
    simpa using this
  have hmem : s⁻¹ • z - γ t ∈ (1 - 0 + 1 : ℝ) • W :=
    hdiff.mem_smul zero_le_one (hcurve.sub continuousOn_const) hWconv hWc
      (mem_of_mem_nhds hW) fun r hr ↦ hεW _ (hseg (by
        rcases le_total 0 s with h | h
        · rw [uIcc_of_le (by linarith)]; constructor <;> nlinarith [hr.1, hr.2]
        · rw [uIcc_of_ge (by linarith)]; constructor <;> nlinarith [hr.1, hr.2]))
  exact hWN (by norm_num at hmem ⊢; exact hmem)

/-- Fundamental theorem of calculus, second part, in a sequentially complete space: the indefinite
integral of a curve that is continuous on an open interval `I` is differentiable on `I`, with
derivative the curve itself. -/
theorem hasDirDerivAt_weakIntegral_right [SeqComplete F] {I : Set ℝ} (hI : IsOpen I)
    (hIc : I.OrdConnected) (hγ : ContinuousOn γ I) (ha : a ∈ I) {t : ℝ} (ht : t ∈ I) :
    HasDirDerivAt (fun s ↦ weakIntegral γ a s) t 1 (γ t) :=
  hasDirDerivAt_weakIntegral_right_of_exists hI hIc hγ ha
    (fun _ hs ↦ exists_hasWeakIntegral (hγ.mono (hIc.uIcc_subset ha hs))) ht

end LCAnalysis
