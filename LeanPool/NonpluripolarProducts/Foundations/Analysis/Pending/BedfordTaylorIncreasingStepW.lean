/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingClaims
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorFixedWeight

/-!
# The collared weighted step of Cegrell's increasing convergence theorem

We prove `IncWCollarClaim n (q + 1)` from `IncPClaim n (q + 1)`, `IncWClaim n q`, the
fixed-weight convergence theorem (step F) and the symmetric integration by parts
`integral_sub_eq_integral_sub_of_eqOn_compl` (step S). This is the heart of Cegrell's
proof of the Bedford–Taylor convergence theorem along increasing sequences (Błocki,
*The complex Monge–Ampère operator in pluripotential theory*, lecture notes,
Thm 2.2.5; U. Cegrell).

Collared data: `Ω` is a ball, `g` is smooth with positive semidefinite complex Hessian,
`K ⊆ Ω` is compact, the slot `i₀ = q` and the weights `G_k ↑ w` all equal `g` off `K`.
Write `μ_j` for the measures of the approximating tuples, `μ` for the limit measure and
`ν(x)` for the Bedford–Taylor measure of the tuple with `x` in slot `i₀`. Fix a cutoff
`0 ≤ η ≤ 1` with compact support in `Ω`, equal to one near `K ∪ supp χ`, and put
`c_j(ψ) = ∫ ψ (G_j - g) dμ_j`, `C(ψ) = ∫ ψ (w - g) dμ`.

* **Upper bound.** For `ψ ≥ 0`, `c_j(ψ) ≤ ∫ ψ (w - g) dμ_j → C(ψ)` (step F).
* **Total mass from below.** For `k ≤ j`, `c_j(η) ≥ ∫ η (G_k - g) dμ_j → ∫ η (G_k - g) dμ`
  (step F). By step S with `u₀ = G_k`, `u₁ = u_q`,
  `∫ η (G_k - g) dμ = ∫ η (G_k - g) dν(g) + ∫ η (u_q - g) dν(G_k) - ∫ η (u_q - g) dν(g)`;
  as `k → ∞` the first term converges by `IncWClaim n q` (the tuple with `g` in slot
  `q` is level-`q` admissible), the second by step F along `ν(G_k) → ν(w)`
  (`IncPClaim n (q + 1)`), and step S with `u₀ = w` identifies the limit with `C(η)`.
  Hence `c_j(η) → C(η)`.
* **Localization.** With `M ≥ |χ|`, the tests `Mη ± χ` are nonnegative, and
  `c_j(χ) = c_j(Mη + χ) - M c_j(η) = M c_j(η) - c_j(Mη - χ)` squeezes `c_j(χ) → C(χ)`.
  Finally `∫ χ g dμ_j → ∫ χ g dμ` by step F.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- The statement of the fixed-weight convergence theorem (step F): along Bedford–Taylor
measures of locally uniformly bounded tuples converging vaguely on `Ω`, the integrals
of `χ f` converge for every locally bounded plurisubharmonic `f`. -/
def FixedWeightConvergence (n : ℕ) : Prop :=
  ∀ (Ω : Opens (ComplexModel n)) (v : ℕ → Fin n → ComplexModel n → ℝ)
    (μs : ℕ → Measure (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (μ : Measure (ComplexModel n)),
    (∀ k i, IsLocallyBoundedPshOn Ω (v k i)) → (∀ k, IsBTLimit Ω (v k) (μs k)) →
    (∀ i, IsLocallyBoundedPshOn Ω (u i)) → IsBTLimit Ω u μ →
    (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Ω →
      ∃ M : ℝ, ∀ k i, ∀ z ∈ K, |v k i z| ≤ M) →
    (∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
      tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
      Tendsto (fun k => ∫ z, χ z ∂(μs k)) atTop (𝓝 (∫ z, χ z ∂μ))) →
    ∀ f : ComplexModel n → ℝ, IsLocallyBoundedPshOn Ω f →
    ∀ χ : ComplexModel n → ℝ, Continuous χ → HasCompactSupport χ →
      tsupport χ ⊆ (Ω : Set (ComplexModel n)) →
      Tendsto (fun k => ∫ z, χ z * f z ∂(μs k)) atTop (𝓝 (∫ z, χ z * f z ∂μ))

/-- Step F, `tendsto_integral_mul_of_isBTLimit`, in the form of `FixedWeightConvergence`. -/
theorem fixedWeightConvergence : FixedWeightConvergence n :=
  fun _ _ _ _ _ hv hμs hu hμ hbd hconv _ hf _ hχ hχc hχΩ =>
    tendsto_integral_mul_of_isBTLimit hv hμs hu hμ hbd hconv hf hχ hχc hχΩ

/-- A locally bounded plurisubharmonic function times a continuous test with compact
support in `Ω` is integrable against a measure finite on compact subsets of `Ω`. -/
theorem IsLocallyBoundedPshOn.integrable_mul_of_tsupport_subset
    {Ω : Opens (ComplexModel n)} {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f)
    {μ : Measure (ComplexModel n)} (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    {ψ : ComplexModel n → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ (Ω : Set (ComplexModel n))) :
    Integrable (fun z => ψ z * f z) μ := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_compact_abs_bound hψc hψΩ
  obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ
  have hzero : ∀ z, z ∉ tsupport ψ → ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hmeas : Measurable fun z => ψ z * f z :=
    measurable_mul_of_plurisubharmonicOn hf.1 hψ hψΩ
  have hbdd : ∀ z, ‖ψ z * f z‖ ≤ B * C := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hB z) (hC z hz) (abs_nonneg _)
        ((norm_nonneg _).trans (hB z))
    · simp only [hzero z hz, zero_mul, norm_zero]
      exact mul_nonneg ((norm_nonneg _).trans (hB z)) hC0
  rw [← integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left _ _).trans (subset_tsupport ψ))]
  exact Measure.integrableOn_of_bounded (M := B * C) (hμ _ hψc hψΩ).ne
    hmeas.aestronglyMeasurable (Eventually.of_forall hbdd)

/-- Local boundedness and plurisubharmonicity on `Ω` only depend on the values on `Ω`. -/
theorem IsLocallyBoundedPshOn.congr_eqOn {Ω : Opens (ComplexModel n)}
    {f f' : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f) (h : EqOn f f' Ω) :
    IsLocallyBoundedPshOn Ω f' := by
  refine ⟨fun x hx => (hf.1 x hx).congr ?_, fun z hz => ?_⟩
  · filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    rw [h hy]
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    exact ⟨V, hzV, hVΩ, C, fun y hy => h (hVΩ hy) ▸ hC y hy⟩

/-- An increasing approximation is locally uniformly bounded. -/
theorem IsIncApprox.exists_abs_le {Ω : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Ω w) (hG : IsIncApprox Ω w G)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ M : ℝ, ∀ k, ∀ z ∈ K, |G k z| ≤ M := by
  obtain ⟨C₀, -, hC₀⟩ := (hG.1 0).exists_compact_abs_bound hK hKΩ
  obtain ⟨C₁, -, hC₁⟩ := hw.exists_compact_abs_bound hK hKΩ
  refine ⟨C₀ + C₁, fun k z hz => abs_le.2 ⟨?_, ?_⟩⟩
  · have h0 := hG.2.1 z (hKΩ hz) (Nat.zero_le k)
    have := abs_le.1 (hC₀ z hz)
    have := abs_le.1 (hC₁ z hz)
    linarith
  · have h1 := hG.2.2.1 k z (hKΩ hz)
    have := abs_le.1 (hC₀ z hz)
    have := abs_le.1 (hC₁ z hz)
    linarith

/-- An admissible increasing family is locally uniformly bounded. -/
theorem IsIncAdmissible.exists_abs_le {q : ℕ} {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hadm : IsIncAdmissible q Ω u F) {K : Set (ComplexModel n)} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) : ∃ M : ℝ, ∀ k i, ∀ z ∈ K, |F i k z| ≤ M := by
  choose M hM using fun i => IsIncApprox.exists_abs_le (hadm.1 i) (hadm.2.1 i) hK hKΩ
  refine ⟨∑ i, |M i|, fun k i z hz => (hM i k z hz).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- Step F along an admissible increasing family, given the unweighted claim. -/
theorem tendsto_integral_mul_of_isIncAdmissible (hF : FixedWeightConvergence n) {q : ℕ}
    (hP : IncPClaim n q) {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {F : Fin n → ℕ → ComplexModel n → ℝ} {μs : ℕ → Measure (ComplexModel n)}
    {μ : Measure (ComplexModel n)} (hadm : IsIncAdmissible q Ω u F)
    (hμs : ∀ k, IsBTLimit Ω (fun i => F i k) (μs k)) (hμ : IsBTLimit Ω u μ)
    {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f) {ψ : ComplexModel n → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ (Ω : Set (ComplexModel n))) :
    Tendsto (fun k => ∫ z, ψ z * f z ∂(μs k)) atTop (𝓝 (∫ z, ψ z * f z ∂μ)) :=
  hF Ω (fun k i => F i k) μs u μ (fun k i => (hadm.2.1 i).1 k) hμs hadm.1 hμ
    (fun _ hK hKΩ => hadm.exists_abs_le hK hKΩ) (hP Ω u F μs μ hadm hμs hμ) f hf ψ hψ hψc hψΩ

theorem integral_lincomb_mul {ν : Measure (ComplexModel n)} {ψ₁ ψ₂ f : ComplexModel n → ℝ}
    (a b : ℝ) (h₁ : Integrable (fun z => ψ₁ z * f z) ν)
    (h₂ : Integrable (fun z => ψ₂ z * f z) ν) :
    ∫ z, (a * ψ₁ z + b * ψ₂ z) * f z ∂ν =
      a * ∫ z, ψ₁ z * f z ∂ν + b * ∫ z, ψ₂ z * f z ∂ν := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h₁.const_mul a)
    (h₂.const_mul b)]
  congr 1
  funext z
  ring

private theorem exists_signed_cutoff_tests {Ω : Opens (ComplexModel n)}
    {η χ : ComplexModel n → ℝ}
    (hηc : Continuous η) (hηs : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hη0 : ∀ z, 0 ≤ η z) (hηone : ∀ z ∈ tsupport χ, η z = 1)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) :
    ∃ M : ℝ, (∀ s : ℝ, s = 1 ∨ s = -1 → ∀ z, 0 ≤ M * η z + s * χ z) ∧
      (∀ s : ℝ, Continuous (fun z => M * η z + s * χ z) ∧
        HasCompactSupport (fun z => M * η z + s * χ z) ∧
        tsupport (fun z => M * η z + s * χ z) ⊆ Ω) := by
  obtain ⟨M₀, hM₀⟩ := hχc.exists_bound_of_continuous hχ
  obtain ⟨M, hM0, hχM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, |χ z| ≤ M :=
    ⟨max M₀ 0, le_max_right _ _, fun z =>
      (by simpa [Real.norm_eq_abs] using hM₀ z : |χ z| ≤ M₀).trans (le_max_left _ _)⟩
  have hpos : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ z, 0 ≤ M * η z + s * χ z := by
    intro s hs z
    by_cases hz : z ∈ tsupport χ
    · rw [hηone z hz]
      have := abs_le.1 (hχM z)
      rcases hs with rfl | rfl <;> linarith
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, add_zero]
      exact mul_nonneg hM0 (hη0 z)
  have hsub : ∀ s : ℝ, tsupport (fun z => M * η z + s * χ z) ⊆
      tsupport η ∪ tsupport χ := fun s =>
    closure_minimal (fun z hz => by
      by_contra h
      simp only [mem_union, not_or] at h
      exact Function.mem_support.1 hz
        (by simp [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2]))
      ((isClosed_tsupport _).union (isClosed_tsupport _))
  have htest : ∀ s : ℝ, Continuous (fun z => M * η z + s * χ z) ∧
      HasCompactSupport (fun z => M * η z + s * χ z) ∧
      tsupport (fun z => M * η z + s * χ z) ⊆ (Ω : Set (ComplexModel n)) := fun s =>
    ⟨(continuous_const.mul hηc).add (continuous_const.mul hχ),
      (hηs.union hχc).of_isClosed_subset (isClosed_tsupport _) (hsub s),
      (hsub s).trans (union_subset hηΩ hχΩ)⟩
  exact ⟨M, hpos, htest⟩

/-- **Collared weighted step** of Cegrell's induction, assuming step F. -/
theorem incWCollarClaim_succ_of_fixedWeight (hF : FixedWeightConvergence n) {q : ℕ}
    (hq : q < n) (hP : IncPClaim n (q + 1)) (hW : IncWClaim n q) :
    IncWCollarClaim n (q + 1) := by
  intro z₀ R u F μs μ g K Ω hg hK hKΩ hadm hcol hμs hμ w G hw hG hwK hGK χ hχ hχc hχΩ
  classical
  set i₀ : Fin n := ⟨q, hq⟩ with hi₀
  have hgb : IsLocallyBoundedPshOn Ω g := hg.isLocallyBoundedPshOn
  -- the cutoff `η`, equal to one near `K ∪ supp χ`
  obtain ⟨η, hη1, hη01⟩ := exists_testFunction_eq_one_nhds_compact (Ω := Ω)
    (hK.union hχc) (union_subset hKΩ hχΩ)
  have hηc : Continuous (η : ComplexModel n → ℝ) := η.continuous
  have hηs : HasCompactSupport (η : ComplexModel n → ℝ) := η.hasCompactSupport
  have hηΩ : tsupport (η : ComplexModel n → ℝ) ⊆ Ω := η.tsupport_subset
  have hη0 : ∀ z, 0 ≤ η z := fun z => (hη01 z).1
  have hηone : ∀ z ∈ K ∪ tsupport χ, η z = 1 := fun z hz =>
    (hη1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  have hηzero : ∀ z, z ∉ (Ω : Set (ComplexModel n)) → η z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hηΩ h)
  have hint : ∀ {ν : Measure (ComplexModel n)}, (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) →
      ∀ {f : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω f → ∀ {ψ : ComplexModel n → ℝ},
      Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ (Ω : Set (ComplexModel n)) →
      Integrable (fun z => ψ z * f z) ν := fun hν _ hf _ hψ hψc hψΩ =>
    IsLocallyBoundedPshOn.integrable_mul_of_tsupport_subset hf hν hψ hψc hψΩ
  -- step F along the given family
  have hFμ : ∀ {f : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω f →
      ∀ {ψ : ComplexModel n → ℝ}, Continuous ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Ω : Set (ComplexModel n)) →
      Tendsto (fun j => ∫ z, ψ z * f z ∂(μs j)) atTop (𝓝 (∫ z, ψ z * f z ∂μ)) :=
    fun hf _ hψ hψc hψΩ =>
      tendsto_integral_mul_of_isIncAdmissible hF hP hadm hμs hμ hf hψ hψc hψΩ
  -- upper bound for nonnegative tests: `G_j ≤ w`
  have hUB : ∀ ψ : ComplexModel n → ℝ, Continuous ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Ω : Set (ComplexModel n)) → (∀ z, 0 ≤ ψ z) → ∀ b,
      (∫ z, ψ z * w z ∂μ) - ∫ z, ψ z * g z ∂μ < b →
      ∀ᶠ j in atTop, (∫ z, ψ z * G j z ∂(μs j)) - ∫ z, ψ z * g z ∂(μs j) < b := by
    intro ψ hψ hψc hψΩ hψ0 b hb
    have h1 := (hFμ hw hψ hψc hψΩ).sub (hFμ hgb hψ hψc hψΩ)
    filter_upwards [(tendsto_order.1 h1).2 b hb] with j hj
    have hle : ∫ z, ψ z * G j z ∂(μs j) ≤ ∫ z, ψ z * w z ∂(μs j) := by
      refine integral_mono (hint (hμs j).2.1 (hG.1 j) hψ hψc hψΩ)
        (hint (hμs j).2.1 hw hψ hψc hψΩ) fun z => ?_
      by_cases hz : z ∈ (Ω : Set (ComplexModel n))
      · exact mul_le_mul_of_nonneg_left (hG.2.2.1 j z hz) (hψ0 z)
      · simp [image_eq_zero_of_notMem_tsupport fun h => hz (hψΩ h)]
    linarith
  -- tuples with a function in slot `i₀`
  have hupd : ∀ {x y : ComplexModel n → ℝ}, EqOn x y Ω → ∀ i,
      EqOn (Function.update u i₀ x i) (Function.update u i₀ y i) Ω := by
    intro x y hxy i
    by_cases h : i = i₀
    · subst h; simpa using hxy
    · simp only [Function.update_of_ne h]; exact fun _ _ => rfl
  have hupdlb : ∀ {x : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω x → ∀ i,
      IsLocallyBoundedPshOn Ω (Function.update u i₀ x i) := by
    intro x hx i
    by_cases h : i = i₀
    · subst h; simpa using hx
    · simpa [Function.update_of_ne h] using hadm.1 i
  -- modification off `Ω`, so that the functions equal `g` off `K` everywhere
  have hpw : ∀ {x : ComplexModel n → ℝ}, (∀ z ∈ (Ω : Set (ComplexModel n)) \ K, x z = g z) →
      EqOn x (fun z => if z ∈ K then x z else g z) Ω ∧
      ∀ z, (if z ∈ K then x z else g z) - g z = η z * x z - η z * g z := by
    intro x hx
    refine ⟨fun z hz => ?_, fun z => ?_⟩
    · by_cases hzK : z ∈ K
      · simp [hzK]
      · simp [hzK, hx z ⟨hz, hzK⟩]
    · by_cases hzK : z ∈ K
      · simp [hzK, hηone z (Or.inl hzK)]
      · by_cases hz : z ∈ (Ω : Set (ComplexModel n))
        · simp [hzK, hx z ⟨hz, hzK⟩]
        · simp [hzK, hηzero z hz]
  -- step S in cutoff form
  have hS : ∀ {x₀ x₁ : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω x₀ →
      IsLocallyBoundedPshOn Ω x₁ → (∀ z ∈ (Ω : Set (ComplexModel n)) \ K, x₀ z = g z) →
      (∀ z ∈ (Ω : Set (ComplexModel n)) \ K, x₁ z = g z) →
      ∀ {μ₀ μ₁ μg : Measure (ComplexModel n)},
      IsBTLimit Ω (Function.update u i₀ x₀) μ₀ → IsBTLimit Ω (Function.update u i₀ x₁) μ₁ →
      IsBTLimit Ω (Function.update u i₀ g) μg →
      ((∫ z, η z * x₀ z ∂μ₁) - ∫ z, η z * g z ∂μ₁) -
          ((∫ z, η z * x₀ z ∂μg) - ∫ z, η z * g z ∂μg) =
        ((∫ z, η z * x₁ z ∂μ₀) - ∫ z, η z * g z ∂μ₀) -
          ((∫ z, η z * x₁ z ∂μg) - ∫ z, η z * g z ∂μg) := by
    intro x₀ x₁ hx₀ hx₁ hx₀K hx₁K μ₀ μ₁ μg h₀ h₁ hμg
    obtain ⟨e₀, p₀⟩ := hpw hx₀K
    obtain ⟨e₁, p₁⟩ := hpw hx₁K
    have key := integral_sub_eq_integral_sub_of_eqOn_compl (v := u) i₀
      (IsLocallyBoundedPshOn.congr_eqOn hx₀ e₀) (IsLocallyBoundedPshOn.congr_eqOn hx₁ e₁) hg
      hK hKΩ (fun z hz => ite_eq_right hz) (fun z hz => ite_eq_right hz)
      (h₀.congr (hupd e₀)) (h₁.congr (hupd e₁)) hμg
    simp only [p₀, p₁] at key
    have hsplit : ∀ {ν : Measure (ComplexModel n)}, (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) →
        ∀ {x : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω x →
        ∫ z, (η z * x z - η z * g z) ∂ν = (∫ z, η z * x z ∂ν) - ∫ z, η z * g z ∂ν :=
      fun hν _ hx => integral_sub (hint hν hx hηc hηs hηΩ) (hint hν hgb hηc hηs hηΩ)
    rw [hsplit h₁.2.1 hx₀, hsplit hμg.2.1 hx₀, hsplit h₀.2.1 hx₁, hsplit hμg.2.1 hx₁] at key
    exact key
  -- the auxiliary measures
  have hhuq : IsLocallyBoundedPshOn Ω (u i₀) := hadm.1 i₀
  have huqK : ∀ z ∈ (Ω : Set (ComplexModel n)) \ K, u i₀ z = g z :=
    (hcol i₀ (Nat.lt_succ_self q)).1
  obtain ⟨νg, hνg⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (hupdlb hgb)
  obtain ⟨νw, hνw⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (hupdlb hw)
  choose νG hνG using fun k => exists_isBTLimit_of_isLocallyBoundedPshOn (hupdlb (hG.1 k))
  have hμ' : IsBTLimit Ω (Function.update u i₀ (u i₀)) μ := by
    simpa only [Function.update_eq_self] using hμ
  -- `IncWClaim n q` for the tuple with `g` in slot `i₀`
  have hadmg : IsIncAdmissible q Ω (Function.update u i₀ g)
      fun i _ => Function.update u i₀ g i := by
    refine ⟨hupdlb hgb, fun i => isIncApprox_const (hupdlb hgb i),
      fun i hi => ⟨?_, fun _ => fun _ _ => rfl⟩⟩
    by_cases h : i = i₀
    · subst h; simpa using hg
    · have hi' : q + 1 ≤ i.val := by
        have : i.val ≠ q := fun e => h (Fin.ext e)
        omega
      simpa [Function.update_of_ne h] using (hadm.2.2 i hi').1
  have hT1 := hW Ω (Function.update u i₀ g) (fun i _ => Function.update u i₀ g i)
    (fun _ => νg) νg hadmg (fun _ => hνg) hνg w G hw hG η hηc hηs hηΩ
  -- `IncPClaim n (q + 1)` and step F along `ν(G_k) → ν(w)`
  have hadmw : IsIncAdmissible (q + 1) Ω (Function.update u i₀ w)
      (Function.update (fun i _ => u i) i₀ G) := by
    refine ⟨hupdlb hw, fun i => ?_, fun i hi => ?_⟩
    · by_cases h : i = i₀
      · subst h; simpa using hG
      · simpa [Function.update_of_ne h] using isIncApprox_const (hadm.1 i)
    · have h : i ≠ i₀ := fun e => by
        rw [e, hi₀] at hi
        simp at hi
      refine ⟨by simpa [Function.update_of_ne h] using (hadm.2.2 i hi).1, fun k => ?_⟩
      simp only [Function.update_of_ne h]
      exact fun _ _ => rfl
  have hνGbt : ∀ k, IsBTLimit Ω (fun i => Function.update (fun i _ => u i) i₀ G i k) (νG k) := by
    intro k
    rw [update_apply_seq_update]
    exact hνG k
  have hT2 : ∀ {f : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω f →
      Tendsto (fun k => ∫ z, η z * f z ∂(νG k)) atTop (𝓝 (∫ z, η z * f z ∂νw)) :=
    fun hf => tendsto_integral_mul_of_isIncAdmissible hF hP hadmw hνGbt hνw hf hηc hηs hηΩ
  -- the total integrals `∫ η (G_k - g) dμ` converge to `∫ η (w - g) dμ`
  have hE {f : ComplexModel n → ℝ} {ν : Measure (ComplexModel n)}
      (hf : IsLocallyBoundedPshOn Ω f) (hfK : ∀ z ∈ (Ω : Set (ComplexModel n)) \ K, f z = g z)
      (hν : IsBTLimit Ω (Function.update u i₀ f) ν) :
      (∫ z, η z * f z ∂μ) - ∫ z, η z * g z ∂μ =
        ((∫ z, η z * f z ∂νg) - ∫ z, η z * g z ∂νg) +
          ((∫ z, η z * u i₀ z ∂ν) - ∫ z, η z * g z ∂ν) -
          ((∫ z, η z * u i₀ z ∂νg) - ∫ z, η z * g z ∂νg) := by
    have := hS hf hhuq hfK huqK hν hμ' hνg
    linarith
  have hBCD : Tendsto (fun k => (∫ z, η z * G k z ∂μ) - ∫ z, η z * g z ∂μ) atTop
      (𝓝 ((∫ z, η z * w z ∂μ) - ∫ z, η z * g z ∂μ)) := by
    rw [hE hw hwK hνw]
    refine Tendsto.congr (fun k => (hE (hG.1 k) (hGK k) (hνG k)).symm) ?_
    exact ((hT1.sub tendsto_const_nhds).add ((hT2 hhuq).sub (hT2 hgb))).sub tendsto_const_nhds
  -- total mass from below: `G_k ≤ G_j` for `k ≤ j`
  have hLB : ∀ b, b < (∫ z, η z * w z ∂μ) - ∫ z, η z * g z ∂μ →
      ∀ᶠ j in atTop, b < (∫ z, η z * G j z ∂(μs j)) - ∫ z, η z * g z ∂(μs j) := by
    intro b hb
    obtain ⟨k, hk⟩ := ((tendsto_order.1 hBCD).1 b hb).exists
    have h1 := (hFμ (hG.1 k) hηc hηs hηΩ).sub (hFμ hgb hηc hηs hηΩ)
    filter_upwards [(tendsto_order.1 h1).1 b hk, eventually_ge_atTop k] with j hj hkj
    have hle : ∫ z, η z * G k z ∂(μs j) ≤ ∫ z, η z * G j z ∂(μs j) := by
      refine integral_mono (hint (hμs j).2.1 (hG.1 k) hηc hηs hηΩ)
        (hint (hμs j).2.1 (hG.1 j) hηc hηs hηΩ) fun z => ?_
      by_cases hz : z ∈ (Ω : Set (ComplexModel n))
      · exact mul_le_mul_of_nonneg_left (hG.2.1 z hz hkj) (hη0 z)
      · simp [hηzero z hz]
    linarith
  have hTη : Tendsto (fun j => (∫ z, η z * G j z ∂(μs j)) - ∫ z, η z * g z ∂(μs j)) atTop
      (𝓝 ((∫ z, η z * w z ∂μ) - ∫ z, η z * g z ∂μ)) :=
    tendsto_order.2 ⟨hLB, hUB η hηc hηs hηΩ hη0⟩
  -- localization with the tests `M η ± χ`
  obtain ⟨M, hpos, htest⟩ := exists_signed_cutoff_tests hηc hηs hηΩ hη0
    (fun z hz => hηone z (Or.inr hz)) hχ hχc hχΩ
  have hlin : ∀ {ν : Measure (ComplexModel n)}, (∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) →
      ∀ {f : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω f → ∀ s : ℝ,
      ∫ z, (M * η z + s * χ z) * f z ∂ν =
        M * ∫ z, η z * f z ∂ν + s * ∫ z, χ z * f z ∂ν :=
    fun hν _ hf s =>
      integral_lincomb_mul M s (hint hν hf hηc hηs hηΩ) (hint hν hf hχ hχc hχΩ)
  have hMη := hTη.const_mul M
  have hTχ : Tendsto (fun j => (∫ z, χ z * G j z ∂(μs j)) - ∫ z, χ z * g z ∂(μs j)) atTop
      (𝓝 ((∫ z, χ z * w z ∂μ) - ∫ z, χ z * g z ∂μ)) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨ε, hε, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧
          2 * ε = (∫ z, χ z * w z ∂μ) - (∫ z, χ z * g z ∂μ) - b :=
        ⟨((∫ z, χ z * w z ∂μ) - (∫ z, χ z * g z ∂μ) - b) / 2, by linarith, by ring⟩
      have hup := hUB _ (htest (-1)).1 (htest (-1)).2.1 (htest (-1)).2.2
        (hpos (-1) (Or.inr rfl))
        (((∫ z, (M * η z + -1 * χ z) * w z ∂μ) - ∫ z, (M * η z + -1 * χ z) * g z ∂μ) + ε)
        (by linarith)
      have hlow := (tendsto_order.1 hMη).1
        (M * ((∫ z, η z * w z ∂μ) - ∫ z, η z * g z ∂μ) - ε) (by linarith)
      filter_upwards [hup, hlow] with j h1 h2
      rw [hlin (hμs j).2.1 (hG.1 j), hlin (hμs j).2.1 hgb, hlin hμ.2.1 hw,
        hlin hμ.2.1 hgb] at h1
      linarith
    · obtain ⟨ε, hε, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧
          2 * ε = b - ((∫ z, χ z * w z ∂μ) - (∫ z, χ z * g z ∂μ)) :=
        ⟨(b - ((∫ z, χ z * w z ∂μ) - (∫ z, χ z * g z ∂μ))) / 2, by linarith, by ring⟩
      have hup := hUB _ (htest 1).1 (htest 1).2.1 (htest 1).2.2 (hpos 1 (Or.inl rfl))
        (((∫ z, (M * η z + 1 * χ z) * w z ∂μ) - ∫ z, (M * η z + 1 * χ z) * g z ∂μ) + ε)
        (by linarith)
      have hlow := (tendsto_order.1 hMη).1
        (M * ((∫ z, η z * w z ∂μ) - ∫ z, η z * g z ∂μ) - ε) (by linarith)
      filter_upwards [hup, hlow] with j h1 h2
      rw [hlin (hμs j).2.1 (hG.1 j), hlin (hμs j).2.1 hgb, hlin hμ.2.1 hw,
        hlin hμ.2.1 hgb] at h1
      linarith
  have hfin := hTχ.add (hFμ hgb hχ hχc hχΩ)
  simp only [sub_add_cancel] at hfin
  exact hfin

/-- **Collared weighted step** of Cegrell's induction (Błocki, Thm 2.2.5): the collared
weighted claim at level `q + 1` follows from the unweighted claim at level `q + 1` and the
weighted claim at level `q`. -/
theorem incWCollarClaim_succ {q : ℕ} (hq : q < n) (hP : IncPClaim n (q + 1))
    (hW : IncWClaim n q) : IncWCollarClaim n (q + 1) :=
  incWCollarClaim_succ_of_fixedWeight fixedWeightConvergence hq hP hW

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
