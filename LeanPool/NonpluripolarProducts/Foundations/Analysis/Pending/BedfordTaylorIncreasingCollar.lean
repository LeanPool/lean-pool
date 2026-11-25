/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingClaims
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorFixedWeight
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicAE

/-!
# Reduction of the increasing weighted convergence claim to collared data

In Cegrell's proof of the convergence of mixed Monge–Ampère measures along increasing
sequences (Błocki, *The complex Monge–Ampère operator in pluripotential theory*, lecture
notes, proofs of Theorems 2.1.5 and 2.2.5) one reduces to data which, on a ball, agree
near the boundary with a fixed smooth plurisubharmonic function `Aψ`,
`ψ(z) = ‖z - z₀‖² - (2R)²`. This file performs that reduction for the weighted claim:

  `IncPClaim n q ∧ IncWCollarClaim n q → IncWClaim n q`.

**Proof.** By a continuous partition of unity subordinate to finitely many balls
`B(z_b, R_b)` with `BBar(z_b, 2R_b) ⊆ Ω` covering `supp χ`, and linearity, it suffices to
treat `supp χ ⊆ B(z₀, R)`, `BBar(z₀, 2R) ⊆ Ω`. On `BBar(z₀, 2R)` all varying slots, their
limits, the weights and their limit are bounded by one constant `M` (increasing
sequences lie between their first term and their limit). Put `c = M + 1`, choose
`A > 0` with `Aψ < -(2M + 1)` on `B(z₀, R)` and `r < 2R` with `Aψ ≥ -1` for
`r < ‖z - z₀‖ < 2R`, and replace every varying slot and every weight `h` by
`hTilde = max(h - c, Aψ)` on `Ω' = B(z₀, 2R)`. Then `hTilde = Aψ` off `K = BBar(z₀, r)` and
`hTilde = h - c` on `B(z₀, R)`. The Bedford–Taylor measures of the modified tuples agree
with the original ones on `B(z₀, R)`: restrict to `Ω'`, subtract the constants (gauge
invariance) and use locality for a maximum with a smooth plurisubharmonic obstacle
(for the fixed smooth slots the obstacle `u_i - 1` is never attained). Hence
`∫ χ G_k dμ_k = ∫ χ GTilde_k dμTilde_k + c ∫ χ dμTilde_k`; the first term converges by the collared
claim and the second by the unweighted claim on `Ω'`.

We also record that an almost everywhere increasing limit dominates every term of a
monotone sequence of plurisubharmonic functions everywhere
(`isIncApprox_of_monotone_ae`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open MeasureLocality (integrable_of_tsupport_subset)

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- A pointwise increasing sequence of locally bounded plurisubharmonic functions
converging almost everywhere on `Ω` to a locally bounded plurisubharmonic `w` is an
increasing approximation of `w`: each term lies below `w` almost everywhere, hence
everywhere on `Ω` by the submean inequality and upper semicontinuity of `w`. -/
theorem isIncApprox_of_monotone_ae {Ω : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Ω w)
    (hG : ∀ k, IsLocallyBoundedPshOn Ω (G k)) (hmono : ∀ z ∈ Ω, Monotone fun k => G k z)
    (hae : ∀ᵐ z, z ∈ Ω → Tendsto (fun k => G k z) atTop (𝓝 (w z))) : IsIncApprox Ω w G := by
  refine ⟨hG, hmono, fun k z hz ↦ ?_, hae⟩
  have hle : ∀ᵐ y ∂(volume.restrict (Ω : Set (ComplexModel n))),
      ((G k y : ℝ) : EReal) ≤ ((w y : ℝ) : EReal) := by
    rw [ae_restrict_iff' Ω.isOpen.measurableSet]
    filter_upwards [hae] with y hy hyΩ
    exact EReal.coe_le_coe_iff.2 ((hmono y hyΩ).ge_of_tendsto (hy hyΩ) k)
  exact EReal.coe_le_coe_iff.1
    ((hG k).1.le_of_ae_le Ω.isOpen hw.1.upperSemicontinuousOn volume hle z hz)

section Collar

/-- `max(f - c, g)` of a locally bounded plurisubharmonic `f` and a smooth function `g`
with positive semidefinite complex Hessian is locally bounded plurisubharmonic. -/
theorem IsLocallyBoundedPshOn.max_sub_const_of_isSmoothPsdOn {Ω : Opens (ComplexModel n)}
    {f g : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f) (hg : IsSmoothPsdOn Ω g)
    (c : ℝ) : IsLocallyBoundedPshOn Ω fun z ↦ max (f z - c) (g z) := by
  have hc : PlurisubharmonicOn (fun _ : ComplexModel n ↦ ((-c : ℝ) : EReal)) Ω :=
    fun x _ ↦ plurisubharmonicAt_const _ (EReal.coe_ne_top _) x
  have hsub : PlurisubharmonicOn (fun z ↦ ((f z - c : ℝ) : EReal)) Ω := by
    have h := hf.1.add hc
    simpa only [sub_eq_add_neg, EReal.coe_add] using h
  have hg' := hg.isLocallyBoundedPshOn
  refine ⟨?_, fun z hz ↦ ?_⟩
  · have h := hsub.max hg'.1
    simpa only [EReal.coe_strictMono.monotone.map_max] using h
  · obtain ⟨V, hzV, hVΩ, C, hC⟩ := hf.2 z hz
    obtain ⟨V', hzV', -, C', hC'⟩ := hg'.2 z hz
    refine ⟨V ⊓ V', ⟨hzV, hzV'⟩, inf_le_left.trans hVΩ, C + |c| + C', fun y hy ↦ ?_⟩
    have h1 := hC y hy.1
    have h2 := hC' y hy.2
    refine (abs_max_le_max_abs_abs).trans (max_le ?_ ?_)
    · refine (abs_sub _ _).trans ?_
      linarith [abs_nonneg (g y)]
    · linarith [abs_nonneg (f y), abs_nonneg c]

/-- Restriction of an increasing approximation to a smaller open set. -/
theorem IsIncApprox.mono_opens {Ω V : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsIncApprox Ω w G) (hVΩ : V ≤ Ω) :
    IsIncApprox V w G :=
  ⟨fun k ↦ IsLocallyBoundedPshOn.mono_opens (hG.1 k) hVΩ, fun z hz ↦ hG.2.1 z (hVΩ hz),
    fun k z hz ↦ hG.2.2.1 k z (hVΩ hz), by
      filter_upwards [hG.2.2.2] with z hz hzV using hz (hVΩ hzV)⟩

/-- The collar modification `max(· - c, g)` of an increasing approximation. -/
theorem IsIncApprox.max_sub_const {Ω V : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsIncApprox Ω w G) (hVΩ : V ≤ Ω)
    {g : ComplexModel n → ℝ} (hg : IsSmoothPsdOn V g) (c : ℝ) :
    IsIncApprox V (fun z ↦ max (w z - c) (g z)) (fun k z ↦ max (G k z - c) (g z)) :=
  ⟨fun k ↦ IsLocallyBoundedPshOn.max_sub_const_of_isSmoothPsdOn
    (IsLocallyBoundedPshOn.mono_opens (hG.1 k) hVΩ) hg c,
    fun z hz _ _ hkl ↦ max_le_max (sub_le_sub_right (hG.2.1 z (hVΩ hz) hkl) c) le_rfl,
    fun k z hz ↦ max_le_max (sub_le_sub_right (hG.2.2.1 k z (hVΩ hz)) c) le_rfl, by
      filter_upwards [hG.2.2.2] with z hz hzV
      exact ((hz (hVΩ hzV)).sub_const c).max tendsto_const_nhds⟩

/-- **Locality for shifted maxima with smooth obstacles.** If `ν` is the Bedford–Taylor
limit on `V ⊆ Ω` of the tuple `max(u_i - s_i, φ_i)` with smooth plurisubharmonic
obstacles `φ_i`, then `ν = μ` on every subset of `V` where `φ_i < u_i - s_i` for all
`i`. -/
theorem IsBTLimit.restrict_eq_of_max_sub_const {Ω V : Opens (ComplexModel n)} (hVΩ : V ≤ Ω)
    {u w φ : Fin n → ComplexModel n → ℝ} {s : Fin n → ℝ} {μ ν : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω u μ) (hν : IsBTLimit V w ν) (hφ : ∀ i, IsSmoothPsdOn V (φ i))
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (u i z - s i) (φ i z)) V)
    {S : Set (ComplexModel n)} (hSV : S ⊆ V) (hS : ∀ z ∈ S, ∀ i, φ i z < u i z - s i) :
    ν.restrict S = μ.restrict S := by
  have hc (i : Fin n) : IsSmoothPluriharmonicOn V fun _ ↦ -s i :=
    ⟨contDiffOn_const, fun z _ ↦ by ext j k; simp [complexHessian]⟩
  have hμ' := (hμ.restrict_opens hVΩ).add_pluriharmonic hc
  have h := restrict_eq_of_max_obstacle (v := fun i z ↦ u i z + -s i) (w := w) hφ hμ'.2.1
    hν.2.1 hμ'.2.2 hν.2.2 fun i z hz ↦ by simp only [hmax i hz, sub_eq_add_neg]
  have hPS : S ⊆ {z | z ∈ V ∧ ∀ i, φ i z < u i z + -s i} := fun z hz ↦
    ⟨hSV hz, fun i ↦ by simpa only [sub_eq_add_neg] using hS z hz i⟩
  rw [← Measure.restrict_restrict_of_subset hPS, h, Measure.restrict_restrict_of_subset hPS,
    Measure.restrict_restrict_of_subset hSV]

/-- If `μ = ν` on a measurable `B ⊇ supp χ` and `f = f' + c` on `B`, then
`∫ χ f dμ = ∫ χ f' dν + c ∫ χ dν`. -/
theorem integral_mul_eq_add_of_restrict_eq {μ ν : Measure (ComplexModel n)}
    {B : Set (ComplexModel n)} (hB : MeasurableSet B) (hμν : μ.restrict B = ν.restrict B)
    {χ f f' : ComplexModel n → ℝ} (hχB : tsupport χ ⊆ B) {c : ℝ}
    (hff' : ∀ z ∈ B, f z = f' z + c) (hi : Integrable (fun z ↦ χ z * f' z) ν)
    (hχi : Integrable χ ν) :
    ∫ z, χ z * f z ∂μ = ∫ z, χ z * f' z ∂ν + c * ∫ z, χ z ∂ν := by
  have hzero (z : ComplexModel n) (hz : z ∉ B) : χ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (hχB h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) fun z hz ↦ by
      simp [hzero z hz], hμν,
    setIntegral_congr_fun hB (g := fun z ↦ χ z * f' z + c * χ z) fun z hz ↦ by
      simp only [hff' z hz]; ring,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by simp [hzero z hz],
    integral_add hi (hχi.const_mul c), integral_const_mul]

/-- A test function times a locally bounded plurisubharmonic function is integrable
against a measure finite on compact subsets of `Ω`. -/
theorem integrable_test_mul_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f) {ν : Measure (ComplexModel n)}
    (hν : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) {χ : ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ (Ω : Set (ComplexModel n))) :
    Integrable (fun z ↦ χ z * f z) ν := by
  obtain ⟨B, hB⟩ := IsLocallyBoundedPshOn.exists_abs_le hf hχc hχΩ
  exact integrable_mul_of_abs_le hχ hχc (hν _ hχc hχΩ)
    (measurable_mul_of_plurisubharmonicOn hf.1 hχ hχΩ) hB

/-- **The collar reduction on one ball.** The weighted claim holds for tests supported in
`B(z₀, R)` when `BBar(z₀, 2R) ⊆ Ω`. -/
theorem tendsto_integral_mul_of_tsupport_subset_ball {q : ℕ} (hP : IncPClaim n q)
    (hC : IncWCollarClaim n q) {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {F : Fin n → ℕ → ComplexModel n → ℝ} {μs : ℕ → Measure (ComplexModel n)}
    {μ : Measure (ComplexModel n)} (hadm : IsIncAdmissible q Ω u F)
    (hμs : ∀ k, IsBTLimit Ω (fun i ↦ F i k) (μs k)) (hμ : IsBTLimit Ω u μ)
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn Ω w)
    (hG : IsIncApprox Ω w G) {z₀ : ComplexModel n} {R : ℝ} (hR : 0 < R)
    (hball : closedBall z₀ (2 * R) ⊆ (Ω : Set (ComplexModel n))) {χ : ComplexModel n → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχB : tsupport χ ⊆ ball z₀ R) :
    Tendsto (fun k ↦ ∫ z, χ z * G k z ∂(μs k)) atTop (𝓝 (∫ z, χ z * w z ∂μ)) := by
  classical
  set K₀ := closedBall z₀ (2 * R) with hK₀_def
  have hK₀ : IsCompact K₀ := isCompact_closedBall _ _
  -- one bound for all slots and weights on `K₀`
  obtain ⟨M, hM0, hMu, hMF, hMw, hMG⟩ : ∃ M : ℝ, 0 ≤ M ∧ (∀ i, ∀ z ∈ K₀, |u i z| ≤ M) ∧
      (∀ i, ∀ z ∈ K₀, |F i 0 z| ≤ M) ∧ (∀ z ∈ K₀, |w z| ≤ M) ∧ ∀ z ∈ K₀, |G 0 z| ≤ M := by
    choose Cu hCu using fun i ↦ IsLocallyBoundedPshOn.exists_abs_le (hadm.1 i) hK₀ hball
    choose CF hCF using fun i ↦
      IsLocallyBoundedPshOn.exists_abs_le ((hadm.2.1 i).1 0) hK₀ hball
    obtain ⟨Cw, hCw⟩ := IsLocallyBoundedPshOn.exists_abs_le hw hK₀ hball
    obtain ⟨CG, hCG⟩ := IsLocallyBoundedPshOn.exists_abs_le (hG.1 0) hK₀ hball
    have hsum (i : Fin n) : |Cu i| + |CF i| ≤ ∑ j, (|Cu j| + |CF j|) :=
      Finset.single_le_sum (f := fun j ↦ |Cu j| + |CF j|) (fun j _ ↦ by positivity)
        (Finset.mem_univ i)
    have hS0 : 0 ≤ ∑ j, (|Cu j| + |CF j|) := Finset.sum_nonneg fun j _ ↦ by positivity
    refine ⟨∑ j, (|Cu j| + |CF j|) + |Cw| + |CG|, by positivity, fun i z hz ↦ ?_,
      fun i z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
    · linarith [hCu i z hz, le_abs_self (Cu i), hsum i, abs_nonneg (CF i), abs_nonneg Cw,
        abs_nonneg CG]
    · linarith [hCF i z hz, le_abs_self (CF i), hsum i, abs_nonneg (Cu i), abs_nonneg Cw,
        abs_nonneg CG]
    · linarith [hCw z hz, le_abs_self Cw, abs_nonneg CG]
    · linarith [hCG z hz, le_abs_self CG, abs_nonneg Cw]
  have hFlow (i : Fin n) (k : ℕ) (z : ComplexModel n) (hz : z ∈ K₀) : -M ≤ F i k z :=
    (abs_le.1 (hMF i z hz)).1.trans ((hadm.2.1 i).2.1 z (hball hz) (Nat.zero_le k))
  have hFup (i : Fin n) (k : ℕ) (z : ComplexModel n) (hz : z ∈ K₀) : F i k z ≤ M :=
    ((hadm.2.1 i).2.2.1 k z (hball hz)).trans (abs_le.1 (hMu i z hz)).2
  have hulow (i : Fin n) (z : ComplexModel n) (hz : z ∈ K₀) : -M ≤ u i z :=
    (hFlow i 0 z hz).trans ((hadm.2.1 i).2.2.1 0 z (hball hz))
  have hGlow (k : ℕ) (z : ComplexModel n) (hz : z ∈ K₀) : -M ≤ G k z :=
    (abs_le.1 (hMG z hz)).1.trans (hG.2.1 z (hball hz) (Nat.zero_le k))
  have hGup (k : ℕ) (z : ComplexModel n) (hz : z ∈ K₀) : G k z ≤ M :=
    (hG.2.2.1 k z (hball hz)).trans (abs_le.1 (hMw z hz)).2
  -- the collar potential
  set c : ℝ := M + 1 with hc_def
  set A : ℝ := (2 * M + 1) / (3 * R ^ 2) with hA_def
  have hA : 0 < A := by positivity
  set δ : ℝ := min R (1 / (4 * R * A)) with hδ_def
  have hδ : 0 < δ := lt_min hR (by positivity)
  set r : ℝ := 2 * R - δ with hr_def
  have hr : r < 2 * R := by linarith
  set g : ComplexModel n → ℝ := collar z₀ A (2 * R) with hg_def
  set Ω' : Opens (ComplexModel n) := ⟨ball z₀ (2 * R), isOpen_ball⟩ with hΩ'_def
  set K : Set (ComplexModel n) := closedBall z₀ r with hK_def
  have hΩ'Ω : Ω' ≤ Ω := fun z hz ↦ hball (ball_subset_closedBall hz)
  have hΩ'K₀ : ∀ z ∈ (Ω' : Set (ComplexModel n)), z ∈ K₀ := fun z hz ↦ ball_subset_closedBall hz
  have hBΩ' : ball z₀ R ⊆ (Ω' : Set (ComplexModel n)) := ball_subset_ball (by linarith)
  have hBK₀ : ∀ z ∈ ball z₀ R, z ∈ K₀ := fun z hz ↦ hΩ'K₀ z (hBΩ' hz)
  have hKΩ' : K ⊆ (Ω' : Set (ComplexModel n)) := closedBall_subset_ball hr
  have hgpsd : IsSmoothPsdOn Ω' g := isSmoothPsdOn_collar Ω' z₀ hA.le (2 * R)
  have hg_lt : ∀ z ∈ ball z₀ R, g z < -(2 * M + 1) := by
    intro z hz
    have ht : ‖z - z₀‖ < R := mem_ball_iff_norm.1 hz
    have ht2 : ‖z - z₀‖ ^ 2 < R ^ 2 := pow_lt_pow_left₀ ht (norm_nonneg _) two_ne_zero
    have hAR : A * (3 * R ^ 2) = 2 * M + 1 := by
      rw [hA_def]; field_simp
    simp only [hg_def, SmoothMax.quadraticCollar]
    nlinarith
  have hg_ge : ∀ z ∈ (Ω' : Set (ComplexModel n)) \ K, -1 ≤ g z := by
    rintro z ⟨hz1, hz2⟩
    have ht1 : ‖z - z₀‖ < 2 * R := mem_ball_iff_norm.1 hz1
    have ht2 : r < ‖z - z₀‖ := by
      simpa [hK_def, mem_closedBall, dist_eq_norm, not_le] using hz2
    have hδ1 : δ ≤ 1 / (4 * R * A) := min_le_right _ _
    have hδA : 4 * R * A * δ ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hδ1; linarith
    have ht0 : 0 ≤ ‖z - z₀‖ := norm_nonneg _
    simp only [hg_def, SmoothMax.quadraticCollar]
    have h1 : 0 ≤ 2 * R - ‖z - z₀‖ := by linarith
    have h2 : 2 * R - ‖z - z₀‖ ≤ δ := by linarith
    have h3 : 2 * R + ‖z - z₀‖ ≤ 4 * R := by linarith
    have h4 : (2 * R - ‖z - z₀‖) * (2 * R + ‖z - z₀‖) ≤ δ * (4 * R) :=
      mul_le_mul h2 h3 (by linarith) hδ.le
    nlinarith
  -- modified data
  set ut : Fin n → ComplexModel n → ℝ :=
    fun i ↦ if i.val < q then fun z ↦ max (u i z - c) (g z) else u i with hut_def
  set Ft : Fin n → ℕ → ComplexModel n → ℝ :=
    fun i k ↦ if i.val < q then fun z ↦ max (F i k z - c) (g z) else F i k with hFt_def
  have hadm' : IsIncAdmissible q Ω' ut Ft := by
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i hi ↦ ?_⟩
    · by_cases hi : i.val < q
      · simp only [hut_def, ite_eq_left hi]
        exact IsLocallyBoundedPshOn.max_sub_const_of_isSmoothPsdOn
          (IsLocallyBoundedPshOn.mono_opens (hadm.1 i) hΩ'Ω) hgpsd c
      · simp only [hut_def, ite_eq_right hi]
        exact IsLocallyBoundedPshOn.mono_opens (hadm.1 i) hΩ'Ω
    · by_cases hi : i.val < q
      · simp only [hut_def, hFt_def, ite_eq_left hi]
        exact (hadm.2.1 i).max_sub_const hΩ'Ω hgpsd c
      · simp only [hut_def, hFt_def, ite_eq_right hi]
        exact (hadm.2.1 i).mono_opens hΩ'Ω
    · have hi' : ¬ i.val < q := not_lt.2 hi
      simp only [hut_def, hFt_def, ite_eq_right hi']
      exact ⟨(hadm.2.2 i hi).1.mono hΩ'Ω, fun k z hz ↦ (hadm.2.2 i hi).2 k (hΩ'Ω hz)⟩
  choose μts hμts using fun k ↦ exists_isBTLimit_of_isLocallyBoundedPshOn (Ω := Ω')
    (u := fun i ↦ Ft i k) fun i ↦ (hadm'.2.1 i).1 k
  obtain ⟨μt, hμt⟩ := exists_isBTLimit_of_isLocallyBoundedPshOn (Ω := Ω') hadm'.1
  have hw' : IsLocallyBoundedPshOn Ω' fun z ↦ max (w z - c) (g z) :=
    IsLocallyBoundedPshOn.max_sub_const_of_isSmoothPsdOn
      (IsLocallyBoundedPshOn.mono_opens hw hΩ'Ω) hgpsd c
  have hG' := hG.max_sub_const hΩ'Ω hgpsd c
  have hslot : ∀ i : Fin n, i.val < q →
      (∀ z ∈ (Ω' : Set (ComplexModel n)) \ K, ut i z = g z) ∧
        ∀ k, ∀ z ∈ (Ω' : Set (ComplexModel n)) \ K, Ft i k z = g z := by
    intro i hi
    refine ⟨fun z hz ↦ ?_, fun k z hz ↦ ?_⟩
    · simp only [hut_def, ite_eq_left hi]
      exact max_eq_right (by
        linarith [(abs_le.1 (hMu i z (hΩ'K₀ z hz.1))).2, hg_ge z hz])
    · simp only [hFt_def, ite_eq_left hi]
      exact max_eq_right (by linarith [hFup i k z (hΩ'K₀ z hz.1), hg_ge z hz])
  have hwcol : ∀ z ∈ (Ω' : Set (ComplexModel n)) \ K, max (w z - c) (g z) = g z :=
    fun z hz ↦ max_eq_right (by linarith [(abs_le.1 (hMw z (hΩ'K₀ z hz.1))).2, hg_ge z hz])
  have hGcol : ∀ k, ∀ z ∈ (Ω' : Set (ComplexModel n)) \ K, max (G k z - c) (g z) = g z :=
    fun k z hz ↦ max_eq_right (by linarith [hGup k z (hΩ'K₀ z hz.1), hg_ge z hz])
  have hχΩ' : tsupport χ ⊆ (Ω' : Set (ComplexModel n)) := hχB.trans hBΩ'
  have hCol := hC z₀ (2 * R) ut Ft μts μt g K hgpsd (isCompact_closedBall _ _) hKΩ' hadm' hslot
    hμts hμt _ _ hw' hG' hwcol hGcol χ hχ hχc hχΩ'
  have hPt := hP Ω' ut Ft μts μt hadm' hμts hμt χ hχ hχc hχΩ'
  -- the measures agree on `B(z₀, R)`
  set φ : Fin n → ComplexModel n → ℝ :=
    fun i ↦ if i.val < q then g else fun z ↦ u i z - 1 with hφ_def
  set s : Fin n → ℝ := fun i ↦ if i.val < q then c else 0 with hs_def
  have hφ : ∀ i, IsSmoothPsdOn Ω' (φ i) := by
    intro i
    by_cases hi : i.val < q
    · simp only [hφ_def, ite_eq_left hi]; exact hgpsd
    · simp only [hφ_def, ite_eq_right hi]
      have hsm := (hadm.2.2 i (not_lt.1 hi)).1
      exact ⟨(hsm.1.sub contDiffOn_const).mono hΩ'Ω, fun z hz ↦ by
        rw [complexHessian_sub_const]; exact hsm.2 z (hΩ'Ω hz)⟩
  have key : ∀ (v : Fin n → ComplexModel n → ℝ) (ν νt : Measure (ComplexModel n)),
      IsBTLimit Ω v ν →
      IsBTLimit Ω' (fun i ↦ if i.val < q then fun z ↦ max (v i z - c) (g z) else v i) νt →
      (∀ i : Fin n, i.val < q → ∀ z ∈ K₀, -M ≤ v i z) →
      (∀ i : Fin n, q ≤ i.val → EqOn (v i) (u i) Ω) →
      νt.restrict (ball z₀ R) = ν.restrict (ball z₀ R) := by
    intro v ν νt hν hνt hvlow hveq
    refine IsBTLimit.restrict_eq_of_max_sub_const hΩ'Ω (φ := φ) (s := s) hν hνt hφ
      (fun i z hz ↦ ?_) hBΩ' fun z hz i ↦ ?_
    · by_cases hi : i.val < q
      · simp only [hφ_def, hs_def, ite_eq_left hi]
      · simp only [hφ_def, hs_def, ite_eq_right hi, sub_zero]
        rw [hveq i (not_lt.1 hi) (hΩ'Ω hz)]
        exact (max_eq_left (by linarith)).symm
    · by_cases hi : i.val < q
      · simp only [hφ_def, hs_def, ite_eq_left hi]
        linarith [hg_lt z hz, hvlow i hi z (hBK₀ z hz)]
      · simp only [hφ_def, hs_def, ite_eq_right hi, sub_zero]
        rw [hveq i (not_lt.1 hi) (hΩ'Ω (hBΩ' hz))]
        linarith
  have hGeq (k : ℕ) : ∀ z ∈ ball z₀ R, G k z = max (G k z - c) (g z) + c := fun z hz ↦ by
    rw [max_eq_left (by linarith [hg_lt z hz, hGlow k z (hBK₀ z hz)])]; ring
  have hweq : ∀ z ∈ ball z₀ R, w z = max (w z - c) (g z) + c := fun z hz ↦ by
    rw [max_eq_left (by linarith [hg_lt z hz, (abs_le.1 (hMw z (hBK₀ z hz))).1])]; ring
  have ek (k : ℕ) : ∫ z, χ z * G k z ∂(μs k) =
      ∫ z, χ z * max (G k z - c) (g z) ∂(μts k) + c * ∫ z, χ z ∂(μts k) :=
    integral_mul_eq_add_of_restrict_eq measurableSet_ball
      (key (fun i ↦ F i k) (μs k) (μts k) (hμs k) (hμts k) (fun i _ z hz ↦ hFlow i k z hz)
        (fun i hi ↦ (hadm.2.2 i hi).2 k)).symm hχB (hGeq k)
      (integrable_test_mul_of_isLocallyBoundedPshOn (hG'.1 k) (hμts k).2.1 hχ hχc hχΩ')
      (integrable_of_tsupport_subset (hμts k).2.1 hχ hχc hχΩ')
  have e : ∫ z, χ z * w z ∂μ =
      ∫ z, χ z * max (w z - c) (g z) ∂μt + c * ∫ z, χ z ∂μt :=
    integral_mul_eq_add_of_restrict_eq measurableSet_ball
      (key u μ μt hμ hμt (fun i _ z hz ↦ hulow i z hz) (fun _ _ _ _ ↦ rfl)).symm hχB hweq
      (integrable_test_mul_of_isLocallyBoundedPshOn hw' hμt.2.1 hχ hχc hχΩ')
      (integrable_of_tsupport_subset hμt.2.1 hχ hχc hχΩ')
  rw [e]
  exact (hCol.add (hPt.const_mul c)).congr fun k ↦ (ek k).symm

/-- **Reduction to collared data** (Błocki, proof of Theorem 2.2.5): the unweighted claim
and the collared weighted claim at level `q` give the weighted claim at level `q`. -/
theorem incWClaim_of_collar {q : ℕ} (hP : IncPClaim n q) (hC : IncWCollarClaim n q) :
    IncWClaim n q := by
  classical
  intro Ω u F μs μ hadm hμs hμ w G hw hG χ hχ hχc hχΩ
  have hR : ∀ z ∈ (Ω : Set (ComplexModel n)), ∃ R > 0, closedBall z (2 * R) ⊆ Ω := by
    intro z hz
    obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 Ω.isOpen z hz
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hεb⟩
  choose! R hRpos hRball using hR
  obtain ⟨t, htK, hcover⟩ := hχc.isCompact.elim_nhds_subcover (fun z ↦ ball z (R z))
    fun z hz ↦ ball_mem_nhds z (hRpos z (hχΩ hz))
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (isClosed_tsupport χ)
    (fun i : t ↦ ball (i : ComplexModel n) (R i)) (fun _ ↦ isOpen_ball) fun z hz ↦ by
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hcover hz)
      exact mem_iUnion.2 ⟨⟨x, hx⟩, hzx⟩
  have hsum (z : ComplexModel n) : χ z = ∑ i : t, ρ i z * χ z := by
    by_cases hz : z ∈ tsupport χ
    · rw [← Finset.sum_mul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one hz, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hcont (i : t) : Continuous fun z ↦ ρ i z * χ z := (ρ i).continuous.mul hχ
  have hcpt (i : t) : HasCompactSupport fun z ↦ ρ i z * χ z := hχc.mul_left
  have hsuppB (i : t) : tsupport (fun z ↦ ρ i z * χ z) ⊆ ball (i : ComplexModel n) (R i) :=
    (tsupport_mul_subset_left).trans (hρ i)
  have hsuppΩ (i : t) : tsupport (fun z ↦ ρ i z * χ z) ⊆ (Ω : Set (ComplexModel n)) :=
    (tsupport_mul_subset_right).trans hχΩ
  have hloc (i : t) := tendsto_integral_mul_of_tsupport_subset_ball hP hC hadm hμs hμ hw hG
    (hRpos i (hχΩ (htK i i.2))) (hRball i (hχΩ (htK i i.2))) (hcont i) (hcpt i) (hsuppB i)
  have hsplit (ν : Measure (ComplexModel n)) (f : ComplexModel n → ℝ)
      (hf : IsLocallyBoundedPshOn Ω f) (hν : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) :
      ∫ z, χ z * f z ∂ν = ∑ i : t, ∫ z, ρ i z * χ z * f z ∂ν := by
    rw [← integral_finsetSum _ fun i _ ↦
      integrable_test_mul_of_isLocallyBoundedPshOn hf hν (hcont i) (hcpt i) (hsuppΩ i)]
    congr 1
    funext z
    rw [← Finset.sum_mul, ← hsum z]
  rw [hsplit μ w hw hμ.2.1]
  refine (tendsto_finsetSum Finset.univ fun i _ ↦ hloc i).congr fun k ↦ ?_
  rw [hsplit (μs k) (G k) (hG.1 k) (hμs k).2.1]

end Collar

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
