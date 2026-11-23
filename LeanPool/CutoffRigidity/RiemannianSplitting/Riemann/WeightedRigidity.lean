/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedPointwise
import LeanPool.CutoffRigidity.L2FatouBounds

/-! # Hessian rigidity of eigenfunctions with eigenvalue `ρ` under `CD(ρ,∞)`

The analytic core of Lemma `lem_rig` (cutcur-lean.tex, line ~1365), under the three geometric
inputs `WeightedIBP`, `WeightedBochnerIneq`, `WeightedCutoffs` (and `WeightedRegular`).
-/

@[expose] public section

open Bundle MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

section Rigidity

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_const (c : ℝ) (x : M) : mgrad F (fun _ : M => c) x = 0 :=
  congrFun (TauCeti.Manifold.mgradient_const (I := 𝓘(ℝ, F)) (M := M) c) x

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_const_mul {f : M → ℝ} (c : ℝ) (hf : MSmooth F f) (x : M) :
    mgrad F (fun y => c * f y) x = c • mgrad F f x := by
  have := mgrad_mul F (f := fun _ : M => c) (g := f) contMDiff_const hf x
  have e : (fun y => c * f y) = (fun _ : M => c) * f := by funext y; simp
  rw [e, this, mgrad_const]; simp

/-- For an eigenfunction, `Γ₂(f) = ½ 𝓛Γ(f) + λ Γ(f)`. -/
theorem carre2_eigen {V f : M → ℝ} {lam : ℝ} (hf : MSmooth F f)
    (hL : ∀ x, mgenerator F V f x = -lam * f x) (x : M) :
    carre2 F V f x = mgenerator F V (carre F f f) x / 2 + lam * carre F f f x := by
  have h : mgenerator F V f = fun y => -lam * f y := funext hL
  have h2 : carre F f (mgenerator F V f) x = -lam * carre F f f x := by
    rw [h]
    simp only [carre, mgrad_const_mul F _ hf, real_inner_smul_right]
  rw [carre2, h2]; ring

/-- For an eigenfunction with eigenvalue `ρ` under the Bochner inequality,
`‖Hess f‖² ≤ ½ 𝓛Γ(f)`. -/
theorem hess_le_half_generator {V f : M → ℝ} {ρ : ℝ} (hB : WeightedBochnerIneq F V ρ)
    (hf : MSmooth F f) (hL : ∀ x, mgenerator F V f x = -ρ * f x) (x : M) :
    mHessNormSq F f x ≤ mgenerator F V (carre F f f) x / 2 := by
  have h1 := hB f hf x
  rw [carre2_eigen F hf hL x] at h1
  linarith

variable [MeasurableSpace M] [BorelSpace M]

/-- Integrability of a continuous compactly supported function w.r.t. a finite measure. -/
theorem integrable_of_cont_cs {μ : Measure M} [IsFiniteMeasure μ] {g : M → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) : Integrable g μ :=
  hg.integrable_of_hasCompactSupport hc

omit [MeasurableSpace M] [BorelSpace M] in
theorem hcs_of_zero {g χ : M → ℝ} (hχ : HasCompactSupport χ) (h : ∀ x, χ x = 0 → g x = 0) :
    HasCompactSupport g :=
  hχ.mono' (fun x hx => subset_tsupport _ (fun h0 => hx (h x h0)))

/-- Caccioppoli inequality for an eigenfunction. -/
theorem caccioppoli {μ : Measure M} [IsFiniteMeasure μ] {V f χ : M → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V)
    (hf : MSmooth F f) (hfL2 : Integrable (fun x => f x ^ 2) μ)
    (hL : ∀ x, mgenerator F V f x = -ρ * f x)
    (hχ : MSmooth F χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχg : ∀ x, ‖mgrad F χ x‖ ≤ 1) :
    ∫ x, χ x ^ 2 * carre F f f x ∂μ ≤ 2 * (ρ + 2) * ∫ x, f x ^ 2 ∂μ := by
  have hG : MSmooth F (carre F f f) := hReg.1 f f hf hf
  have hχχ : MSmooth F (χ * χ) := hχ.mul hχ
  have hu : MSmooth F ((χ * χ) * f) := hχχ.mul hf
  have huc : HasCompactSupport ((χ * χ) * f) := (hχc.mul_right.mul_right)
  have hibp := hIBP ((χ * χ) * f) f hu hf huc
  have hpt : ∀ x, carre F ((χ * χ) * f) f x =
      χ x ^ 2 * carre F f f x + 2 * (f x * (χ x * carre F χ f x)) := by
    intro x
    rw [carre_mul_left F hχχ hf x, carre_mul_left F hχ hχ x]
    simp only [Pi.mul_apply]; ring
  have hrhs : -∫ x, ((χ * χ) * f) x * mgenerator F V f x ∂μ =
      ρ * ∫ x, χ x ^ 2 * f x ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, hL x]; ring
  have hint_uf : Integrable (fun x => carre F ((χ * χ) * f) f x) μ :=
    integrable_of_cont_cs (hReg.1 _ _ hu hf).continuous (hasCompactSupport_carre F f huc)
  have hint_G : Integrable (fun x => χ x ^ 2 * carre F f f x) μ := by
    refine integrable_of_cont_cs ((hχ.continuous.pow 2).mul hG.continuous) ?_
    exact hcs_of_zero hχc (fun x hx => by simp [hx])
  have hint_f2 : Integrable (fun x => χ x ^ 2 * f x ^ 2) μ := by
    refine hfL2.mono' ((hχ.continuous.pow 2).mul (hf.continuous.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨h0, h1⟩ := hχ01 x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : χ x ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (f x)]
  have hpw : ∀ x, χ x ^ 2 * carre F f f x / 2 ≤ carre F ((χ * χ) * f) f x + 2 * f x ^ 2 := by
    intro x
    rw [hpt x]
    obtain ⟨h0, h1⟩ := hχ01 x
    set s := Real.sqrt (carre F f f x) with hs
    have hs2 : s ^ 2 = carre F f f x := Real.sq_sqrt (carre_nonneg F f x)
    have hgs : ‖mgrad F f x‖ = s := by
      rw [hs, carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
    have hc : |carre F χ f x| ≤ s := by
      refine (abs_carre_le F χ f x).trans ?_
      rw [hgs]
      calc ‖mgrad F χ x‖ * s ≤ 1 * s := by gcongr; exact hχg x
        _ = s := one_mul s
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have habs : |f x * (χ x * carre F χ f x)| ≤ |f x| * (χ x * s) := by
      rw [abs_mul, abs_mul, abs_of_nonneg h0]
      gcongr
    have hlow := neg_abs_le (f x * (χ x * carre F χ f x))
    rw [← hs2]
    nlinarith [sq_nonneg (χ x * s - 2 * |f x|), sq_abs (f x)]
  have h1 : ∫ x, χ x ^ 2 * carre F f f x / 2 ∂μ ≤
      ∫ x, (carre F ((χ * χ) * f) f x + 2 * f x ^ 2) ∂μ :=
    integral_mono (hint_G.div_const 2) (hint_uf.add (hfL2.const_mul 2)) hpw
  have h2 : ∫ x, (carre F ((χ * χ) * f) f x + 2 * f x ^ 2) ∂μ =
      ∫ x, carre F ((χ * χ) * f) f x ∂μ + 2 * ∫ x, f x ^ 2 ∂μ := by
    rw [integral_add hint_uf (hfL2.const_mul 2), integral_const_mul]
  have h3 : ∫ x, χ x ^ 2 * f x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
    refine integral_mono hint_f2 hfL2 fun x => ?_
    obtain ⟨h0, h1⟩ := hχ01 x
    have : χ x ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (f x)]
  have h4 : ∫ x, χ x ^ 2 * carre F f f x / 2 ∂μ = (∫ x, χ x ^ 2 * carre F f f x ∂μ) / 2 := by
    rw [integral_div]
  rw [h4, h2, hibp, hrhs] at h1
  nlinarith [mul_le_mul_of_nonneg_left h3 hρ]

/-- Cutoff estimate for the Hessian: `∫ χ² ‖Hess f‖² ≤ 4 ε² ∫ Γ(f)` if `‖∇χ‖ ≤ ε`. -/
theorem hess_cutoff_bound {μ : Measure M} [IsFiniteMeasure μ] {V f χ : M → ℝ} {ρ ε : ℝ}
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hB : WeightedBochnerIneq F V ρ)
    (hf : MSmooth F f) (hL : ∀ x, mgenerator F V f x = -ρ * f x)
    (hχ : MSmooth F χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (_hε0 : 0 ≤ ε) (hε : ∀ x, ‖mgrad F χ x‖ ≤ ε) (hGint : Integrable (fun x => carre F f f x) μ) :
    ∫ x, χ x ^ 2 * mHessNormSq F f x ∂μ ≤ 4 * ε ^ 2 * ∫ x, carre F f f x ∂μ := by
  have hw : MSmooth F (carre F f f) := hReg.1 f f hf hf
  have hχχ : MSmooth F (χ * χ) := hχ.mul hχ
  have hχχc : HasCompactSupport (χ * χ) := hχc.mul_right
  have hibp := hIBP (χ * χ) (carre F f f) hχχ hw hχχc
  have hint_H : Integrable (fun x => χ x ^ 2 * mHessNormSq F f x) μ := by
    refine integrable_of_cont_cs ((hχ.continuous.pow 2).mul (hReg.2.2 f hf)) ?_
    exact hcs_of_zero hχc (fun x hx => by simp [hx])
  have hLw : MSmooth F (mgenerator F V (carre F f f)) := hReg.2.1 _ hw
  have hint_Lw : Integrable (fun x => (χ * χ) x * mgenerator F V (carre F f f) x) μ := by
    refine integrable_of_cont_cs (hχχ.continuous.mul hLw.continuous) ?_
    exact hcs_of_zero hχc (fun x hx => by simp [hx])
  have hint_cw : Integrable (fun x => carre F (χ * χ) (carre F f f) x) μ :=
    integrable_of_cont_cs (hReg.1 _ _ hχχ hw).continuous (hasCompactSupport_carre F _ hχχc)
  have hp1 : ∀ x, 2 * (χ x ^ 2 * mHessNormSq F f x) ≤
      (χ * χ) x * mgenerator F V (carre F f f) x := by
    intro x
    have := hess_le_half_generator F hB hf hL x
    simp only [Pi.mul_apply]
    nlinarith [sq_nonneg (χ x)]
  have hp2 : ∀ x, -carre F (χ * χ) (carre F f f) x ≤
      χ x ^ 2 * mHessNormSq F f x + 4 * ε ^ 2 * carre F f f x := by
    intro x
    obtain ⟨h0, h1⟩ := hχ01 x
    rw [carre_mul_left F hχ hχ x]
    set a := Real.sqrt (mHessNormSq F f x) with ha
    set s := Real.sqrt (carre F f f x) with hs
    have ha2 : a ^ 2 = mHessNormSq F f x := Real.sq_sqrt (mHessNormSq_nonneg F f x)
    have hs2 : s ^ 2 = carre F f f x := Real.sq_sqrt (carre_nonneg F f x)
    have hc := abs_carre_carre_le F hf χ x
    have hc2 : |carre F χ (carre F f f) x| ≤ 2 * ε * a * s := by
      refine hc.trans ?_
      have : 2 * ‖mgrad F χ x‖ ≤ 2 * ε := by linarith [hε x]
      have has : 0 ≤ a * s := by positivity
      calc 2 * ‖mgrad F χ x‖ * a * s = (2 * ‖mgrad F χ x‖) * (a * s) := by ring
        _ ≤ (2 * ε) * (a * s) := by gcongr
        _ = _ := by ring
    have hlow := neg_abs_le (carre F χ (carre F f f) x)
    have hmul : -(χ x * carre F χ (carre F f f) x + χ x * carre F χ (carre F f f) x) ≤
        4 * χ x * ε * a * s := by
      have : χ x * |carre F χ (carre F f f) x| ≤ χ x * (2 * ε * a * s) := by gcongr
      nlinarith [mul_le_mul_of_nonneg_left hlow h0]
    rw [← ha2, ← hs2]
    nlinarith [sq_nonneg (χ x * a - 2 * ε * s)]
  have h1 : ∫ x, 2 * (χ x ^ 2 * mHessNormSq F f x) ∂μ ≤
      ∫ x, (χ * χ) x * mgenerator F V (carre F f f) x ∂μ :=
    integral_mono (hint_H.const_mul 2) hint_Lw hp1
  have h2 : ∫ x, -carre F (χ * χ) (carre F f f) x ∂μ ≤
      ∫ x, (χ x ^ 2 * mHessNormSq F f x + 4 * ε ^ 2 * carre F f f x) ∂μ :=
    integral_mono hint_cw.neg (hint_H.add (hGint.const_mul _)) hp2
  have h3 : ∫ x, (χ x ^ 2 * mHessNormSq F f x + 4 * ε ^ 2 * carre F f f x) ∂μ =
      ∫ x, χ x ^ 2 * mHessNormSq F f x ∂μ + 4 * ε ^ 2 * ∫ x, carre F f f x ∂μ := by
    rw [integral_add hint_H (hGint.const_mul _), integral_const_mul]
  rw [integral_const_mul] at h1
  rw [integral_neg, h3] at h2
  have h4 : ∫ x, carre F (χ * χ) (carre F f f) x ∂μ =
      -∫ x, (χ * χ) x * mgenerator F V (carre F f f) x ∂μ := hibp
  linarith

theorem integrable_cutoff_sq_mul {μ : Measure M} [IsFiniteMeasure μ] {χ g : M → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hg : Continuous g) :
    Integrable (fun x => χ x ^ 2 * g x) μ :=
  integrable_of_cont_cs ((hχ.pow 2).mul hg) (hcs_of_zero hχc (fun x hx => by simp [hx]))

omit [EMetricSpace M] [BorelSpace M] in
/-- Fatou-type bound for an approximating sequence. -/
theorem lintegral_ofReal_le_of_approx {μ : Measure M} {g : M → ℝ} {h : ℕ → M → ℝ}
    (hmeas : ∀ n, Measurable (h n)) (hg : ∀ x, ∀ᶠ n in atTop, h n x = g x)
    {b : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hb : ∀ n, ∫⁻ x, ENNReal.ofReal (h n x) ∂μ ≤ b n)
    (hbc : Tendsto b atTop (𝓝 c)) : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤ c := by
  refine CutoffRigidity.lintegral_le_of_ae_tendsto_bounds
    (fun n ↦ (hmeas n).ennreal_ofReal.aemeasurable) (Eventually.of_forall fun x ↦ ?_) hb hbc
  exact tendsto_const_nhds.congr' ((hg x).mono fun n hn ↦ (congrArg ENNReal.ofReal hn).symm)

/-- **Hessian rigidity of eigenfunctions** (analytic core of `lem_rig`): if `f` is a smooth
`L²` eigenfunction with eigenvalue `ρ ≥ 0`, under the integration by parts formula, the
Bochner inequality `Γ₂ ≥ ‖Hess‖² + ρΓ`, cutoffs, and full support of `μ`, then
`Hess f = 0`. -/
theorem hess_eq_zero_of_eigenfunction {μ : Measure M} [IsProbabilityMeasure μ] {V f : M → ℝ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V)
    (hB : WeightedBochnerIneq F V ρ) (hC : WeightedCutoffs F M)
    (hpos : ∀ U : Set M, IsOpen U → U.Nonempty → 0 < μ U)
    (hf : MSmooth F f) (hfL2 : MemLp f 2 μ) (hL : ∀ x, mgenerator F V f x = -ρ * f x) (x : M) :
    mHessNormSq F f x = 0 := by
  obtain ⟨χ, hχ, hlim⟩ := hC
  have hf2 : Integrable (fun x => f x ^ 2) μ := hfL2.integrable_sq
  have hG : MSmooth F (carre F f f) := hReg.1 f f hf hf
  set K := ∫ x, f x ^ 2 ∂μ with hK
  have hχ1 : ∀ n x, ‖mgrad F (χ n) x‖ ≤ 1 := fun n x => by
    refine ((hχ n).2.2 x).2.2.trans ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  -- Step 1: `Γ(f)` is integrable
  have hcacc : ∀ n, ∫ x, χ n x ^ 2 * carre F f f x ∂μ ≤ 2 * (ρ + 2) * K := fun n =>
    caccioppoli F hρ hIBP hReg hf hf2 hL (hχ n).1 (hχ n).2.1 (fun x => ⟨((hχ n).2.2 x).1,
      ((hχ n).2.2 x).2.1⟩) (hχ1 n)
  have hmeasG : ∀ n, Measurable (fun x => χ n x ^ 2 * carre F f f x) := fun n =>
    ((hχ n).1.continuous.pow 2 |>.mul hG.continuous).measurable
  have hev : ∀ x, ∀ᶠ n in atTop, χ n x ^ 2 * carre F f f x = carre F f f x := by
    intro x
    filter_upwards [hlim x] with n hn
    simp [hn]
  have hlinG : ∫⁻ x, ENNReal.ofReal (carre F f f x) ∂μ ≤ ENNReal.ofReal (2 * (ρ + 2) * K) := by
    refine lintegral_ofReal_le_of_approx (h := fun n x => χ n x ^ 2 * carre F f f x) hmeasG hev
      (b := fun _ => ENNReal.ofReal (2 * (ρ + 2) * K)) ?_ tendsto_const_nhds
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_cutoff_sq_mul (hχ n).1.continuous (hχ n).2.1 hG.continuous)
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (carre_nonneg F f x))]
    exact ENNReal.ofReal_le_ofReal (hcacc n)
  have hGint : Integrable (fun x => carre F f f x) μ := by
    refine ⟨hG.continuous.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (carre_nonneg F f))]
    exact lt_of_le_of_lt hlinG ENNReal.ofReal_lt_top
  -- Step 2: `‖Hess f‖²` integrates to `0`
  set J := ∫ x, carre F f f x ∂μ with hJ
  have hmeasH : ∀ n, Measurable (fun x => χ n x ^ 2 * mHessNormSq F f x) := fun n =>
    ((hχ n).1.continuous.pow 2 |>.mul (hReg.2.2 f hf)).measurable
  have hevH : ∀ x, ∀ᶠ n in atTop, χ n x ^ 2 * mHessNormSq F f x = mHessNormSq F f x := by
    intro x
    filter_upwards [hlim x] with n hn
    simp [hn]
  have hlinH : ∫⁻ x, ENNReal.ofReal (mHessNormSq F f x) ∂μ ≤ 0 := by
    refine lintegral_ofReal_le_of_approx (h := fun n x => χ n x ^ 2 * mHessNormSq F f x) hmeasH
      hevH (b := fun n => ENNReal.ofReal (4 * (1 / ((n : ℝ) + 1)) ^ 2 * J)) ?_ ?_
    · intro n
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_cutoff_sq_mul (hχ n).1.continuous (hχ n).2.1 (hReg.2.2 f hf))
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (mHessNormSq_nonneg F f x))]
      refine ENNReal.ofReal_le_ofReal ?_
      exact hess_cutoff_bound F hIBP hReg hB hf hL (hχ n).1 (hχ n).2.1
        (fun x => ⟨((hχ n).2.2 x).1, ((hχ n).2.2 x).2.1⟩) (by positivity)
        (fun x => ((hχ n).2.2 x).2.2) hGint
    · have h0 : Tendsto (fun n : ℕ => 4 * (1 / ((n : ℝ) + 1)) ^ 2 * J) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
        simpa using (this.const_mul 4).mul_const J
      simpa using (ENNReal.tendsto_ofReal h0)
  -- Step 3: conclude
  have hH0 : ∀ᵐ y ∂μ, mHessNormSq F f y = 0 := by
    have h1 : ∫⁻ y, ENNReal.ofReal (mHessNormSq F f y) ∂μ = 0 := le_antisymm hlinH bot_le
    have h2 := (lintegral_eq_zero_iff (hReg.2.2 f hf).measurable.ennreal_ofReal).mp h1
    filter_upwards [h2] with y hy
    have := ENNReal.ofReal_eq_zero.mp hy
    exact le_antisymm this (mHessNormSq_nonneg F f y)
  by_contra hne
  have hposx : 0 < mHessNormSq F f x := lt_of_le_of_ne (mHessNormSq_nonneg F f x) (Ne.symm hne)
  have hopen : IsOpen {y | 0 < mHessNormSq F f y} :=
    isOpen_lt continuous_const (hReg.2.2 f hf)
  have hmu := hpos _ hopen ⟨x, hposx⟩
  have hzero : μ {y | 0 < mHessNormSq F f y} = 0 := by
    rw [ae_iff] at hH0
    refine measure_mono_null (fun y hy => ?_) hH0
    simp only [Set.mem_ofPred_eq] at hy ⊢
    exact ne_of_gt hy
  exact absurd hzero (ne_of_gt hmu)

/-- **Parallel gradient** of `L²` eigenfunctions with eigenvalue `ρ` (conditional on the three
geometric inputs): the Levi-Civita derivative of `∇f` vanishes. -/
theorem parallel_gradient_of_geometry {μ : Measure M} [IsProbabilityMeasure μ] {V f : M → ℝ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V)
    (hB : WeightedBochnerIneq F V ρ) (hC : WeightedCutoffs F M)
    (hpos : ∀ U : Set M, IsOpen U → U.Nonempty → 0 < μ U)
    (hf : MSmooth F f) (hfL2 : MemLp f 2 μ) (hL : ∀ x, mgenerator F V f x = -ρ * f x) (x : M) :
    CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x = 0 :=
  (CutoffRigidity.manifoldHessianNormSq_eq_zero_iff 𝓘(ℝ, F) f x).mp
    (hess_eq_zero_of_eigenfunction F hρ hIBP hReg hB hC hpos hf hfL2 hL x)

end Rigidity

end CutCur
