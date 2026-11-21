/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsWeakDerivative
public import LeanPool.CutoffRigidity.EuclideanL2Translations
public import LeanPool.CutoffRigidity.L2FatouBounds
public import LeanPool.CutoffRigidity.GibbsSobolevApproximation

/-! # Actual localized translations of closed Gibbs H¹ functions

Compact cutoff multipliers compare the genuine weighted and unweighted L²
norms. The compact-test translation inequality passes through the actual
closed gradient graph by almost-everywhere subsequences and Fatou.
No Rellich or compact-embedding hypothesis is assumed.
-/

public section

namespace CutoffRigidity

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}

/-- The actual gradient product rule for a single cutoff multiplier. -/
theorem gradient_cutoff_mul {χ f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : Differentiable ℝ χ) (hf : Differentiable ℝ f) (x : EuclideanSpace ℝ (Fin d)) :
    gradient (fun y => χ y * f y) x = χ x • gradient f x + f x • gradient χ x := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, fderiv_fun_mul (hχ x) (hf x)]
  simp only [add_apply, smul_apply, smul_eq_mul, inner_add_left, inner_smul_left,
    inner_gradient_left]
  simp only [RCLike.conj_to_real]

/-- Compactness bounds the inverse-density weighted cutoff and its gradient. -/
theorem exists_inverse_density_cutoff_bounds
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Continuous V)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      (∀ x, ‖Real.exp (V x / 2) * χ x‖ ≤ A) ∧
      (∀ x, ‖Real.exp (V x / 2) • gradient χ x‖ ≤ B) := by
  let H := fun x => Real.exp (V x / 2) * χ x
  have hH : Continuous H := (Real.continuous_exp.comp (hV.div_const 2)).mul hχ.continuous
  have hHc : HasCompactSupport H := by
    simpa only [H, Pi.mul_def] using hχc.mul_left (f := fun x => Real.exp (V x / 2))
  have hG : Continuous (gradient χ) := (differentiable_gradient_of_contDiff_two hχ).continuous
  have hGc : HasCompactSupport (gradient χ) :=
    (hχc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm)
      (by simp)
  let K := fun x => Real.exp (V x / 2) • gradient χ x
  have hK : Continuous K := (Real.continuous_exp.comp (hV.div_const 2)).smul hG
  have hKc : HasCompactSupport K := by
    apply hGc.mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    apply hx
    simp only [K, hz, smul_zero]
  obtain ⟨A, hA, hAb⟩ := (hHc.isCompact_range hH).isBounded.exists_pos_norm_le
  obtain ⟨B, hB, hBb⟩ := (hKc.isCompact_range hK).isBounded.exists_pos_norm_le
  exact ⟨A, B, hA, hB, fun x => hAb (H x) ⟨x, rfl⟩, fun x => hBb (K x) ⟨x, rfl⟩⟩

private theorem norm_add_sq_bound {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

/-- The actual localized gradient energy has a pointwise density comparison. -/
theorem cutoff_gradient_density_bound
    {V χ f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hχ : Differentiable ℝ χ) (hf : Differentiable ℝ f)
    {A B : ℝ}
    (hAb : ∀ x, ‖Real.exp (V x / 2) * χ x‖ ≤ A)
    (hBb : ∀ x, ‖Real.exp (V x / 2) • gradient χ x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.exp (V x) * ‖gradient (fun y => χ y * f y) x‖ ^ 2 ≤
      2 * A ^ 2 * ‖gradient f x‖ ^ 2 + 2 * B ^ 2 * f x ^ 2 := by
  have he : Real.exp (V x / 2) ^ 2 = Real.exp (V x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hg : Real.exp (V x / 2) • gradient (fun y => χ y * f y) x =
      (Real.exp (V x / 2) * χ x) • gradient f x +
        f x • (Real.exp (V x / 2) • gradient χ x) := by
    simp only [gradient_cutoff_mul hχ hf, smul_add, smul_smul, mul_comm]
  have hn := norm_add_sq_bound ((Real.exp (V x / 2) * χ x) • gradient f x)
    (f x • (Real.exp (V x / 2) • gradient χ x))
  have ha := pow_le_pow_left₀ (norm_nonneg _) (hAb x) 2
  have hb := pow_le_pow_left₀ (norm_nonneg _) (hBb x) 2
  have ha' := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖gradient f x‖)
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (f x))
  rw [← hg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, he] at hn
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at ha' hb' hn
  nlinarith

/-- Actual Lebesgue gradient energy of a compact localized test is controlled
by its actual weighted L² norm and weighted gradient energy. -/
theorem compact_cutoff_gradient_energy_le
    {V χ f : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {A B : ℝ}
    (hAb : ∀ x, ‖Real.exp (V x / 2) * χ x‖ ≤ A)
    (hBb : ∀ x, ‖Real.exp (V x / 2) • gradient χ x‖ ≤ B) :
    (∫ x, ‖gradient (fun y => χ y * f y) x‖ ^ 2 ∂volume) ≤
      2 * A ^ 2 * (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) +
        2 * B ^ 2 * (∫ x, f x ^ 2 ∂gibbsMeasure volume V) := by
  let := hprob
  have hprod : ContDiff ℝ 2 (fun x => χ x * f x) := hχ.mul hf
  have hpc : HasCompactSupport (fun x => χ x * f x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := f)
  have hG : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf).continuous
  have hGc : HasCompactSupport (gradient f) :=
    (hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm)
      (by simp)
  have hGL : MemLp (gradient f) 2 (gibbsMeasure volume V) := hG.memLp_of_hasCompactSupport hGc
  have hfL : MemLp f 2 (gibbsMeasure volume V) := hf.continuous.memLp_of_hasCompactSupport hfc
  have hWGc : HasCompactSupport (fun x => Real.exp (V x) * ‖gradient (fun y => χ y * f y) x‖ ^ 2)
    := by
    have hc : HasCompactSupport (gradient (fun y => χ y * f y)) :=
      (hpc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm)
        (by simp)
    have hc' := hc.comp_left (g := fun z => ‖z‖ ^ 2) (by simp)
    convert! hc'.mul_left (f := fun x => Real.exp (V x)) using 1
  have hWG : Integrable (fun x => Real.exp (V x) * ‖gradient (fun y => χ y * f y) x‖ ^ 2)
      (gibbsMeasure volume V) := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous _ hWGc
    exact (Real.continuous_exp.comp hV.continuous).mul ((differentiable_gradient_of_contDiff_two
      hprod).continuous.norm.pow 2)
  rw [← integral_exp_potential_mul_gibbs_eq_volume hV.continuous.measurable]
  have h := integral_mono hWG
    (((hGL.norm.integrable_sq).const_mul (2 * A ^ 2)).add (hfL.integrable_sq.const_mul (2 * B ^ 2)))
    (cutoff_gradient_density_bound (hχ.differentiable (by norm_num)) (hf.differentiable
      (by norm_num)) hAb hBb)
  simp only [Pi.add_apply] at h
  rwa [integral_add ((hGL.norm.integrable_sq).const_mul (2 * A ^ 2)) (hfL.integrable_sq.const_mul
    (2 * B ^ 2)),
    integral_const_mul, integral_const_mul] at h


/-- Fatou transfers varying convergent second-moment bounds through an
actual almost-everywhere limit. -/
theorem integral_sq_le_of_ae_tendsto_bounds {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {fn : ℕ → α → ℝ} {g : α → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => fn n x) atTop (𝓝 (g x)))
    {bn : ℕ → ℝ} {b : ℝ} (hb : Tendsto bn atTop (𝓝 b)) (hb0 : 0 ≤ b)
    (hbound : ∀ n, (∫ x, fn n x ^ 2 ∂μ) ≤ bn n) :
    (∫ x, g x ^ 2 ∂μ) ≤ b := by
  let F := fun n x => ENNReal.ofReal (fn n x ^ 2)
  have hFm (n : ℕ) : AEMeasurable (F n) μ :=
    ((hfn n).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal
  have hpoint : (fun x => liminf (fun n => F n x) atTop) =ᵐ[μ]
      (fun x => ENNReal.ofReal (g x ^ 2)) := by
    filter_upwards [hlim] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _ |>.comp (hx.pow 2)).liminf_eq
  have hF := lintegral_liminf_le' (μ := μ) (f := F) (u := atTop) hFm
  rw [lintegral_congr_ae hpoint] at hF
  have hEach (n : ℕ) : (∫⁻ x, F n x ∂μ) ≤ ENNReal.ofReal (bn n) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfn n).integrable_sq
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hh := liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall hEach)
  have hblim := ENNReal.continuous_ofReal.tendsto b |>.comp hb
  change Tendsto (fun n => ENNReal.ofReal (bn n)) atTop (𝓝 (ENNReal.ofReal b)) at hblim
  rw [hblim.liminf_eq] at hh
  have hfinal := hF.trans hh
  rw [← ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))] at hfinal
  exact (ENNReal.ofReal_le_ofReal_iff hb0).mp hfinal

/-- Actual cutoff differences of a genuine closed Gibbs H¹ function are
Lebesgue L² functions, independently of any compactness theorem. -/
theorem gibbsSobolev_cutoff_translation_memLp
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (u : gibbsSobolevGraph hV hprob) (h : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun x => χ (x + h) * gibbsSobolevInclusion hV hprob u (x + h) -
      χ x * gibbsSobolevInclusion hV hprob u x) 2 volume := by
  have hL := compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ hχc
    (gibbsSobolevInclusion hV hprob u)
  convert! (hL.comp_measurePreserving (measurePreserving_add_right volume h)).sub hL using 1

/-- The actual closed H¹ cutoff translation energy is bounded by the actual
weighted graph energies. Compact approximants supply the estimate; Haar
translation preserves their a.e. subsequential limit. -/
theorem gibbsSobolev_cutoff_translation_integral_sq_le
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    {A B : ℝ}
    (hAb : ∀ x, ‖Real.exp (V x / 2) * χ x‖ ≤ A)
    (hBb : ∀ x, ‖Real.exp (V x / 2) • gradient χ x‖ ≤ B)
    (u : gibbsSobolevGraph hV hprob) (h : EuclideanSpace ℝ (Fin d)) :
    (∫ x, (χ (x + h) * gibbsSobolevInclusion hV hprob u (x + h) -
      χ x * gibbsSobolevInclusion hV hprob u x) ^ 2 ∂volume) ≤
      ‖h‖ ^ 2 * (2 * A ^ 2 * ‖gibbsSobolevDerivative hV hprob u‖ ^ 2 +
        2 * B ^ 2 * ‖gibbsSobolevInclusion hV hprob u‖ ^ 2) := by
  let μ := gibbsMeasure volume V
  let G := compactGibbsGradient hV.continuous hprob
  let U := gibbsSobolevInclusion hV hprob u
  let Du := gibbsSobolevDerivative hV hprob u
  obtain ⟨p, hp, hfirst, hsecond, hAE⟩ := gibbsSobolev_approximation_seq hV hprob u
  choose v hv1 hv2 using (fun n => G.mem_graph_iff.mp (hp n))
  let f := fun n => compactGibbsRepresentative V (v n)
  have hf (n : ℕ) : ContDiff ℝ 2 (f n) := (compactGibbsRepresentative_spec V (v n)).1
  have hfc (n : ℕ) : HasCompactSupport (f n) := (compactGibbsRepresentative_spec V (v n)).2.1
  have hrep : ∀ᵐ x ∂μ, ∀ n, f n x = (p n).1 x := by
    apply ae_all_iff.mpr
    intro n
    have hh := (compactGibbsRepresentative_spec V (v n)).2.2
    simp only [hv1] at hh
    convert! hh using 1
  have hlimμ : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (U x)) := by
    filter_upwards [hAE, hrep] with x hx hfx
    exact hx.congr' (Filter.Eventually.of_forall (fun n => (hfx n).symm))
  have hlimvol := (absolutelyContinuous_gibbsMeasure volume hV.continuous.measurable).ae_le hlimμ
  have hshift := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hlimvol
  let fn := fun n x => χ (x + h) * f n (x + h) - χ x * f n x
  let g := fun x => χ (x + h) * U (x + h) - χ x * U x
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => fn n x) atTop (𝓝 (g x)) := by
    filter_upwards [hlimvol, hshift] with x hx hxh
    exact (hxh.const_mul (χ (x + h))).sub (hx.const_mul (χ x))
  have hfn (n : ℕ) : MemLp (fn n) 2 volume := by
    have hc : HasCompactSupport (fun x => χ x * f n x) := by
      simpa only [Pi.mul_def] using hχc.mul_right (f' := f n)
    exact c1_compact_translation_memLp ((hχ.mul (hf n)).of_le (by norm_num)) hc h
  have hg : MemLp g 2 volume := gibbsSobolev_cutoff_translation_memLp hV hprob hχ.continuous hχc u h
  let bn := fun n => ‖h‖ ^ 2 * (2 * A ^ 2 * ‖(p n).2‖ ^ 2 + 2 * B ^ 2 * ‖(p n).1‖ ^ 2)
  let b := ‖h‖ ^ 2 * (2 * A ^ 2 * ‖Du‖ ^ 2 + 2 * B ^ 2 * ‖U‖ ^ 2)
  have hb : Tendsto bn atTop (𝓝 b) :=
    (((hsecond.norm.pow 2).const_mul (2 * A ^ 2)).add
      ((hfirst.norm.pow 2).const_mul (2 * B ^ 2))).const_mul (‖h‖ ^ 2)
  apply integral_sq_le_of_ae_tendsto_bounds hfn hg hlim hb (by dsimp [b]; positivity)
  intro n
  have hcutc : HasCompactSupport (fun x => χ x * f n x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := f n)
  have ht := c1_compact_translation_integral_sq_le ((hχ.mul (hf n)).of_le (by norm_num)) hcutc h
  have he := compact_cutoff_gradient_energy_le hV hprob hχ hχc (hf n) (hfc n) hAb hBb
  have hN : (∫ x, f n x ^ 2 ∂μ) = ‖(p n).1‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [← hx n, Real.inner_apply, pow_two]
  have hD : (∫ x, ‖gradient (f n) x‖ ^ 2 ∂μ) = ‖(p n).2‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    have hh := (compactGibbsGradient_memLp hprob (v n)).coeFn_toLp
    filter_upwards [hh] with x hx
    rw [← hv2 n]
    change ‖gradient (f n) x‖ ^ 2 = inner ℝ ((compactGibbsGradient_memLp hprob (v n)).toLp _ x)
      ((compactGibbsGradient_memLp hprob (v n)).toLp _ x)
    rw [hx, real_inner_self_eq_norm_sq]
  change (∫ x, (χ (x + h) * f n (x + h) - χ x * f n x) ^ 2 ∂volume) ≤ _
  rw [hD, hN] at he
  exact ht.trans (mul_le_mul_of_nonneg_left he (sq_nonneg ‖h‖))


/-- Uniform local translation control for the actual closed Gibbs H¹ unit
ball, with the constant derived solely from the cutoff and potential. -/
theorem exists_gibbsSobolev_cutoff_translation_integral_bound
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : gibbsSobolevGraph hV hprob) (h : EuclideanSpace ℝ (Fin d)),
      (∫ x, (χ (x + h) * gibbsSobolevInclusion hV hprob u (x + h) -
        χ x * gibbsSobolevInclusion hV hprob u x) ^ 2 ∂volume) ≤ C * ‖h‖ ^ 2 * ‖u‖ ^ 2 := by
  obtain ⟨A, B, hA, hB, hAb, hBb⟩ := exists_inverse_density_cutoff_bounds hV.continuous hχ hχc
  let C := 2 * (A ^ 2 + B ^ 2)
  have hC : 0 < C := by dsimp [C]; nlinarith [sq_pos_of_pos hA, sq_pos_of_pos hB]
  refine ⟨C, hC, ?_⟩
  intro u h
  have hb := gibbsSobolev_cutoff_translation_integral_sq_le hV hprob hχ hχc hAb hBb u h
  let D := ‖gibbsSobolevDerivative hV hprob u‖
  let U := ‖gibbsSobolevInclusion hV hprob u‖
  have hid : ‖u‖ ^ 2 = U ^ 2 + D ^ 2 :=
    (gibbsSobolev_norm_sq hV hprob u).trans
      (congrArg (U ^ 2 + ·) (real_inner_self_eq_norm_sq (gibbsSobolevDerivative hV hprob u)))
  have hsum : 2 * A ^ 2 * D ^ 2 + 2 * B ^ 2 * U ^ 2 ≤ C * (U ^ 2 + D ^ 2) := by
    dsimp only [C]
    nlinarith only [mul_nonneg (sq_nonneg A) (sq_nonneg U),
      mul_nonneg (sq_nonneg B) (sq_nonneg D)]
  have he := hsum.trans_eq (congrArg (C * ·) hid.symm)
  calc
    _ ≤ ‖h‖ ^ 2 * (C * ‖u‖ ^ 2) := hb.trans (mul_le_mul_of_nonneg_left he (sq_nonneg ‖h‖))
    _ = C * ‖h‖ ^ 2 * ‖u‖ ^ 2 := by ring


/-- The actual local L² translation norm estimate requested by the
mollification argument, on every element of the genuine closed H¹ graph. -/
theorem exists_gibbsSobolev_cutoff_translation_L2_bound
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : gibbsSobolevGraph hV hprob) (h : EuclideanSpace ℝ (Fin d)),
      ‖(gibbsSobolev_cutoff_translation_memLp hV hprob hχ.continuous hχc u h).toLp
        (fun x => χ (x + h) * gibbsSobolevInclusion hV hprob u (x + h) -
          χ x * gibbsSobolevInclusion hV hprob u x)‖ ≤ C * ‖h‖ * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := exists_gibbsSobolev_cutoff_translation_integral_bound hV hprob hχ hχc
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro u h
  have hn : ‖(gibbsSobolev_cutoff_translation_memLp hV hprob hχ.continuous hχc u h).toLp
      (fun x => χ (x + h) * gibbsSobolevInclusion hV hprob u (x + h) -
        χ x * gibbsSobolevInclusion hV hprob u x)‖ ^ 2 =
      ∫ x, (χ (x + h) * gibbsSobolevInclusion hV hprob u (x + h) -
        χ x * gibbsSobolevInclusion hV hprob u x) ^ 2 ∂volume := by
    exact norm_toLp_sq (gibbsSobolev_cutoff_translation_memLp hV hprob hχ.continuous hχc u h)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hscale : (Real.sqrt C * ‖h‖ * ‖u‖) ^ 2 = C * ‖h‖ ^ 2 * ‖u‖ ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hC.le]
  exact hn.trans_le ((hb u h).trans_eq hscale.symm)


/-- Compact cutoff multiplication is genuinely bounded from Gibbs L² into
Lebesgue L², not merely an assertion of local membership. -/
theorem exists_compact_cutoff_gibbsLp_L2_norm_bound
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ,
      ‖(compact_cutoff_gibbsLp_memLp_volume hV hprob hχ.continuous hχc u).toLp
        (fun x => χ x * u x)‖ ≤ A * ‖u‖ := by
  let := hprob
  obtain ⟨A, B, hA, hB, hAb, hBb⟩ := exists_inverse_density_cutoff_bounds hV hχ hχc
  refine ⟨A, hA, ?_⟩
  intro u
  let H := fun x => Real.exp (V x / 2) * χ x
  have hH : Continuous H := (Real.continuous_exp.comp (hV.div_const 2)).mul hχ.continuous
  have hHc : HasCompactSupport H := by
    simpa only [H, Pi.mul_def] using hχc.mul_left (f := fun x => Real.exp (V x / 2))
  have hHL : MemLp H ⊤ (gibbsMeasure volume V) := hH.memLp_of_hasCompactSupport hHc
  have hm : MemLp (fun x => H x * u x) 2 (gibbsMeasure volume V) := hHL.fun_mul (Lp.memLp u)
  have he (x : EuclideanSpace ℝ (Fin d)) : Real.exp (V x / 2) ^ 2 = Real.exp (V x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpoint (x : EuclideanSpace ℝ (Fin d)) : Real.exp (V x) * (χ x * u x) ^ 2 = (H x * u x) ^ 2
    := by
    dsimp only [H]
    simp only [mul_pow, he]
    ring
  have hi : (∫ x, (χ x * u x) ^ 2 ∂volume) ≤ A ^ 2 * ‖u‖ ^ 2 := by
    rw [← integral_exp_potential_mul_gibbs_eq_volume hV.measurable]
    simp_rw [hpoint]
    have h := integral_mono hm.integrable_sq ((Lp.memLp u).integrable_sq.const_mul (A ^ 2))
      (fun x => by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (hAb x) 2
      simp only [Real.norm_eq_abs, sq_abs] at hh
      change (H x * u x) ^ 2 ≤ _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hh (sq_nonneg (u x)))
    rw [integral_const_mul] at h
    have hu : (∫ x, u x ^ 2 ∂gibbsMeasure volume V) = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [Real.inner_apply, pow_two]
    rwa [hu] at h
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA.le (norm_nonneg _))).mp
  rw [norm_toLp_sq, mul_pow]
  exact hi

end CutoffRigidity
