/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import LeanPool.Triangular.Auto.Grid
public import LeanPool.Triangular.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Principal values and the symmetric triangular Hilbert bound

Derived from the corresponding part of the upstream triangular Hilbert form proof.
-/

@[expose] public section

namespace Triangular.Auto

open MeasureTheory Filter Topology Matrix Real

open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section

lemma abs_kernIntegrand_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → ∀ t, |kernIntegrand m s t| ≤ C / (s * √s) := by
  obtain ⟨M, hM⟩ := abs_gaussianD_le_const m (σ := 63 / 20) (by norm_num)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun s hs t => ?_⟩
  have hss : 0 < √s := Real.sqrt_pos.2 hs
  unfold kernIntegrand
  rw [gaussianD_scale m (by norm_num) hs]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos (by positivity : (0 : ℝ) < √s ^ m),
    abs_of_pos (by positivity : (0 : ℝ) < (√s)⁻¹ ^ (m + 1))]
  have h1 := hM ((√s)⁻¹ * t)
  have e : √s ^ m * ((√s)⁻¹ ^ (m + 1) * |gaussianD m (63 / 20) ((√s)⁻¹ * t)|) / s =
      |gaussianD m (63 / 20) ((√s)⁻¹ * t)| / (s * √s) := by
    rw [inv_pow, pow_succ]
    field_simp
  rw [e]
  gcongr

lemma abs_Kern_le (m : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, ∀ t, |Kern m a b t| ≤ C := by
  obtain ⟨C, hC, h⟩ := abs_kernIntegrand_le m
  refine ⟨C / (a * √a) * (b - a), fun t => ?_⟩
  rw [Kern_eq]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun s => kernIntegrand m s t) (C := C / (a * √a)) ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at this
    exact this
  intro s hs
  rw [Set.uIoc_of_le hab] at hs
  have hs0 : 0 < s := ha.trans hs.1
  rw [Real.norm_eq_abs]
  refine (h s hs0 t).trans ?_
  have : a * √a ≤ s * √s := mul_le_mul hs.1.le (Real.sqrt_le_sqrt hs.1.le) (Real.sqrt_nonneg _)
    hs0.le
  exact div_le_div_of_nonneg_left hC (by positivity) this

/-- The explicit third derivative used in source Section 3, equation `dist`. -/
theorem triangular_gaussian_third {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gaussianD 3 σ t = (3 * t / σ ^ 2 - t ^ 3 / σ ^ 3) * gaussian σ t := by
  rw [gaussianD_eq_profile 3 hσ, gaussian_eq_profile hσ]
  rw [show 3 = 1 + 2 from rfl, gaussProfileD_succ_succ,
    show 1 + 1 = 0 + 2 from rfl, gaussProfileD_succ_succ]
  simp only [Nat.cast_zero, Nat.cast_one, zero_add, gaussProfileD_one, gaussProfileD_zero]
  have hs := Real.sq_sqrt hσ.le
  have hp := Real.sqrt_pos.mpr hσ
  generalize Real.sqrt σ = r at *; rw [← hs]
  generalize gaussProfile (r⁻¹ * t) = g; simp only [inv_pow]
  field_simp [ne_of_gt hp]; ring

/-- An explicit scale primitive for the third differentiated Gaussian. -/
def triangularGaussianPrimitive (c s t : ℝ) : ℝ :=
  (2 / (c * Real.sqrt (2 * Real.pi * c) * t)) *
    ((1 - t ^ 2 / (c * s)) * Real.exp (-(t ^ 2 / (c * s)) / 2))

/-- Source `dist`: the scale primitive differentiates to the third Gaussian kernel. -/
theorem triangularGaussianPrimitive_hasDerivAt {c s t : ℝ} (hc : 0 < c) (hs : 0 < s)
    (ht : t ≠ 0) :
    HasDerivAt (fun u => triangularGaussianPrimitive c u t) (Real.sqrt s ^ 3 * gaussianD 3 (c *
      s) t / s) s := by
  have hd := (hasDerivAt_const s (t ^ 2)).div ((hasDerivAt_id s).const_mul c)
    (mul_ne_zero (ne_of_gt hc) (ne_of_gt hs))
  have hh := (((hasDerivAt_const s 1).sub hd).mul (hd.neg.div_const 2).exp).const_mul
    (2 / (c * Real.sqrt (2 * Real.pi * c) * t))
  convert hh using 1
  · rfl
  · rw [triangular_gaussian_third (mul_pos hc hs), gaussian]
    rw [show 2 * Real.pi * (c * s) = (2 * Real.pi * c) * s by ring,
      Real.sqrt_mul (by positivity)]
    have he : -(t ^ 2 / (c * s)) / 2 = -(t ^ 2) / (2 * (c * s)) := by ring
    dsimp only [id_eq, Pi.neg_apply, Pi.div_apply, Pi.sub_apply, Pi.mul_apply]; rw [he]
    have hsq := Real.sq_sqrt hs.le
    have hp := Real.sqrt_pos.mpr hs
    generalize Real.sqrt s = r at *; rw [← hsq]
    generalize Real.exp (-t ^ 2 / (2 * (c * r ^ 2))) = e; field_simp; ring

/-- Source `dist`: the Gaussian interval kernel is the difference of its scale primitives. -/
theorem triangular_Kern_eq_primitive {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {t : ℝ} (ht : t ≠ 0) :
    Kern 3 a b t = triangularGaussianPrimitive (63 / 20) b t - triangularGaussianPrimitive (63 /
      20) a t := by
  rw [Kern_eq]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact triangularGaussianPrimitive_hasDerivAt (by norm_num) (ha.trans_le hs.1) ht
  · have hpair : Continuous (fun s : ℝ => (s, t)) := continuous_id.prodMk continuous_const
    have hmaps : Set.MapsTo (fun s : ℝ => (s, t)) (Set.Icc a b) {z : ℝ × ℝ | 0 < z.1} :=
      fun _ hs => ha.trans_le hs.1
    have hcont := (continuousOn_kernIntegrand_joint 3).comp hpair.continuousOn hmaps
    exact hcont.intervalIntegrable_of_Icc hab

/-- The scalar cutoff profile in the explicit Gaussian scale primitive. -/
def triangularCutoffProfile (u : ℝ) : ℝ := (1 - 2 * u) * Real.exp (-u)

theorem triangularCutoffProfile_bound {u : ℝ} (hu : 0 ≤ u) : |triangularCutoffProfile u| ≤ 3 := by
  have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-u)
  have hm : u * Real.exp (-u) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one u).trans (Real.exp_le_one_iff.mpr (by norm_num))
  rw [triangularCutoffProfile, abs_le]
  constructor <;> nlinarith

theorem triangularCutoffProfile_tendsto : Tendsto triangularCutoffProfile atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.sub
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 2)
  convert h using 1
  · ext u; simp [triangularCutoffProfile]; ring
  · simp

theorem triangularGaussianPrimitive_eq_profile (c s t : ℝ) :
    triangularGaussianPrimitive c s t = (2 / (c * Real.sqrt (2 * Real.pi * c) * t)) *
      triangularCutoffProfile (t ^ 2 / (2 * c * s)) := by
  unfold triangularGaussianPrimitive triangularCutoffProfile; ring_nf

/-- The upper scale endpoint in the Hilbert-kernel recovery. -/
theorem triangularGaussianPrimitive_tendsto_top {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun s => triangularGaussianPrimitive c s t) atTop (𝓝 (2 / (c * Real.sqrt (2 *
      Real.pi * c) * t))) := by
  have hu : Tendsto (fun s : ℝ => t ^ 2 / (2 * c * s)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by positivity) tendsto_id)
  have hp : Continuous triangularCutoffProfile := by unfold triangularCutoffProfile; fun_prop
  have h := (hp.continuousAt.tendsto.comp hu).const_mul
    (2 / (c * Real.sqrt (2 * Real.pi * c) * t))
  simpa [triangularGaussianPrimitive_eq_profile, triangularCutoffProfile] using h

/-- The lower scale endpoint in the Hilbert-kernel recovery. -/
theorem triangularGaussianPrimitive_tendsto_zero {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    Tendsto (fun s => triangularGaussianPrimitive c s t) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun s : ℝ => t ^ 2 / (2 * c * s)) (𝓝[>] 0) atTop := by
    have h := Tendsto.const_mul_atTop (show 0 < t ^ 2 / (2 * c) by positivity)
      (tendsto_inv_nhdsGT_zero : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] 0) atTop)
    convert h using 1
    ext s; simp [div_eq_mul_inv, _root_.mul_inv_rev, mul_comm, mul_left_comm]
  have h := (triangularCutoffProfile_tendsto.comp hu).const_mul
    (2 / (c * Real.sqrt (2 * Real.pi * c) * t))
  simpa [triangularGaussianPrimitive_eq_profile] using h

/-- Source `dist`: Gaussian scales recover a fixed positive multiple of 1/t. -/
theorem triangular_Kern_tendsto {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) t) atTop (𝓝 (2 / ((63 / 20 : ℝ) *
      Real.sqrt (2 * Real.pi * (63 / 20)) * t))) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htop := (triangularGaussianPrimitive_tendsto_top (by norm_num : (0 : ℝ) < 63 / 20) t).comp hn
  have hzero := (triangularGaussianPrimitive_tendsto_zero (by norm_num : (0 : ℝ) < 63 / 20) ht).comp
    (tendsto_inv_atTop_nhdsGT_zero.comp hn)
  have h := htop.sub hzero
  simp only [sub_zero] at h
  apply h.congr
  intro n
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact (triangular_Kern_eq_primitive (inv_pos.mpr hn0)
    ((inv_le_one₀ hn0).mpr hn1 |>.trans hn1) ht).symm

/-- The positive normalization constant recovered by the Gaussian kernels. -/
def triangularKernelCoefficient : ℝ :=
  2 / ((63 / 20 : ℝ) * Real.sqrt (2 * Real.pi * (63 / 20)))

theorem triangularKernelCoefficient_pos : 0 < triangularKernelCoefficient := by
  unfold triangularKernelCoefficient
  positivity

/-- Cancellation leaves a uniformly bounded multiplier, independent of scale. -/
theorem triangular_Kern_mul_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    |t * Kern 3 a b t| ≤ 6 * triangularKernelCoefficient := by
  by_cases ht : t = 0
  · simp only [ht, zero_mul, abs_zero]
    positivity [triangularKernelCoefficient_pos]
  have he : t * Kern 3 a b t = triangularKernelCoefficient *
      (triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * b)) -
        triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * a))) := by
    rw [triangular_Kern_eq_primitive ha hab ht,
      triangularGaussianPrimitive_eq_profile, triangularGaussianPrimitive_eq_profile]
    unfold triangularKernelCoefficient; field_simp
  rw [he, abs_mul, abs_of_pos triangularKernelCoefficient_pos]
  have hb := triangularCutoffProfile_bound
    (show 0 ≤ t ^ 2 / (2 * (63 / 20) * b) by have := ha.trans_le hab; positivity)
  have ha' := triangularCutoffProfile_bound
    (show 0 ≤ t ^ 2 / (2 * (63 / 20) * a) by positivity)
  have hd := abs_sub_le (triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * b)))
    0 (triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * a)))
  simp only [sub_zero, zero_sub, abs_neg] at hd
  have hle : |triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * b)) -
      triangularCutoffProfile (t ^ 2 / (2 * (63 / 20) * a))| ≤ 6 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle triangularKernelCoefficient_pos.le]

/-- The normalized cancellation multipliers converge away from the singular plane. -/
theorem triangular_Kern_mul_tendsto {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => t * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) t) atTop (𝓝
      triangularKernelCoefficient) := by
  convert (triangular_Kern_tendsto ht).const_mul t using 1
  congr 1
  unfold triangularKernelCoefficient; field_simp

/-- Source `dist`: dominated convergence for integrable cancelled kernel pairings. -/
theorem triangular_kernel_pairing_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : X → ℂ} {r : X → ℝ} (hg : Integrable g μ) (hr : Measurable r) (hz : ∀ᵐ x ∂μ, r x ≠ 0) :
    Tendsto (fun n : ℕ => ∫ x, g x * ((r x * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) (r x) : ℝ) :
      ℂ) ∂μ) atTop (𝓝 ((triangularKernelCoefficient : ℂ) * ∫ x, g x ∂μ)) := by
  have hp : ∀ n : ℕ, 0 < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have hab : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ ≤ (n : ℝ) + 1 := by
    intro n
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact ((inv_le_one₀ hn0).mpr hn1).trans hn1
  have hlim : Tendsto (fun n : ℕ => ∫ x, g x *
      ((r x * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) (r x) : ℝ) : ℂ) ∂μ)
      atTop (𝓝 (∫ x, g x * (triangularKernelCoefficient : ℂ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => (6 * triangularKernelCoefficient) * ‖g x‖)
    · intro n
      have hm : Measurable (fun x =>
          ((r x * Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) (r x) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp
          (hr.mul ((continuous_Kern 3 (hp n) (hab n)).measurable.comp hr))
      exact hg.aestronglyMeasurable.mul hm.aestronglyMeasurable
    · exact hg.norm.const_mul _
    · intro n
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h := triangular_Kern_mul_bound (hp n) (hab n) (r x)
      nlinarith [mul_le_mul_of_nonneg_left h (norm_nonneg (g x))]
    · filter_upwards [hz] with x hx
      exact tendsto_const_nhds.mul
        (Complex.continuous_ofReal.continuousAt.tendsto.comp (triangular_Kern_mul_tendsto hx))
  simpa [integral_mul_const, mul_comm] using hlim

/-- Product in the sheared coordinates of the triangular form. -/
def triangularShiftProduct (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (t : ℝ) : ℂ :=
  F (p.1 + t, p.2) * G (p.1, p.2 + t)

/-- The odd difference quotient giving the symmetric principal value. -/
def triangularOddQuotient (H F G : ℝ × ℝ → ℂ) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  H q.1 * (triangularShiftProduct F G q.1 q.2 -
    triangularShiftProduct F G q.1 (-q.2)) / (q.2 : ℂ)

/-- Lipschitz cancellation controls the quotient at the singular plane. -/
theorem triangularOddQuotient_bound {H F G : ℝ × ℝ → ℂ} {M : ℝ≥0} (hF : LipschitzWith M F)
    (hG : LipschitzWith M G) (bF : ∀ p, ‖F p‖ ≤ M) (bG : ∀ p, ‖G p‖ ≤ M) (p : ℝ × ℝ) (t : ℝ) :
    ‖triangularOddQuotient H F G (p, t)‖ ≤ ‖H p‖ * (4 * (M : ℝ) ^ 2) := by
  by_cases ht : t = 0
  · simp only [triangularOddQuotient, ht, neg_zero, sub_self, mul_zero,
      Complex.ofReal_zero, div_zero, norm_zero]
    positivity
  have hdF : ‖F (p.1 + t, p.2) - F (p.1 - t, p.2)‖ ≤ (M : ℝ) * (2 * |t|) := by
    have h := hF.norm_sub_le (p.1 + t, p.2) (p.1 - t, p.2)
    have he : (p.1 + t, p.2) - (p.1 - t, p.2) = (2 * t, 0) := by ext <;> simp; ring
    simpa [he, Prod.norm_def, Real.norm_eq_abs, abs_mul] using h
  have hdG : ‖G (p.1, p.2 + t) - G (p.1, p.2 - t)‖ ≤ (M : ℝ) * (2 * |t|) := by
    have h := hG.norm_sub_le (p.1, p.2 + t) (p.1, p.2 - t)
    have he : (p.1, p.2 + t) - (p.1, p.2 - t) = (0, 2 * t) := by ext <;> simp; ring
    simpa [he, Prod.norm_def, Real.norm_eq_abs, abs_mul] using h
  have hd : ‖triangularShiftProduct F G p t - triangularShiftProduct F G p (-t)‖ ≤
      4 * (M : ℝ) ^ 2 * |t| := by
    unfold triangularShiftProduct; simp only [← sub_eq_add_neg]
    calc
      _ = ‖(F (p.1 + t, p.2) - F (p.1 - t, p.2)) * G (p.1, p.2 + t) +
          F (p.1 - t, p.2) * (G (p.1, p.2 + t) - G (p.1, p.2 - t))‖ := by congr 1; ring
      _ ≤ ‖F (p.1 + t, p.2) - F (p.1 - t, p.2)‖ * ‖G (p.1, p.2 + t)‖ +
          ‖F (p.1 - t, p.2)‖ * ‖G (p.1, p.2 + t) - G (p.1, p.2 - t)‖ := by
        simpa only [norm_mul] using norm_add_le
          ((F (p.1 + t, p.2) - F (p.1 - t, p.2)) * G (p.1, p.2 + t))
          (F (p.1 - t, p.2) * (G (p.1, p.2 + t) - G (p.1, p.2 - t)))
      _ ≤ ((M : ℝ) * (2 * |t|)) * M + M * (M * (2 * |t|)) := by
        gcongr <;> first | exact bF _ | exact bG _
      _ = _ := by ring
  rw [triangularOddQuotient, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    div_le_iff₀ (abs_pos.mpr ht)]
  nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (H p))]

/-- Uniform size, derivative, and one-coordinate decay bounds for a Schwartz input. -/
theorem triangular_schwartz_bounds (F : SchwartzMap (ℝ × ℝ) ℂ) :
    ∃ M : ℝ≥0, LipschitzWith M F ∧ (∀ p, ‖F p‖ ≤ M) ∧ ∀ p : ℝ × ℝ, ‖F p‖ ≤ (M : ℝ) * (1 + p.1 ^
      2)⁻¹ := by
  let A := SchwartzMap.seminorm ℝ 0 0 F
  let B := SchwartzMap.seminorm ℝ 2 0 F
  let D := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℂ F)
  have hA : 0 ≤ A := apply_nonneg _ _
  have hB : 0 ≤ B := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  let M : ℝ≥0 := ⟨A + B + D, by positivity⟩
  have hsize : ∀ p, ‖F p‖ ≤ (M : ℝ) := by
    intro p
    have h := F.norm_le_seminorm ℝ p
    change ‖F p‖ ≤ A at h
    change ‖F p‖ ≤ A + B + D
    linarith
  refine ⟨M, ?_, hsize, ?_⟩
  · apply lipschitzWith_of_nnnorm_fderiv_le F.differentiable
    intro p
    have h := (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℂ F).norm_le_seminorm ℝ p
    change ‖fderiv ℝ F p‖ ≤ D at h
    change ‖fderiv ℝ F p‖₊ ≤ M
    apply NNReal.coe_le_coe.mp
    change ‖fderiv ℝ F p‖ ≤ A + B + D
    linarith
  · intro p
    have h0 := F.norm_le_seminorm ℝ p
    have h2 := F.norm_pow_mul_le_seminorm ℝ 2 p
    have hp : |p.1| ≤ ‖p‖ := by simp [Prod.norm_def, Real.norm_eq_abs]
    have hp2 : p.1 ^ 2 ≤ ‖p‖ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg p.1) hp 2
    change ‖F p‖ ≤ A at h0
    change ‖p‖ ^ 2 * ‖F p‖ ≤ B at h2
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    change ‖F p‖ * (1 + p.1 ^ 2) ≤ A + B + D
    nlinarith [mul_le_mul_of_nonneg_right hp2 (norm_nonneg (F p))]

/-- An integrable decay majorant remains integrable after shearing its last coordinate. -/
theorem triangular_integrable_decay {H : ℝ × ℝ → ℝ} (hH : Integrable H) (sign : ℝ)
    (hsign : sign = 1 ∨ sign = -1) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * (1 + (q.1.1 + sign * q.2) ^ 2)⁻¹) := by
  have hbase := hH.mul_prod integrable_inv_one_add_sq
  have hp : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => (q.1, q.1.1 + sign * q.2))
      (volume.prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
      (g := fun (p : ℝ × ℝ) (t : ℝ) => p.1 + sign * t)
      (μc := volume) (μd := volume) (by fun_prop) ?_
    filter_upwards [] with p
    rcases hsign with rfl | rfl
    · simpa using (measurePreserving_add_left volume p.1).map_eq
    · have h := (measurePreserving_add_left volume p.1).comp (Measure.measurePreserving_neg (volume
        : Measure ℝ))
      simpa [Function.comp_def] using h.map_eq
  exact hp.integrable_comp_of_integrable hbase

/-- The odd quotient is controlled at infinity by the decay of one input. -/
theorem triangularOddQuotient_tail_bound {H F G : ℝ × ℝ → ℂ} {M : ℝ≥0}
    (bF : ∀ p : ℝ × ℝ, ‖F p‖ ≤ (M : ℝ) * (1 + p.1 ^ 2)⁻¹) (bG : ∀ p, ‖G p‖ ≤ M) (p : ℝ × ℝ)
    (t : ℝ) (ht : 1 ≤ |t|) :
    ‖triangularOddQuotient H F G (p, t)‖ ≤ ‖H p‖ * (M : ℝ) ^ 2 * ((1 + (p.1 + t) ^ 2)⁻¹ + (1 +
      (p.1 - t) ^ 2)⁻¹) := by
  have hd : ‖triangularShiftProduct F G p t - triangularShiftProduct F G p (-t)‖ ≤
      (M : ℝ) ^ 2 * ((1 + (p.1 + t) ^ 2)⁻¹ + (1 + (p.1 - t) ^ 2)⁻¹) := by
    calc
      _ ≤ ‖triangularShiftProduct F G p t‖ + ‖triangularShiftProduct F G p (-t)‖ := norm_sub_le _ _
      _ = ‖F (p.1 + t, p.2)‖ * ‖G (p.1, p.2 + t)‖ +
          ‖F (p.1 - t, p.2)‖ * ‖G (p.1, p.2 - t)‖ := by
        simp [triangularShiftProduct, sub_eq_add_neg]
      _ ≤ ((M : ℝ) * (1 + (p.1 + t) ^ 2)⁻¹) * M +
          (M * (1 + (p.1 - t) ^ 2)⁻¹) * M := by
        gcongr <;> first | exact bF _ | exact bG _
      _ = _ := by ring
  rw [triangularOddQuotient, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖H p‖ * ((M : ℝ) ^ 2 *
        ((1 + (p.1 + t) ^ 2)⁻¹ + (1 + (p.1 - t) ^ 2)⁻¹)) / |t| := by gcongr
    _ ≤ ‖H p‖ * ((M : ℝ) ^ 2 *
        ((1 + (p.1 + t) ^ 2)⁻¹ + (1 + (p.1 - t) ^ 2)⁻¹)) :=
      div_le_self (by positivity) ht
    _ = _ := by ring

/-- Integrability of the actual odd quotient: local cancellation and decay at infinity. -/
theorem triangularOddQuotient_integrable_of_bounds {H F G : ℝ × ℝ → ℂ} {M : ℝ≥0}
    (hH : Continuous H) (iH : Integrable H) (hF : LipschitzWith M F) (hG : LipschitzWith M G)
    (bF : ∀ p, ‖F p‖ ≤ M) (bG : ∀ p, ‖G p‖ ≤ M)
    (dF : ∀ p : ℝ × ℝ, ‖F p‖ ≤ (M : ℝ) * (1 + p.1 ^ 2)⁻¹) :
    Integrable (triangularOddQuotient H F G) := by
  let j : ℝ → ℝ := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => 1)
  have ij : Integrable j :=
    (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have i0 := (iH.norm.mul_prod ij).const_mul (4 * (M : ℝ) ^ 2)
  have ip := (triangular_integrable_decay iH.norm 1 (Or.inl rfl)).const_mul ((M : ℝ) ^ 2)
  have im := (triangular_integrable_decay iH.norm (-1) (Or.inr rfl)).const_mul ((M : ℝ) ^ 2)
  apply ((i0.add ip).add im).mono'
  · have hFc := hF.continuous
    have hGc := hG.continuous
    apply Measurable.aestronglyMeasurable
    unfold triangularOddQuotient triangularShiftProduct
    fun_prop
  · filter_upwards [] with q
    dsimp only [Pi.add_apply]
    have hb0 := triangularOddQuotient_bound (H := H) hF hG bF bG q.1 q.2
    have hp0 : 0 ≤ (M : ℝ) ^ 2 * (‖H q.1‖ * (1 + (q.1.1 + q.2) ^ 2)⁻¹) := by positivity
    have hm0 : 0 ≤ (M : ℝ) ^ 2 * (‖H q.1‖ * (1 + (q.1.1 - q.2) ^ 2)⁻¹) := by positivity
    by_cases ht : q.2 ∈ Set.Icc (-1 : ℝ) 1
    · simp only [j, Set.indicator_of_mem ht, mul_one, one_mul, neg_one_mul, ← sub_eq_add_neg]
      nlinarith
    · have habs : 1 ≤ |q.2| := by
        have hnot : ¬ |q.2| ≤ 1 := by simpa only [abs_le, Set.mem_Icc] using ht
        exact le_of_lt (lt_of_not_ge hnot)
      have hb := triangularOddQuotient_tail_bound (H := H) dF bG q.1 q.2 habs
      simp only [j, Set.indicator_of_notMem ht, mul_zero, zero_add, one_mul,
        neg_one_mul, ← sub_eq_add_neg]
      nlinarith

/-- Source Section 3: Schwartz inputs have an integrable odd difference quotient. -/
theorem triangularOddQuotient_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Integrable (triangularOddQuotient H F G) := by
  obtain ⟨MF, hF, bF, dF⟩ := triangular_schwartz_bounds F
  obtain ⟨MG, hG, bG, _⟩ := triangular_schwartz_bounds G
  have hMF : MF ≤ MF + MG := le_add_of_nonneg_right zero_le
  have hMG : MG ≤ MF + MG := le_add_of_nonneg_left zero_le
  apply triangularOddQuotient_integrable_of_bounds H.continuous H.integrable
    (hF.weaken hMF) (hG.weaken hMG)
  · intro p; exact (bF p).trans (NNReal.coe_le_coe.mpr hMF)
  · intro p; exact (bG p).trans (NNReal.coe_le_coe.mpr hMG)
  · intro p
    exact (dF p).trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hMF) (by positivity))

/-- Reflection in the singular coordinate preserves volume. -/
theorem triangular_reflection_preserving :
    MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => (q.1, -q.2)) := by
  exact (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- The singular coordinate is nonzero almost everywhere. -/
theorem triangular_snd_ne_zero : ∀ᵐ q : (ℝ × ℝ) × ℝ, q.2 ≠ 0 :=
  Measure.quasiMeasurePreserving_snd.ae
    (show ∀ᵐ t : ℝ, t ≠ 0 from by simp [ae_iff])

/-- Candidate principal value, expressed by its absolutely integrable cancellation. -/
def triangularPV (H F G : SchwartzMap (ℝ × ℝ) ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * ∫ q, triangularOddQuotient H F G q

/-- The cancelled scale kernels converge to the principal-value candidate. -/
theorem triangular_cancelled_scale_tendsto (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (fun n : ℕ => (2 : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, triangularOddQuotient H F G q * ((q.2 *
      Kern 3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) q.2 : ℝ) : ℂ)) atTop (𝓝 ((triangularKernelCoefficient :
      ℂ) * triangularPV H F G)) := by
  have h := (triangular_kernel_pairing_tendsto
    (triangularOddQuotient_integrable H F G) measurable_snd triangular_snd_ne_zero).const_mul
      (2 : ℂ)⁻¹
  simpa [triangularPV, mul_left_comm] using h

/-- Absolute integrability of the unweighted Schwartz product in sheared coordinates. -/
theorem triangular_product_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * triangularShiftProduct F G q.1 q.2) := by
  obtain ⟨MF, _, _, dF⟩ := triangular_schwartz_bounds F
  obtain ⟨MG, _, bG, _⟩ := triangular_schwartz_bounds G
  have hi := (triangular_integrable_decay H.integrable.norm 1 (Or.inl rfl)).const_mul
    ((MF : ℝ) * MG)
  apply hi.mono'
  · apply Measurable.aestronglyMeasurable
    unfold triangularShiftProduct
    fun_prop
  · filter_upwards [] with q
    have hb := mul_le_mul (dF (q.1.1 + q.2, q.1.2)) (bG (q.1.1, q.1.2 + q.2))
      (norm_nonneg _) (by positivity)
    dsimp at hb
    simp only [triangularShiftProduct, norm_mul, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (H q.1))]

/-- Symmetrization of any integrable function in the singular coordinate. -/
theorem triangular_integral_symmetrize {f : (ℝ × ℝ) × ℝ → ℂ} (hf : Integrable f) :
    ∫ q, f q = (2 : ℂ)⁻¹ * ∫ q, (f q + f (q.1, -q.2)) := by
  have hi : Integrable (fun q : (ℝ × ℝ) × ℝ => f (q.1, -q.2)) :=
    triangular_reflection_preserving.integrable_comp_of_integrable hf
  have he : MeasurableEmbedding (fun q : (ℝ × ℝ) × ℝ => (q.1, -q.2)) :=
    (Homeomorph.prodCongr (Homeomorph.refl (ℝ × ℝ)) (Homeomorph.neg
        ℝ)).isClosedEmbedding.measurableEmbedding
  rw [integral_add hf hi, triangular_reflection_preserving.integral_comp he]; ring

/-- Symmetric hard truncations of the Hilbert kernel. -/
def triangularTruncation (H F G : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) : ℂ :=
  ∫ q : (ℝ × ℝ) × ℝ, if ε < |q.2| then
    H q.1 * triangularShiftProduct F G q.1 q.2 / (q.2 : ℂ) else 0

/-- Every positive hard truncation is an absolutely convergent integral. -/
theorem triangular_truncation_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => if ε < |q.2| then H q.1 * triangularShiftProduct F G q.1
      q.2 / (q.2 : ℂ) else 0) := by
  have hi := (triangular_product_integrable H F G).mul_bdd (c := ε⁻¹)
    (g := fun q : (ℝ × ℝ) × ℝ => if ε < |q.2| then (q.2 : ℂ)⁻¹ else 0)
    (by
      apply Measurable.aestronglyMeasurable
      exact Measurable.ite (measurableSet_lt measurable_const measurable_snd.abs)
        (by fun_prop) measurable_const) (by
      filter_upwards [] with q
      split_ifs with h
      · simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs]
        exact inv_anti₀ hε h.le
      · simp only [norm_zero, inv_nonneg]; positivity)
  simpa only [mul_ite, mul_zero, div_eq_mul_inv] using hi

/-- Reflection turns a hard truncation into an integrable odd difference quotient. -/
theorem triangularTruncation_eq (H F G : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ} (hε : 0 < ε) :
    triangularTruncation H F G ε = (2 : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, if ε < |q.2| then
      triangularOddQuotient H F G q else 0 := by
  rw [triangularTruncation, triangular_integral_symmetrize (triangular_truncation_integrable H F G
      hε)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [abs_neg, Complex.ofReal_neg]
  split_ifs <;> simp [triangularOddQuotient]; ring

/-- Source equation `dist`: symmetric hard truncations converge for Schwartz inputs. -/
theorem triangularTruncation_tendsto (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (triangularTruncation H F G) (𝓝[>] (0 : ℝ)) (𝓝 (triangularPV H F G)) := by
  have hi := triangularOddQuotient_integrable H F G
  have hc : Tendsto (fun ε : ℝ => ∫ q : (ℝ × ℝ) × ℝ,
      if ε < |q.2| then triangularOddQuotient H F G q else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q, triangularOddQuotient H F G q)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun q => ‖triangularOddQuotient H F G q‖)
    · filter_upwards [] with ε
      exact hi.aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const measurable_snd.abs)
    · filter_upwards [] with ε
      filter_upwards [] with q
      split_ifs <;> simp
    · exact hi.norm
    · filter_upwards [triangular_snd_ne_zero] with q hq
      have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < |q.2| :=
        (eventually_lt_nhds (abs_pos.mpr hq)).filter_mono nhdsWithin_le_nhds
      exact tendsto_const_nhds.congr' (he.mono fun ε hε => (ite_eq_left hε).symm)
  apply (hc.const_mul (2 : ℂ)⁻¹).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (triangularTruncation_eq H F G hε).symm

/-- The third-derivative Gaussian interval kernels are odd. -/
theorem triangular_Kern_odd {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (t : ℝ) :
    Kern 3 a b (-t) = -Kern 3 a b t := by
  rw [Kern_eq, Kern_eq, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs; rw [Set.uIcc_of_le hab] at hs
  have hp : 0 < (63 / 20 : ℝ) * s := mul_pos (by norm_num) (ha.trans_le hs.1)
  simp only [kernIntegrand, triangular_gaussian_third hp, gaussian, neg_sq]; ring

/-- Absolute convergence of a Gaussian scale pairing for Schwartz inputs. -/
theorem triangular_scale_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern 3 a b
      q.2 : ℂ)) := by
  obtain ⟨C, hC⟩ := abs_Kern_le 3 ha hab
  apply (triangular_product_integrable H F G).mul_bdd (c := C)
  · exact (Complex.continuous_ofReal.comp ((continuous_Kern 3 ha hab).comp
      continuous_snd)).aestronglyMeasurable
  · filter_upwards [] with q
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hC q.2

/-- The Gaussian pairing agrees with the cancelled expression. -/
theorem triangular_scale_eq (H F G : SchwartzMap (ℝ × ℝ) ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ q : (ℝ × ℝ) × ℝ, H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern 3 a b q.2 : ℂ)) = (2
      : ℂ)⁻¹ * ∫ q : (ℝ × ℝ) × ℝ, triangularOddQuotient H F G q * ((q.2 * Kern 3 a b q.2 : ℝ) : ℂ)
          := by
  rw [triangular_integral_symmetrize (triangular_scale_integrable H F G ha hab)]
  congr 1
  apply integral_congr_ae
  filter_upwards [triangular_snd_ne_zero] with q hq
  simp only [triangular_Kern_odd ha hab, Complex.ofReal_neg, triangularOddQuotient,
    Complex.ofReal_mul]
  have hz : (q.2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  field_simp; ring

/-- Source equation `dist`: the Gaussian scale limit is the symmetric principal value. -/
theorem triangular_scale_tendsto (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (fun n : ℕ => ∫ q : (ℝ × ℝ) × ℝ, H q.1 * triangularShiftProduct F G q.1 q.2 * (Kern
      3 ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) q.2 : ℂ)) atTop (𝓝 ((triangularKernelCoefficient : ℂ) *
      triangularPV H F G)) := by
  apply (triangular_cancelled_scale_tendsto H F G).congr
  intro n
  apply (triangular_scale_eq H F G (by positivity) _).symm
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  exact ((inv_le_one₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr hn).trans hn

/-- The planar coordinate change for the second source input. -/
def triangularPlaneEquiv : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (p.2, -p.1 - p.2)
  invFun p := (-p.1 - p.2, p.1)
  left_inv p := by ext <;> dsimp; ring
  right_inv p := by ext <;> dsimp; ring
  map_add' p q := by ext <;> simp; ring
  map_smul' c p := by ext <;> simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Pullback of the second input under `(r,s) ↦ (s,-r-s)`. -/
def triangularPullback₁ : SchwartzMap (ℝ × ℝ) ℂ →L[ℂ] SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ triangularPlaneEquiv

/-- Pullback of the third input under `(r,s) ↦ (-r-s,r)`. -/
def triangularPullback₂ : SchwartzMap (ℝ × ℝ) ℂ →L[ℂ] SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ triangularPlaneEquiv.symm

/-- The volume-preserving substitution `z = -x-y-t`. -/
def triangularSpaceEquiv : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun q := (q.1, -q.1.1 - q.1.2 - q.2)
  invFun q := (q.1, -q.1.1 - q.1.2 - q.2)
  left_inv q := by ext <;> dsimp; ring
  right_inv q := by ext <;> dsimp; ring
  map_add' p q := by ext <;> simp; ring
  map_smul' c p := by ext <;> simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem triangularSpaceEquiv_preserving : MeasurePreserving triangularSpaceEquiv := by
  apply (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
    (g := fun p t => -p.1 - p.2 - t) (μc := volume) (μd := volume) (by fun_prop)
  filter_upwards [] with p
  convert ((measurePreserving_add_left volume (-p.1 - p.2)).comp
    (Measure.measurePreserving_neg volume)).map_eq using 1
  simp only [Function.comp_def, sub_eq_add_neg]

/-- Source Theorem 1: symmetric truncation of the displayed triangular integral. -/
def triangularHilbertTruncation (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) : ℂ :=
  ∫ q : (ℝ × ℝ) × ℝ, if ε < |q.1.1 + q.1.2 + q.2| then
    F₀ q.1 * F₁ (q.1.2, q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ)
    else 0

/-- The source principal value, whose defining truncation limit is proved below. -/
def triangularHilbert (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) : ℂ :=
  -triangularPV F₀ (triangularPullback₁ F₁) (triangularPullback₂ F₂)

/-- The coordinate substitution identifies the two truncated integrands pointwise. -/
theorem triangularHilbert_integrand_comp (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ)
    (q : (ℝ × ℝ) × ℝ) :
    (let r := triangularSpaceEquiv q
     if ε < |r.1.1 + r.1.2 + r.2| then
       F₀ r.1 * F₁ (r.1.2, r.2) * F₂ (r.2, r.1.1) / ((r.1.1 + r.1.2 + r.2 : ℝ) : ℂ) else 0) =
    -(if ε < |q.2| then F₀ q.1 *
      triangularShiftProduct (triangularPullback₁ F₁) (triangularPullback₂ F₂) q.1 q.2 /
        (q.2 : ℂ) else 0) := by
  have he : q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2) = -q.2 := by ring
  change (if ε < |q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2)| then _ else _) = _
  rw [he, abs_neg]
  split_ifs
  swap
  · simp only [neg_zero]
  change F₀ q.1 * F₁ (q.1.2, -q.1.1 - q.1.2 - q.2) *
      F₂ (-q.1.1 - q.1.2 - q.2, q.1.1) /
      ((q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2) : ℝ) : ℂ) =
    -(F₀ q.1 * (F₁ (q.1.2, -(q.1.1 + q.2) - q.1.2) *
      F₂ (-q.1.1 - (q.1.2 + q.2), q.1.1)) / (q.2 : ℂ))
  have he₁ : -(q.1.1 + q.2) - q.1.2 = -q.1.1 - q.1.2 - q.2 := by ring
  have he₂ : -q.1.1 - (q.1.2 + q.2) = -q.1.1 - q.1.2 - q.2 := by ring
  rw [he, he₁, he₂, Complex.ofReal_neg]; ring

theorem triangularHilbertTruncation_eq (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) :
    triangularHilbertTruncation F₀ F₁ F₂ ε = -triangularTruncation F₀ (triangularPullback₁ F₁)
      (triangularPullback₂ F₂) ε := by
  unfold triangularHilbertTruncation; rw [← triangularSpaceEquiv_preserving.integral_comp
    triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding]
  unfold triangularTruncation; rw [← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall (triangularHilbert_integrand_comp F₀ F₁ F₂
      ε))

/-- The source's positive hard truncations are absolutely convergent. -/
theorem triangularHilbertTruncation_integrable (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => if ε < |q.1.1 + q.1.2 + q.2| then F₀ q.1 * F₁ (q.1.2,
      q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ) else 0) := by
  apply (triangularSpaceEquiv_preserving.integrable_comp_emb
    triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding).mp
  convert (triangular_truncation_integrable F₀ (triangularPullback₁ F₁)
    (triangularPullback₂ F₂) hε).neg using 1
  exact funext (triangularHilbert_integrand_comp F₀ F₁ F₂ ε)

/-- Source Theorem 1: the displayed principal value exists for every Schwartz triple. -/
theorem triangularHilbert_principal_value (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (triangularHilbertTruncation F₀ F₁ F₂) (𝓝[>] (0 : ℝ)) (𝓝 (triangularHilbert F₀ F₁
      F₂)) := by
  exact ((triangularTruncation_tendsto F₀ (triangularPullback₁ F₁)
    (triangularPullback₂ F₂)).neg).congr (fun ε => (triangularHilbertTruncation_eq F₀ F₁ F₂ ε).symm)

/-- The measurable identification of three real coordinates with `(ℝ × ℝ) × ℝ`. -/
def fin3Equiv : (Fin 3 → ℝ) ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow).trans
      MeasurableEquiv.prodComm)

lemma measurePreserving_fin3Equiv :
    MeasurePreserving fin3Equiv volume ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have h2 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  have h3 := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (ℝ × ℝ)))
  exact h3.comp (h2.comp h1)

/-- The Gaussian pairing integrand for Schwartz inputs on the product coordinates. -/
def sourceGaussianPairing (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ) (a b : ℝ)
    (q : (ℝ × ℝ) × ℝ) : ℂ :=
  F 0 q.1 * F 1 (q.1.2, q.2) * F 2 (q.2, q.1.1) *
    (Kern 3 a b (q.1.1 + q.1.2 + q.2) : ℂ)

lemma sourceGaussianPairing_comp (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (q : (ℝ × ℝ) × ℝ) :
    sourceGaussianPairing F a b (triangularSpaceEquiv q) =
      -(F 0 q.1 * triangularShiftProduct (triangularPullback₁ (F 1))
        (triangularPullback₂ (F 2)) q.1 q.2 * (Kern 3 a b q.2 : ℂ)) := by
  change F 0 q.1 * F 1 (q.1.2, -q.1.1 - q.1.2 - q.2) *
      F 2 (-q.1.1 - q.1.2 - q.2, q.1.1) *
      (Kern 3 a b (q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2)) : ℂ) =
    -(F 0 q.1 * (F 1 (q.1.2, -(q.1.1 + q.2) - q.1.2) *
      F 2 (-q.1.1 - (q.1.2 + q.2), q.1.1)) * (Kern 3 a b q.2 : ℂ))
  rw [show q.1.1 + q.1.2 + (-q.1.1 - q.1.2 - q.2) = -q.2 by ring,
    triangular_Kern_odd ha hab, Complex.ofReal_neg]
  rw [show -(q.1.1 + q.2) - q.1.2 = -q.1.1 - q.1.2 - q.2 by ring,
    show -q.1.1 - (q.1.2 + q.2) = -q.1.1 - q.1.2 - q.2 by ring]
  ring

lemma sourceGaussian_schwartz_integrable (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (sourceGaussianIntegrand (fun v => F v) a b) := by
  have hi : Integrable (sourceGaussianPairing F a b) := by
    apply (triangularSpaceEquiv_preserving.integrable_comp_emb
      triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding).mp
    convert (triangular_scale_integrable (F 0) (triangularPullback₁ (F 1))
      (triangularPullback₂ (F 2)) ha hab).neg using 1
    exact funext (sourceGaussianPairing_comp F ha hab)
  exact (measurePreserving_fin3Equiv.integrable_comp_emb
    fin3Equiv.measurableEmbedding).mpr hi

lemma sourceGaussian_integral_eq (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, sourceGaussianIntegrand (fun v => F v) a b x) =
      -(∫ q : (ℝ × ℝ) × ℝ, F 0 q.1 *
        triangularShiftProduct (triangularPullback₁ (F 1)) (triangularPullback₂ (F 2))
          q.1 q.2 * (Kern 3 a b q.2 : ℂ)) := by
  change (∫ x, sourceGaussianPairing F a b (fin3Equiv x)) = _
  rw [measurePreserving_fin3Equiv.integral_comp fin3Equiv.measurableEmbedding]
  change (∫ q, sourceGaussianPairing F a b q) = _
  conv_lhs => rw [← triangularSpaceEquiv_preserving.integral_comp
    triangularSpaceEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding]
  rw [← integral_neg]
  exact integral_congr_ae (Eventually.of_forall (sourceGaussianPairing_comp F ha hab))

/-- The norm bound for the principal value after rescaling the Gaussian estimate. -/
def triangularBoundConstant : ℝ := 3 * heatBoundConstant / triangularKernelCoefficient

lemma triangularBoundConstant_nonneg : 0 ≤ triangularBoundConstant := by
  exact div_nonneg (mul_nonneg (by norm_num) heatBoundConstant_nonneg)
    triangularKernelCoefficient_pos.le

theorem triangularHilbert_bound (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    ‖triangularHilbert F₀ F₁ F₂‖ ≤ triangularBoundConstant *
      (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal := by
  let F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ := ![F₀, F₁, F₂]
  have hlim : Tendsto
      (fun n : ℕ => ∫ x, sourceGaussianIntegrand (fun v => F v)
        ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) x) atTop
      (𝓝 ((triangularKernelCoefficient : ℂ) * triangularHilbert F₀ F₁ F₂)) := by
    convert (triangular_scale_tendsto F₀ (triangularPullback₁ F₁)
      (triangularPullback₂ F₂)).neg using 1
    · ext n
      exact sourceGaussian_integral_eq F (by positivity) (by
        have h : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
        exact ((inv_le_one₀ (by positivity)).mpr h).trans h)
    · simp [triangularHilbert]
  have hb : ‖(triangularKernelCoefficient : ℂ) * triangularHilbert F₀ F₁ F₂‖ ≤
      3 * heatBoundConstant *
        (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal := by
    apply le_of_tendsto' hlim.norm
    intro n
    have ha : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    have hab : ((n : ℝ) + 1)⁻¹ ≤ (n : ℝ) + 1 := by
      have h : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
      exact ((inv_le_one₀ (by positivity)).mpr h).trans h
    have h := sourceGaussian_bound (fun v => F v) (fun v => (F v).continuous)
      (fun v => (F v).memLp 3) ha hab (sourceGaussian_schwartz_integrable F ha hab)
    simpa [F, Fin.prod_univ_succ, mul_assoc] using h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos triangularKernelCoefficient_pos] at hb
  have hd := (le_div_iff₀ triangularKernelCoefficient_pos).mpr
    (show ‖triangularHilbert F₀ F₁ F₂‖ * triangularKernelCoefficient ≤
      3 * heatBoundConstant *
        (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal from by
      simpa only [mul_comm] using hb)
  convert hd using 1
  unfold triangularBoundConstant
  ring

theorem triangularPV_add_1 (H F G H' : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV (H + H') F G = triangularPV H F G + triangularPV H' F G := by
  have he : triangularOddQuotient ((H + H') : SchwartzMap (ℝ × ℝ) ℂ) F G =
      fun q => triangularOddQuotient H F G q + triangularOddQuotient H' F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.add_apply]; ring
  simp only [triangularPV, he, integral_add
    (triangularOddQuotient_integrable H F G) (triangularOddQuotient_integrable H' F G)]; ring

/-- Complex homogeneity in input 1 of the principal-value formula. -/
theorem triangularPV_smul_1 (c : ℂ) (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV (c • H) F G = c • triangularPV H F G := by
  have he : triangularOddQuotient ((c • H) : SchwartzMap (ℝ × ℝ) ℂ) F G =
      fun q => c * triangularOddQuotient H F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.smul_apply,
        smul_eq_mul]; ring
  simp only [triangularPV, he, integral_const_mul, smul_eq_mul]; ring

/-- Additivity in input 2 of the absolutely convergent principal-value formula. -/
theorem triangularPV_add_2 (H F G F' : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H (F + F') G = triangularPV H F G + triangularPV H F' G := by
  have he : triangularOddQuotient H ((F + F') : SchwartzMap (ℝ × ℝ) ℂ) G =
      fun q => triangularOddQuotient H F G q + triangularOddQuotient H F' G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.add_apply]; ring
  simp only [triangularPV, he, integral_add
    (triangularOddQuotient_integrable H F G) (triangularOddQuotient_integrable H F' G)]; ring

/-- Complex homogeneity in input 2 of the principal-value formula. -/
theorem triangularPV_smul_2 (c : ℂ) (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H (c • F) G = c • triangularPV H F G := by
  have he : triangularOddQuotient H ((c • F) : SchwartzMap (ℝ × ℝ) ℂ) G =
      fun q => c * triangularOddQuotient H F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.smul_apply,
        smul_eq_mul]; ring
  simp only [triangularPV, he, integral_const_mul, smul_eq_mul]; ring

/-- Additivity in input 3 of the absolutely convergent principal-value formula. -/
theorem triangularPV_add_3 (H F G G' : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H F (G + G') = triangularPV H F G + triangularPV H F G' := by
  have he : triangularOddQuotient H F ((G + G') : SchwartzMap (ℝ × ℝ) ℂ) =
      fun q => triangularOddQuotient H F G q + triangularOddQuotient H F G' q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.add_apply]; ring
  simp only [triangularPV, he, integral_add
    (triangularOddQuotient_integrable H F G) (triangularOddQuotient_integrable H F G')]; ring

/-- Complex homogeneity in input 3 of the principal-value formula. -/
theorem triangularPV_smul_3 (c : ℂ) (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H F (c • G) = c • triangularPV H F G := by
  have he : triangularOddQuotient H F ((c • G) : SchwartzMap (ℝ × ℝ) ℂ) =
      fun q => c * triangularOddQuotient H F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.smul_apply,
        smul_eq_mul]; ring
  simp only [triangularPV, he, integral_const_mul, smul_eq_mul]; ring

/-- The principal value is complex trilinear on Schwartz functions. -/
def triangularPVLinear :
    SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun H F => {
      toFun := fun G => triangularPV H F G
      map_add' := fun G G' => triangularPV_add_3 H F G G'
      map_smul' := fun c G => triangularPV_smul_3 c H F G })
    (fun H H' F => by ext G; exact triangularPV_add_1 H F G H')
    (fun c H F => by ext G; exact triangularPV_smul_1 c H F G)
    (fun H F F' => by ext G; exact triangularPV_add_2 H F G F')
    (fun c H F => by ext G; exact triangularPV_smul_2 c H F G)

/-- Source Theorem 1: the triangular Hilbert principal value as a trilinear map. -/
def triangularHilbertLinear :
    SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] ℂ :=
  -((triangularPVLinear.compl₂ triangularPullback₁.toLinearMap).compr₂
    (LinearMap.lcomp ℂ ℂ triangularPullback₂.toLinearMap))

@[simp]
theorem triangularHilbertLinear_apply (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularHilbertLinear F₀ F₁ F₂ = triangularHilbert F₀ F₁ F₂ := rfl

section DenseExtension

variable {𝕜 E V W : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace
    W]

/-- Extend a bounded bilinear form along a dense linear map. -/
theorem triangular_bilinear_dense_extension (e : E →ₗ[𝕜] V) (hd : DenseRange e)
    (B : E →ₗ[𝕜] E →ₗ[𝕜] W) {C : ℝ} (hC : 0 ≤ C) (hB : ∀ a b, ‖B a b‖ ≤ C * ‖e a‖ * ‖e b‖) :
    ∃ B' : V →L[𝕜] V →L[𝕜] W, (∀ a b, B' (e a) (e b) = B a b) ∧ ∀ x, ‖B' x‖ ≤ C * ‖x‖ := by
  have hb₂ : ∀ a b, ‖B a b‖ ≤ (C * ‖e a‖) * ‖e b‖ := hB
  let B₁ : E →ₗ[𝕜] (V →L[𝕜] W) :=
    { toFun := fun a => (B a).extendOfNorm e
      map_add' := fun a a' => by
        apply LinearMap.extendOfNorm_unique hd (C * ‖e (a + a')‖) (hb₂ (a + a'))
        ext b
        simp [LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a⟩, LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a'⟩]
      map_smul' := fun r a => by
        apply LinearMap.extendOfNorm_unique hd (C * ‖e (r • a)‖) (hb₂ (r • a))
        ext b
        simp [LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a⟩] }
  have hB₁ : ∀ a b, B₁ a (e b) = B a b := fun a b => LinearMap.extendOfNorm_eq hd ⟨_, hb₂ a⟩ b
  have hb₁ : ∀ a, ‖B₁ a‖ ≤ C * ‖e a‖ := fun a =>
    LinearMap.opNorm_extendOfNorm_le hd (by positivity) (hb₂ a)
  refine ⟨B₁.extendOfNorm e, fun a b => ?_, LinearMap.norm_extendOfNorm_apply_le hd C hb₁⟩
  rw [LinearMap.extendOfNorm_eq hd ⟨_, hb₁⟩ a, hB₁]

/-- Source Theorem 1: a norm-controlled trilinear map extends uniquely along a dense linear map. -/
theorem triangular_trilinear_dense_extension (e : E →ₗ[𝕜] V) (hd : DenseRange e)
    (T : E →ₗ[𝕜] E →ₗ[𝕜] E →ₗ[𝕜] W) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ a b c, ‖T a b c‖ ≤ C * ‖e a‖ * ‖e b‖ * ‖e c‖) :
    ∃ T' : V →L[𝕜] V →L[𝕜] V →L[𝕜] W, (∀ a b c, T' (e a) (e b) (e c) = T a b c) ∧ (∀ x y z, ‖T'
      x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) ∧ ∀ S : V →L[𝕜] V →L[𝕜] V →L[𝕜] W, (∀ a b c, S (e a) (e b) (e
      c) = T a b c) → S = T' := by
  have hb₃ : ∀ a b c, ‖T a b c‖ ≤ (C * ‖e a‖ * ‖e b‖) * ‖e c‖ := hT
  have hT₁e : ∀ a b c, (T a b).extendOfNorm e (e c) = T a b c := fun a b c =>
    LinearMap.extendOfNorm_eq hd ⟨_, hb₃ a b⟩ c
  let T₁ : E →ₗ[𝕜] E →ₗ[𝕜] (V →L[𝕜] W) := LinearMap.mk₂ 𝕜
    (fun a b => (T a b).extendOfNorm e)
    (fun a a' b => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e (a + a')‖ * ‖e b‖) (hb₃ (a + a') b)
      ext c; simp [hT₁e])
    (fun r a b => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e (r • a)‖ * ‖e b‖) (hb₃ (r • a) b)
      ext c; simp [hT₁e])
    (fun a b b' => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e a‖ * ‖e (b + b')‖) (hb₃ a (b + b'))
      ext c; simp [hT₁e])
    (fun r a b => by
      apply LinearMap.extendOfNorm_unique hd (C * ‖e a‖ * ‖e (r • b)‖) (hb₃ a (r • b))
      ext c; simp [hT₁e])
  have hT₁ : ∀ a b c, T₁ a b (e c) = T a b c := hT₁e
  have hb₂ : ∀ a b, ‖T₁ a b‖ ≤ C * ‖e a‖ * ‖e b‖ := fun a b =>
    LinearMap.opNorm_extendOfNorm_le hd (by positivity) (hb₃ a b)
  obtain ⟨T', hT', hT'n⟩ := triangular_bilinear_dense_extension e hd T₁ hC hb₂
  refine ⟨T', fun a b c => by rw [hT', hT₁], fun x y z => ?_, fun S hS => ?_⟩
  · calc ‖T' x y z‖ ≤ ‖T' x y‖ * ‖z‖ := (T' x y).le_opNorm z
      _ ≤ ‖T' x‖ * ‖y‖ * ‖z‖ := by gcongr; exact (T' x).le_opNorm y
      _ ≤ C * ‖x‖ * ‖y‖ * ‖z‖ := by gcongr; exact hT'n x
  · have h₃ : ∀ a b, S (e a) (e b) = T' (e a) (e b) := fun a b =>
      ContinuousLinearMap.ext fun z => congrFun (hd.equalizer (S (e a) (e b)).continuous
        (T' (e a) (e b)).continuous (funext fun c => by simp [hS, hT', hT₁])) z
    have h₂ : ∀ a, S (e a) = T' (e a) := fun a =>
      ContinuousLinearMap.ext fun y => congrFun (hd.equalizer (S (e a)).continuous
        (T' (e a)).continuous (funext fun b => h₃ a b)) y
    exact ContinuousLinearMap.ext fun x => congrFun (hd.equalizer S.continuous T'.continuous
      (funext fun a => h₂ a)) x

end DenseExtension

instance triangular_fact_one_le_three : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- The complex Lebesgue space `L³` on the plane. -/
abbrev TriangularL3 := Lp ℂ 3 (volume : Measure (ℝ × ℝ))

/-- Source Theorem 1: unique bounded complex trilinear extension to L3(R2), with the same bound. -/
theorem triangularHilbert_unique_extension :
    ∃ T : TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] ℂ,
      (∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
        T (F₀.toLp 3) (F₁.toLp 3) (F₂.toLp 3) = triangularHilbert F₀ F₁ F₂) ∧
      (∀ f₀ f₁ f₂, ‖T f₀ f₁ f₂‖ ≤ triangularBoundConstant * ‖f₀‖ * ‖f₁‖ * ‖f₂‖) ∧
      ∀ S : TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] TriangularL3 →L[ℂ] ℂ,
        (∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
          S (F₀.toLp 3) (F₁.toLp 3) (F₂.toLp 3) = triangularHilbert F₀ F₁ F₂) → S = T := by
  let e := (SchwartzMap.toLpCLM ℂ ℂ (3 : ℝ≥0∞) (volume : Measure (ℝ × ℝ))).toLinearMap
  have hd : DenseRange e := SchwartzMap.denseRange_toLpCLM (F := ℂ) (by norm_num)
  apply triangular_trilinear_dense_extension e hd triangularHilbertLinear
    triangularBoundConstant_nonneg
  intro F₀ F₁ F₂
  simpa only [triangularHilbertLinear_apply, e, ContinuousLinearMap.coe_coe,
    SchwartzMap.toLpCLM_apply, SchwartzMap.toLp, Lp.norm_toLp] using
    triangularHilbert_bound F₀ F₁ F₂

/-- Source Theorem 1: existence and the uniform L3 bound for the symmetric principal value. -/
theorem triangularHilbert_main :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ, ∃ L : ℂ,
      Tendsto (fun ε : ℝ => ∫ xyz : (ℝ × ℝ) × ℝ,
        let ((x, y), z) := xyz
        if ε < |x + y + z| then
          F₀ (x, y) * F₁ (y, z) * F₂ (z, x) / ↑(x + y + z) else 0)
        (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      ‖L‖ ≤ C * (eLpNorm F₀ 3).toReal * (eLpNorm F₁ 3).toReal * (eLpNorm F₂ 3).toReal :=
  ⟨triangularBoundConstant, triangularBoundConstant_nonneg, fun F₀ F₁ F₂ =>
    ⟨triangularHilbert F₀ F₁ F₂, triangularHilbert_principal_value F₀ F₁ F₂,
      triangularHilbert_bound F₀ F₁ F₂⟩⟩

section Statements

/-! The main theorem restated in terms of the definitions in `Triangular.Defs`. -/

theorem truncatedForm_eq (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) :
    Triangular.truncatedForm F₀ F₁ F₂ ε = triangularHilbertTruncation F₀ F₁ F₂ ε := by
  change ∫ q in {q : (ℝ × ℝ) × ℝ | ε < |q.1.1 + q.1.2 + q.2|},
    F₀ q.1 * F₁ (q.1.2, q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ) = _
  rw [← integral_indicator (measurableSet_lt measurable_const (by fun_prop))]
  unfold triangularHilbertTruncation
  congr 1

theorem T_eq (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    Triangular.T F₀ F₁ F₂ = triangularHilbert F₀ F₁ F₂ :=
  ((triangularHilbert_principal_value F₀ F₁ F₂).congr
    fun ε => (truncatedForm_eq F₀ F₁ F₂ ε).symm).limUnder_eq

theorem tendsto_truncatedForm (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (Triangular.truncatedForm F₀ F₁ F₂) (𝓝[>] 0) (𝓝 (Triangular.T F₀ F₁ F₂)) := by
  rw [T_eq]
  exact (triangularHilbert_principal_value F₀ F₁ F₂).congr fun ε =>
    (truncatedForm_eq F₀ F₁ F₂ ε).symm

theorem triangular_ht_bound :
    ∃ C : ℝ, ∀ F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ,
      ‖Triangular.T F₀ F₁ F₂‖ₑ ≤
        ENNReal.ofReal C * eLpNorm F₀ 3 * eLpNorm F₁ 3 * eLpNorm F₂ 3 := by
  refine ⟨triangularBoundConstant, fun F₀ F₁ F₂ => ?_⟩
  have h := triangularHilbert_bound F₀ F₁ F₂
  rw [T_eq, ← ofReal_norm, ← ENNReal.ofReal_toReal ((F₀.memLp 3 volume).eLpNorm_ne_top),
    ← ENNReal.ofReal_toReal ((F₁.memLp 3 volume).eLpNorm_ne_top),
    ← ENNReal.ofReal_toReal ((F₂.memLp 3 volume).eLpNorm_ne_top),
    ← ENNReal.ofReal_mul triangularBoundConstant_nonneg,
    ← ENNReal.ofReal_mul (by have := triangularBoundConstant_nonneg; positivity),
    ← ENNReal.ofReal_mul (by have := triangularBoundConstant_nonneg; positivity)]
  exact ENNReal.ofReal_le_ofReal h

end Statements

end

end Triangular.Auto
