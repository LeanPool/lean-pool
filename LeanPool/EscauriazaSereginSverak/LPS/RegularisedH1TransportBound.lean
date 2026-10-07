/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevFour
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportPairing
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingMollifierPhysical
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1GradientDerivative
public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcePressureSlice

/-!
# The transport pairing of the regularized `H¹` estimate

The pairing `⟨(J_ε U_ε · ∇) U_ε, ΔU_ε⟩` of the regularized velocity is bounded by
`C ‖∇U_ε‖₂^{3/2} ‖∇²U_ε‖₂^{3/2}` with an absolute constant, by Hölder's inequality with exponents
`(6, 3, 2)`, interpolation of `∇U_ε` between `L²` and `L⁶`, and the homogeneous `H¹ → L⁶`
inequality (`eq:lps-uniform-H1`).
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/--
Interpolation between the whole-space `L²` and `L⁶` norms at the `L³` exponent
(`eq:lps-uniform-H1`).
-/
theorem lps_eLpNorm_three_le_two_six {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 3 volume ≤
      eLpNorm f 2 volume ^ (1 / 2 : ℝ) * eLpNorm f 6 volume ^ (1 / 2 : ℝ) := by
  let w : Vec3 → ℝ := fun x => ‖f x‖ ^ (1 / 2 : ℝ)
  have hw : AEStronglyMeasurable w volume :=
    (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have htriple : ENNReal.HolderTriple 4 12 3 := by
    refine ⟨?_⟩
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      show (12 : ℝ≥0∞) = ENNReal.ofReal 12 by norm_num,
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 12),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
  have hholder : eLpNorm (fun x => w x * w x) 3 volume ≤
      eLpNorm w 4 volume * eLpNorm w 12 volume := by
    simpa [ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (μ := volume) (p := 4) (q := 12) (r := 3)
        (fun a b : ℝ => a * b) 1 continuous_mul hw hw
        (Filter.Eventually.of_forall fun x => by
          simp [w, Real.norm_eq_abs, one_mul]))
  have hprod : (fun x => w x * w x) = fun x => ‖f x‖ := by
    funext x
    change ‖f x‖ ^ (1 / 2 : ℝ) * ‖f x‖ ^ (1 / 2 : ℝ) = ‖f x‖
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num)]
    norm_num
  have hw2 : eLpNorm w 4 volume = eLpNorm f 2 volume ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_norm_rpow f hf (by norm_num : (0 : ℝ) < 1 / 2)]
    have he : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [he]
  have hv6 : eLpNorm w 12 volume = eLpNorm f 6 volume ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_norm_rpow f hf (by norm_num : (0 : ℝ) < 1 / 2)]
    have he : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 6 := by
      rw [show (12 : ℝ≥0∞) = ENNReal.ofReal 12 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12)]
      norm_num
    rw [he]
  rw [hprod, eLpNorm_norm f hf, hw2, hv6] at hholder
  exact hholder

/-- Hölder's inequality for a product in `L²`, with exponents `6` and `3` (`eq:lps-uniform-H1`). -/
theorem lps_eLpNorm_mul_two_le {f g : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun x => f x * g x) 2 volume ≤ eLpNorm f 6 volume * eLpNorm g 3 volume := by
  have htriple : ENNReal.HolderTriple 6 3 2 := by
    refine ⟨?_⟩
    rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by norm_num,
      show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 6),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
  simpa [ENNReal.smul_def, one_mul] using
    (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (μ := volume) (p := 6) (q := 3) (r := 2)
      (fun a b : ℝ => a * b) 1 continuous_mul hf hg
      (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, one_mul]))

/-- The `L²` norm of a square-integrable function is the square root of its integral of squares. -/
theorem lps_eLpNorm_two_toReal {f : Vec3 → ℝ} (hf : MemLp f 2 volume) :
    (eLpNorm f 2 volume).toReal = Real.sqrt (∫ x, f x ^ 2) := by
  have h : lpNorm f 2 volume = Real.sqrt (∫ x, f x ^ 2) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num)
      (by norm_num) hf.aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  rw [← h]
  rfl

/-- The homogeneous `H¹ → L⁶` inequality for a smooth function with square-integrable value and
gradient. -/
theorem lps_smooth_eLpNorm_six_le {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 volume) (hgd : ∀ k, MemLp (spatialDeriv g k) 2 volume) :
    eLpNorm g 6 volume ≤ gagliardoNirenbergSobolevConstant *
      eLpNorm (fun x => vec3EuclideanNorm (fun k => spatialDeriv g k x)) 2 volume := by
  let v : H1Function (Set.univ : Set Vec3) :=
    { toFun := g
      grad := fun x k => spatialDeriv g k x
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hg2
      gradMemL2 := by
        intro k
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn,
          CKN.volumeOn, Measure.restrict_univ] using hgd k
      hasWeakGradient := by
        intro k
        exact HasWeakPartialDerivOn.of_contDiff
          (hg.of_le (by simp)) }
  have hvgrad2 : MemLp v.grad 2 volume :=
    (memLp_pi_iff).2 (fun k => by simpa [v] using hgd k)
  have hgradLe : eLpNorm v.grad 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    rw [← eLpNorm_norm v.grad hvgrad2.aestronglyMeasurable]
    apply eLpNorm_mono_ae_real (hvgrad2.aestronglyMeasurable.norm)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm (v.grad x)
  calc
    _ ≤ gagliardoNirenbergSobolevConstant * eLpNorm v.grad 2 volume := by
      simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
        CKN.weakGradientLpNormOn, Measure.restrict_univ, v] using
        (Classical.choose_spec CKN.sobolev_L6_global).2 v
    _ ≤ _ := mul_le_mul_of_nonneg_left hgradLe (by positivity)

/-- The Euclidean norm of the gradient of a smooth function with square-integrable gradient is
square integrable, with the expected integral of squares. -/
theorem lps_gradNorm_memLp_and_integral {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgd : ∀ k, MemLp (spatialDeriv g k) 2 volume) :
    MemLp (fun x => vec3EuclideanNorm (fun k => spatialDeriv g k x)) 2 volume ∧
    (∫ x, vec3EuclideanNorm (fun k => spatialDeriv g k x) ^ 2) =
      ∑ k : Fin 3, ∫ x, spatialDeriv g k x ^ 2 := by
  set h : Vec3 → ℝ := fun x => vec3EuclideanNorm (fun k => spatialDeriv g k x) with hh
  have hgsm (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g k) := by
    simpa [wordDeriv] using contDiff_wordDeriv hg [k]
  have hhcont : Continuous h := by
    have hc (k : Fin 3) : Continuous (fun x => spatialDeriv g k x ^ 2) := (hgsm k).continuous.pow 2
    exact (continuous_finsetSum _ fun k _ => hc k).sqrt
  have hhmem : MemLp h 2 volume := by
    refine (memLp_finsetSum (Finset.univ : Finset (Fin 3)) fun k _ => (hgd k).norm).mono'
      hhcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have h1 : h x ≤ ∑ k : Fin 3, |spatialDeriv g k x| := by
      have hs : (∑ k : Fin 3, spatialDeriv g k x ^ 2) ≤ (∑ k : Fin 3, |spatialDeriv g k x|) ^ 2
        := by
        simp only [Fin.sum_univ_three]
        nlinarith only [abs_nonneg (spatialDeriv g 0 x), abs_nonneg (spatialDeriv g 1 x),
          abs_nonneg (spatialDeriv g 2 x), sq_abs (spatialDeriv g 0 x),
          sq_abs (spatialDeriv g 1 x), sq_abs (spatialDeriv g 2 x)]
      calc h x = Real.sqrt (∑ k : Fin 3, spatialDeriv g k x ^ 2) := rfl
        _ ≤ Real.sqrt ((∑ k : Fin 3, |spatialDeriv g k x|) ^ 2) := Real.sqrt_le_sqrt hs
        _ = ∑ k : Fin 3, |spatialDeriv g k x| :=
          Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)
    have h0 : 0 ≤ h x := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simpa [Real.norm_eq_abs] using h1
  refine ⟨hhmem, ?_⟩
  have : (fun x => h x ^ 2) = fun x => ∑ k : Fin 3, spatialDeriv g k x ^ 2 := by
    funext x
    exact CKN.Foundation.Heat.vec3EuclideanNorm_sq _
  change (∫ x, h x ^ 2) = _
  rw [this, integral_finsetSum _ fun k _ => (hgd k).integrable_sq]

/-- A smooth function with square-integrable value and gradient lies in `L⁶`. -/
theorem lps_smooth_memLp_six {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 volume) (hgd : ∀ k, MemLp (spatialDeriv g k) 2 volume) :
    MemLp g 6 volume := by
  exact (lps_smooth_eLpNorm_six_le hg hg2 hgd).trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top)
      (lps_gradNorm_memLp_and_integral hg hgd).1.eLpNorm_lt_top)

/-- Real-valued form of the `H¹ → L⁶` inequality:
`‖g‖₆ ≤ S (∑ₖ ‖∂ₖ g‖₂²)^{1/2}`. -/
theorem lps_smooth_six_toReal_le {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg2 : MemLp g 2 volume) (hgd : ∀ k, MemLp (spatialDeriv g k) 2 volume) :
    (eLpNorm g 6 volume).toReal ≤ gagliardoNirenbergSobolevConstant.toReal *
      Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv g k x ^ 2) := by
  obtain ⟨hhmem, hint⟩ := lps_gradNorm_memLp_and_integral hg hgd
  have hmain := lps_smooth_eLpNorm_six_le hg hg2 hgd
  have hne : gagliardoNirenbergSobolevConstant *
      eLpNorm (fun x => vec3EuclideanNorm (fun k => spatialDeriv g k x)) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top CKN.Leray.gagliardoNirenbergSobolevConstant_ne_top hhmem.eLpNorm_ne_top
  calc (eLpNorm g 6 volume).toReal ≤ (gagliardoNirenbergSobolevConstant *
      eLpNorm (fun x => vec3EuclideanNorm (fun k => spatialDeriv g k x)) 2 volume).toReal :=
        ENNReal.toReal_mono hne hmain
    _ = gagliardoNirenbergSobolevConstant.toReal * (eLpNorm
      (fun x => vec3EuclideanNorm (fun k => spatialDeriv g k x)) 2 volume).toReal :=
        ENNReal.toReal_mul
    _ = _ := by rw [lps_eLpNorm_two_toReal hhmem, hint]

/-- Hölder bound for one summand of the transport pairing (`eq:lps-uniform-H1`). -/
theorem lps_transport_term_le {V d L : Vec3 → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV2 : MemLp V 2 volume)
    (hVd : ∀ k, MemLp (spatialDeriv V k) 2 volume)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hd2 : MemLp d 2 volume)
    (hdd : ∀ k, MemLp (spatialDeriv d k) 2 volume) (hL : MemLp L 2 volume) :
    |∫ x, V x * d x * L x| ≤
      gagliardoNirenbergSobolevConstant.toReal * Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv V k x
        ^ 2) *
        (Real.sqrt (∫ x, d x ^ 2) ^ (1 / 2 : ℝ) *
          (gagliardoNirenbergSobolevConstant.toReal *
            Real.sqrt (∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2)) ^ (1 / 2 : ℝ)) *
        Real.sqrt (∫ x, L x ^ 2) := by
  set S := gagliardoNirenbergSobolevConstant.toReal with hS
  have hV6 := lps_smooth_memLp_six hV hV2 hVd
  have hd6 := lps_smooth_memLp_six hd hd2 hdd
  have hdm : AEStronglyMeasurable d volume := hd.continuous.aestronglyMeasurable
  have hVm : AEStronglyMeasurable V volume := hV.continuous.aestronglyMeasurable
  have hd3 : eLpNorm d 3 volume ≤ eLpNorm d 2 volume ^ (1 / 2 : ℝ) * eLpNorm d 6 volume ^ (1 / 2
    : ℝ) :=
    lps_eLpNorm_three_le_two_six hdm
  have hd3fin : eLpNorm d 3 volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hd3
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd2.eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd6.eLpNorm_ne_top)
  have hVd2 : eLpNorm (fun x => V x * d x) 2 volume ≤ eLpNorm V 6 volume * eLpNorm d 3 volume :=
    lps_eLpNorm_mul_two_le hVm hdm
  have hVdfin : eLpNorm (fun x => V x * d x) 2 volume ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hV6.eLpNorm_ne_top hd3fin) hVd2
  have hVdmem : MemLp (fun x => V x * d x) 2 volume := lt_top_iff_ne_top.mpr hVdfin
  -- pairing bound
  have hpair : |∫ x, V x * d x * L x| ≤
      Real.sqrt (∫ x, (V x * d x) ^ 2) * Real.sqrt (∫ x, L x ^ 2) := by
    refine (abs_integral_le_integral_abs).trans ?_
    have h := lps_integral_pairing_le (fun x => |V x * d x|) (fun x => |L x|) hVdmem.abs hL.abs
    have habs : ∫ x, |V x * d x * L x| = ∫ x, |V x * d x| * |L x| := by
      congr 1; funext x; rw [abs_mul]
    have hsq : ∫ x, |V x * d x| ^ 2 = ∫ x, (V x * d x) ^ 2 := by
      congr 1; funext x; exact sq_abs _
    have hsq2 : ∫ x, |L x| ^ 2 = ∫ x, L x ^ 2 := by
      congr 1; funext x; exact sq_abs _
    rw [habs]
    rw [hsq, hsq2] at h
    exact h
  rw [← lps_eLpNorm_two_toReal hVdmem] at hpair
  refine hpair.trans ?_
  have h1 : (eLpNorm (fun x => V x * d x) 2 volume).toReal ≤
      (eLpNorm V 6 volume).toReal * ((eLpNorm d 2 volume).toReal ^ (1 / 2 : ℝ) *
        (eLpNorm d 6 volume).toReal ^ (1 / 2 : ℝ)) := by
    have hfin : eLpNorm V 6 volume * (eLpNorm d 2 volume ^ (1 / 2 : ℝ) *
        eLpNorm d 6 volume ^ (1 / 2 : ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top hV6.eLpNorm_ne_top (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd2.eLpNorm_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hd6.eLpNorm_ne_top))
    have h2 := ENNReal.toReal_mono hfin (hVd2.trans (by gcongr))
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h2
    exact h2
  have hA := lps_smooth_six_toReal_le hV hV2 hVd
  have hB6 := lps_smooth_six_toReal_le hd hd2 hdd
  rw [lps_eLpNorm_two_toReal hd2] at h1
  have hA0 : 0 ≤ (eLpNorm V 6 volume).toReal := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ (eLpNorm d 6 volume).toReal := ENNReal.toReal_nonneg
  have hN0 : 0 ≤ Real.sqrt (∫ x, L x ^ 2) := Real.sqrt_nonneg _
  refine mul_le_mul_of_nonneg_right (h1.trans ?_) hN0
  gcongr

/-- Exponent bookkeeping for the transport bound. -/
theorem lps_core_rpow {S y h : ℝ} (hS : 0 ≤ S) (hy : 0 ≤ y) (hh : 0 ≤ h) :
    S * Real.sqrt y * (Real.sqrt y ^ (1 / 2 : ℝ) * (S * Real.sqrt h) ^ (1 / 2 : ℝ)) *
      Real.sqrt h = S ^ (3 / 2 : ℝ) * y ^ (3 / 4 : ℝ) * h ^ (3 / 4 : ℝ) := by
  have e1 : Real.sqrt y = y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow y
  have e2 : Real.sqrt h = h ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow h
  rw [e1, e2, Real.mul_rpow hS (Real.rpow_nonneg hh _)]
  have a1 : (y ^ (1 / 2 : ℝ)) * (y ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = y ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_mul hy, ← Real.rpow_add' hy (by norm_num)]; norm_num
  have a2 : (h ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ) = h ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_mul hh, ← Real.rpow_add' hh (by norm_num)]; norm_num
  have a3 : S * S ^ (1 / 2 : ℝ) = S ^ (3 / 2 : ℝ) := by
    rcases hS.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · rw [← Real.rpow_one_add' hS (by norm_num)]; norm_num
  calc S * y ^ (1 / 2 : ℝ) * ((y ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) * (S ^ (1 / 2 : ℝ) * (h ^ (1 / 2 :
    ℝ)) ^ (1 / 2 : ℝ))) * h ^ (1 / 2 : ℝ)
      = (S * S ^ (1 / 2 : ℝ)) * ((y ^ (1 / 2 : ℝ)) * (y ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) *
        ((h ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) * h ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [a1, a2, a3]

/-- The transport summand is bounded by `S^{3/2} y^{3/4} h^{3/4}` once the norms of `V`, `d`, `L`
are bounded by `y` and `h` (`eq:lps-uniform-H1`). -/
theorem lps_transport_term_le' {V d L : Vec3 → ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV2 : MemLp V 2 volume)
    (hVd : ∀ k, MemLp (spatialDeriv V k) 2 volume)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hd2 : MemLp d 2 volume)
    (hdd : ∀ k, MemLp (spatialDeriv d k) 2 volume) (hL : MemLp L 2 volume)
    {y0 h0 : ℝ} (hy : 0 ≤ y0) (hh : 0 ≤ h0)
    (h1 : (∑ k : Fin 3, ∫ x, spatialDeriv V k x ^ 2) ≤ y0) (h2 : (∫ x, d x ^ 2) ≤ y0)
    (h3 : (∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2) ≤ h0) (h4 : (∫ x, L x ^ 2) ≤ h0) :
    |∫ x, V x * d x * L x| ≤
      gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) * y0 ^ (3 / 4 : ℝ) * h0 ^ (3 / 4 :
        ℝ) := by
  have hS0 : 0 ≤ gagliardoNirenbergSobolevConstant.toReal := ENNReal.toReal_nonneg
  refine (lps_transport_term_le hV hV2 hVd hd hd2 hdd hL).trans ?_
  rw [← lps_core_rpow hS0 hy hh]
  have p1 : 0 ≤ ∫ x, d x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have p2 : 0 ≤ ∑ k : Fin 3, ∫ x, spatialDeriv d k x ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have p3 : 0 ≤ ∑ k : Fin 3, ∫ x, spatialDeriv V k x ^ 2 :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  have p4 : 0 ≤ ∫ x, L x ^ 2 := integral_nonneg fun x => sq_nonneg _
  gcongr

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The mollified transport velocity has smooth components with all ordered derivatives square
integrable. -/
theorem lps_regR12_V_smooth_memLp {t : ℝ} (ht : 0 ≤ t) :
    (∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => lpsRegV ρ ε hε b hb (x, t) k)) ∧
    (∀ (k : Fin 3) (α : List (Fin 3)),
      MemLp (wordDeriv α (fun x : Vec3 => lpsRegV ρ ε hε b hb (x, t) k)) 2 volume) :=
  lps_regUniformMollifiedVelocity_smooth_memLp ρ ε hε (lpsRegU ρ ε hε b hb) t
    (lps_regR12Velocity_slice_isInJ ρ ε hε b hb t ht).1
    (lps_regR12_slice_smooth ρ ε hε b hb t ht)
    (fun i α => lps_regR12_slice_memLp ρ ε hε b hb t ht i α)

/-- The mollification does not increase the `L²` norm of a first derivative of the velocity. -/
theorem lps_regR12_V_grad_contraction {t : ℝ} (ht : 0 ≤ t) (k j : Fin 3) :
    (∫ x, spatialDeriv (fun y => lpsRegV ρ ε hε b hb (y, t) k) j x ^ 2) ≤
      ∫ x, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) k) j x ^ 2 := by
  obtain ⟨hκ, hκc, hκn, hκ1⟩ := lps_regUniformMollifierKernel_properties ρ ε hε
  have hfun : (fun y => lpsRegV ρ ε hε b hb (y, t) k) =
      convolution (CKN.Leray.regUniformMollifierKernel ρ ε hε)
        (fun y : Vec3 => lpsRegU ρ ε hε b hb (y, t) k)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    funext fun x => lps_regR12_V_eq_conv ρ ε hε b hb ht x k
  have hle := lps_wordDeriv_convolution_eLpNorm_le hκ hκc hκn hκ1
    (lps_regR12_slice_smooth ρ ε hε b hb t ht k)
    (fun α => lps_regR12_slice_memLp ρ ε hε b hb t ht k α) [j]
  rw [← hfun] at hle
  exact lps_integral_sq_le_of_eLpNorm_le
    ((lps_regR12_V_smooth_memLp ρ ε hε b hb ht).2 k [j])
    (lps_regR12_slice_memLp ρ ε hε b hb t ht k [j]) hle


/-- The transport pairing of the regularized velocity is bounded by
`9 S^{3/2} ‖∇U_ε‖₂^{3/2} ‖∇²U_ε‖₂^{3/2}` with an absolute constant (`eq:lps-uniform-H1`). -/
theorem lps_regR12_transportPairing_le {t : ℝ} (ht : 0 ≤ t) :
    |lpsRegTransportPairing ρ ε hε b hb t| ≤
      9 * (gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) *
        lpsRegGradEnergy ρ ε hε b hb t ^ (3 / 4 : ℝ) *
        lpsRegHessEnergy ρ ε hε b hb t ^ (3 / 4 : ℝ)) := by
  set y := lpsRegGradEnergy ρ ε hε b hb t with hy
  set Dd := lpsRegHessEnergy ρ ε hε b hb t with hDd
  have hy0 : 0 ≤ y := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    integral_nonneg fun x => sq_nonneg _
  have hDd0 : 0 ≤ Dd := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  set C0 := gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) * y ^ (3 / 4 : ℝ) *
    Dd ^ (3 / 4 : ℝ) with hC0
  have hterm (i k : Fin 3) : |∫ x, lpsRegV ρ ε hε b hb (x, t) k *
      spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x *
      lpsRegLap ρ ε hε b hb i t x| ≤ C0 := by
    obtain ⟨hVs, hVL2⟩ := lps_regR12_V_smooth_memLp ρ ε hε b hb ht
    refine lps_transport_term_le' (V := fun x => lpsRegV ρ ε hε b hb (x, t) k)
      (d := fun x => spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x)
      (L := lpsRegLap ρ ε hε b hb i t) (hVs k) (hVL2 k [])
      (fun j => hVL2 k [j])
      (by simpa [wordDeriv] using contDiff_wordDeriv (lps_regR12_slice_smooth ρ ε hε b hb t ht
        i) [k])
      (lps_regR12_slice_memLp ρ ε hε b hb t ht i [k])
      (fun j => lps_regR12_slice_memLp ρ ε hε b hb t ht i [k, j])
      (lps_regR12_lap_memLp ρ ε hε b hb t ht i) hy0 hDd0 ?_ ?_ ?_ ?_
    · calc (∑ j : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegV ρ ε hε b hb (y, t) k) j x ^ 2)
          ≤ ∑ j : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) k) j x ^ 2 :=
            Finset.sum_le_sum fun j _ => lps_regR12_V_grad_contraction ρ ε hε b hb ht k j
        _ ≤ y := by
            refine le_trans ?_ (Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j : Fin 3, ∫ x,
              spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i') j x ^ 2)
              (fun i' _ => Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)
              (Finset.mem_univ k))
            exact le_rfl
    · calc (∫ x, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x ^ 2)
          ≤ ∑ j : Fin 3, ∫ x, spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2 :=
            Finset.single_le_sum (f := fun j : Fin 3 => ∫ x,
              spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) j x ^ 2)
              (fun j _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ k)
        _ ≤ y := by
            refine le_trans ?_ (Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j : Fin 3, ∫ x,
              spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i') j x ^ 2)
              (fun i' _ => Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)
              (Finset.mem_univ i))
            exact le_rfl
    · calc (∑ j : Fin 3, ∫ x, spatialDeriv (spatialDeriv
            (fun y => lpsRegU ρ ε hε b hb (y, t) i) k) j x ^ 2)
          ≤ ∑ k' : Fin 3, ∑ j : Fin 3, ∫ x, spatialDeriv (spatialDeriv
            (fun y => lpsRegU ρ ε hε b hb (y, t) i) k') j x ^ 2 :=
            Finset.single_le_sum (f := fun k' : Fin 3 => ∑ j : Fin 3, ∫ x, spatialDeriv
              (spatialDeriv
              (fun y => lpsRegU ρ ε hε b hb (y, t) i) k') j x ^ 2)
              (fun k' _ => Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)
              (Finset.mem_univ k)
        _ ≤ ∑ i' : Fin 3, ∑ k' : Fin 3, ∑ j : Fin 3, ∫ x, spatialDeriv (spatialDeriv
            (fun y => lpsRegU ρ ε hε b hb (y, t) i') k') j x ^ 2 :=
            Finset.single_le_sum (f := fun i' : Fin 3 => ∑ k' : Fin 3, ∑ j : Fin 3, ∫ x,
              spatialDeriv (spatialDeriv
                (fun y => lpsRegU ρ ε hε b hb (y, t) i') k') j x ^ 2)
              (fun i' _ => Finset.sum_nonneg fun k' _ => Finset.sum_nonneg fun j _ =>
                integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
        _ = Dd := rfl
    · calc (∫ x, lpsRegLap ρ ε hε b hb i t x ^ 2)
          ≤ ∑ i' : Fin 3, ∫ x, lpsRegLap ρ ε hε b hb i' t x ^ 2 :=
            Finset.single_le_sum (f := fun i' : Fin 3 => ∫ x, lpsRegLap ρ ε hε b hb i' t x ^ 2)
              (fun i' _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ i)
        _ = Dd := lps_regR12_lap_sq_eq_hess ρ ε hε b hb ht
  have hsplit (i : Fin 3) : (∫ x, lpsRegTransport ρ ε hε b hb i t x * lpsRegLap ρ ε hε b hb i t x) =
      ∑ k : Fin 3, ∫ x, lpsRegV ρ ε hε b hb (x, t) k *
        spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x * lpsRegLap ρ ε hε b hb i t x := by
    have hi (k : Fin 3) : Integrable (fun x => lpsRegV ρ ε hε b hb (x, t) k *
        spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x *
        lpsRegLap ρ ε hε b hb i t x) volume :=
      (lps_regR12_transportTerm_memLp ρ ε hε b hb ht k i).integrable_mul
        (lps_regR12_lap_memLp ρ ε hε b hb t ht i)
    rw [← integral_finsetSum _ fun k _ => hi k]
    congr 1; funext x
    simp only [lpsRegTransport, Finset.sum_mul]
  unfold lpsRegTransportPairing
  simp only [hsplit]
  calc |∑ i : Fin 3, ∑ k : Fin 3, ∫ x, lpsRegV ρ ε hε b hb (x, t) k *
        spatialDeriv (fun y => lpsRegU ρ ε hε b hb (y, t) i) k x * lpsRegLap ρ ε hε b hb i t x|
      ≤ ∑ i : Fin 3, ∑ k : Fin 3, C0 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm i k)
    _ = 9 * C0 := by simp; ring

end

end ESS.LPS

end
