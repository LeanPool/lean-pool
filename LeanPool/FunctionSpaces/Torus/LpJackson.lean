/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.EuclideanConvolution
public import LeanPool.FunctionSpaces.Rd.Approximation.BandJackson
public import LeanPool.FunctionSpaces.Rd.Approximation.BandInverse

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's and Bernstein's inequalities in `L_p(𝕋^d)`

The kernels of `ℝ^d` act on the torus by `(Φ ⋆ f)(t) = ∫ Φ(y) f(t - π y) dy`
(`Torus.econvLp`), and their Fourier transforms at the lattice points are the Fourier multipliers.
This transfers the band-limited approximation of `ℝ^d` to trigonometric polynomials, for every
`1 ≤ p < ∞`.

**Jackson's inequality.** With the kernel `Φ` of `Rd.lpKernel` (`𝓕Φ = 0` for `|ξ| ≥ 2`,
`∫ Φ = 1`), the approximant `J_k f = ∑_{l<r} (-1)^l C(r, l + 1) Φ_{2^k/(l+1)} ⋆ f`
(`Torus.jacksonApprox`) is a trigonometric polynomial of degree `< 2^(k+1)`
(`Torus.jacksonApprox_mem_trigPolyLp`) and an averaged difference,
`f - J_k f = ∫ Φ(z) (-1)^r Δ^r_{π(-2^(-k) z)} f dz` (`Torus.ae_sub_jacksonApprox_eq`). With
`ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` (`Torus.modulus_mul_le`) this gives
`‖f - J_k f‖_p ≤ C ω_r(f, 2^(-k))_p` with the constant of `ℝ^d`
(`Torus.enorm_sub_jacksonApprox_le`).

**Bernstein's inequality.** The band-limiting kernel `Θ_J`, `J = j + #d`, has `𝓕Θ_J = 1` at the
lattice points of degree `< 2^j`, so `Θ_J ⋆ a = a` for every trigonometric polynomial `a` of
degree `< 2^j` (`Torus.econvLp_Theta_eq_self`). Then `Δ^r_{π x} a = (Δ^r_x Θ_J) ⋆ a`, and Young's
inequality with `‖Δ^r_x Θ_J‖_1 ≤ (2^J ‖x‖)^r ‖D^r Θ‖_1` gives
`ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` (`Torus.lpModulus_le_of_mem_trigPolyLp`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter
open scoped ENNReal FourierTransform TorusHaar

open ENNReal (dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### Dilated kernels on the torus -/

/-- **Convolution with a dilation**: `(Φ_c ⋆ f)(t) = ∫ Φ(z) f(t - π(c^(-1) z)) dz` for `c > 0`
(substitute `y = c^(-1) z`). -/
theorem econv_dilate_apply (Φ : EuclideanSpace ℝ d → ℂ) (f : UnitAddTorus d → ℂ) {c : ℝ}
    (hc : 0 < c) (t : UnitAddTorus d) :
    econv (Rd.dilate c Φ) f t = ∫ z, Φ z * f (t - proj (c⁻¹ • z)) := by
  have hpow : (0 : ℝ) < c ^ Module.finrank ℝ (EuclideanSpace ℝ d) := pow_pos hc _
  rw [econv]
  have h : ∀ y, Rd.dilate c Φ y * f (t - proj y) =
      (((c ^ Module.finrank ℝ (EuclideanSpace ℝ d) : ℝ)) : ℂ) *
        (fun z => Φ z * f (t - proj (c⁻¹ • z))) (c • y) := fun y => by
    simp only [Rd.dilate, inv_smul_smul₀ hc.ne']
    ring
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_smul volume
      (fun z => Φ z * f (t - proj (c⁻¹ • z))) c,
    abs_of_pos (inv_pos.2 hpow), Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ hpow.ne', Complex.ofReal_one, one_mul]

/-- **The averaged translates are integrable**: for integrable `Φ`, `f ∈ L_1(𝕋)`, `c > 0` and
almost every `t`, `z ↦ Φ(z) f(t - π(c^(-1) z))` is integrable. -/
theorem ae_integrable_dilate_mul {Φ : EuclideanSpace ℝ d → ℂ} (hΦ : Integrable Φ)
    {f : UnitAddTorus d → ℂ} (hf : Measurable f) (hfi : Integrable f volume) {c : ℝ}
    (hc : 0 < c) : ∀ᵐ t ∂volume, Integrable (fun z => Φ z * f (t - proj (c⁻¹ • z))) := by
  have hpow : (0 : ℝ) < c ^ Module.finrank ℝ (EuclideanSpace ℝ d) := pow_pos hc _
  filter_upwards [ae_integrable_econv (Rd.integrable_dilate hΦ hc.ne') hf hfi] with t ht
  have h2 := (ht.comp_smul (inv_ne_zero hc.ne')).const_mul
    ((((c ^ Module.finrank ℝ (EuclideanSpace ℝ d))⁻¹ : ℝ)) : ℂ)
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only [Rd.dilate, smul_inv_smul₀ hc.ne']
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpow.ne',
    Complex.ofReal_one, one_mul]

omit [Fintype d] in
/-- **Averaged differences on the torus**: `(-1)^r Δ^r_{π(-c^(-1) z)} f(t) =
f(t) - ∑_{l<r} (-1)^l C(r, l + 1) f(t - π((c/(l+1))^(-1) z))`. -/
theorem neg_one_pow_mul_higherDiff_proj (f : UnitAddTorus d → ℂ) (r : ℕ) (c : ℝ)
    (z : EuclideanSpace ℝ d) (t : UnitAddTorus d) :
    (-1 : ℂ) ^ r * (fwdDiff (proj (-c⁻¹ • z)))^[r] f t =
      f t - ∑ l ∈ Finset.range r,
        Rd.jacksonCoeff r l * f (t - proj ((c / ((l : ℝ) + 1))⁻¹ • z)) := by
  have hsmul : ∀ l : ℕ, (l + 1) • proj (-c⁻¹ • z) = -proj ((c / ((l : ℝ) + 1))⁻¹ • z) :=
    fun l => by
      rw [← map_nsmul, ← map_neg, ← Nat.cast_smul_eq_nsmul ℝ, inv_div, smul_smul, mul_neg,
        neg_smul, div_eq_mul_inv, Nat.cast_succ]
  have h := Rd.neg_one_pow_mul_sum_higherDiff_coeff r (fun l => f (t + l • proj (-c⁻¹ • z)))
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [zsmul_eq_mul]
  push_cast
  rw [h]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsmul l, ← sub_eq_add_neg]

/-! ### The Jackson approximant -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **Jackson approximant on the torus** `J_k f = ∑_{l<r} (-1)^l C(r, l + 1) Φ_{2^k/(l+1)} ⋆ f`,
with the kernel `Φ` of `Rd.lpKernel` on `ℝ^d` acting by `Torus.econvLp`. -/
noncomputable def jacksonApprox (hp : p ≠ ∞) (r k : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  ∑ l ∈ Finset.range r, Rd.jacksonCoeff r l •
    econvLp hp (Rd.integrable_dilate (V := EuclideanSpace ℝ d) Rd.integrable_lpKernel
      (Rd.jacksonScale_pos k l).ne') f

/-- **The Jackson approximant is a trigonometric polynomial of degree `< 2^(k+1)`**:
`𝓕Φ_c(ξ) = 𝓕Φ(ξ/c) = 0` for `‖ξ‖ ≥ 2c`, `c = 2^k/(l+1)`, and `‖m‖ ≥ deg m`. -/
theorem jacksonApprox_mem_trigPolyLp (hp : p ≠ ∞) (r k : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    jacksonApprox hp r k f ∈ trigPolyLp p (2 ^ (k + 1)) := by
  refine Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ _ (econvLp_mem_trigPolyLp hp _ (fun m hm => ?_) f)
  rw [Rd.fourier_dilate _ (Rd.jacksonScale_pos k l), Rd.fourier_lpKernel]
  refine Rd.cutoff_eq_zero one_pos one_lt_two ?_
  have hdeg : (2 : ℝ) ^ (k + 1) ≤ ‖latticeVec m‖ := by
    have h := (Nat.cast_le (α := ℝ)).2 hm
    push_cast at h
    exact h.trans (deg_le_norm_latticeVec m)
  have hl : (1 : ℝ) ≤ (l : ℝ) + 1 := by linarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Rd.jacksonScale_pos k l).le), Rd.jacksonScale,
    inv_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc 2 * 2 ^ k = 1 * 2 ^ (k + 1) := by ring
    _ ≤ ((l : ℝ) + 1) * ‖latticeVec m‖ := by gcongr

/-- **The Jackson approximant as an averaged difference**: for almost every `t`,
`f(t) - J_k f(t) = ∫ Φ(z) (-1)^r Δ^r_{π(-2^(-k) z)} f(t) dz`. -/
theorem ae_sub_jacksonApprox_eq (hp : p ≠ ∞) (r k : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ⇑(f - jacksonApprox hp r k f) =ᵐ[volume] fun t => ∫ z, Rd.lpKernel z *
      ((-1 : ℂ) ^ r * (fwdDiff (proj (-((2 : ℝ) ^ k)⁻¹ • z)))^[r] (f : UnitAddTorus d → ℂ) t) := by
  have hfm := (Lp.stronglyMeasurable f).measurable
  have hfi := (Lp.memLp f).integrable (Fact.out : 1 ≤ p)
  set Φ := Rd.lpKernel (V := EuclideanSpace ℝ d)
  have hJ : ⇑(jacksonApprox hp r k f) =ᵐ[volume] fun t => ∑ l ∈ Finset.range r,
      Rd.jacksonCoeff r l * econv (Rd.dilate (Rd.jacksonScale k l) Φ) f t := by
    unfold jacksonApprox
    refine (Lp.coeFn_finsetSum _ _).trans ((eventuallyEq_sum fun l _ =>
      (Lp.coeFn_smul _ _).trans ((econvLp_apply_ae hp (Rd.integrable_dilate
        (V := EuclideanSpace ℝ d) Rd.integrable_lpKernel (Rd.jacksonScale_pos k l).ne')
        f).const_smul (Rd.jacksonCoeff r l))).trans (.of_eq ?_))
    funext t
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply, smul_eq_mul]
  have hint : ∀ᵐ t ∂volume, ∀ l ∈ Finset.range r, Integrable
      (fun z => Φ z * (f : UnitAddTorus d → ℂ) (t - proj ((Rd.jacksonScale k l)⁻¹ • z))) :=
    (Filter.eventually_all_finset _).2 fun l _ =>
      ae_integrable_dilate_mul Rd.integrable_lpKernel hfm hfi (Rd.jacksonScale_pos k l)
  filter_upwards [Lp.coeFn_sub f (jacksonApprox hp r k f), hJ, hint] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2]
  have hsum : ∑ l ∈ Finset.range r,
      Rd.jacksonCoeff r l * econv (Rd.dilate (Rd.jacksonScale k l) Φ) f t =
      ∑ l ∈ Finset.range r, ∫ z, Rd.jacksonCoeff r l *
        (Φ z * (f : UnitAddTorus d → ℂ) (t - proj ((Rd.jacksonScale k l)⁻¹ • z))) :=
    Finset.sum_congr rfl fun l _ => by
      rw [econv_dilate_apply _ _ (Rd.jacksonScale_pos k l), integral_const_mul]
  have hf0 : (f : UnitAddTorus d → ℂ) t = ∫ z, Φ z * (f : UnitAddTorus d → ℂ) t := by
    rw [integral_mul_const, Rd.integral_lpKernel, one_mul]
  rw [hsum, hf0, ← integral_finsetSum _ fun l hl => (h3 l hl).const_mul _,
    ← integral_sub (Rd.integrable_lpKernel.mul_const _)
      (integrable_finsetSum _ fun l hl => (h3 l hl).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [neg_one_pow_mul_higherDiff_proj, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Rd.jacksonScale]
  ring

/-! ### Jackson's inequality -/

/-- **Jackson's inequality on the torus**: for `f ∈ L_p(𝕋^d)`, `1 ≤ p < ∞`,
`‖f - J_k f‖_p ≤ C ω_r(f, 2^(-k))_p`, with the constant `Rd.jacksonConst` of `ℝ^d`: by the weighted
averages of `Rd.eLpNorm_integral_lpKernel_mul_le` and
`ω_r(f, 2^(-k) |z|)_p ≤ (1 + |z|)^r ω_r(f, 2^(-k))_p`. -/
theorem enorm_sub_jacksonApprox_le (hp : p ≠ ∞) (r k : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖f - jacksonApprox hp r k f‖ₑ ≤
      Rd.jacksonConst (EuclideanSpace ℝ d) r p * Rd.lpModulus p r f k := by
  have hp1 : 1 ≤ p := Fact.out
  have hfm : Measurable (f : UnitAddTorus d → ℂ) := (Lp.stronglyMeasurable f).measurable
  set w : EuclideanSpace ℝ d → UnitAddTorus d := fun z => proj (-((2 : ℝ) ^ k)⁻¹ • z) with hw
  set G : UnitAddTorus d → EuclideanSpace ℝ d → ℂ :=
    fun t z => (-1 : ℂ) ^ r * (fwdDiff (w z))^[r] (f : UnitAddTorus d → ℂ) t with hGdef
  have hwl : ∀ l : ℕ, Measurable fun z => l • w z := fun l =>
    ((continuous_proj.comp (continuous_const_smul _)).nsmul l).measurable
  have hG : Measurable (Function.uncurry G) := by
    have heq : Function.uncurry G = fun y : UnitAddTorus d × EuclideanSpace ℝ d =>
        (-1 : ℂ) ^ r * ∑ l ∈ Finset.range (r + 1),
          (((-1 : ℤ) ^ (r - l) * (r.choose l : ℤ) : ℤ) : ℂ) *
            (f : UnitAddTorus d → ℂ) (y.1 + l • w y.2) := by
      funext y
      simp only [Function.uncurry, G]
      rw [fwdDiff_iter_eq_sum_shift]
      simp only [zsmul_eq_mul]
    rw [heq]
    exact measurable_const.mul (Finset.measurable_sum _ fun l _ => measurable_const.mul
      (hfm.comp (measurable_fst.add ((hwl l).comp measurable_snd))))
  have hω : Rd.lpModulus p r f k ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) eNorm_ne_top) (Rd.lpModulus_le r f k)
  -- the differences at the step `π(-2^(-k) z)`
  have hbound : ∀ z, eLpNorm (fun t => G t z) p volume ≤
      ENNReal.ofReal (1 + ‖z‖) ^ r * Rd.lpModulus p r f k := fun z => by
    have hnorm : ‖w z‖ ≤ ‖z‖ * (1 / 2 ^ k) := by
      refine (norm_proj_le _).trans ?_
      rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (by positivity), one_div,
        mul_comm]
    have hD := Rd.aestronglyMeasurable_higherDiff (Lp.aestronglyMeasurable f) r (w z)
    calc eLpNorm (fun t => G t z) p volume
        = eLpNorm ((fwdDiff (w z))^[r] (f : UnitAddTorus d → ℂ)) p volume := by
          refine eLpNorm_congr_norm_ae ((hG.comp measurable_prodMk_right).aestronglyMeasurable)
            hD (Eventually.of_forall fun t => ?_)
          simp [G]
      _ ≤ Rd.modulus volume r p (f : UnitAddTorus d → ℂ) (‖z‖ * (1 / 2 ^ k)) :=
          Rd.eLpNorm_higherDiff_le_modulus hnorm
      _ ≤ ENNReal.ofReal (1 + ‖z‖) ^ r *
            Rd.modulus volume r p (f : UnitAddTorus d → ℂ) (1 / 2 ^ k) :=
          modulus_mul_le (Lp.aestronglyMeasurable f) hp1 r (norm_nonneg z) (by positivity)
  have hlhs : ‖f - jacksonApprox hp r k f‖ₑ =
      eLpNorm (fun t => ∫ z, Rd.lpKernel z * G t z) p volume := by
    rw [Lp.eNorm_def]
    exact eLpNorm_congr_ae (ae_sub_jacksonApprox_eq hp r k f)
  rw [hlhs]
  exact Rd.eLpNorm_integral_lpKernel_mul_le hp1 hp r hG hω hbound

/-- **Jackson's inequality for the trigonometric polynomials**:
`E_{2^(k+1)}(f)_p ≤ C ω_r(f, 2^(-k))_p` in `L_p(𝕋^d)`. -/
theorem approxError_trigScheme_le (hp : p ≠ ∞) (r k : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume p).approxError f (2 ^ (k + 1)) ≤
      Rd.jacksonConst (EuclideanSpace ℝ d) r p * Rd.lpModulus p r f k :=
  (ApproximationScheme.approxError_le_of_mem
    (mem_toLp_trigScheme_iff.2 (jacksonApprox_mem_trigPolyLp hp r k f)) f).trans
    (enorm_sub_jacksonApprox_le hp r k f)

/-- **Halving the step**: `ω_r(f, 2^(-k))_p ≤ 2^r ω_r(f, 2^(-(k+1)))_p` on the torus
(`Torus.modulus_nat_mul_le` with `m = 2`). -/
theorem lpModulus_le_two_pow_mul_succ (r k : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Rd.lpModulus p r f k ≤ 2 ^ r * Rd.lpModulus p r f (k + 1) := by
  have h := modulus_nat_mul_le (Lp.aestronglyMeasurable f) (Fact.out : 1 ≤ p) r (m := 2)
    one_le_two (t := 1 / 2 ^ (k + 1)) (by positivity)
  rw [show ((2 : ℕ) : ℝ) * (1 / 2 ^ (k + 1)) = 1 / 2 ^ k by
    push_cast; rw [pow_succ]; field_simp] at h
  simpa [Rd.lpModulus] using h

/-! ### Bernstein's inequality -/

variable (d) in
/-- The **constant of the inverse inequality on the torus**, `2^r + (2^(#d) #d)^r ‖D^r Θ‖_1`. -/
noncomputable def bernsteinConst (r : ℕ) : ℝ≥0∞ :=
  2 ^ r + ENNReal.ofReal ((2 : ℝ) ^ Fintype.card d * Fintype.card d) ^ r *
    ∫⁻ x, ‖iteratedFDeriv ℝ r (Rd.bandKernelS (V := EuclideanSpace ℝ d) :
      EuclideanSpace ℝ d → ℂ) x‖ₑ

/-- The constant of the inverse inequality is finite. -/
theorem bernsteinConst_ne_top (r : ℕ) : bernsteinConst d r ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨by simp, ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (Rd.lintegral_enorm_iteratedFDeriv_ne_top r _)⟩

/-- **The band-limiting kernel reproduces trigonometric polynomials**: `Θ_{j+#d} ⋆ a = a` for `a`
of degree `< 2^j`, since `‖m‖ ≤ #d deg m < 2^(#d) 2^j` and `𝓕Θ_J = 1` on `‖ξ‖ ≤ 2^(J+1)`. -/
theorem econvLp_Theta_eq_self (hp : p ≠ ∞) {j : ℕ}
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p (2 ^ j)) :
    econvLp hp (Rd.integrable_Theta (V := EuclideanSpace ℝ d) (j + Fintype.card d)) a = a := by
  refine econvLp_eq_self_of_mem hp _ (fun m hm => Rd.fourier_Theta_eq_one ?_) ha
  have hcard : (Fintype.card d : ℝ) ≤ 2 ^ Fintype.card d := by
    have h := (Nat.cast_le (α := ℝ)).2 (Fintype.card d).lt_two_pow_self.le
    push_cast at h
    exact h
  have hdeg : (deg m : ℝ) ≤ 2 ^ j := by
    have h := (Nat.cast_le (α := ℝ)).2 hm.le
    push_cast at h
    exact h
  calc ‖latticeVec m‖ ≤ Fintype.card d * deg m := norm_latticeVec_le m
    _ ≤ 2 ^ Fintype.card d * 2 ^ j := by gcongr
    _ = 2 ^ (j + Fintype.card d) := by rw [pow_add, mul_comm]
    _ ≤ 2 ^ (j + Fintype.card d + 1) := pow_le_pow_right₀ one_le_two (Nat.le_succ _)

/-- **The inverse inequality on the torus** (Bernstein): for a trigonometric polynomial `a` of
degree `< 2^j`, `ω_r(a, 2^(-k))_p ≤ C 2^(-(k-j) r) ‖a‖_p` (with `k - j` truncated at `0`). For
`k ≥ j` and `‖h‖ ≤ 2^(-k)`, `h = π x` with `‖x‖ ≤ #d ‖h‖`, `Δ^r_h a = (Δ^r_x Θ_J) ⋆ a`, and Young's
inequality gives `‖Δ^r_h a‖_p ≤ (2^J ‖x‖)^r ‖D^r Θ‖_1 ‖a‖_p`. -/
theorem lpModulus_le_of_mem_trigPolyLp (hp : p ≠ ∞) (r : ℕ) {j k : ℕ}
    {a : Lp ℂ p (volume : Measure (UnitAddTorus d))} (ha : a ∈ trigPolyLp p (2 ^ j)) :
    Rd.lpModulus p r a k ≤ bernsteinConst d r * dyadicWeight (-(r : ℝ)) (k - j) * ‖a‖ₑ := by
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    exact (Rd.lpModulus_le r a k).trans (by gcongr; exact le_self_add)
  · set J := j + Fintype.card d
    set Θ := Rd.Theta (V := EuclideanSpace ℝ d) J
    have hΘ : Integrable Θ := Rd.integrable_Theta J
    have hae : (a : UnitAddTorus d → ℂ) =ᵐ[volume] econv Θ a := by
      have h1 := econvLp_apply_ae hp hΘ a
      rw [econvLp_Theta_eq_self hp ha] at h1
      exact h1
    have ham := (Lp.stronglyMeasurable a).measurable
    have hai := (Lp.memLp a).integrable (Fact.out : 1 ≤ p)
    set D := ∫⁻ x, ‖iteratedFDeriv ℝ r (Rd.bandKernelS (V := EuclideanSpace ℝ d) :
      EuclideanSpace ℝ d → ℂ) x‖ₑ
    set c := (2 : ℝ) ^ Fintype.card d * Fintype.card d
    rw [Rd.lpModulus, Rd.modulus_congr_ae hae]
    refine iSup₂_le fun h hh => ?_
    obtain ⟨x, rfl, hxn⟩ := exists_proj_eq h
    have h1 : eLpNorm ((fwdDiff (proj x))^[r] (econv Θ a)) p volume ≤
        eLpNorm ((fwdDiff x)^[r] Θ) 1 volume * ‖a‖ₑ := by
      rw [eLpNorm_congr_ae (higherDiff_econv_ae hΘ ham hai r x), Lp.eNorm_def,
        eLpNorm_one_eq_lintegral_eNorm (Rd.integrable_higherDiff hΘ r x).aestronglyMeasurable]
      exact eLpNorm_econv_le Fact.out hp (Rd.integrable_higherDiff hΘ r x) ham
    have h2 : ENNReal.ofReal (2 ^ J * ‖x‖) ^ r ≤
        ENNReal.ofReal c ^ r * dyadicWeight (-(r : ℝ)) (k - j) := by
      have hle : (2 : ℝ) ^ J * ‖x‖ ≤ c * (2 ^ j * ‖proj x‖) := by
        calc (2 : ℝ) ^ J * ‖x‖ ≤ 2 ^ J * (Fintype.card d * ‖proj x‖) := by gcongr
          _ = c * (2 ^ j * ‖proj x‖) := by rw [pow_add]; ring
      calc ENNReal.ofReal (2 ^ J * ‖x‖) ^ r ≤ ENNReal.ofReal (c * (2 ^ j * ‖proj x‖)) ^ r := by
            gcongr
        _ = ENNReal.ofReal c ^ r * ENNReal.ofReal (2 ^ j * ‖proj x‖) ^ r := by
            rw [ENNReal.ofReal_mul (by positivity), mul_pow]
        _ ≤ ENNReal.ofReal c ^ r * dyadicWeight (-(r : ℝ)) (k - j) := by
            gcongr
            rw [← ENNReal.rpow_natCast]
            exact ENNReal.ofReal_two_pow_mul_rpow_le hjk hh (Nat.cast_nonneg r)
    calc eLpNorm ((fwdDiff (proj x))^[r] (econv Θ a)) p volume
        ≤ ENNReal.ofReal (2 ^ J * ‖x‖) ^ r * D * ‖a‖ₑ :=
          h1.trans (by gcongr; exact Rd.eLpNorm_higherDiff_Theta_le r J x)
      _ ≤ ENNReal.ofReal c ^ r * dyadicWeight (-(r : ℝ)) (k - j) * D * ‖a‖ₑ := by gcongr
      _ = (ENNReal.ofReal c ^ r * D) * dyadicWeight (-(r : ℝ)) (k - j) * ‖a‖ₑ := by ring
      _ ≤ bernsteinConst d r * dyadicWeight (-(r : ℝ)) (k - j) * ‖a‖ₑ := by
          gcongr
          exact le_add_self

end Torus
