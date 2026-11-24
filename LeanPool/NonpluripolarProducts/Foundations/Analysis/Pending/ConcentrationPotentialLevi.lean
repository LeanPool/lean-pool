/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LogLevi
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PluriharmonicLogNorm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-!
# Demailly--Păun's Hessian estimate for `log (∑ c_j² |G_j|² + s)`

Source: Demailly--Păun, *Numerical characterization of the Kähler cone of a compact Kähler
manifold*, Lemma 2.1, the computation (2.2)--(2.3) (`dp04-kahler-cone:2.1`,
`references/dp04-kahler-cone/source/0105176.tex:640-690 ((2.2) at :671, (2.3) at :687)`),
    quoted by Boucksom as the
concentration of mass (`bou02-volume:4.11`).  This is the local calculus needed for
Boucksom 4.8 (programme TN.4): the global potentials
`ψ_ε = ½ log(∑ θ_j² ∑_k |g_{j,k}|² + ε²)` have `ddᶜψ_ε ≥ -A ω` uniformly in `ε`.

For real `C²` functions `c_j` and holomorphic `G_j` near `z`, `s > 0` and
`S = ∑_j c_j² |G_j|² + s`:

* `leviForm_sq_mul_normSq` — one term, dp04 (2.2):
  `ddᶜ(c² |G|²)(v, vBar) = |γ(v)|² + 2 |G|² (c ddᶜc(v, vBar) - |∂c(v)|²)` with `γ = c ∂G + 2 G ∂c`;
* `fderiv_sq_mul_normSq` — its `(1,0)`-derivative `∂(c² |G|²) = c GBar γ`;
* `le_leviForm_log_sum` — dp04 (2.2)+(2.3): the Levi form of `log S` is at least
  `s ∑ |γ_j|² / S² + 2 ∑ |G_j|² (c_j ddᶜc_j - |∂c_j|²) / S` (Cauchy--Schwarz on the first big sum,
  exactly as in the source, which writes `θ_j` for `c_j`, `ε²` for `s` and `½ log`);
  (`le_leviForm_log_sum_of_pos`: any `s` with `S(z) > 0`, e.g. `s = 0` off the zero set);
* `neg_le_leviForm_log_sum` — the first term dropped, the form used for `ddᶜψ_ε ≥ -A ω`
  (`neg_le_leviForm_log_sum_of_nonneg`: `s ≥ 0` and `S(z) > 0`).

Calculus used: `realHessian_mul`, `realHessian_log_of_pos`, `leviForm_mul`, `leviForm_log_of_pos`,
`leviForm_sum` (pointwise `C²` versions of the product, logarithm and sum rules; the existing
`realHessian_log` and `PlaneTubePositivity.leviForm_finsetSum` need global hypotheses), and the
pluriharmonicity of the real and imaginary parts of a holomorphic function
(`leviForm_re_eq_zero`, `leviForm_im_eq_zero`, from `PluriharmonicLogNorm`).

The Levi form is the project's `leviForm u z v = (D²u(v,v) + D²u(iv,iv))/4`, i.e.
`∑ ∂²u/∂z_j∂zBar_k v_j vBar_k`.  The global construction (`ψ_ε` on a compact manifold
along a closed submanifold) is the next module.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi

open FirstPass

noncomputable section

section RealHessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product rule for the genuine second derivative, at a point. -/
theorem realHessian_mul {u w : E → ℝ} {z : E} (hu : ContDiffAt ℝ 2 u z)
    (hw : ContDiffAt ℝ 2 w z) (a b : E) :
    realHessian (fun y => u y * w y) z a b =
      u z * realHessian w z a b + fderiv ℝ u z a * fderiv ℝ w z b +
        fderiv ℝ w z a * fderiv ℝ u z b + w z * realHessian u z a b := by
  have hDu : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDw : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ w y :=
    (hw.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hDDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDDw : DifferentiableAt ℝ (fderiv ℝ w) z :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : fderiv ℝ (fun y => u y * w y) =ᶠ[𝓝 z]
      fun y => u y • fderiv ℝ w y + w y • fderiv ℝ u y := by
    filter_upwards [hDu, hDw] with y hu' hw'
    exact fderiv_mul hu' hw'
  have hsm : HasFDerivAt (fun y => u y • fderiv ℝ w y + w y • fderiv ℝ u y) _ z :=
    ((hu.differentiableAt (by simp)).hasFDerivAt.smul hDDw.hasFDerivAt).add
      ((hw.differentiableAt (by simp)).hasFDerivAt.smul hDDu.hasFDerivAt)
  rw [realHessian_eq_fderiv, hev.fderiv_eq, hsm.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, realHessian_eq_fderiv]
  ring

/-- The second-order chain rule for the logarithm of a function positive at the point. -/
theorem realHessian_log_of_pos {S : E → ℝ} {z : E} (hS : ContDiffAt ℝ 2 S z)
    (hpos : 0 < S z) (a b : E) :
    realHessian (fun y => Real.log (S y)) z a b =
      realHessian S z a b / S z - fderiv ℝ S z a * fderiv ℝ S z b / S z ^ 2 := by
  have hDS : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ S y :=
    (hS.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hpos' : ∀ᶠ y in 𝓝 z, 0 < S y :=
    (hS.continuousAt).eventually (lt_mem_nhds hpos)
  have hDDS : DifferentiableAt ℝ (fderiv ℝ S) z :=
    (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : fderiv ℝ (fun y => Real.log (S y)) =ᶠ[𝓝 z]
      fun y => (S y)⁻¹ • fderiv ℝ S y := by
    filter_upwards [hDS, hpos'] with y hy hy'
    exact fderiv.log hy hy'.ne'
  have hi : HasFDerivAt (fun y => (S y)⁻¹) (-(S z ^ 2)⁻¹ • fderiv ℝ S z) z := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv hpos.ne').comp_hasFDerivAt z
        (hS.differentiableAt (by simp)).hasFDerivAt
  have hsm : HasFDerivAt (fun y => (S y)⁻¹ • fderiv ℝ S y) _ z := hi.smul hDDS.hasFDerivAt
  rw [realHessian_eq_fderiv, hev.fderiv_eq, hsm.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, realHessian_eq_fderiv]
  field_simp
  ring

/-- The product rule for the first derivative, evaluated. -/
theorem fderiv_mul_apply {u w : E → ℝ} {z : E} (hu : DifferentiableAt ℝ u z)
    (hw : DifferentiableAt ℝ w z) (a : E) :
    fderiv ℝ (fun y => u y * w y) z a = u z * fderiv ℝ w z a + w z * fderiv ℝ u z a := by
  rw [show (fun y => u y * w y) = u * w from rfl, fderiv_mul hu hw]
  simp only [add_apply, smul_apply, smul_eq_mul]

end RealHessian

section Levi

variable {n : ℕ}

local notation "E" => ComplexModel n

/-- The product rule for the Levi form. -/
theorem leviForm_mul {u w : E → ℝ} {z : E} (hu : ContDiffAt ℝ 2 u z)
    (hw : ContDiffAt ℝ 2 w z) (v : E) :
    leviForm (fun y => u y * w y) z v =
      u z * leviForm w z v + w z * leviForm u z v +
        (fderiv ℝ u z v * fderiv ℝ w z v +
          fderiv ℝ u z (Complex.I • v) * fderiv ℝ w z (Complex.I • v)) / 2 := by
  simp only [leviForm, realHessian_mul hu hw]
  ring

/-- The Levi form of the logarithm of a function positive at the point. -/
theorem leviForm_log_of_pos {S : E → ℝ} {z : E} (hS : ContDiffAt ℝ 2 S z)
    (hpos : 0 < S z) (v : E) :
    leviForm (fun y => Real.log (S y)) z v =
      leviForm S z v / S z -
        (fderiv ℝ S z v ^ 2 + fderiv ℝ S z (Complex.I • v) ^ 2) / (4 * S z ^ 2) := by
  simp only [leviForm, realHessian_log_of_pos hS hpos]
  field_simp
  ring

/-- The Levi form of a finite sum, at a point. -/
theorem leviForm_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {z : E}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) (v : E) :
    leviForm (fun y => ∑ i ∈ s, f i y) z v = ∑ i ∈ s, leviForm (f i) z v := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have hsum : ContDiffAt ℝ 2 (fun y => ∑ i ∈ s, f i y) z :=
        ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hfun : (fun y => ∑ i ∈ insert j s, f i y) =
          (f j) + (fun y => ∑ i ∈ s, f i y) := by
        funext y; simp [Finset.sum_insert hj]
      rw [hfun, leviForm_add (hf j (Finset.mem_insert_self j s)) hsum,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi), Finset.sum_insert hj]

end Levi

section Holomorphic

variable {n : ℕ}

local notation "E" => ComplexModel n

/-- A function holomorphic near `z` is real-smooth at `z`. -/
theorem contDiffAt_of_eventually_differentiableAt {G : E → ℂ} {z : E}
    (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) : ContDiffAt ℝ ∞ G z := by
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hG
  exact contDiffAt_real_of_differentiableOn_complex
    (fun y hy => (hUsub hy).differentiableWithinAt) hU hzU

theorem contDiffAt_re {G : E → ℂ} {z : E} (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) :
    ContDiffAt ℝ ∞ (fun y => (G y).re) z :=
  Complex.reCLM.contDiff.contDiffAt.comp z (contDiffAt_of_eventually_differentiableAt hG)

theorem contDiffAt_im {G : E → ℂ} {z : E} (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) :
    ContDiffAt ℝ ∞ (fun y => (G y).im) z :=
  Complex.imCLM.contDiff.contDiffAt.comp z (contDiffAt_of_eventually_differentiableAt hG)

theorem fderiv_re {G : E → ℂ} {z : E} (hG : DifferentiableAt ℂ G z) (a : E) :
    fderiv ℝ (fun y => (G y).re) z a = (fderiv ℂ G z a).re := by
  have h : HasFDerivAt (fun y => (G y).re)
      (Complex.reCLM.comp ((fderiv ℂ G z).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hG.hasFDerivAt.restrictScalars ℝ)
  rw [h.fderiv]
  rfl

theorem fderiv_im {G : E → ℂ} {z : E} (hG : DifferentiableAt ℂ G z) (a : E) :
    fderiv ℝ (fun y => (G y).im) z a = (fderiv ℂ G z a).im := by
  have h : HasFDerivAt (fun y => (G y).im)
      (Complex.imCLM.comp ((fderiv ℂ G z).restrictScalars ℝ)) z :=
    Complex.imCLM.hasFDerivAt.comp z (hG.hasFDerivAt.restrictScalars ℝ)
  rw [h.fderiv]
  rfl

/-- The real part of a holomorphic function is pluriharmonic: its Levi form vanishes. -/
theorem leviForm_re_eq_zero {G : E → ℂ} {z : E} (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y)
    (v : E) : leviForm (fun y => (G y).re) z v = 0 := by
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hG
  have hdd := PluriharmonicLogNorm.smoothDDC_re_comp_eq_zero hU
    (fun y hy => (hUsub hy).differentiableWithinAt) hzU
  have h2 : ContDiffAt ℝ 2 (fun y => (G y).re) z :=
    (contDiffAt_re hG).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have := smoothDDC_complexDiagonal_eq_leviForm h2 v
  rw [hdd] at this
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h0 : leviForm (fun y => (G y).re) z v / Real.pi = 0 := this.symm.trans rfl
  rcases div_eq_zero_iff.mp h0 with h | h
  · exact h
  · exact absurd h hpi

/-- The imaginary part of a holomorphic function is pluriharmonic. -/
theorem leviForm_im_eq_zero {G : E → ℂ} {z : E} (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y)
    (v : E) : leviForm (fun y => (G y).im) z v = 0 := by
  have hG' : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (fun y => -Complex.I * G y) y :=
    hG.mono fun y hy => hy.const_mul _
  have h := leviForm_re_eq_zero hG' v
  have hfun : (fun y => (-Complex.I * G y).re) = fun y => (G y).im := by
    funext y; simp
  rwa [hfun] at h

end Holomorphic

section Concentration

variable {n : ℕ}

local notation "E" => ComplexModel n

/-- The `(1,0)`-part `∂c(v) = (dc(v) - i dc(iv))/2` of the differential of a real function. -/
def delC (c : E → ℝ) (z v : E) : ℂ :=
  ((fderiv ℝ c z v : ℂ) - Complex.I * (fderiv ℝ c z (Complex.I • v) : ℂ)) / 2

/-- Demailly--Păun's `(1,0)`-form `γ = c ∂g + 2 g ∂c` (dp04 (2.2), with `θ_j = c`, `g_{j,k} = G`),
evaluated on `v`. -/
def gammaTerm (c : E → ℝ) (G : E → ℂ) (z v : E) : ℂ :=
  (c z : ℂ) * fderiv ℂ G z v + 2 * G z * delC c z v

theorem normSq_delC (c : E → ℝ) (z v : E) :
    Complex.normSq (delC c z v) =
      (fderiv ℝ c z v ^ 2 + fderiv ℝ c z (Complex.I • v) ^ 2) / 4 := by
  simp [delC, Complex.normSq_apply]
  ring

theorem contDiffAt_normSq {G : E → ℂ} {z : E} (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (G y)) z := by
  have h1 := (contDiffAt_re hG).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h2 := (contDiffAt_im hG).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hfun : (fun y => Complex.normSq (G y)) =
      fun y => (G y).re * (G y).re + (G y).im * (G y).im := by
    funext y; exact Complex.normSq_apply _
  rw [hfun]
  exact (h1.mul h1).add (h2.mul h2)

/-- The data of one term `c² |G|²` in coordinates: the real and imaginary parts of `G`, their
derivatives through Cauchy--Riemann, and the pluriharmonicity of both parts. -/
private theorem term_data {c : E → ℝ} {G : E → ℂ} {z : E} (hc : ContDiffAt ℝ 2 c z)
    (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) (v : E) :
    let g₁ : E → ℝ := fun y => (G y).re
    let g₂ : E → ℝ := fun y => (G y).im
    ContDiffAt ℝ 2 (fun y => c y * g₁ y) z ∧ ContDiffAt ℝ 2 (fun y => c y * g₂ y) z ∧
    leviForm (fun y => c y * g₁ y) z v = g₁ z * leviForm c z v +
      (fderiv ℝ c z v * (fderiv ℂ G z v).re -
        fderiv ℝ c z (Complex.I • v) * (fderiv ℂ G z v).im) / 2 ∧
    leviForm (fun y => c y * g₂ y) z v = g₂ z * leviForm c z v +
      (fderiv ℝ c z v * (fderiv ℂ G z v).im +
        fderiv ℝ c z (Complex.I • v) * (fderiv ℂ G z v).re) / 2 ∧
    (∀ a, fderiv ℝ (fun y => c y * g₁ y) z a =
      c z * (fderiv ℂ G z a).re + g₁ z * fderiv ℝ c z a) ∧
    (∀ a, fderiv ℝ (fun y => c y * g₂ y) z a =
      c z * (fderiv ℂ G z a).im + g₂ z * fderiv ℝ c z a) ∧
    fderiv ℂ G z (Complex.I • v) = Complex.I * fderiv ℂ G z v := by
  intro g₁ g₂
  have hGz : DifferentiableAt ℂ G z := hG.self_of_nhds
  have h1 : ContDiffAt ℝ 2 g₁ z :=
    (contDiffAt_re hG).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h2 : ContDiffAt ℝ 2 g₂ z :=
    (contDiffAt_im hG).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hI : fderiv ℂ G z (Complex.I • v) = Complex.I * fderiv ℂ G z v := by
    rw [(fderiv ℂ G z).map_smul, smul_eq_mul]
  have hdc : DifferentiableAt ℝ c z := hc.differentiableAt (by norm_num)
  refine ⟨hc.mul h1, hc.mul h2, ?_, ?_, ?_, ?_, hI⟩
  · rw [leviForm_mul hc h1, leviForm_re_eq_zero hG, fderiv_re hGz, fderiv_re hGz, hI]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    ring
  · rw [leviForm_mul hc h2, leviForm_im_eq_zero hG, fderiv_im hGz, fderiv_im hGz, hI]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    ring
  · intro a
    rw [fderiv_mul_apply hdc (h1.differentiableAt (by norm_num)), fderiv_re hGz]
  · intro a
    rw [fderiv_mul_apply hdc (h2.differentiableAt (by norm_num)), fderiv_im hGz]

/-- **dp04 (2.2), one term.**  For a real `C²` function `c` and a holomorphic `G`,
`ddᶜ(c² |G|²)(v, vBar) = |γ(v)|² + 2 |G|² (c ddᶜc(v, vBar) - |∂c(v)|²)`. -/
theorem leviForm_sq_mul_normSq {c : E → ℝ} {G : E → ℂ} {z : E} (hc : ContDiffAt ℝ 2 c z)
    (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) (v : E) :
    leviForm (fun y => c y ^ 2 * Complex.normSq (G y)) z v =
      Complex.normSq (gammaTerm c G z v) +
        2 * Complex.normSq (G z) * (c z * leviForm c z v - Complex.normSq (delC c z v)) := by
  obtain ⟨h1, h2, hL1, hL2, hd1, hd2, hI⟩ := term_data hc hG v
  have hfun : (fun y => c y ^ 2 * Complex.normSq (G y)) =
      (fun y => (c y * (G y).re) * (c y * (G y).re)) +
        (fun y => (c y * (G y).im) * (c y * (G y).im)) := by
    funext y; simp only [Pi.add_apply, Complex.normSq_apply]; ring
  rw [hfun, leviForm_add (h1.mul h1) (h2.mul h2), leviForm_mul h1 h1, leviForm_mul h2 h2,
    hL1, hL2, hd1, hd1, hd2, hd2, hI, normSq_delC]
  simp only [gammaTerm, delC, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
    Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- **dp04 (2.2), the first derivative of one term.**
`∂(c² |G|²)(v) = c GBar γ(v)`, written as `d f(v) - i d f(iv) = 2 c GBar γ(v)`. -/
theorem fderiv_sq_mul_normSq {c : E → ℝ} {G : E → ℂ} {z : E} (hc : ContDiffAt ℝ 2 c z)
    (hG : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ G y) (v : E) :
    (fderiv ℝ (fun y => c y ^ 2 * Complex.normSq (G y)) z v : ℂ) -
        Complex.I * (fderiv ℝ (fun y => c y ^ 2 * Complex.normSq (G y)) z (Complex.I • v) : ℂ) =
      2 * (c z : ℂ) * (starRingEnd ℂ) (G z) * gammaTerm c G z v := by
  obtain ⟨h1, h2, -, -, hd1, hd2, hI⟩ := term_data hc hG v
  beta_reduce at h1 h2 hd1 hd2
  have hfun : (fun y => c y ^ 2 * Complex.normSq (G y)) =
      fun y => (c y * (G y).re) * (c y * (G y).re) + (c y * (G y).im) * (c y * (G y).im) := by
    funext y; simp only [Complex.normSq_apply]; ring
  have hD1 := h1.differentiableAt (by norm_num)
  have hD2 := h2.differentiableAt (by norm_num)
  have hder : ∀ a, fderiv ℝ (fun y => (c y * (G y).re) * (c y * (G y).re) +
      (c y * (G y).im) * (c y * (G y).im)) z a =
      2 * (c z * (G z).re) * fderiv ℝ (fun y => c y * (G y).re) z a +
        2 * (c z * (G z).im) * fderiv ℝ (fun y => c y * (G y).im) z a := by
    intro a
    have hh : HasFDerivAt (fun y => (c y * (G y).re) * (c y * (G y).re) +
        (c y * (G y).im) * (c y * (G y).im)) _ z :=
      (hD1.hasFDerivAt.mul hD1.hasFDerivAt).add (hD2.hasFDerivAt.mul hD2.hasFDerivAt)
    rw [hh.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun, hder, hder, hd1, hd1, hd2, hd2, hI]
  apply Complex.ext <;>
  simp only [gammaTerm, delC, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.conj_re, Complex.conj_im, Complex.normSq_ofNat] <;>
  ring

/-- Cauchy--Schwarz for finite sums of complex products. -/
theorem normSq_sum_mul_le {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    Complex.normSq (∑ j, x j * y j) ≤
      (∑ j, Complex.normSq (x j)) * ∑ j, Complex.normSq (y j) := by
  have h1 : ‖∑ j, x j * y j‖ ≤ ∑ j, ‖x j‖ * ‖y j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖x j‖) (fun j => ‖y j‖)
  rw [Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ j, x j * y j‖ ^ 2 ≤ (∑ j, ‖x j‖ * ‖y j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **Demailly--Păun's Hessian estimate (dp04-kahler-cone:2.1, (2.2)--(2.3)).**  Let `c_j` be real
`C²` functions and `G_j` holomorphic functions near `z`, `s ∈ ℝ` and
`S = ∑_j c_j² |G_j|² + s` with `S(z) > 0` (dp04: `s = ε² > 0`; `s = 0` is allowed off the common
zero set).  Then the Levi form of `log S` at `z` is at least
`s ∑_j |γ_j(v)|² / S² + 2 ∑_j |G_j|² (c_j ddᶜc_j(v, vBar) - |∂c_j(v)|²) / S`,
`γ_j = c_j ∂G_j + 2 G_j ∂c_j`.  The first term is the Cauchy--Schwarz remainder of the
source's first big sum; the second is its last line.  (dp04 writes `θ_j` for `c_j`, `ε²` for `s`
and uses `½ log S`.) -/
theorem le_leviForm_log_sum_of_pos {ι : Type*} [Fintype ι] {c : ι → E → ℝ} {G : ι → E → ℂ}
    {s : ℝ} {z : E} (hpos : 0 < ∑ j, c j z ^ 2 * Complex.normSq (G j z) + s)
    (hc : ∀ j, ContDiffAt ℝ 2 (c j) z)
    (hG : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G j) y) (v : E) :
    s * (∑ j, Complex.normSq (gammaTerm (c j) (G j) z v)) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s) ^ 2 +
      2 * (∑ j, Complex.normSq (G j z) *
          (c j z * leviForm (c j) z v - Complex.normSq (delC (c j) z v))) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s) ≤
      leviForm (fun y => Real.log (∑ j, c j y ^ 2 * Complex.normSq (G j y) + s)) z v := by
  set f : ι → E → ℝ := fun j y => c j y ^ 2 * Complex.normSq (G j y) with hfdef
  have hf : ∀ j, ContDiffAt ℝ 2 (f j) z := fun j => ((hc j).pow 2).mul (contDiffAt_normSq (hG j))
  have hfD : ∀ j, DifferentiableAt ℝ (f j) z := fun j => (hf j).differentiableAt (by norm_num)
  set S : E → ℝ := fun y => ∑ j, f j y + s with hSdef
  have hS : ContDiffAt ℝ 2 S z := (ContDiffAt.sum fun j _ => hf j).add contDiffAt_const
  have hB : 0 ≤ ∑ j, c j z ^ 2 * Complex.normSq (G j z) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have hSz : S z = ∑ j, c j z ^ 2 * Complex.normSq (G j z) + s := rfl
  have hSpos : 0 < S z := hpos
  change _ ≤ leviForm (fun y => Real.log (S y)) z v
  rw [leviForm_log_of_pos hS hSpos]
  -- the Levi form of `S`
  have hLS : leviForm S z v = ∑ j, (Complex.normSq (gammaTerm (c j) (G j) z v) +
      2 * Complex.normSq (G j z) * (c j z * leviForm (c j) z v -
        Complex.normSq (delC (c j) z v))) := by
    have hsum : ContDiffAt ℝ 2 (fun y => ∑ j, f j y) z := ContDiffAt.sum fun j _ => hf j
    rw [show S = (fun y => ∑ j, f j y) + fun _ => s from rfl,
      leviForm_add hsum contDiffAt_const, leviForm_const, add_zero,
      leviForm_sum Finset.univ (fun j _ => hf j)]
    exact Finset.sum_congr rfl fun j _ => leviForm_sq_mul_normSq (hc j) (hG j) v
  -- the first derivative of `S`
  have hdS : ∀ a, fderiv ℝ S z a = ∑ j, fderiv ℝ (f j) z a := by
    intro a
    have hh : HasFDerivAt S (∑ j, fderiv ℝ (f j) z) z := by
      have := (HasFDerivAt.sum (u := Finset.univ) fun j _ => (hfD j).hasFDerivAt).add_const s
      simpa [hSdef] using this
    rw [hh.fderiv, sum_apply]
  have hW : ((fderiv ℝ S z v : ℂ) - Complex.I * (fderiv ℝ S z (Complex.I • v) : ℂ)) =
      2 * ∑ j, ((c j z : ℂ) * (starRingEnd ℂ) (G j z)) * gammaTerm (c j) (G j) z v := by
    rw [hdS, hdS, Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fderiv_sq_mul_normSq (hc j) (hG j) v]
    ring
  have hD : (fderiv ℝ S z v ^ 2 + fderiv ℝ S z (Complex.I • v) ^ 2) / 4 =
      Complex.normSq (∑ j, ((c j z : ℂ) * (starRingEnd ℂ) (G j z)) *
        gammaTerm (c j) (G j) z v) := by
    have h := congrArg Complex.normSq hW
    rw [Complex.normSq_mul] at h
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat] at h ⊢
    linarith
  have hCS := normSq_sum_mul_le (fun j => (c j z : ℂ) * (starRingEnd ℂ) (G j z))
    (fun j => gammaTerm (c j) (G j) z v)
  have hxj : ∀ j, Complex.normSq ((c j z : ℂ) * (starRingEnd ℂ) (G j z)) =
      c j z ^ 2 * Complex.normSq (G j z) := by
    intro j; rw [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_ofReal]; ring
  simp only [hxj] at hCS
  set A := ∑ j, Complex.normSq (gammaTerm (c j) (G j) z v)
  set B := ∑ j, c j z ^ 2 * Complex.normSq (G j z)
  set C := ∑ j, Complex.normSq (G j z) * (c j z * leviForm (c j) z v -
    Complex.normSq (delC (c j) z v))
  have hLS' : leviForm S z v = A + 2 * C := by
    rw [hLS, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hDle : (fderiv ℝ S z v ^ 2 + fderiv ℝ S z (Complex.I • v) ^ 2) / 4 ≤ B * A := by
    rw [hD]; exact hCS
  rw [hLS', hSz]
  rw [hSz] at hSpos
  have key : (fderiv ℝ S z v ^ 2 + fderiv ℝ S z (Complex.I • v) ^ 2) / (4 * (B + s) ^ 2) ≤
      B * A / (B + s) ^ 2 := by
    rw [show (fderiv ℝ S z v ^ 2 + fderiv ℝ S z (Complex.I • v) ^ 2) / (4 * (B + s) ^ 2) =
      ((fderiv ℝ S z v ^ 2 + fderiv ℝ S z (Complex.I • v) ^ 2) / 4) / (B + s) ^ 2 by
        field_simp]
    exact div_le_div_of_nonneg_right hDle (sq_nonneg _)
  have hfin : s * A / (B + s) ^ 2 + 2 * C / (B + s) =
      (A + 2 * C) / (B + s) - B * A / (B + s) ^ 2 := by
    field_simp
    ring
  rw [hfin]
  linarith

/-- `le_leviForm_log_sum_of_pos` for `s > 0` (dp04's `ε² > 0`). -/
theorem le_leviForm_log_sum {ι : Type*} [Fintype ι] {c : ι → E → ℝ} {G : ι → E → ℂ}
    {s : ℝ} (hs : 0 < s) {z : E} (hc : ∀ j, ContDiffAt ℝ 2 (c j) z)
    (hG : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G j) y) (v : E) :
    s * (∑ j, Complex.normSq (gammaTerm (c j) (G j) z v)) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s) ^ 2 +
      2 * (∑ j, Complex.normSq (G j z) *
          (c j z * leviForm (c j) z v - Complex.normSq (delC (c j) z v))) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s) ≤
      leviForm (fun y => Real.log (∑ j, c j y ^ 2 * Complex.normSq (G j y) + s)) z v := by
  have hB : 0 ≤ ∑ j, c j z ^ 2 * Complex.normSq (G j z) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  exact le_leviForm_log_sum_of_pos (by linarith) hc hG v

/-- The part of `le_leviForm_log_sum` used for the global lower bound `ddᶜψ_ε ≥ -A ω`:
the positive first term dropped. -/
theorem neg_le_leviForm_log_sum_of_nonneg {ι : Type*} [Fintype ι] {c : ι → E → ℝ}
    {G : ι → E → ℂ} {s : ℝ} (hs : 0 ≤ s) {z : E}
    (hpos : 0 < ∑ j, c j z ^ 2 * Complex.normSq (G j z) + s) (hc : ∀ j, ContDiffAt ℝ 2 (c j) z)
    (hG : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G j) y) (v : E) :
    -(2 * (∑ j, Complex.normSq (G j z) *
          (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s)) ≤
      leviForm (fun y => Real.log (∑ j, c j y ^ 2 * Complex.normSq (G j y) + s)) z v := by
  refine le_trans ?_ (le_leviForm_log_sum_of_pos hpos hc hG v)
  have hS := hpos
  have h1 : 0 ≤ s * (∑ j, Complex.normSq (gammaTerm (c j) (G j) z v)) /
      (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s) ^ 2 := by
    have : 0 ≤ ∑ j, Complex.normSq (gammaTerm (c j) (G j) z v) :=
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
    positivity
  have h2 : -(2 * (∑ j, Complex.normSq (G j z) *
          (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s)) =
      2 * (∑ j, Complex.normSq (G j z) *
          (c j z * leviForm (c j) z v - Complex.normSq (delC (c j) z v))) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s) := by
    have hs' : ∑ j, Complex.normSq (G j z) *
          (c j z * leviForm (c j) z v - Complex.normSq (delC (c j) z v)) =
        -∑ j, Complex.normSq (G j z) *
          (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs']
    ring
  linarith

/-- `neg_le_leviForm_log_sum_of_nonneg` for `s > 0`. -/
theorem neg_le_leviForm_log_sum {ι : Type*} [Fintype ι] {c : ι → E → ℝ} {G : ι → E → ℂ}
    {s : ℝ} (hs : 0 < s) {z : E} (hc : ∀ j, ContDiffAt ℝ 2 (c j) z)
    (hG : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G j) y) (v : E) :
    -(2 * (∑ j, Complex.normSq (G j z) *
          (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) /
        (∑ j, c j z ^ 2 * Complex.normSq (G j z) + s)) ≤
      leviForm (fun y => Real.log (∑ j, c j y ^ 2 * Complex.normSq (G j y) + s)) z v := by
  have hB : 0 ≤ ∑ j, c j z ^ 2 * Complex.normSq (G j z) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  exact neg_le_leviForm_log_sum_of_nonneg hs.le (by linarith) hc hG v

end Concentration

end

end SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
