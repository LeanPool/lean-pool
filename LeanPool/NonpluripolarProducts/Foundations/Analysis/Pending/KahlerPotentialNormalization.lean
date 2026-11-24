/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MollifierPeanoHessian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ComplexHessianDeterminant

/-!
# Normalising a local potential of a Kähler form at a point, uniformly

Let `ρ` be `C²` on an open `W ⊆ ℂⁿ` with positive Levi form (a local potential of a Kähler form),
and `closedBall c (3R) ⊆ W`.  There are `r ∈ (0, R]` and `a > 0` such that for EVERY
`z₀ ∈ closedBall c R` the function

`g(z) = ρ(z) - ρ(z₀) - Dρ(z₀)(z - z₀) - ¼ (D²ρ(z₀)(z - z₀, z - z₀) - D²ρ(z₀)(i(z - z₀), i(z - z₀)))`

has the same complex Hessian as `ρ` (the subtracted quadratic polynomial is pluriharmonic),
`g(z₀) = 0`, `g ≥ 0` on `B(z₀, 2r)` and `g ≥ a` on `B(z₀, 2r) \ B(z₀, r)`
(`exists_normalized_potential`).

This is the normalisation step of Błocki's proof of the uniform estimate
(`blocki05-uniform-estimate:page-0003`--`page-0004`: "Replacing `g` with `g - Re P - const.`
    (which does not
change the Kähler form `ω`) we may thus assume that there exist `a, r > 0` depending only on `M`
    such
that `g < 0` in `B(z₀, 2r)`, `g` attains minimum in `B(z₀, 2r)` at `z₀` and `g ≥ g(z₀) + a` on
`B(z₀, 2r) \ B(z₀, r)`"; `lnm2038-monge-ampere:page-0221`).  We use the Levi form directly:
`g(z₀ + h) = Φ(h) + L_{z₀}(h)` with `L_{z₀}(h) ≥ λ|h|²` (compactness) and the Taylor remainder
`|Φ(h)| ≤ (λ/2)|h|²` for `|h| < 2r` (uniform continuity of `D²ρ`, mean value inequality twice)
    in place
of the source's third-order bound `c₂|h|³`.  The constant `g < 0` normalisation is not needed
(the local stability estimate takes `∫ (-u)⁺`).

TN.4 B5, nonlinear track N2 (d).
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.KahlerPotentialNormalization

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- Multiplication by `i` as a real continuous linear map. -/
noncomputable abbrev mulI : ComplexModel n →L[ℝ] ComplexModel n :=
  modelComplexStructure n

@[simp] theorem mulI_apply (v : ComplexModel n) : mulI v = Complex.I • v := rfl

/-- The `J`-anti-invariant half of a bilinear form, `S v w = (B v w - B (iv) (iw)) / 2`. -/
noncomputable def antiHalf (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • (B - B.bilinearComp mulI mulI)

theorem antiHalf_apply (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (v w : ComplexModel n) :
    antiHalf B v w = (B v w - B (Complex.I • v) (Complex.I • w)) / 2 := by
  simp [antiHalf]; ring

/-- The pluriharmonic quadratic polynomial subtracted from the potential. -/
noncomputable def pluriharmonicPart (ρ : ComplexModel n → ℝ) (z₀ : ComplexModel n) :
    ComplexModel n → ℝ := fun z =>
  (ρ z₀ + fderiv ℝ ρ z₀ (z - z₀) +
    antiHalf (fderiv ℝ (fderiv ℝ ρ) z₀) (z - z₀) (z - z₀) / 2) + 0

theorem contDiff_pluriharmonicPart (ρ : ComplexModel n → ℝ) (z₀ : ComplexModel n) :
    ContDiff ℝ 2 (pluriharmonicPart ρ z₀) := by
  unfold pluriharmonicPart
  have h1 : ContDiff ℝ 2 (fun z : ComplexModel n => z - z₀) := contDiff_id.sub contDiff_const
  have h2 : ContDiff ℝ 2 (fun z : ComplexModel n =>
      antiHalf (fderiv ℝ (fderiv ℝ ρ) z₀) (z - z₀) (z - z₀)) :=
    ((antiHalf (fderiv ℝ (fderiv ℝ ρ) z₀)).contDiff.comp h1).clm_apply h1
  have h3 : ContDiff ℝ 2 (fun z : ComplexModel n => fderiv ℝ ρ z₀ (z - z₀)) :=
    (fderiv ℝ ρ z₀).contDiff.comp h1
  exact ((contDiff_const.add h3).add (h2.div_const 2)).add contDiff_const

/-- The subtracted polynomial is pluriharmonic: its complex Hessian vanishes. -/
theorem complexHessian_pluriharmonicPart {ρ : ComplexModel n → ℝ} {z₀ : ComplexModel n}
    (hsymm : ∀ v w, fderiv ℝ (fderiv ℝ ρ) z₀ v w = fderiv ℝ (fderiv ℝ ρ) z₀ w v)
    (x : ComplexModel n) : complexHessian (pluriharmonicPart ρ z₀) x = 0 := by
  set B := fderiv ℝ (fderiv ℝ ρ) z₀ with hB
  have hA : ∀ v w, antiHalf B v w = antiHalf B w v := fun v w => by
    rw [antiHalf_apply, antiHalf_apply, hsymm v w, hsymm (Complex.I • v) (Complex.I • w)]
  have hH : ∀ v w, realHessian (pluriharmonicPart ρ z₀) x v w = antiHalf B v w := fun v w =>
    SemiconcaveHessian.realHessian_quadratic hA x v w
  ext j k
  simp only [complexHessian, hH, antiHalf_apply, smul_smul, Complex.I_mul_I, neg_one_smul,
    map_neg, neg_apply, neg_neg, Matrix.zero_apply]
  push_cast
  ring

/-- Subtracting the pluriharmonic part does not change the complex Hessian. -/
theorem complexHessian_sub_pluriharmonicPart {ρ f : ComplexModel n → ℝ} {z₀ z : ComplexModel n}
    (hsymm : ∀ v w, fderiv ℝ (fderiv ℝ ρ) z₀ v w = fderiv ℝ (fderiv ℝ ρ) z₀ w v)
    (hf : ContDiffAt ℝ 2 f z) :
    complexHessian (fun w => f w - pluriharmonicPart ρ z₀ w) z = complexHessian f z := by
  have hp : ContDiffAt ℝ 2 ((-1 : ℝ) • pluriharmonicPart ρ z₀) z :=
    ((contDiff_pluriharmonicPart ρ z₀).const_smul (-1 : ℝ)).contDiffAt
  have heq : (fun w => f w - pluriharmonicPart ρ z₀ w) =
      f + (-1 : ℝ) • pluriharmonicPart ρ z₀ := by
    funext w; simp [sub_eq_add_neg]
  rw [heq, complexHessian_add hf hp,
    complexHessian_smul (contDiff_pluriharmonicPart ρ z₀).contDiffAt,
    complexHessian_pluriharmonicPart hsymm, smul_zero, add_zero]

/-- Homogeneity of the Levi form. -/
theorem leviForm_smul_right (u : ComplexModel n → ℝ) (z v : ComplexModel n) (t : ℝ) :
    leviForm u z (t • v) = t ^ 2 * leviForm u z v := by
  simp only [leviForm, realHessian_smul_left, realHessian_smul_right]
  rw [smul_comm Complex.I t v, realHessian_smul_left, realHessian_smul_right]
  ring

/-- A uniform lower bound `λ |v|² ≤ L_z(v)` on a compact set. -/
theorem exists_pos_mul_norm_sq_le_leviForm (hn : 0 < n) {ρ : ComplexModel n → ℝ}
    {W : Set (ComplexModel n)} (hW : IsOpen W) (hρ : ContDiffOn ℝ 2 ρ W)
    (hlevi : ∀ z ∈ W, ∀ v, v ≠ 0 → 0 < leviForm ρ z v) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ l : ℝ, 0 < l ∧ ∀ z ∈ K, ∀ v, l * ‖v‖ ^ 2 ≤ leviForm ρ z v := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, by simp [hKe]⟩
  have : Nontrivial (ComplexModel n) := by
    have : 0 < Module.finrank ℂ (ComplexModel n) := by
      rw [finrank_euclideanSpace, Fintype.card_fin]; exact hn
    exact Module.nontrivial_of_finrank_pos this
  set S := K ×ˢ sphere (0 : ComplexModel n) 1 with hS
  have hSc : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hSne : S.Nonempty := hKne.prod (NormedSpace.sphere_nonempty.mpr zero_le_one)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ ρ)) W :=
    (hρ.fderiv_of_isOpen hW (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hW le_rfl
  have hfc : ContinuousOn (fun p : ComplexModel n × ComplexModel n => leviForm ρ p.1 p.2) S := by
    have hD2S : ContinuousOn (fun p : ComplexModel n × ComplexModel n =>
        fderiv ℝ (fderiv ℝ ρ) p.1) S :=
      hD2.comp continuous_fst.continuousOn fun p hp => hKW hp.1
    have h1 : ContinuousOn (fun p : ComplexModel n × ComplexModel n =>
        fderiv ℝ (fderiv ℝ ρ) p.1 p.2 p.2) S :=
      (hD2S.clm_apply continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
    have h2 : ContinuousOn (fun p : ComplexModel n × ComplexModel n =>
        fderiv ℝ (fderiv ℝ ρ) p.1 (Complex.I • p.2) (Complex.I • p.2)) S :=
      (hD2S.clm_apply (continuous_snd.const_smul Complex.I).continuousOn).clm_apply
        (continuous_snd.const_smul Complex.I).continuousOn
    refine ((h1.add h2).div_const 4).congr fun p _ => ?_
    simp only [leviForm, realHessian_eq_fderiv, Pi.add_apply]
  obtain ⟨p, hpS, hpmin⟩ := hSc.exists_isMinOn hSne hfc
  have hp2 : p.2 ≠ 0 := by
    intro h; have := hpS.2; rw [mem_sphere_zero_iff_norm, h, norm_zero] at this;
      exact zero_ne_one this
  refine ⟨leviForm ρ p.1 p.2, hlevi _ (hKW hpS.1) _ hp2, fun z hz v => ?_⟩
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u := ‖v‖⁻¹ • v with hu
  have huS : (z, u) ∈ S := ⟨hz, by simp [hu, norm_smul, inv_mul_cancel₀ hvn.ne']⟩
  have hmin : leviForm ρ p.1 p.2 ≤ leviForm ρ z u := hpmin huS
  have hvu : v = ‖v‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hvn.ne', one_smul]
  rw [hvu, leviForm_smul_right, norm_smul, Real.norm_of_nonneg hvn.le,
    show ‖u‖ = 1 by simp [hu, norm_smul, inv_mul_cancel₀ hvn.ne']]
  nlinarith [sq_nonneg ‖v‖]

/-- Uniform continuity on a compact set, in normed form (stated for a general normed group so
that it applies to the nested type `E →L[ℝ] E →L[ℝ] ℝ`). -/
theorem exists_pos_forall_norm_sub_lt {Y : Type*} [NormedAddCommGroup Y]
    {K : Set (ComplexModel n)} (hK : IsCompact K) {f : ComplexModel n → Y} (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → ‖f x - f y‖ < ε := by
  obtain ⟨δ, hδ, h⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hf) ε hε
  exact ⟨δ, hδ, fun x hx y hy hxy => by rw [← dist_eq_norm]; exact h x hx y hy hxy⟩

/-- **Second-order Taylor bound with a nearly constant Hessian**: if `‖D²ρ(z₀ + y) - D²ρ(z₀)‖ ≤ ε`
for `‖y‖ ≤ ‖h‖` (and `ρ` is `C²` there), then
`ρ(z₀ + h) - ρ(z₀) - Dρ(z₀) h - ½ D²ρ(z₀)(h, h) ≥ -ε ‖h‖²`. -/
theorem neg_mul_le_taylor_remainder {ρ : ComplexModel n → ℝ} {z₀ h : ComplexModel n} {ε : ℝ}
    (hρ : ∀ y ∈ closedBall (0 : ComplexModel n) ‖h‖, ContDiffAt ℝ 2 ρ (z₀ + y))
    (hε : ∀ y ∈ closedBall (0 : ComplexModel n) ‖h‖,
      ‖fderiv ℝ (fderiv ℝ ρ) (z₀ + y) - fderiv ℝ (fderiv ℝ ρ) z₀‖ ≤ ε) :
    -(ε * ‖h‖ ^ 2) ≤ ρ (z₀ + h) - ρ z₀ - fderiv ℝ ρ z₀ h -
      fderiv ℝ (fderiv ℝ ρ) z₀ h h / 2 := by
  set s := closedBall (0 : ComplexModel n) ‖h‖ with hs
  set B := fderiv ℝ (fderiv ℝ ρ) z₀ with hB
  have h0s : (0 : ComplexModel n) ∈ s := mem_closedBall_self (norm_nonneg h)
  have hhs : h ∈ s := by simp [hs]
  have hz₀ : ContDiffAt ℝ 2 ρ z₀ := by simpa using hρ 0 h0s
  have hsymm : ∀ v w, B v w = B w v := fun v w => hz₀.isSymmSndFDerivAt (by simp) v w
  -- the derivative of the remainder
  set DΦ : ComplexModel n → (ComplexModel n →L[ℝ] ℝ) :=
    fun y => fderiv ℝ ρ (z₀ + y) - fderiv ℝ ρ z₀ - B y with hDΦ
  have hDΦd : ∀ y ∈ s, HasFDerivWithinAt DΦ (fderiv ℝ (fderiv ℝ ρ) (z₀ + y) - B) s y := by
    intro y hy
    have hD : DifferentiableAt ℝ (fderiv ℝ ρ) (z₀ + y) :=
      ((hρ y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h1 : HasFDerivAt (fun y => fderiv ℝ ρ (z₀ + y)) (fderiv ℝ (fderiv ℝ ρ) (z₀ + y)) y := by
      have := hD.hasFDerivAt.comp y ((hasFDerivAt_id y).const_add z₀)
      simpa [Function.comp_def] using this
    exact ((h1.sub_const _).sub B.hasFDerivAt).hasFDerivWithinAt
  have hDΦ0 : DΦ 0 = 0 := by simp [hDΦ]
  have hDΦb : ∀ y ∈ s, ‖DΦ y‖ ≤ ε * ‖h‖ := by
    intro y hy
    have := (convex_closedBall (0 : ComplexModel n)
      ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hDΦd (fun x hx => hε x hx) h0s hy
    rw [hDΦ0, sub_zero, sub_zero] at this
    have hε0 : 0 ≤ ε := (ContinuousLinearMap.opNorm_nonneg _).trans (hε 0 h0s)
    have hy' : ‖y‖ ≤ ‖h‖ := by simpa [hs] using hy
    exact this.trans (mul_le_mul_of_nonneg_left hy' hε0)
  -- the remainder itself
  set Φ : ComplexModel n → ℝ :=
    fun y => ρ (z₀ + y) - ρ z₀ - fderiv ℝ ρ z₀ y - B y y / 2 with hΦ
  have hΦd : ∀ y ∈ s, HasFDerivWithinAt Φ (DΦ y) s y := by
    intro y hy
    have hρd : DifferentiableAt ℝ ρ (z₀ + y) := (hρ y hy).differentiableAt (by norm_num)
    have h1 : HasFDerivAt (fun y => ρ (z₀ + y)) (fderiv ℝ ρ (z₀ + y)) y := by
      have := hρd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_add z₀)
      simpa [Function.comp_def] using this
    have hquad : HasFDerivAt (fun y => B y y) (B y + B.flip y) y := by
      have h2 : HasFDerivAt (fun y => B y) B y := B.hasFDerivAt
      simpa using h2.clm_apply (hasFDerivAt_id y)
    have h3 : HasFDerivAt Φ (fderiv ℝ ρ (z₀ + y) - fderiv ℝ ρ z₀ - (2⁻¹ : ℝ) • (B y + B.flip y))
      y := by
      have := ((h1.sub_const (ρ z₀)).sub (fderiv ℝ ρ z₀).hasFDerivAt).sub
        (hquad.const_mul (2⁻¹ : ℝ))
      have hfun : Φ = (fun x => ρ (z₀ + x) - ρ z₀) - ⇑(fderiv ℝ ρ z₀) -
          fun y => 2⁻¹ * (B y) y := by
        funext y'
        simp only [hΦ, Pi.sub_apply]; ring
      rw [hfun]; exact this
    have heq : fderiv ℝ ρ (z₀ + y) - fderiv ℝ ρ z₀ - (2⁻¹ : ℝ) • (B y + B.flip y) = DΦ y := by
      ext w
      simp only [hDΦ, sub_apply, smul_apply,
        add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul, hsymm w y]
      ring
    rw [heq] at h3
    exact h3.hasFDerivWithinAt
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  have hmvt := (convex_closedBall (0 : ComplexModel n)
    ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hΦd hDΦb h0s hhs
  rw [hΦ0, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
  have : -(ε * ‖h‖ ^ 2) ≤ Φ h := by
    have := neg_abs_le (Φ h)
    nlinarith
  simpa [hΦ] using this

/-- **The normalised potential** (Błocki, `blocki05-uniform-estimate:page-0004`,
`lnm2038-monge-ampere:page-0221`): uniform `r, a` such that for every `z₀ ∈ closedBall c R`,
`g = ρ - pluriharmonicPart ρ z₀` vanishes at `z₀`, is `≥ 0` on `B(z₀, 2r)` and `≥ a` on
`B(z₀, 2r) \ B(z₀, r)`. -/
theorem exists_normalized_potential (hn : 0 < n) {ρ : ComplexModel n → ℝ}
    {W : Set (ComplexModel n)} (hW : IsOpen W) (hρ : ContDiffOn ℝ 2 ρ W)
    (hlevi : ∀ z ∈ W, ∀ v, v ≠ 0 → 0 < leviForm ρ z v) {c : ComplexModel n} {R : ℝ}
    (hR : 0 < R) (hcW : closedBall c (3 * R) ⊆ W) :
    ∃ r a : ℝ, 0 < r ∧ r ≤ R ∧ 0 < a ∧ ∀ z₀ ∈ closedBall c R,
      ρ z₀ - pluriharmonicPart ρ z₀ z₀ = 0 ∧
      (∀ z ∈ ball z₀ (2 * r), 0 ≤ ρ z - pluriharmonicPart ρ z₀ z) ∧
      (∀ z ∈ ball z₀ (2 * r), r ≤ ‖z - z₀‖ → a ≤ ρ z - pluriharmonicPart ρ z₀ z) := by
  set K := closedBall c (3 * R) with hKdef
  have hKc : IsCompact K := isCompact_closedBall c (3 * R)
  obtain ⟨l, hl, hlK⟩ := exists_pos_mul_norm_sq_le_leviForm hn hW hρ hlevi hKc hcW
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ ρ)) W :=
    (hρ.fderiv_of_isOpen hW (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hW le_rfl
  obtain ⟨δ, hδ, hδK⟩ := exists_pos_forall_norm_sub_lt
    (Y := ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) hKc (hD2.mono hcW) (half_pos hl)
  set r := min R (δ / 2) with hrdef
  have hr : 0 < r := lt_min hR (half_pos hδ)
  have hrR : r ≤ R := min_le_left _ _
  have hrδ : 2 * r ≤ δ := by have := min_le_right R (δ / 2); linarith
  refine ⟨r, l * r ^ 2 / 2, hr, hrR, by positivity, fun z₀ hz₀ => ?_⟩
  -- the key lower bound `g (z₀ + h) ≥ (l/2) ‖h‖²` for `‖h‖ < 2r`
  have hmemK : ∀ y : ComplexModel n, ‖y‖ < 2 * r → z₀ + y ∈ K := by
    intro y hy
    rw [hKdef, mem_closedBall, dist_eq_norm]
    have : ‖z₀ - c‖ ≤ R := by simpa [dist_eq_norm] using hz₀
    calc ‖z₀ + y - c‖ = ‖(z₀ - c) + y‖ := by congr 1; abel
      _ ≤ ‖z₀ - c‖ + ‖y‖ := norm_add_le _ _
      _ ≤ 3 * R := by linarith
  have hz₀K : z₀ ∈ K := by
    have hzero : ‖(0 : ComplexModel n)‖ < 2 * r := by
      simpa only [norm_zero] using mul_pos two_pos hr
    simpa only [add_zero] using hmemK 0 hzero
  have hkey : ∀ h : ComplexModel n, ‖h‖ < 2 * r →
      l / 2 * ‖h‖ ^ 2 ≤ ρ (z₀ + h) - pluriharmonicPart ρ z₀ (z₀ + h) := by
    intro h hh
    have hball : ∀ y ∈ closedBall (0 : ComplexModel n) ‖h‖, ‖y‖ < 2 * r := fun y hy => by
      have : ‖y‖ ≤ ‖h‖ := by simpa using hy
      linarith
    have hρy : ∀ y ∈ closedBall (0 : ComplexModel n) ‖h‖, ContDiffAt ℝ 2 ρ (z₀ + y) :=
      fun y hy => hρ.contDiffAt (hW.mem_nhds (hcW (hmemK y (hball y hy))))
    have hεy : ∀ y ∈ closedBall (0 : ComplexModel n) ‖h‖,
        ‖fderiv ℝ (fderiv ℝ ρ) (z₀ + y) - fderiv ℝ (fderiv ℝ ρ) z₀‖ ≤ l / 2 := by
      intro y hy
      have hd : dist (z₀ + y) z₀ < δ := by
        rw [dist_eq_norm, add_sub_cancel_left]; linarith [hball y hy]
      exact (hδK (z₀ + y) (hmemK y (hball y hy)) z₀ hz₀K hd).le
    have hT := neg_mul_le_taylor_remainder hρy hεy
    have hL := hlK z₀ hz₀K h
    have hgeq : ρ (z₀ + h) - pluriharmonicPart ρ z₀ (z₀ + h) =
        (ρ (z₀ + h) - ρ z₀ - fderiv ℝ ρ z₀ h - fderiv ℝ (fderiv ℝ ρ) z₀ h h / 2) +
          leviForm ρ z₀ h := by
      simp only [pluriharmonicPart, add_sub_cancel_left, antiHalf_apply, leviForm,
        realHessian_eq_fderiv, add_zero]
      ring
    rw [hgeq]
    nlinarith
  refine ⟨by simp [pluriharmonicPart], fun z hz => ?_, fun z hz hrz => ?_⟩
  · have hh : ‖z - z₀‖ < 2 * r := by rwa [mem_ball, dist_eq_norm] at hz
    have := hkey (z - z₀) hh
    rw [add_sub_cancel] at this
    exact le_trans (by positivity) this
  · have hh : ‖z - z₀‖ < 2 * r := by rwa [mem_ball, dist_eq_norm] at hz
    have := hkey (z - z₀) hh
    rw [add_sub_cancel] at this
    refine le_trans ?_ this
    have : r ^ 2 ≤ ‖z - z₀‖ ^ 2 := by gcongr
    nlinarith

end SGPT.Foundations.Analysis.Pending.KahlerPotentialNormalization
