/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedFourierEnergy

/-!
# The weak form of one damped frequency

At a fixed frequency the forced mild equation of `lem:regularised-forced` is
the damped Duhamel formula `y(t) = e^{-λt} y₀ + ∫₀ᵗ e^{-λ(t-s)} g(s) ds`.
Against a continuously differentiable test vanishing at both ends of the time
interval it satisfies `∫ ⟨y, -θ' + λθ⟩ = ∫ ⟨g, θ⟩`, by integration by parts for
absolutely continuous functions. This is the frequency form of
`eq:reg-momentum-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace CKN.Leray

/-- The weak form of a real damped Duhamel formula with integrable source. -/
theorem damped_duhamel_test_identity (lam a0 : ℝ) (g a θ θ' : ℝ → ℝ) {T : ℝ}
    (hg : IntervalIntegrable g volume 0 T)
    (ha : ∀ τ ∈ uIcc 0 T, a τ = Real.exp (-lam * τ) * a0 +
      ∫ s in (0 : ℝ)..τ, Real.exp (-lam * (τ - s)) * g s)
    (hθ : ∀ t, HasDerivAt θ (θ' t) t) (hθ' : Continuous θ') (h0 : θ 0 = 0) (hT : θ T = 0) :
    ∫ t in (0 : ℝ)..T, a t * (-θ' t + lam * θ t) = ∫ t in (0 : ℝ)..T, g t * θ t := by
  let e : ℝ → ℝ := fun s => Real.exp (lam * s) * g s
  have heint : IntervalIntegrable e volume 0 T :=
    hg.continuousOn_mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  let A : ℝ → ℝ := fun τ => a0 + ∫ s in (0 : ℝ)..τ, e s
  have haA : ∀ τ ∈ uIcc 0 T, a τ = Real.exp (-lam * τ) * A τ := by
    intro τ hτ
    rw [ha τ hτ]
    simp only [A, mul_add]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [e]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hAac : AbsolutelyContinuousOnInterval A 0 T := by
    have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => a0) 0 T :=
      (contDiffOn_const (c := a0)).absolutelyContinuousOnInterval
    have h2 := heint.absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) Set.left_mem_uIcc
    exact h1.add h2
  let E : ℝ → ℝ := fun τ => Real.exp (-lam * τ) * θ τ
  let E' : ℝ → ℝ := fun τ => -lam * Real.exp (-lam * τ) * θ τ + Real.exp (-lam * τ) * θ' τ
  have hEd : ∀ τ, HasDerivAt E (E' τ) τ := by
    intro τ
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-lam * s)) (Real.exp (-lam * τ) * -lam) τ := by
      have := ((hasDerivAt_id τ).const_mul (-lam)).exp
      simpa using this
    have h2 := h1.mul (hθ τ)
    convert h2 using 1
    simp only [E']
    ring
  have hE'c : Continuous E' := by
    have hθc : Continuous θ := continuous_iff_continuousAt.2 fun τ => (hθ τ).continuousAt
    simp only [E']
    fun_prop
  have hEac : AbsolutelyContinuousOnInterval E 0 T := by
    refine ContDiffOn.absolutelyContinuousOnInterval ?_
    have hc : ContDiff ℝ 1 E := by
      rw [contDiff_one_iff_deriv]
      refine ⟨fun τ => (hEd τ).differentiableAt, ?_⟩
      have : deriv E = E' := funext fun τ => (hEd τ).deriv
      rw [this]
      exact hE'c
    exact hc.contDiffOn
  have hIBP := hAac.integral_mul_deriv_eq_deriv_mul hEac
  have hE0 : E 0 = 0 := by simp [E, h0]
  have hET : E T = 0 := by simp [E, hT]
  rw [hE0, hET, mul_zero, mul_zero, sub_zero, zero_sub] at hIBP
  have hderivE : ∀ τ, deriv E τ = E' τ := fun τ => (hEd τ).deriv
  have hderivA : ∀ᵐ s, s ∈ uIoc 0 T → deriv A s * E s = g s * θ s := by
    filter_upwards [heint.ae_hasDerivAt_integral] with s hs hsmem
    have hsI : s ∈ uIcc 0 T := uIoc_subset_uIcc hsmem
    have hAd : HasDerivAt A (e s) s := by
      have := hs hsI 0 Set.left_mem_uIcc
      simpa [A] using this.const_add a0
    rw [hAd.deriv]
    simp only [e, E]
    have hexp : Real.exp (lam * s) * Real.exp (-lam * s) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (g s * θ s) * hexp
  rw [intervalIntegral.integral_congr_ae hderivA] at hIBP
  have hleft : ∫ t in (0 : ℝ)..T, a t * (-θ' t + lam * θ t) =
      ∫ t in (0 : ℝ)..T, -(A t * deriv E t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [haA t ht, hderivE]
    simp only [E']
    ring
  rw [hleft, intervalIntegral.integral_neg, hIBP, neg_neg]

/-- The weak form of a damped Duhamel formula with values in complex
three-vectors: `∫ Re ⟨y, -Θ' + λΘ⟩ = ∫ Re ⟨g, Θ⟩`. -/
theorem damped_duhamel_complexVec3_test_identity (lam : ℝ) (y0 : ComplexVec3)
    (g y Θ Θ' : ℝ → ComplexVec3) {T : ℝ} (hg : IntervalIntegrable g volume 0 T)
    (hy : ∀ τ ∈ uIcc 0 T, y τ = (Real.exp (-lam * τ) : ℂ) • y0 +
      ∫ s in (0 : ℝ)..τ, (Real.exp (-lam * (τ - s)) : ℂ) • g s)
    (hΘ : ∀ t, HasDerivAt Θ (Θ' t) t) (hΘ' : Continuous Θ') (h0 : Θ 0 = 0) (hT : Θ T = 0) :
    ∫ t in (0 : ℝ)..T, (inner ℂ (y t) (-Θ' t + (lam : ℂ) • Θ t)).re =
      ∫ t in (0 : ℝ)..T, (inner ℂ (g t) (Θ t)).re := by
  let L := complexVec3RealCoord
  have hgk : ∀ k, IntervalIntegrable (fun s => L k (g s)) volume 0 T := fun k =>
    ⟨(L k).integrable_comp hg.1, (L k).integrable_comp hg.2⟩
  have hsmul : ∀ (k : Fin 3 × Bool) (c : ℝ) (x : ComplexVec3),
      L k ((c : ℂ) • x) = c * L k x := by
    intro k c x
    rcases k with ⟨i, b⟩
    cases b
    · simp only [L, complexVec3RealCoord_false, PiLp.smul_apply, smul_eq_mul,
        Complex.im_ofReal_mul]
    · simp only [L, complexVec3RealCoord_true, PiLp.smul_apply, smul_eq_mul,
        Complex.re_ofReal_mul]
  have hcomp : ∀ k, ∀ τ ∈ uIcc 0 T, L k (y τ) = Real.exp (-lam * τ) * L k y0 +
      ∫ s in (0 : ℝ)..τ, Real.exp (-lam * (τ - s)) * L k (g s) := by
    intro k τ hτ
    have hsub : uIcc 0 τ ⊆ uIcc 0 T := Set.uIcc_subset_uIcc Set.left_mem_uIcc hτ
    have hint : IntervalIntegrable
        (fun s => (Real.exp (-lam * (τ - s)) : ℂ) • g s) volume 0 τ := by
      refine (hg.mono_set hsub).continuousOn_smul ?_
      exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn
    rw [hy τ hτ, map_add, hsmul, ← (L k).intervalIntegral_comp_comm hint]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    exact hsmul k _ _
  have hθk : ∀ k t, HasDerivAt (fun s => L k (Θ s)) (L k (Θ' t)) t := fun k t =>
    (L k).hasFDerivAt.comp_hasDerivAt t (hΘ t)
  have hid : ∀ k, ∫ t in (0 : ℝ)..T, L k (y t) * (-L k (Θ' t) + lam * L k (Θ t)) =
      ∫ t in (0 : ℝ)..T, L k (g t) * L k (Θ t) := fun k =>
    damped_duhamel_test_identity lam (L k y0) (fun s => L k (g s)) (fun s => L k (y s))
      (fun s => L k (Θ s)) (fun s => L k (Θ' s)) (hgk k) (hcomp k) (hθk k)
      ((L k).continuous.comp hΘ') (by simp [h0]) (by simp [hT])
  have hcont : ∀ k, ContinuousOn (fun s => L k (y s)) (uIcc 0 T) := fun k =>
    damped_duhamel_continuousOn lam (L k y0) (fun s => L k (g s)) (fun s => L k (y s))
      (hgk k) (hcomp k)
  have hΘc : Continuous Θ := continuous_iff_continuousAt.2 fun τ => (hΘ τ).continuousAt
  have hleftint : ∀ k, IntervalIntegrable
      (fun t => L k (y t) * (-L k (Θ' t) + lam * L k (Θ t))) volume 0 T := fun k =>
    ((hcont k).mul (((L k).continuous.comp hΘ').neg.add
      (continuous_const.mul ((L k).continuous.comp hΘc))).continuousOn).intervalIntegrable
  have hrightint : ∀ k, IntervalIntegrable (fun t => L k (g t) * L k (Θ t)) volume 0 T :=
    fun k => (hgk k).mul_continuousOn ((L k).continuous.comp hΘc).continuousOn
  have hinnerL : ∀ t, (inner ℂ (y t) (-Θ' t + (lam : ℂ) • Θ t)).re =
      ∑ k, L k (y t) * (-L k (Θ' t) + lam * L k (Θ t)) := by
    intro t
    rw [complexVec3_inner_re_eq_sum_realCoord]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_neg, hsmul]
  have hinnerR : ∀ t, (inner ℂ (g t) (Θ t)).re = ∑ k, L k (g t) * L k (Θ t) := fun t =>
    complexVec3_inner_re_eq_sum_realCoord (g t) (Θ t)
  simp_rw [hinnerL, hinnerR]
  rw [intervalIntegral.integral_finsetSum fun k _ => hleftint k,
    intervalIntegral.integral_finsetSum fun k _ => hrightint k]
  exact Finset.sum_congr rfl fun k _ => hid k

/-- The weak form of the forced frequency representative at one frequency:
against a test vanishing at `0` and `T`, `∫ Re ⟨Y, -Θ' + λΘ⟩ = ∫ Re ⟨ℙ̂ g, Θ⟩`
with the unprojected source `g`. -/
theorem forcedFourierRep_test_identity {B : L2Vec3 → ComplexVec3}
    {Fh : L2Vec3 × ℝ → ComplexTensor3} {Hh : L2Vec3 × ℝ → ComplexVec3}
    (ξ : L2Vec3) {T : ℝ} (hT : 0 ≤ T)
    (hgint : IntegrableOn (fun s => forcedFourierSource Fh Hh (ξ, s)) (Ioc 0 T))
    {Θ Θ' : ℝ → ComplexVec3} (hΘ : ∀ t, HasDerivAt Θ (Θ' t) t) (hΘ' : Continuous Θ')
    (h0 : Θ 0 = 0) (hTz : Θ T = 0) :
    ∫ t in Ioc 0 T, (inner ℂ (forcedFourierRep B Fh Hh (ξ, t))
        (-Θ' t + (forcedFourierLam ξ : ℂ) • Θ t)).re =
      ∫ t in Ioc 0 T, (inner ℂ (leraySymbol ξ (forcedFourierSource Fh Hh (ξ, t))) (Θ t)).re := by
  let P := leraySymbol ξ
  let g : ℝ → ComplexVec3 := fun s => P (forcedFourierSource Fh Hh (ξ, s))
  have hgOn : IntegrableOn g (Ioc 0 T) := P.integrable_comp hgint
  have hg : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 hgOn
  have hy : ∀ τ ∈ uIcc 0 T, forcedFourierRep B Fh Hh (ξ, τ) =
      (Real.exp (-forcedFourierLam ξ * τ) : ℂ) • B ξ +
      ∫ s in (0 : ℝ)..τ, (Real.exp (-forcedFourierLam ξ * (τ - s)) : ℂ) • g s := by
    intro τ hτ
    rw [uIcc_of_le hT] at hτ
    simp only [forcedFourierRep, heatSymbol_eq_exp_lam]
    rw [intervalIntegral.integral_of_le hτ.1]
  have hid := damped_duhamel_complexVec3_test_identity (forcedFourierLam ξ) (B ξ) g
    (fun τ => forcedFourierRep B Fh Hh (ξ, τ)) Θ Θ' hg hy hΘ hΘ' h0 hTz
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT] at hid
  exact hid

end CKN.Leray

end
