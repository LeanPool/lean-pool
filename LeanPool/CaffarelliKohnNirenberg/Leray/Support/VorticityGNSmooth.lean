/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityDivCurlSmooth

/-!
# A local Gagliardo–Nirenberg estimate for bounded smooth functions

For a smooth function bounded by `M` on a ball, the fourth power of its gradient on a smaller ball
is controlled by `M²` times the square integrals of its first and second derivatives on the larger
ball. This is the smooth estimate `‖∇v‖₄² ≤ C ‖v‖_∞ ‖∇²v‖₂` behind the first product bound of
`lem:vorticity-products` of the Escauriaza–Seregin–Šverák manuscript. With `A = |∇f|²` and a cutoff `η`, one integration by parts gives
`∫ η⁴ A² = -Σⱼ ∫ f ∂ⱼ(η⁴ A ∂ⱼ f)`, and a pointwise Young inequality absorbs three quarters of the
left side.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace CKN

/-- Young's inequality in the form used for absorption. -/
theorem vorticityGNSmooth_young {c P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hc : c ^ 2 ≤ 4 * P * Q) : c ≤ P + Q := by
  nlinarith only [sq_nonneg (P - Q), hP, hQ, hc]

/-- A bounded factor in front of a product. -/
theorem vorticityGNSmooth_neg_mul_le {F M T : ℝ} (hF : |F| ≤ M) : -(F * T) ≤ M * |T| := by
  calc
    -(F * T) ≤ |F * T| := neg_le_abs _
    _ = |F| * |T| := abs_mul _ _
    _ ≤ M * |T| := mul_le_mul_of_nonneg_right hF (abs_nonneg _)

/-- The quadratic form of a matrix is controlled by its Frobenius norm. -/
theorem vorticityGNSmooth_quadratic_sq_le (g : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ) :
    (∑ j : Fin 3, ∑ k : Fin 3, (g j * g k) * H j k) ^ 2 ≤
      (∑ j : Fin 3, g j ^ 2) ^ 2 * ∑ j : Fin 3, ∑ k : Fin 3, H j k ^ 2 := by
  have hprod : ∀ F : Fin 3 → Fin 3 → ℝ, ∑ j : Fin 3, ∑ k : Fin 3, F j k =
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin 3 × Fin 3)), F p.1 p.2 :=
    fun F => (Finset.sum_product Finset.univ Finset.univ
      (fun p : Fin 3 × Fin 3 => F p.1 p.2)).symm
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ ×ˢ Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p => g p.1 * g p.2) (fun p => H p.1 p.2)
  have hsq : ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin 3 × Fin 3)),
      (g p.1 * g p.2) ^ 2 = (∑ j : Fin 3, g j ^ 2) ^ 2 := by
    rw [← hprod (fun j k => (g j * g k) ^ 2), sq (∑ j : Fin 3, g j ^ 2), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hprod (fun j k => (g j * g k) * H j k), hprod (fun j k => H j k ^ 2), ← hsq]
  exact hCS

/-- The pointwise inequality behind the absorption argument. -/
theorem vorticityGNSmooth_pointwise {F M η : ℝ} (d g : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ)
    (hF : |F| ≤ M) :
    -(F * (4 * η ^ 3 * (∑ j : Fin 3, g j ^ 2) * (∑ j : Fin 3, d j * g j) +
        η ^ 4 * ((∑ j : Fin 3, ∑ k : Fin 3, 2 * g k * H j k * g j) +
          (∑ j : Fin 3, g j ^ 2) * ∑ j : Fin 3, H j j))) ≤
      3 / 4 * (η ^ 4 * (∑ j : Fin 3, g j ^ 2) ^ 2) +
        M ^ 2 * (16 * η ^ 2 * (∑ j : Fin 3, d j ^ 2) * (∑ j : Fin 3, g j ^ 2) +
          7 * η ^ 4 * ∑ j : Fin 3, ∑ k : Fin 3, H k j ^ 2) := by
  set A : ℝ := ∑ j : Fin 3, g j ^ 2 with hAdef
  set D : ℝ := ∑ j : Fin 3, d j ^ 2 with hDdef
  set HH : ℝ := ∑ j : Fin 3, ∑ k : Fin 3, H k j ^ 2 with hHHdef
  set S1 : ℝ := ∑ j : Fin 3, d j * g j with hS1def
  set S2 : ℝ := ∑ j : Fin 3, ∑ k : Fin 3, 2 * g k * H j k * g j with hS2def
  set S3 : ℝ := ∑ j : Fin 3, H j j with hS3def
  have hM : 0 ≤ M := (abs_nonneg F).trans hF
  have hA : 0 ≤ A := by positivity
  have hD : 0 ≤ D := by positivity
  have hHH : 0 ≤ HH := by positivity
  have hS1 : S1 ^ 2 ≤ D * A := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ d g
  have hHHcomm : HH = ∑ j : Fin 3, ∑ k : Fin 3, H j k ^ 2 := by
    rw [hHHdef, Finset.sum_comm]
  have hS2 : S2 ^ 2 ≤ 4 * A ^ 2 * HH := by
    have hre : S2 = 2 * ∑ j : Fin 3, ∑ k : Fin 3, (g j * g k) * H j k := by
      rw [hS2def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hre, hHHcomm, mul_pow]
    have := vorticityGNSmooth_quadratic_sq_le g H
    nlinarith only [this]
  have hS3 : S3 ^ 2 ≤ 3 * HH := by
    have h1 := vorticityDivCurlSmooth_sum_sq_le (fun j => H j j)
    have h2 : ∑ j : Fin 3, H j j ^ 2 ≤ HH := by
      rw [hHHdef]
      refine Finset.sum_le_sum fun j _ => ?_
      exact Finset.single_le_sum (f := fun k => H k j ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have h1' : S3 ^ 2 ≤ 3 * ∑ j : Fin 3, H j j ^ 2 := h1
    linarith only [h1', h2]
  set P : ℝ := η ^ 4 * A ^ 2 / 4 with hPdef
  have hP : 0 ≤ P := by positivity
  -- first term
  have hT1 : -(F * (4 * η ^ 3 * A * S1)) ≤ P + 16 * M ^ 2 * η ^ 2 * D * A := by
    refine (vorticityGNSmooth_neg_mul_le hF).trans ?_
    apply vorticityGNSmooth_young hP (by positivity)
    calc
      (M * |4 * η ^ 3 * A * S1|) ^ 2 = M ^ 2 * 16 * η ^ 6 * A ^ 2 * S1 ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
      _ ≤ M ^ 2 * 16 * η ^ 6 * A ^ 2 * (D * A) := by gcongr
      _ = 4 * P * (16 * M ^ 2 * η ^ 2 * D * A) := by
        rw [hPdef]
        ring
  have hT2 : -(F * (η ^ 4 * S2)) ≤ P + 4 * M ^ 2 * η ^ 4 * HH := by
    refine (vorticityGNSmooth_neg_mul_le hF).trans ?_
    apply vorticityGNSmooth_young hP (by positivity)
    calc
      (M * |η ^ 4 * S2|) ^ 2 = M ^ 2 * η ^ 8 * S2 ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
      _ ≤ M ^ 2 * η ^ 8 * (4 * A ^ 2 * HH) := by gcongr
      _ = 4 * P * (4 * M ^ 2 * η ^ 4 * HH) := by
        rw [hPdef]
        ring
  have hT3 : -(F * (η ^ 4 * (A * S3))) ≤ P + 3 * M ^ 2 * η ^ 4 * HH := by
    refine (vorticityGNSmooth_neg_mul_le hF).trans ?_
    apply vorticityGNSmooth_young hP (by positivity)
    calc
      (M * |η ^ 4 * (A * S3)|) ^ 2 = M ^ 2 * η ^ 8 * A ^ 2 * S3 ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
      _ ≤ M ^ 2 * η ^ 8 * A ^ 2 * (3 * HH) := by gcongr
      _ = 4 * P * (3 * M ^ 2 * η ^ 4 * HH) := by
        rw [hPdef]
        ring
  have hsplit : -(F * (4 * η ^ 3 * A * S1 + η ^ 4 * (S2 + A * S3))) =
      -(F * (4 * η ^ 3 * A * S1)) + -(F * (η ^ 4 * S2)) + -(F * (η ^ 4 * (A * S3))) := by
    ring
  rw [hsplit]
  have hfin : P + 16 * M ^ 2 * η ^ 2 * D * A + (P + 4 * M ^ 2 * η ^ 4 * HH) +
      (P + 3 * M ^ 2 * η ^ 4 * HH) =
      3 / 4 * (η ^ 4 * A ^ 2) + M ^ 2 * (16 * η ^ 2 * D * A + 7 * η ^ 4 * HH) := by
    rw [hPdef]
    ring
  linarith only [hT1, hT2, hT3, hfin]

/-- Coordinate derivative of a square. -/
theorem vorticityGNSmooth_deriv_sq {g : Vec3 → ℝ} {x : Vec3}
    (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    spatialDeriv (fun y => g y ^ 2) j x = 2 * g x * spatialDeriv g j x := by
  have hfun : (fun y => g y ^ 2) = fun y => g y * g y := by
    funext y
    ring
  rw [hfun, spatialDeriv_mul hg hg]
  ring

/-- Coordinate derivative of a sum of three squares. -/
theorem vorticityGNSmooth_deriv_sum_sq {g : Fin 3 → Vec3 → ℝ}
    (hg : ∀ k, Differentiable ℝ (g k)) (j : Fin 3) (x : Vec3) :
    spatialDeriv (fun y => ∑ k : Fin 3, g k y ^ 2) j x =
      ∑ k : Fin 3, 2 * g k x * spatialDeriv (g k) j x := by
  have hfun : (fun y => ∑ k : Fin 3, g k y ^ 2) =
      fun y => (g 0 y ^ 2 + g 1 y ^ 2) + g 2 y ^ 2 := by
    funext y
    simp only [Fin.sum_univ_three]
  have h01 : DifferentiableAt ℝ (fun y => g 0 y ^ 2 + g 1 y ^ 2) x :=
    (((hg 0) x).pow 2).add (((hg 1) x).pow 2)
  have h2 : DifferentiableAt ℝ (fun y => g 2 y ^ 2) x := ((hg 2) x).pow 2
  have h0 : DifferentiableAt ℝ (fun y => g 0 y ^ 2) x := ((hg 0) x).pow 2
  have h1 : DifferentiableAt ℝ (fun y => g 1 y ^ 2) x := ((hg 1) x).pow 2
  rw [hfun, spatialDeriv_add h01 h2, spatialDeriv_add h0 h1,
    vorticityGNSmooth_deriv_sq ((hg 0) x), vorticityGNSmooth_deriv_sq ((hg 1) x),
    vorticityGNSmooth_deriv_sq ((hg 2) x), Fin.sum_univ_three]

/-- Coordinate derivative of a fourth power. -/
theorem vorticityGNSmooth_deriv_pow_four {η : Vec3 → ℝ} {x : Vec3}
    (hη : Differentiable ℝ η) (j : Fin 3) :
    spatialDeriv (fun y => η y ^ 4) j x = 4 * η x ^ 3 * spatialDeriv η j x := by
  have hfun : (fun y => η y ^ 4) = fun y => (η y * η y) * (η y * η y) := by
    funext y
    ring
  have hsq : DifferentiableAt ℝ (fun y => η y * η y) x := (hη x).mul (hη x)
  rw [hfun, spatialDeriv_mul hsq hsq, spatialDeriv_mul (hη x) (hη x)]
  ring

/-- Local Gagliardo–Nirenberg estimate for smooth functions bounded on a ball
(`lem:vorticity-products`, ESS). -/
theorem vorticityGNSmooth_local {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (f : Vec3 → ℝ) (M : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → 0 ≤ M → (∀ x ∈ vec3Ball x₀ R, |f x| ≤ M) →
      ∫ x in vec3Ball x₀ r, (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2 ≤
        C * M ^ 2 * ∫ x in vec3Ball x₀ R,
          (∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv f j) k x ^ 2 +
            ∑ j : Fin 3, spatialDeriv f j x ^ 2) := by
  obtain ⟨φ₀, hφ₀, hφ₀c, hφ₀supp, hφ₀one, hφ₀nn, hφ₀le⟩ := vorticitySpatialCutoff_exists hr hrR
  obtain ⟨L, hL0, hL1, _hL2⟩ := vorticitySmooth_derivative_bounds hφ₀ hφ₀c
  refine ⟨4 * (48 * L ^ 2 + 7), by positivity, ?_⟩
  intro x₀ f M hf hM hfM
  let η : Vec3 → ℝ := fun x => φ₀ (x - x₀)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := hφ₀.comp (contDiff_id.sub contDiff_const)
  have hηdiff : Differentiable ℝ η := hη.differentiable (by simp)
  have hηc : HasCompactSupport η := hφ₀c.comp_homeomorph (Homeomorph.subRight x₀)
  have hηd : ∀ x j, spatialDeriv η j x = spatialDeriv φ₀ j (x - x₀) := fun x j =>
    vorticitySpatialDeriv_translate φ₀ x₀ x j
  let g : Fin 3 → Vec3 → ℝ := fun j => spatialDeriv f j
  have hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) := fun j => contDiff_spatialDeriv_smooth hf j
  have hgdiff : ∀ j, Differentiable ℝ (g j) := fun j => (hg j).differentiable (by simp)
  let A : Vec3 → ℝ := fun y => ∑ k : Fin 3, g k y ^ 2
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := ContDiff.sum fun k _ => (hg k).pow 2
  let w : Vec3 → ℝ := fun y => η y ^ 4
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := hη.pow 4
  have hwc : HasCompactSupport w := by
    apply hηc.mono
    intro y hy hy0
    apply hy
    simp [w, hy0]
  let Φ : Fin 3 → Vec3 → ℝ := fun j y => w y * (A y * g j y)
  have hΦ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Φ j) := fun j => hw.mul (hA.mul (hg j))
  have hΦc : ∀ j, HasCompactSupport (Φ j) := fun j => hwc.mul_right
  have hΦd : ∀ j x, spatialDeriv (Φ j) j x =
      4 * η x ^ 3 * spatialDeriv η j x * (A x * g j x) +
        w x * ((∑ k : Fin 3, 2 * g k x * spatialDeriv (g k) j x) * g j x +
          A x * spatialDeriv (g j) j x) := by
    intro j x
    have hAx : DifferentiableAt ℝ A x := (hA.differentiable (by simp)) x
    have hwx : DifferentiableAt ℝ w x := (hw.differentiable (by simp)) x
    have hAg : DifferentiableAt ℝ (fun y => A y * g j y) x := hAx.mul ((hgdiff j) x)
    change spatialDeriv (fun y => w y * (A y * g j y)) j x = _
    rw [spatialDeriv_mul hwx hAg, spatialDeriv_mul hAx ((hgdiff j) x),
      vorticityGNSmooth_deriv_pow_four hηdiff j, vorticityGNSmooth_deriv_sum_sq hgdiff j x]
  have hK : IsCompact (tsupport η) := hηc
  have hout : ∀ x, x ∉ tsupport η → η x = 0 ∧ ∀ j, spatialDeriv η j x = 0 := by
    intro x hx
    refine ⟨image_eq_zero_of_notMem_tsupport hx, fun j => ?_⟩
    simp [spatialDeriv, fderiv_of_notMem_tsupport ℝ hx]
  -- the integrand identity and the integration by parts
  let E : Vec3 → ℝ := fun x => -∑ j : Fin 3, f x * spatialDeriv (Φ j) j x
  have hEformula : ∀ x, E x =
      -(f x * (4 * η x ^ 3 * A x * (∑ j : Fin 3, spatialDeriv η j x * g j x) +
        η x ^ 4 * ((∑ j : Fin 3, ∑ k : Fin 3, 2 * g k x * spatialDeriv (g k) j x * g j x) +
          A x * ∑ j : Fin 3, spatialDeriv (g j) j x))) := by
    intro x
    simp only [E, hΦd, w, Fin.sum_univ_three]
    ring
  have hΦderivCont : ∀ j, Continuous (spatialDeriv (Φ j) j) := fun j =>
    (contDiff_spatialDeriv_smooth (hΦ j) j).continuous
  have hΦderivc : ∀ j, HasCompactSupport (spatialDeriv (Φ j) j) := fun j =>
    (hΦc j).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hfΦint : ∀ j, Integrable (fun x => f x * spatialDeriv (Φ j) j x)
      (volume : Measure Vec3) := fun j =>
    (hf.continuous.mul (hΦderivCont j)).integrable_of_hasCompactSupport (hΦderivc j).mul_left
  have hgΦint : ∀ j, Integrable (fun x => g j x * Φ j x) (volume : Measure Vec3) := fun j =>
    ((hg j).continuous.mul (hΦ j).continuous).integrable_of_hasCompactSupport (hΦc j).mul_left
  have hEint : Integrable E (volume : Measure Vec3) :=
    (integrable_finsetSum _ fun j _ => hfΦint j).neg
  have hwA : ∀ x, w x * A x ^ 2 = ∑ j : Fin 3, g j x * Φ j x := by
    intro x
    simp only [Φ, A, Fin.sum_univ_three]
    ring
  have hwAint : Integrable (fun x => w x * A x ^ 2) (volume : Measure Vec3) := by
    simp only [hwA]
    exact integrable_finsetSum _ fun j _ => hgΦint j
  have hX : ∫ x, w x * A x ^ 2 = ∫ x, E x := by
    simp only [hwA, E]
    rw [integral_finsetSum _ fun j _ => hgΦint j, integral_neg,
      integral_finsetSum _ fun j _ => hfΦint j, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hibp := integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul hf (hΦ j) (hΦc j) j
    rw [hibp, neg_neg]
  -- the pointwise bound
  let HHs : Vec3 → ℝ := fun x => ∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv f j) k x ^ 2
  let G : Vec3 → ℝ := fun x =>
    16 * η x ^ 2 * (∑ j : Fin 3, spatialDeriv η j x ^ 2) * A x + 7 * η x ^ 4 * HHs x
  have hηderivCont : ∀ j, Continuous (spatialDeriv η j) := fun j =>
    (contDiff_spatialDeriv_smooth hη j).continuous
  have hHHcont : Continuous HHs :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      (contDiff_spatialDeriv_smooth (hg j) k).continuous.pow 2
  have hGint : Integrable G (volume : Measure Vec3) := by
    apply vorticityDivCurlSmooth_integrable hK
    · exact (((continuous_const.mul (hη.continuous.pow 2)).mul
        (continuous_finsetSum _ fun j _ => (hηderivCont j).pow 2)).mul hA.continuous).add
        ((continuous_const.mul (hη.continuous.pow 4)).mul hHHcont)
    · intro x hx
      simp [G, (hout x hx).1]
  have hpoint : ∀ x, E x ≤ 3 / 4 * (w x * A x ^ 2) + M ^ 2 * G x := by
    intro x
    by_cases hx : x ∈ vec3Ball x₀ R
    · rw [hEformula]
      exact vorticityGNSmooth_pointwise (fun j => spatialDeriv η j x) (fun j => g j x)
        (fun j k => spatialDeriv (g k) j x) (hfM x hx)
    · have hy : x ∉ tsupport η := by
        intro h
        apply hx
        have h' := hφ₀supp (show x - x₀ ∈ tsupport φ₀ from by
          rw [show η = φ₀ ∘ (Homeomorph.subRight x₀) from rfl,
            tsupport_comp_eq_preimage] at h
          exact h)
        simpa [vec3Ball] using h'
      obtain ⟨h0, hd0⟩ := hout x hy
      have hE0 : E x = 0 := by
        rw [hEformula]
        simp [h0, hd0]
      have hG0 : G x = 0 := by simp [G, h0]
      rw [hE0, hG0]
      simp [w, h0]
  have hRHS : ∫ x, (3 / 4 * (w x * A x ^ 2) + M ^ 2 * G x) =
      3 / 4 * (∫ x, w x * A x ^ 2) + M ^ 2 * ∫ x, G x := by
    rw [integral_add (hwAint.const_mul _) (hGint.const_mul _), integral_const_mul,
      integral_const_mul]
  have hmain : ∫ x, w x * A x ^ 2 ≤ 3 / 4 * (∫ x, w x * A x ^ 2) + M ^ 2 * ∫ x, G x := by
    calc
      ∫ x, w x * A x ^ 2 = ∫ x, E x := hX
      _ ≤ ∫ x, (3 / 4 * (w x * A x ^ 2) + M ^ 2 * G x) :=
        integral_mono hEint ((hwAint.const_mul _).add (hGint.const_mul _)) hpoint
      _ = 3 / 4 * (∫ x, w x * A x ^ 2) + M ^ 2 * ∫ x, G x := hRHS
  have hX4 : ∫ x, w x * A x ^ 2 ≤ 4 * M ^ 2 * ∫ x, G x := by
    linarith only [hmain]
  -- the integral of the error term
  have hBR : MeasurableSet (vec3Ball x₀ R) := (isOpen_vec3Ball x₀ R).measurableSet
  have hBr : MeasurableSet (vec3Ball x₀ r) := (isOpen_vec3Ball x₀ r).measurableSet
  let IR : Vec3 → ℝ := fun x => HHs x + A x
  have hIRcont : Continuous IR := hHHcont.add hA.continuous
  have hBRsub : vec3Ball x₀ R ⊆ Metric.closedBall x₀ R := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact ((norm_le_vec3EuclideanNorm (y - x₀)).trans (le_of_lt hy))
  have hIRint : IntegrableOn (fun x => (48 * L ^ 2 + 7) * IR x) (vec3Ball x₀ R)
      (volume : Measure Vec3) :=
    ((hIRcont.const_mul _).continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ R)).mono_set hBRsub
  have hGpoint : ∀ x, G x ≤ (vec3Ball x₀ R).indicator (fun x => (48 * L ^ 2 + 7) * IR x) x := by
    intro x
    by_cases hx : x ∈ vec3Ball x₀ R
    · rw [Set.indicator_of_mem hx]
      have hη1 : η x ≤ 1 := hφ₀le _
      have hη0 : 0 ≤ η x := hφ₀nn _
      have hη2 : η x ^ 2 ≤ 1 := by nlinarith only [hη1, hη0]
      have hη4 : η x ^ 4 ≤ 1 := by nlinarith only [hη2, sq_nonneg (η x)]
      have hdsum : ∑ j : Fin 3, spatialDeriv η j x ^ 2 ≤ 3 * L ^ 2 := by
        have hj : ∀ j, spatialDeriv η j x ^ 2 ≤ L ^ 2 := by
          intro j
          have h := pow_le_pow_left₀ (abs_nonneg _) (show |spatialDeriv η j x| ≤ L by
            rw [hηd]; exact hL1 _ j) 2
          rwa [sq_abs] at h
        simp only [Fin.sum_univ_three]
        linarith only [hj 0, hj 1, hj 2]
      have hAnn : 0 ≤ A x := by positivity
      have hHnn : 0 ≤ HHs x := by positivity
      have hdnn : 0 ≤ ∑ j : Fin 3, spatialDeriv η j x ^ 2 := by positivity
      have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
      have h1 : 16 * η x ^ 2 * (∑ j : Fin 3, spatialDeriv η j x ^ 2) * A x ≤
          48 * L ^ 2 * A x := by
        have : η x ^ 2 * (∑ j : Fin 3, spatialDeriv η j x ^ 2) ≤ 3 * L ^ 2 := by
          nlinarith only [hη2, hdsum, hdnn, sq_nonneg (η x)]
        nlinarith only [this, hAnn]
      have h2 : 7 * η x ^ 4 * HHs x ≤ 7 * HHs x := by nlinarith only [hη4, hHnn]
      simp only [G, IR]
      nlinarith only [h1, h2, hAnn, hHnn, hL2]
    · rw [Set.indicator_of_notMem hx]
      have hy : x ∉ tsupport η := by
        intro h
        apply hx
        have h' := hφ₀supp (show x - x₀ ∈ tsupport φ₀ from by
          rw [show η = φ₀ ∘ (Homeomorph.subRight x₀) from rfl,
            tsupport_comp_eq_preimage] at h
          exact h)
        simpa [vec3Ball] using h'
      simp [G, (hout x hy).1]
  have hGle : ∫ x, G x ≤ (48 * L ^ 2 + 7) * ∫ x in vec3Ball x₀ R, IR x := by
    have h := integral_mono hGint ((integrable_indicator_iff hBR).2 hIRint) hGpoint
    rwa [integral_indicator hBR, integral_const_mul] at h
  -- the inner ball
  have hinner : ∫ x in vec3Ball x₀ r, (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2 =
      ∫ x in vec3Ball x₀ r, w x * A x ^ 2 := by
    refine setIntegral_congr_fun hBr fun x hx => ?_
    have hxr : vec3EuclideanNorm (x - x₀) < r := hx
    have hone : η x = 1 := hφ₀one _ hxr.le
    simp only [w, A, g, hone]
    ring
  have hinner2 : ∫ x in vec3Ball x₀ r, w x * A x ^ 2 ≤ ∫ x, w x * A x ^ 2 :=
    setIntegral_le_integral hwAint (Eventually.of_forall fun x => by
      have : 0 ≤ η x := hφ₀nn _
      positivity)
  rw [hinner]
  calc
    ∫ x in vec3Ball x₀ r, w x * A x ^ 2 ≤ 4 * M ^ 2 * ∫ x, G x := hinner2.trans hX4
    _ ≤ 4 * M ^ 2 * ((48 * L ^ 2 + 7) * ∫ x in vec3Ball x₀ R, IR x) := by gcongr
    _ = 4 * (48 * L ^ 2 + 7) * M ^ 2 * ∫ x in vec3Ball x₀ R, IR x := by ring

end CKN
