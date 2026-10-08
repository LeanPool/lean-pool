/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnstrophyBalanceTerms

/-!
# The differential inequality `eq:aniso:closure:tested`

This module assembles the tested enstrophy balance of
*Regularity of asymptotically axisymmetric solutions to the 3D Navier–Stokes equations with
analytic forcing*, arXiv:2609.20803, from the three tested terms of
`CIV.Closure.EnstrophyBalanceTerms`.

Substituting the Cartesian vorticity equation `cartesian_vorticity_pde` in the time derivative
of `Y` splits it into a transport, a diffusion, a stretching and a force term. The first two
are integrated by parts, the cutoff errors they leave behind are constants because `∇χ` is
supported where `|u|` and `|ω|` are bounded, and the force term is bounded by `C (Y + 1)`.
What remains is

`½ Y' + M ≤ ∫ χ² (ω·∇u)·ω + C (Y + 1)`,

stated with `deriv Y t`, which is the form `closure_gronwall_bound` consumes.
-/

public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- Splitting the integral of a four-term sum. -/
private lemma integral_add4 {f1 f2 f3 f4 : Vec3 → ℝ} (h1 : Integrable f1) (h2 : Integrable f2)
    (h3 : Integrable f3) (h4 : Integrable f4) :
    ∫ x : Vec3, (f1 x + f2 x + f3 x + f4 x)
      = (∫ x : Vec3, f1 x) + (∫ x : Vec3, f2 x) + (∫ x : Vec3, f3 x) + ∫ x : Vec3, f4 x := by
  have h12 : Integrable (fun x : Vec3 => f1 x + f2 x) := h1.add h2
  have h123 : Integrable (fun x : Vec3 => f1 x + f2 x + f3 x) := h12.add h3
  rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]

/-! ### Stage (iii): the tested enstrophy balance -/

section Balance

variable {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-- **The tested enstrophy balance `eq:aniso:closure:tested`.** For a classical solution with a
`C²`-bounded force and a cutoff `χ` whose gradient is supported in a closed set `A` on which
`|u|` and `|ω|` are bounded on a time window `(t₀, 0)`, the cutoff enstrophy `Y` is
differentiable in time and

`½ Y' + M ≤ ∫ χ² (ω·∇u)·ω + C (Y + 1)`

on that same time window, with a constant depending only on `χ`, on the force bound and on
the bounds on `A`. The derivative is written as `deriv Y t`, the form in which
`closure_gronwall_bound` consumes it. -/
theorem cutoff_enstrophy_balance
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (hMf : ForceC2Bounded f)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ vec3Ball 0 1)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    {A : Set Vec3} (hAcl : IsClosed A) (hχA : ∀ x : Vec3, x ∉ A → fderiv ℝ χ x = 0)
    {Mu Mω : ℝ} (hMu : 0 ≤ Mu)
    (hubd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, |u (x, t) i| ≤ Mu)
    (hωbd : ∀ x ∈ A, ∀ t ∈ Ioo t₀ 0, ∀ i : Fin 3, |vorticityField u (x, t) i| ≤ Mω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ 0,
      HasDerivAt (cutoffEnstrophy χ u) (deriv (cutoffEnstrophy χ u) t) t ∧
        (1 / 2) * deriv (cutoffEnstrophy χ u) t + cutoffEnstrophyDissipation χ u t
          ≤ cutoffStretching χ u t + C * (cutoffEnstrophy χ u t + 1) := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hfc : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder := hsol.2.2.1
  have hdivu : ∀ z ∈ unitCylinder, ∑ j : Fin 3, spatialPartial (fun w => u w j) j z = 0 :=
    hsol.2.2.2.2
  have hsqχ : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => χ x ^ 2) := hχ.pow 2
  obtain ⟨C1, hC10, hC1⟩ :=
    abs_integral_cutoff_gradient_error_le hu hχ hχs hχU ht₀ hχA hMu hubd hωbd
  obtain ⟨C2, hC20, hC2⟩ :=
    abs_integral_cutoff_laplacian_error_le hu hχ hχs hχU ht₀ hAcl hχA hωbd
  obtain ⟨C3, hC30, hC3⟩ := abs_integral_cutoff_vorticity_force_le hu hfc hMf hχ hχs hχU ht₀
  refine ⟨C1 + C2 + C3, by linarith only [hC10, hC20, hC30], ?_⟩
  intro t ht
  have ht1 : t ∈ Ioo (-1 : ℝ) 0 := ⟨lt_trans ht₀.1 ht.1, ht.2⟩
  have hder : HasDerivAt (cutoffEnstrophy χ u)
      (∫ x : Vec3, χ x ^ 2 * (2 * ∑ i : Fin 3,
        curlComp u i (x, t) * timePartial (curlComp u i) (x, t))) t :=
    hasDerivAt_cutoffEnstrophy hu hχ hχs hχU ht1
  refine ⟨hder.differentiableAt.hasDerivAt, ?_⟩
  -- the four tested terms, written with the classical partial derivatives of the slice
  have hT : (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
        ∑ j : Fin 3, u (x, t) j *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
      = -(1 / 2) * ∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
          ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j :=
    integral_cutoff_vorticity_transport hu hdivu hχ hχs hχU ht1
  have hDf : (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
        ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 =>
          fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x (basisVec j))
      = - cutoffEnstrophyDissipation χ u t
        + (1 / 2) * ∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
            ∑ j : Fin 3, fderiv ℝ
              (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x
                (basisVec j) :=
    integral_cutoff_vorticity_diffusion hu hχ hχs hχU ht1
  have hS : cutoffStretching χ u t = ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      curlComp u j (x, t) * fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j) *
        curlComp u i (x, t) := rfl
  have hE1 : |∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j| ≤ C1 :=
    hC1 t ht
  have hE2 : |∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
      ∑ j : Fin 3, fderiv ℝ
        (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j)|
        ≤ C2 := hC2 t ht
  have hE3 : |∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) * curlComp f i (x, t)|
      ≤ C3 * (cutoffEnstrophy χ u t + 1) := hC3 t ht
  -- integrability of the four tested integrands
  have hIA : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
      ∑ j : Fin 3, u (x, t) j *
        fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)) := by
    refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul
      (continuousOn_finsetSum Finset.univ (fun i _ => (continuousOn_curl_slice hu i ht1).mul
        (continuousOn_finsetSum Finset.univ (fun j _ => (continuousOn_vel_slice hu j ht1).mul
          (continuousOn_dcurl_slice hu i j ht1)))))) (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hIB : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 =>
        fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x (basisVec j)) := by
    refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul
      (continuousOn_finsetSum Finset.univ (fun i _ => (continuousOn_curl_slice hu i ht1).mul
        (continuousOn_finsetSum Finset.univ (fun j _ =>
          continuousOn_ddcurl_slice hu i j ht1))))) (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hIC : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      curlComp u j (x, t) * fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j) *
        curlComp u i (x, t)) := by
    refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul
      (continuousOn_finsetSum Finset.univ (fun i _ =>
        continuousOn_finsetSum Finset.univ (fun j _ =>
          ((continuousOn_curl_slice hu j ht1).mul (continuousOn_dvel_slice hu i j ht1)).mul
            (continuousOn_curl_slice hu i ht1))))) (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hID : Integrable (fun x : Vec3 => χ x ^ 2 * ∑ i : Fin 3,
      curlComp u i (x, t) * curlComp f i (x, t)) := by
    refine integrable_of_cutoff hχs hχU ((hsqχ.continuous.continuousOn).mul
      (continuousOn_finsetSum Finset.univ (fun i _ => (continuousOn_curl_slice hu i ht1).mul
        (continuousOn_curl_slice hfc i ht1)))) (fun x hx => ?_)
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  -- substituting the vorticity equation in the integrand
  have hInt : ∀ x : Vec3, χ x ^ 2 * (2 * ∑ i : Fin 3,
        curlComp u i (x, t) * timePartial (curlComp u i) (x, t))
      = 2 * (-(χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
              ∑ j : Fin 3, u (x, t) j *
                fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
          + χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
              ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 =>
                fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x (basisVec j)
          + χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, curlComp u j (x, t) *
              fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j) * curlComp u i (x, t)
          + χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) * curlComp f i (x, t)) := by
    intro x
    by_cases hx : x ∈ vec3Ball 0 1
    · have hpde : ∀ i : Fin 3, timePartial (curlComp u i) (x, t)
          = -(∑ j : Fin 3, u (x, t) j *
                fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
            + (∑ j : Fin 3, fderiv ℝ (fun y : Vec3 =>
                fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x (basisVec j))
            + (∑ j : Fin 3, curlComp u j (x, t) *
                fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j))
            + curlComp f i (x, t) := by
        intro i
        have hi : timePartial (curlComp u i) (x, t)
            + ∑ j : Fin 3, u (x, t) j *
                fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j)
            - ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 =>
                fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x (basisVec j)
            = ∑ j : Fin 3, curlComp u j (x, t) *
                fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j) + curlComp f i (x, t) :=
          cartesian_vorticity_pde u p f hsol (x, t) ⟨hx, ht1⟩ i
        linarith only [hi]
      simp only [hpde, Fin.sum_univ_three]
      ring
    · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (hχU hm))
      rw [hχ0]
      ring
  -- the derivative of `Y`, split into the four tested terms
  have hsum : deriv (cutoffEnstrophy χ u) t
      = 2 * (-(∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
              ∑ j : Fin 3, u (x, t) j *
                fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))
          + (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
              ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 =>
                fderiv ℝ (fun z : Vec3 => curlComp u i (z, t)) y (basisVec j)) x (basisVec j))
          + (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, curlComp u j (x, t) *
              fderiv ℝ (fun y : Vec3 => u (y, t) i) x (basisVec j) * curlComp u i (x, t))
          + (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3,
              curlComp u i (x, t) * curlComp f i (x, t))) := by
    have hIAn : Integrable (fun x : Vec3 => -(χ x ^ 2 * ∑ i : Fin 3, curlComp u i (x, t) *
        ∑ j : Fin 3, u (x, t) j *
          fderiv ℝ (fun y : Vec3 => curlComp u i (y, t)) x (basisVec j))) := hIA.neg
    rw [hder.deriv, integral_congr_ae (Filter.Eventually.of_forall hInt), integral_const_mul,
      integral_add4 hIAn hIB hIC hID, integral_neg]
  -- assembling the inequality
  have hYnn : (0 : ℝ) ≤ cutoffEnstrophy χ u t :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg (χ x))
      (Finset.sum_nonneg (fun i _ => sq_nonneg (vorticityField u (x, t) i))))
  have hg1 := le_abs_self (∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
    ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => χ y ^ 2) x (basisVec j) * u (x, t) j)
  have hg2 := le_abs_self (∫ x : Vec3, (∑ i : Fin 3, (curlComp u i (x, t)) ^ 2) *
    ∑ j : Fin 3, fderiv ℝ
      (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => χ z ^ 2) y (basisVec j)) x (basisVec j))
  have hg3 := le_abs_self (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3,
    curlComp u i (x, t) * curlComp f i (x, t))
  have hp1 : (0 : ℝ) ≤ C1 * cutoffEnstrophy χ u t := mul_nonneg hC10 hYnn
  have hp2 : (0 : ℝ) ≤ C2 * cutoffEnstrophy χ u t := mul_nonneg hC20 hYnn
  rw [hsum, hT, hDf, hS]
  nlinarith only [hE1, hE2, hE3, hg1, hg2, hg3, hp1, hp2, hC10, hC20, hC30, hYnn]

end Balance

end CIV
