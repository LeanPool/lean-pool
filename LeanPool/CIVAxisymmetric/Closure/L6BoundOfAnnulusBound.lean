/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.CutoffExistence
public import LeanPool.CIVAxisymmetric.Closure.L6Assembly
public import LeanPool.CIVAxisymmetric.Regularity.RegularSphereFull

/-!
# The `L⁶` bound from an order-0 annulus bound

This file assembles the `L⁶(B(ρ))` bound `eq:aniso:closure:elliptic` (the Sobolev step of the
closure lemma `lem:aniso:closure`) and the Gustafson–Kang–Tsai smallness hypothesis from a plain
order-0 bound on a space–time annulus, instantiating the generic cutoff of
`l6_ball_bound_of_enstrophy_bound`/`closure_from_enstrophy_bound` with the concrete
`CKN.canonicalBallCutoff`. The last theorem uses the statement `CIV.timeZeroSingularSetNull`, an
input of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section



namespace CIV

/-- A gradient vanishes at a point outside the topological support of the function. -/
theorem gradVec_eq_zero_of_notMem_tsupport {φ : Vec3 → ℝ} {x : Vec3} (hx : x ∉ tsupport φ) :
    gradVec φ x = 0 := by
  have hopen : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  have heq : φ =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun y hy =>
      image_eq_zero_of_notMem_tsupport hy
  ext i
  simp [gradVec, heq.fderiv_eq]

/-- The gradient of the canonical ball cutoff vanishes inside the inner ball. -/
theorem gradVec_canonicalBallCutoff_eq_zero_of_mem_inner {ρ Rstar : ℝ} (hρ : 0 < ρ)
    (hρR : ρ < Rstar) {x : Vec3} (hx : x ∈ vec3Ball (0 : Vec3) ρ) :
    gradVec (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) x = 0 := by
  have hopen := isOpen_vec3Ball (0 : Vec3) ρ
  have hev : (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) =ᶠ[nhds x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun y hy =>
      CKN.canonicalBallCutoff_eq_one_on_inner hρ.le hρR (by
        rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hρ])
  ext i
  simp [gradVec, hev.fderiv_eq]

/-- If `u` is bounded by `Mu` on an annulus `{Rlo < |x| < Rhi} × (tη, 0)`, then the
canonical ball cutoff's gradient bound implies the pointwise squared norm bound
`|u(·,t)|² ≤ Mu²` wherever `∇χ ≠ 0`. -/
theorem hMu_canonicalBallCutoff_of_annulus_bound
    {u : ParabolicPoint → Vec3} {ρ Rstar Rlo Rhi tη Mu : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < Rstar) (hRloρ : Rlo < ρ) (hRstarRhi : Rstar ≤ Rhi)
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo tη (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ Mu) :
    ∀ t ∈ Ioo tη (0 : ℝ), ∀ x : Vec3,
      gradVec (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) x ≠ 0 →
      ∑ i : Fin 3, (u (x, t) i) ^ 2 ≤ Mu ^ 2 := by
  intro t ht x hne
  have hRpos : 0 < Rstar := lt_trans hρ hρR
  have hnotinner : x ∉ vec3Ball (0 : Vec3) ρ := by
    intro hx
    have hzero := gradVec_canonicalBallCutoff_eq_zero_of_mem_inner hρ hρR hx
    exact hne hzero
  have hxRstar : x ∈ vec3Ball (0 : Vec3) Rstar := by
    by_contra hx
    have htsupport : x ∉ tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) := by
      intro hxts
      apply hx
      have hsub := CKN.canonicalBallCutoff_tsupport_subset_outer hρ.le hρR hxts
      rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hRpos] at hsub
    have hzero := gradVec_eq_zero_of_notMem_tsupport htsupport
    exact hne hzero
  have hxRstar_norm : vec3EuclideanNorm x < Rstar := by
    rwa [mem_vec3Ball, sub_zero] at hxRstar
  have hx_norm_lo : Rlo < vec3EuclideanNorm x := by
    rw [mem_vec3Ball, sub_zero] at hnotinner
    linarith only [hnotinner, hRloρ]
  have hx_norm_hi : vec3EuclideanNorm x < Rhi := by
    linarith only [hRstarRhi, hxRstar_norm]
  have hnorm_bound := hbound x hx_norm_lo hx_norm_hi t ht
  have hsq : vec3EuclideanNorm (u (x, t)) ^ 2 ≤ Mu ^ 2 :=
    pow_le_pow_left₀ (vec3EuclideanNorm_nonneg _) hnorm_bound 2
  have hsum : vec3EuclideanNorm (u (x, t)) ^ 2 = ∑ i : Fin 3, (u (x, t) i) ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt (by positivity : 0 ≤ ∑ i : Fin 3, (u (x, t) i) ^ 2)]
  rw [hsum] at hsq
  exact hsq

/-- The `L⁶` bound on `B(ρ)` from an order-0 annulus bound: assembles the Sobolev step
`l6_ball_bound_of_enstrophy_bound` with the canonical ball cutoff. -/
theorem l6_ball_bound_of_annulus_bound
    {u : ParabolicPoint → Vec3} {ρ Rstar Rlo Rhi tη a C' : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < Rstar) (hRloρ : Rlo < ρ) (hRstarRhi : Rstar ≤ Rhi)
    (hu : ∀ t ∈ Ioo tη (0 : ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t)) (vec3Ball (0 : Vec3) Rstar))
    (hdiv : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0)
    {Mu : ℝ}
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo tη (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ Mu)
    (hC' : 0 ≤ C')
    (hY : ∀ t ∈ Ioo tη (0 : ℝ),
      (∫ x : Vec3, (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar x) ^ 2
          * ∑ i : Fin 3, (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2) + 1
        ≤ C' * (-t) ^ (-a)) :
    ∃ C'' : ℝ, 0 ≤ C'' ∧ ∀ t ∈ Ioo tη (0 : ℝ),
      (∫⁻ x in vec3Ball 0 ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        ≤ ENNReal.ofReal (C'' * (-t) ^ (-(a / 2))) := by
  have hRpos : 0 < Rstar := lt_trans hρ hρR
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) :=
    CKN.canonicalBallCutoff_smooth (0 : Vec3) hρ.le hρR
  have hχ_compact : HasCompactSupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) :=
    CKN.canonicalBallCutoff_hasCompactSupport hρ.le hρR
  have hχ_tsupport : tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) ⊆
      vec3Ball (0 : Vec3) Rstar := by
    intro y hy
    have hy' := CKN.canonicalBallCutoff_tsupport_subset_outer hρ.le hρR hy
    rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hRpos] at hy'
  have hχ_one : ∀ x ∈ vec3Ball (0 : Vec3) ρ,
      CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar x = 1 := by
    intro x hx
    exact CKN.canonicalBallCutoff_eq_one_on_inner hρ.le hρR (by
      rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hρ])
  exact l6_ball_bound_of_enstrophy_bound (isOpen_vec3Ball (0 : Vec3) Rstar)
    hχ_smooth hχ_compact hχ_tsupport hχ_one hu hdiv
    (hMu_canonicalBallCutoff_of_annulus_bound hρ hρR hRloρ hRstarRhi hbound) hC' hY

/-- The closure step from an order-0 annulus bound: with `η = 1/(16C_*)` the annulus bound
yields the parabolic smallness hypothesis of the Gustafson–Kang–Tsai criterion. -/
theorem closure_from_annulus_bound
    {u : ParabolicPoint → Vec3} {ρ Rstar Rlo Rhi tη Cstar η C' : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < Rstar) (hRloρ : Rlo < ρ) (hRstarRhi : Rstar ≤ Rhi)
    (hu : ∀ t ∈ Ioo tη (0 : ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t)) (vec3Ball (0 : Vec3) Rstar))
    (hdiv : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0)
    {Mu : ℝ}
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo tη (0 : ℝ), vec3EuclideanNorm (u (x, t)) ≤ Mu)
    (htη : tη < 0) (hCstar : 0 < Cstar) (hη : η = 1 / (16 * Cstar)) (hC' : 0 ≤ C')
    (hY : ∀ t ∈ Ioo tη (0 : ℝ),
      (∫ x : Vec3, (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar x) ^ 2
          * ∑ i : Fin 3, (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2) + 1
        ≤ C' * (-t) ^ (-(Cstar * η))) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε := by
  have hRpos : 0 < Rstar := lt_trans hρ hρR
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) :=
    CKN.canonicalBallCutoff_smooth (0 : Vec3) hρ.le hρR
  have hχ_compact : HasCompactSupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) :=
    CKN.canonicalBallCutoff_hasCompactSupport hρ.le hρR
  have hχ_tsupport : tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) ⊆
      vec3Ball (0 : Vec3) Rstar := by
    intro y hy
    have hy' := CKN.canonicalBallCutoff_tsupport_subset_outer hρ.le hρR hy
    rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hRpos] at hy'
  have hχ_one : ∀ x ∈ vec3Ball (0 : Vec3) ρ,
      CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar x = 1 := by
    intro x hx
    exact CKN.canonicalBallCutoff_eq_one_on_inner hρ.le hρR (by
      rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hρ])
  exact closure_from_enstrophy_bound (isOpen_vec3Ball (0 : Vec3) Rstar) hρ hχ_smooth hχ_compact
    hχ_tsupport hχ_one hu hdiv
    (hMu_canonicalBallCutoff_of_annulus_bound hρ hρR hRloρ hRstarRhi hbound) htη hCstar hη hC' hY

/-- The time-zero singular set null implies the `L⁶`-smallness condition: from the statement
`CIV.timeZeroSingularSetNull` and the order-0 annulus bound
`exists_annulus_bound_of_timeZeroSingularSetNull`, the `L⁶` bound on small balls
declines to zero as the radius shrinks, which is the parabolic smallness hypothesis
of the Gustafson–Kang–Tsai criterion.

The window parameter `tη` of `hu`, `hdiv` and `hC'` ranges over `Ioo (-1) 0`, the time interval
of the unit cylinder on which the solution class is defined: the radius selection returns its
`t₀` there, and a `tη ≤ -1` would ask for data at times where `u` is not given. -/
theorem closure_from_timeZeroSingularSetNull (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1 : ℝ) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (R₁ R₀ : ℝ) (hR₁ : 0 ≤ R₁) (hR₁R₀ : R₁ < R₀) (hR₀ : R₀ < 1)
    {Cstar : ℝ} (hCstar : 0 < Cstar)
    (hu : ∀ Rstar : ℝ, Rstar < 1 → ∀ tη ∈ Ioo (-1 : ℝ) 0, ∀ t ∈ Ioo tη (0 : ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t)) (vec3Ball (0 : Vec3) Rstar))
    (hdiv : ∀ Rstar : ℝ, Rstar < 1 → ∀ tη ∈ Ioo (-1 : ℝ) 0, ∀ t ∈ Ioo tη (0 : ℝ),
      ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
        ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0)
    (hC' : ∀ ρ Rstar : ℝ, ∀ tη ∈ Ioo (-1 : ℝ) 0, 0 < ρ → ρ < Rstar → Rstar < 1 →
      ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ t ∈ Ioo tη (0 : ℝ),
        (∫ x : Vec3, (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar x) ^ 2
            * ∑ i : Fin 3, (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2) + 1
          ≤ C' * (-t) ^ (-(Cstar * (1 / (16 * Cstar))))) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε := by
  obtain ⟨Rlo, Rhi, t₀, M, hR₁_Rlo, hRlo_Rhi, hRhi_R₀, ht₀, hbound⟩ :=
    exists_annulus_bound_of_timeZeroSingularSetNull q u Du p f hsol henergy hu' hp hf hMf
      R₁ R₀ hR₁ hR₁R₀ hR₀
  have hRlo_nonneg : 0 ≤ Rlo := by linarith only [hR₁, hR₁_Rlo]
  have hRhi_pos : 0 < Rhi := by linarith only [hRlo_nonneg, hRlo_Rhi]
  set ρ := (2 * Rlo + Rhi) / 3 with hρ_def
  set Rstar := (Rlo + 2 * Rhi) / 3 with hRstar_def
  have hρpos : 0 < ρ := by
    rw [hρ_def]
    positivity
  have hρR : ρ < Rstar := by
    rw [hρ_def, hRstar_def]
    nlinarith only [hRlo_Rhi]
  have hRloρ : Rlo < ρ := by
    rw [hρ_def]
    nlinarith only [hRlo_Rhi]
  have hRstarRhi : Rstar ≤ Rhi := by
    rw [hRstar_def]
    nlinarith only [hRlo_Rhi]
  have hRstar_lt_1 : Rstar < 1 := by
    linarith only [hRstarRhi, hRhi_R₀, hR₀]
  have hu_Rstar : ∀ t ∈ Ioo t₀ (0 : ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t)) (vec3Ball (0 : Vec3) Rstar) :=
    hu Rstar hRstar_lt_1 t₀ ht₀
  have hdiv_Rstar : ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0 :=
    hdiv Rstar hRstar_lt_1 t₀ ht₀
  obtain ⟨C'', hC''_nonneg, hC''_bound⟩ :=
    hC' ρ Rstar t₀ ht₀ hρpos hρR hRstar_lt_1
  exact closure_from_annulus_bound (η := 1 / (16 * Cstar)) hρpos hρR hRloρ hRstarRhi
    hu_Rstar hdiv_Rstar hbound ht₀.2 hCstar rfl hC''_nonneg hC''_bound

end CIV
