/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Gkt.HolderMixedNorm
public import LeanPool.CIVAxisymmetric.Prerequisites.Gkt.PressureStep
public import LeanPool.CIVAxisymmetric.Prerequisites.Gkt.TopBoundedness
public import LeanPool.CIVAxisymmetric.Setting.EnergyClassLemmas

/-!
# The Gustafson–Kang–Tsai criterion at the endpoint `p* = 6`, `q = 4`

If `∫_{-r²}^0 ‖u(t)‖_{L⁶(B_r)}^4 dt → 0` as `r → 0` for a suitable weak solution on
`Q = B(1) × (-1, 0)` in the energy class, smooth inside `Q`, with a `C²`-bounded force, then
`(0, 0)` is a regular point. This is Theorem 1.1(i) of Gustafson, Kang and Tsai 2007 at the
endpoint `3/p* + 2/q = 1` of its range, where their Lemmas 3.1 and 3.2 are not needed: Hölder
gives the scale-invariant `L³` smallness of `u` directly on every small cylinder, the integrated
Lin estimate (their Lemma 3.4) iterated finitely many times makes the pressure quantity small on
interior cylinders `Q_r(0, s)` uniformly in `s` close to `0`, and CKN's Theorem A at the top
boundary concludes. This is the criterion applied at the end of the proof of `lem:aniso:closure`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The pressure recursion along the scales `θ^n ρ₀`, `n < N`, at every base time `s ∈ (-3 (θ^N
ρ₀)², 0)`: each step halves `D` up to an additive term controlled by the velocity level `η` and
the force constant `C_f`. -/
theorem gkt_pressureD_recursion {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {Cf θ η ρ₀ r₁ : ℝ} {N : ℕ}
    (hCf : 0 ≤ Cf)
    (hlam : ∀ (x : Vec3) (s r : ℝ), 0 < r → s < 0 → -1 < s - r ^ 2 →
      vec3Ball x r ⊆ vec3Ball 0 1 → lambda q f (x, s) r ≤ Cf * r ^ 3)
    (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2)
    (hAθ : CKN.Core.Endgame.theoremALin34Constant q * θ ≤ 1 / 2)
    (hη : 0 ≤ η) (hρ₀ : 0 < ρ₀) (hρ₀half : ρ₀ ≤ 1 / 2) (hρ₀r₁ : 2 * ρ₀ < r₁)
    (hvel : ∀ r : ℝ, 0 < r → r < r₁ →
      (∫⁻ z in vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (η * r ^ 2))
    {s : ℝ} (hs : s ∈ Ioo (-(3 * (θ ^ N * ρ₀) ^ 2)) 0) :
    ∀ n < N, pressureD p ((0 : Vec3), s) (θ ^ (n + 1) * ρ₀) ≤
      (1 / 2 : ℝ) * pressureD p ((0 : Vec3), s) (θ ^ n * ρ₀) +
        CKN.Core.Endgame.theoremALin34Constant q *
          (8 * θ⁻¹ ^ 2 * (4 * η) + θ ^ (3 / 2 : ℝ) * (Cf * ρ₀ ^ 3) ^ (3 / 2 : ℝ)) := by
  intro n hn
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hA : 0 ≤ CKN.Core.Endgame.theoremALin34Constant q :=
    CKN.Core.Endgame.theoremALin34Constant_nonneg q hq
  set ρ : ℝ := θ ^ n * ρ₀ with hρdef
  have hθ1 : θ ≤ 1 := by linarith only [hθ2]
  have hρ : 0 < ρ := by positivity
  have hpow_le : θ ^ n ≤ 1 := pow_le_one₀ hθ.le hθ1
  have hρle : ρ ≤ ρ₀ := by
    calc ρ = θ ^ n * ρ₀ := rfl
      _ ≤ 1 * ρ₀ := mul_le_mul_of_nonneg_right hpow_le hρ₀.le
      _ = ρ₀ := one_mul ρ₀
  have hNle : θ ^ N * ρ₀ ≤ ρ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ.le hθ1 hn.le) hρ₀.le
  have hs0 : s < 0 := hs.2
  have hs3 : -(3 * ρ ^ 2) ≤ s := by
    have h1 := hs.1
    have hN0 : 0 ≤ θ ^ N * ρ₀ := by positivity
    nlinarith only [h1, hNle, hN0]
  have hlow : -1 < s - ρ ^ 2 := by
    have h1 := hs.1
    have hN0 : 0 ≤ θ ^ N * ρ₀ := by positivity
    nlinarith only [h1, hNle, hN0, hρle, hρ₀half, hρ, hρle]
  have hρ1 : ρ < 1 := by linarith only [hρle, hρ₀half]
  have hclo := gkt_closure_parabolicCylinder_subset hρ hρ1 hs0 hlow
  have hstep := gkt_pressureD_step (f := f) hsol (z := ((0 : Vec3), s)) hρ hθ hθ2 hclo
  have hsucc : θ ^ (n + 1) * ρ₀ = θ * ρ := by rw [hρdef, pow_succ]; ring
  rw [hsucc]
  -- velocity
  have h2ρ : 2 * ρ < r₁ := by linarith only [hρle, hρ₀r₁]
  have hcube := gkt_lintegral_cube_parabolicCylinder_le hρ hs0 hs3 (hvel (2 * ρ) (by positivity)
    h2ρ)
  have hgam : gamma u ((0 : Vec3), s) ρ ^ 3 ≤ 4 * η :=
    gkt_gamma_cube_le_of_lintegral (z := ((0 : Vec3), s)) hρ (by positivity) hcube
  -- force
  have hlam0 : 0 ≤ lambda q f ((0 : Vec3), s) ρ := lambda_nonneg q f _ hρ.le
  have hlamle : lambda q f ((0 : Vec3), s) ρ ≤ Cf * ρ₀ ^ 3 := by
    refine le_trans (hlam 0 s ρ hρ hs0 hlow (vec3Ball_mono hρ1.le)) ?_
    gcongr
  have hlampow : lambda q f ((0 : Vec3), s) ρ ^ (3 / 2 : ℝ) ≤ (Cf * ρ₀ ^ 3) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hlam0 hlamle (by norm_num)
  have hD0 := gkt_pressureD_nonneg p ((0 : Vec3), s) ρ
  have hfirst : CKN.Core.Endgame.theoremALin34Constant q * θ * pressureD p ((0 : Vec3), s) ρ ≤
      (1 / 2 : ℝ) * pressureD p ((0 : Vec3), s) ρ :=
    mul_le_mul_of_nonneg_right hAθ hD0
  refine le_trans hstep (add_le_add hfirst ?_)
  gcongr

/-- The uniform descent: for every `τ > 0` and `ρ_max > 0` there are a radius `r ≤ ρ_max`, `r ≤
1/2`, and a window `σ ∈ (0, r²]` such that the `L³` integral of `u` and the `L^{3/2}` integral
of `π` over `Q_r(0, s)` are at most `τ r²` for every `s ∈ (-σ, 0)`. -/
theorem gkt_exists_uniform_small_cylinder (q : ℝ) {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p) (hMf : ForceC2Bounded f)
    (hvel : ∀ η : ℝ, 0 < η → ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r < r₁ →
      (∫⁻ z in vec3Ball (0 : Vec3) r ×ˢ Ioo (-(r ^ 2)) 0,
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (η * r ^ 2))
    (τ : ℝ) (hτ : 0 < τ) (ρmax : ℝ) (hρmax : 0 < ρmax) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρmax ∧ r ≤ 1 / 2 ∧ ∃ σ : ℝ, 0 < σ ∧ σ ≤ r ^ 2 ∧
      ∀ s ∈ Ioo (-σ) 0,
        (∫⁻ z in parabolicCylinder (0 : Vec3) s r,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (τ * r ^ 2) ∧
        (∫⁻ z in parabolicCylinder (0 : Vec3) s r,
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) ≤ ENNReal.ofReal (τ * r ^ 2) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  set A : ℝ := CKN.Core.Endgame.theoremALin34Constant q with hAdef
  have hA : 0 ≤ A := CKN.Core.Endgame.theoremALin34Constant_nonneg q hq
  -- the contraction ratio
  set θ : ℝ := 1 / (2 * (A + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  have hθ2 : θ ≤ 1 / 2 := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hA]
  have hAθ : A * θ ≤ 1 / 2 := by
    rw [hθdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hA]
  -- the force constant
  obtain ⟨Cf, hCf, hlam⟩ := lambda_le_of_forceC2Bounded q hq hMf
  -- the velocity level
  set K₁ : ℝ := A * (8 * θ⁻¹ ^ 2 * 4) with hK₁def
  have hK₁ : 0 ≤ K₁ := by positivity
  set η : ℝ := τ / (8 * (K₁ + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hηK : K₁ * η ≤ τ / 8 := by
    rw [hηdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hK₁, hτ]
  have hη4 : 4 * η ≤ τ := by
    rw [hηdef, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith only [hK₁, hτ]
  obtain ⟨r₁, hr₁, -, hvelη⟩ := hvel η hη
  -- the force scale
  obtain ⟨ρf, hρf, -, hρfle⟩ := exists_rho_le_of_rpow_bound
    (C := A * θ ^ (3 / 2 : ℝ) * Cf ^ (3 / 2 : ℝ)) (B := τ / 8) (e := 9 / 2)
    (by positivity) (by positivity) (by norm_num)
  set ρ₀ : ℝ := min (min ρmax (1 / 2)) (min (r₁ / 4) ρf) with hρ₀def
  have hρ₀ : 0 < ρ₀ := by positivity
  have hρ₀max : ρ₀ ≤ ρmax := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ₀half : ρ₀ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ₀r₁4 : ρ₀ ≤ r₁ / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ₀f : ρ₀ ≤ ρf := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρ₀r₁ : 2 * ρ₀ < r₁ := by linarith only [hρ₀r₁4, hr₁]
  have hforce : A * (θ ^ (3 / 2 : ℝ) * (Cf * ρ₀ ^ 3) ^ (3 / 2 : ℝ)) ≤ τ / 8 := by
    have hrw : (Cf * ρ₀ ^ 3) ^ (3 / 2 : ℝ) = Cf ^ (3 / 2 : ℝ) * ρ₀ ^ (9 / 2 : ℝ) := by
      rw [Real.mul_rpow hCf (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hρ₀.le]
      norm_num
    rw [hrw]
    refine le_trans ?_ hρfle
    have hmono : ρ₀ ^ (9 / 2 : ℝ) ≤ ρf ^ (9 / 2 : ℝ) :=
      Real.rpow_le_rpow hρ₀.le hρ₀f (by norm_num)
    have hc : 0 ≤ A * θ ^ (3 / 2 : ℝ) * Cf ^ (3 / 2 : ℝ) := by positivity
    calc A * (θ ^ (3 / 2 : ℝ) * (Cf ^ (3 / 2 : ℝ) * ρ₀ ^ (9 / 2 : ℝ)))
        = A * θ ^ (3 / 2 : ℝ) * Cf ^ (3 / 2 : ℝ) * ρ₀ ^ (9 / 2 : ℝ) := by ring
      _ ≤ A * θ ^ (3 / 2 : ℝ) * Cf ^ (3 / 2 : ℝ) * ρf ^ (9 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hmono hc
  set B : ℝ := A * (8 * θ⁻¹ ^ 2 * (4 * η) + θ ^ (3 / 2 : ℝ) * (Cf * ρ₀ ^ 3) ^ (3 / 2 : ℝ))
    with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hB : B ≤ τ / 4 := by
    have hsplit : B = K₁ * η + A * (θ ^ (3 / 2 : ℝ) * (Cf * ρ₀ ^ 3) ^ (3 / 2 : ℝ)) := by
      rw [hBdef, hK₁def]; ring
    rw [hsplit]
    linarith only [hηK, hforce]
  -- the crude initial bound and the number of steps
  set P₀ : ℝ := ρ₀⁻¹ ^ 2 * (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal
    with hP₀def
  have hP₀ : 0 ≤ P₀ := by positivity
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := τ / (2 * (P₀ + 1))) (y := (1 / 2 : ℝ))
    (by positivity) (by norm_num)
  have hNP : (1 / 2 : ℝ) ^ N * P₀ ≤ τ / 2 := by
    have h1 : (1 / 2 : ℝ) ^ N * (P₀ + 1) < τ / 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (P₀ + 1))] at hN
      linarith only [hN]
    have h2 : (1 / 2 : ℝ) ^ N * P₀ ≤ (1 / 2 : ℝ) ^ N * (P₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
    linarith only [h1, h2]
  -- the final radius and time window
  set r : ℝ := θ ^ N * ρ₀ with hrdef
  have hr : 0 < r := by positivity
  have hrρ₀ : r ≤ ρ₀ := by
    have : θ ^ N ≤ 1 := pow_le_one₀ hθ.le (by linarith only [hθ2])
    calc r = θ ^ N * ρ₀ := rfl
      _ ≤ 1 * ρ₀ := mul_le_mul_of_nonneg_right this hρ₀.le
      _ = ρ₀ := one_mul ρ₀
  refine ⟨r, hr, le_trans hrρ₀ hρ₀max, le_trans hrρ₀ hρ₀half, r ^ 2, by positivity, le_rfl, ?_⟩
  intro s hs
  have hs0 : s < 0 := hs.2
  have hsr : -(r ^ 2) < s := hs.1
  have hs3 : s ∈ Ioo (-(3 * (θ ^ N * ρ₀) ^ 2)) 0 := by
    refine ⟨?_, hs0⟩
    have : 0 ≤ r ^ 2 := by positivity
    change -(3 * r ^ 2) < s
    linarith only [hsr, this]
  have hr1 : r < 1 := by linarith only [hrρ₀, hρ₀half]
  have hlow : -1 < s - r ^ 2 := by nlinarith only [hsr, hrρ₀, hρ₀half, hr]
  have hclo := gkt_closure_parabolicCylinder_subset hr hr1 hs0 hlow
  refine ⟨?_, ?_⟩
  · -- velocity
    have h2r : 2 * r < r₁ := by linarith only [hrρ₀, hρ₀r₁]
    have hs3' : -(3 * r ^ 2) ≤ s := by
      have : 0 ≤ r ^ 2 := by positivity
      linarith only [hsr, this]
    refine le_trans (gkt_lintegral_cube_parabolicCylinder_le hr hs0 hs3'
      (hvelη (2 * r) (by positivity) h2r)) (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ r ^ 2 := by positivity
    nlinarith only [hη4, this]
  · -- pressure
    rw [gkt_lintegral_pressure_eq hsol (z := ((0 : Vec3), s)) hr hclo]
    refine ENNReal.ofReal_le_ofReal ?_
    have hrec := gkt_pressureD_recursion (f := f) hsol hCf hlam hθ hθ2 hAθ hη.le hρ₀ hρ₀half
      hρ₀r₁ hvelη hs3
    have hiter := gkt_le_half_pow_of_forall_lt
      (a := fun n => pressureD p ((0 : Vec3), s) (θ ^ n * ρ₀)) hB0 hrec
    simp only [pow_zero, one_mul] at hiter
    have hlow₀ : -1 < s - ρ₀ ^ 2 := by nlinarith only [hsr, hrρ₀, hρ₀half, hr]
    have hcrude := gkt_pressureD_le_crude henergy (s := s) hρ₀ hs0 hlow₀ (by linarith only
      [hρ₀half])
    have hD : pressureD p ((0 : Vec3), s) r ≤ τ := by
      have h1 : (1 / 2 : ℝ) ^ N * pressureD p ((0 : Vec3), s) ρ₀ ≤ (1 / 2 : ℝ) ^ N * P₀ :=
        mul_le_mul_of_nonneg_left hcrude (by positivity)
      linarith only [hiter, h1, hNP, hB]
    have : 0 ≤ r ^ 2 := by positivity
    nlinarith only [hD, this]

/-- The Gustafson–Kang–Tsai criterion with `p* = 6`, `q = 4` at the top boundary point `(0, 0)`
(Theorem 1.1(i) of Gustafson, Kang and Tsai 2007), in the form consumed at the end of the proof
of `lem:aniso:closure`. -/
theorem boundedNearOrigin_of_L4L6_small (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hMf : ForceC2Bounded f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε) :
    BoundedNearOrigin u := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  have hucont : ContinuousOn (fun z : Vec3 × ℝ => u z) unitCylinder := hu.continuousOn
  obtain ⟨ε₀, hε₀, hA⟩ := gkt_boundedNearOrigin_of_top_small q hq
  obtain ⟨Mf, hMf0, hMbound⟩ := exists_bound_of_forceC2Bounded hMf
  -- force scale: `4π/3 · Mf^q · ρ^{3q} ≤ ε₀ / 2`
  obtain ⟨ρf, hρf, -, hρfle⟩ := exists_rho_le_of_rpow_bound
    (C := 4 * Real.pi / 3 * Mf ^ q) (B := ε₀ / 2) (e := 3 * q) (by positivity) (by positivity)
    (by linarith only [hq])
  have hvel := gkt_exists_topCylinder_cube_small hu hsmall
  obtain ⟨r, hr, hrρ, hr2, σ, hσ, hσr, hint⟩ :=
    gkt_exists_uniform_small_cylinder q hsol henergy hMf hvel (ε₀ / 4) (by positivity) ρf hρf
  have htop := gkt_topCylinder_small_of_interior hsol henergy hMf0 hMbound (by positivity) hr
    hr2 hσ hσr hint
  refine hA u Du p f r hr hr2 hsol hucont (le_trans htop (ENNReal.ofReal_le_ofReal ?_))
  have hforce : 4 * Real.pi / 3 * Mf ^ q * r ^ (3 * q) ≤ ε₀ / 2 := by
    refine le_trans ?_ hρfle
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrρ (by linarith only [hq]))
      (by positivity)
  have hr2pos : 0 < r ^ 2 := by positivity
  nlinarith only [hforce, hr2pos]

end CIV
