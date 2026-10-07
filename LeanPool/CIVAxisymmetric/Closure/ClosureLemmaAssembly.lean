/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EnergyInequalityClosure
public import LeanPool.CIVAxisymmetric.Closure.ClosureEnstrophyDecayConcrete
public import LeanPool.CIVAxisymmetric.Closure.L6BoundOfAnnulusBound
public import LeanPool.CIVAxisymmetric.Closure.CanonicalCutoffAnnulusData
public import LeanPool.CIVAxisymmetric.Closure.SwirlBound
public import LeanPool.CIVAxisymmetric.Closure.SwirlBoundaryInitialData
public import LeanPool.CIVAxisymmetric.Closure.MeridionalSmallnessRadialQuotient
public import LeanPool.CIVAxisymmetric.Closure.MeridionalGDomination
public import LeanPool.CIVAxisymmetric.Closure.AnnulusEuclideanNormBound
public import LeanPool.CIVAxisymmetric.Closure.CirculationBound
public import LeanPool.CIVAxisymmetric.Closure.EllipticBoundsApply
public import LeanPool.CIVAxisymmetric.Reduction.ClassicalSolutionSliceBridge
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.ClassicalBridge
public import LeanPool.CIVAxisymmetric.Main.RegularAnnulus
public import LeanPool.CIVAxisymmetric.Main.GktCriterion

/-!
# Assembly of the closure lemma `lem:aniso:closure`

The proof of `lem:aniso:closure` from its steps. A regular annulus
`R₋ < |x| < R₊` inside `B(ρ₀)` comes from `lem:aniso:annulus` with `R₁ = 0`, `R₀ = ρ₀`; the
cutoff is the canonical ball cutoff between the radii `ρ = (2R₋ + R₊)/3` and
`R_* = (R₋ + 2R₊)/3`. The two suprema entering the energy inequality
`eq:aniso:closure:energy` are fixed *before* the constant `C_*` is produced:
`G = meridionalG ρ₀ u` (`eq:aniso:G`) and `W = meridionalSwirlSup R_* u`
(`eq:aniso:closure:w`), both read on the meridional plane, which is all the stretching, angular
and mixed-term estimates consume. Only then is `η = 1/(16 C_*)` chosen,
`t_η` taken from `eq:aniso:closure:small`, the swirl bound `eq:aniso:closure:w` obtained by
the axis maximum principle, and the Grönwall, `L⁶` and Gustafson–Kang–Tsai steps run.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The swirl supremum `W(t) = ‖u_θ(·, t)‖_{L^∞(B(R))}` of `eq:aniso:closure:w`, read on the
meridional plane, where the Cartesian component `u₁` is the azimuthal velocity `u_θ`. -/
@[expose] def meridionalSwirlSup (R : ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball 0 R ∧
    a = |u (meridional x₁ x₃, t) 1|}

/-- The swirl supremum is nonnegative. -/
theorem meridionalSwirlSup_nonneg (R : ℝ) (u : ParabolicPoint → Vec3) (t : ℝ) :
    0 ≤ meridionalSwirlSup R u t := by
  refine Real.sSup_nonneg fun a ha => ?_
  obtain ⟨x₁, x₃, -, rfl⟩ := ha
  exact abs_nonneg _

/-- Every meridional value of `|u_θ|` in `B(R)` is at most the swirl supremum, once the
values are bounded. -/
theorem abs_apply_one_le_meridionalSwirlSup {R B t : ℝ} {u : ParabolicPoint → Vec3}
    (hB : ∀ x ∈ vec3Ball (0 : Vec3) R, |u (x, t) 1| ≤ B)
    {x₁ x₃ : ℝ} (hmem : meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) R) :
    |u (meridional x₁ x₃, t) 1| ≤ meridionalSwirlSup R u t := by
  refine le_csSup ⟨B, ?_⟩ ⟨x₁, x₃, hmem, rfl⟩
  rintro a ⟨y₁, y₃, hy, rfl⟩
  exact hB _ hy

/-- The swirl supremum is at most any bound on the meridional values of `|u_θ|` in `B(R)`,
for `R > 0`. -/
theorem meridionalSwirlSup_le {R B t : ℝ} {u : ParabolicPoint → Vec3} (hR : 0 < R)
    (hB : ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) R →
      |u (meridional x₁ x₃, t) 1| ≤ B) :
    meridionalSwirlSup R u t ≤ B := by
  have h0 : meridional 0 0 ∈ vec3Ball (0 : Vec3) R :=
    (meridional_mem_vec3Ball_zero_iff 0 0 R).2 ⟨by nlinarith only [hR], hR⟩
  refine csSup_le ⟨_, 0, 0, h0, rfl⟩ ?_
  rintro a ⟨x₁, x₃, hmem, rfl⟩
  exact hB x₁ x₃ hmem

/-- The rearrangement of the weighted swirl bound of `eq:aniso:closure:w`: from
`(-t)^η a ≤ (-t_η)^η B + (-t_η)^η M_f (t - t_η)` on `(t_η, 0)` one gets
`a ≤ C_η (-t)^{-η}` with `C_η = (-t_η)^η (B + M_f (-t_η))`. -/
theorem le_mul_rpow_neg_of_weighted_le {tη t η a B Mf : ℝ} (hMf : 0 ≤ Mf)
    (ht : t ∈ Ioo tη (0 : ℝ))
    (h : (-t) ^ η * a ≤ (-tη) ^ η * B + (-tη) ^ η * Mf * (t - tη)) :
    a ≤ ((-tη) ^ η * (B + Mf * (-tη))) * (-t) ^ (-η) := by
  have hpos : 0 < -t := by linarith only [ht.2]
  have hwpos : 0 < (-t) ^ η := Real.rpow_pos_of_pos hpos η
  have htη : 0 ≤ (-tη) ^ η := Real.rpow_nonneg (by linarith only [ht.1, ht.2]) η
  have hstep : (-tη) ^ η * Mf * (t - tη) ≤ (-tη) ^ η * Mf * (-tη) :=
    mul_le_mul_of_nonneg_left (by linarith only [ht.2]) (mul_nonneg htη hMf)
  have hle : (-t) ^ η * a ≤ (-tη) ^ η * (B + Mf * (-tη)) := by
    have hring : (-tη) ^ η * (B + Mf * (-tη)) = (-tη) ^ η * B + (-tη) ^ η * Mf * (-tη) := by
      ring
    rw [hring]
    exact h.trans (by linarith only [hstep])
  rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hwpos, mul_comm]
  exact hle

/-- **The closure lemma `lem:aniso:closure`.** For an axisymmetric suitable weak solution,
smooth on the unit cylinder, with an axisymmetric force satisfying `eq:interior:force:c-two`, the
smallness `lim_{t↑0} (-t) G_{ρ₀}(t) = 0` of `eq:aniso:closure:small` makes `(0,0)` a regular
point. -/
theorem boundedNearOrigin_of_meridionalSmallness (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hfaxi : IsAxisymmetricOn f unitCylinder)
    (hMf : ForceC2Bounded f)
    (ρ₀ : ℝ) (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) (hsmall : MeridionalSmallness ρ₀ u) :
    BoundedNearOrigin u := by
  have hcl : IsClassicalSolutionOn u p f unitCylinder :=
    isClassicalSolutionOn_of_suitable hsol hu hp hf
  -- the regular annulus of `lem:aniso:annulus` with `R₁ = 0`, `R₀ = ρ₀`
  obtain ⟨Rm, Rp, t₀, hRm, hRmRp, hRpρ₀, ht₀, ⟨Mu₀, hMu₀⟩, -⟩ :=
    Main.regularAnnulus q u Du p f hsol henergy hu hp hf haxi hfaxi hMf 0 ρ₀
      ⟨le_rfl, hρ₀.1, hρ₀.2⟩
  set Mu : ℝ := max Mu₀ 0 with hMu_def
  have hMu : 0 ≤ Mu := le_max_right _ _
  have hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu :=
    fun x h1 h2 t ht i α hα => (hMu₀ x h1 h2 t ht i α hα).trans (le_max_left _ _)
  -- the radii `R₋ < ρ < R_* < R₊` and the cutoff
  set ρ : ℝ := (2 * Rm + Rp) / 3 with hρ_def
  set Rstar : ℝ := (Rm + 2 * Rp) / 3 with hRstar_def
  have hρpos : 0 < ρ := by rw [hρ_def]; linarith only [hRm, hRmRp]
  have hRmρ : Rm < ρ := by rw [hρ_def]; linarith only [hRmRp]
  have hρR : ρ < Rstar := by rw [hρ_def, hRstar_def]; linarith only [hRmRp]
  have hRRp : Rstar < Rp := by rw [hRstar_def]; linarith only [hRmRp]
  have hRpos : 0 < Rstar := hρpos.trans hρR
  have hRρ₀ : Rstar < ρ₀ := hRRp.trans hRpρ₀
  have hR1 : Rstar < 1 := hRρ₀.trans hρ₀.2
  obtain ⟨hχ, hχs, hχsupp, -, hAcl, hχA, -⟩ := canonicalBallCutoff_closedAnnulus_data hρpos hρR
  have hAsub : {y : Vec3 | ρ ≤ vec3EuclideanNorm y ∧ vec3EuclideanNorm y ≤ Rstar} ⊆
      {x : Vec3 | Rm < vec3EuclideanNorm x ∧ vec3EuclideanNorm x < Rp} :=
    fun y hy => ⟨hRmρ.trans_le hy.1, hy.2.trans_lt hRRp⟩
  have hB1 : vec3Ball (0 : Vec3) Rstar ⊆ vec3Ball (0 : Vec3) 1 := vec3Ball_mono hR1.le
  have hne : ∃ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ₀ :=
    ⟨0, 0, (meridional_mem_vec3Ball_zero_iff 0 0 ρ₀).2 ⟨by nlinarith only [hρ₀.1], hρ₀.1⟩⟩
  -- a window on which the meridional quantities are bounded (`ε = 1`)
  obtain ⟨t₁, ht₁, hsm1⟩ := hsmall 1 one_pos
  set t₂ : ℝ := max t₀ t₁ with ht₂_def
  have ht₂ : t₂ ∈ Ioo (-1 : ℝ) 0 :=
    ⟨lt_of_lt_of_le ht₀.1 (le_max_left _ _), max_lt ht₀.2 ht₁.2⟩
  -- `G = G_{ρ₀}` and `W = ‖u_θ‖_{L^∞(B(R_*))}`, fixed before `C_*`
  have hGnn : ∀ t, 0 ≤ meridionalG ρ₀ u t := fun t => meridionalG_nonneg hne
  have hG : ∀ t ∈ Ioo t₂ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
      meridionalQuantity u (meridional x₁ x₃, t) ≤ meridionalG ρ₀ u t := by
    intro t ht x₁ x₃ hmem
    have ht1 : t ∈ Ioo t₁ (0 : ℝ) := ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, ht.2⟩
    have hpos : 0 < -t := by linarith only [ht.2]
    refine meridionalQuantity_le_meridionalG ⟨1 / (-t), ?_⟩ (vec3Ball_mono hRρ₀.le hmem)
    rintro a ⟨y₁, y₃, hy, rfl⟩
    rw [le_div_iff₀ hpos, mul_comm]
    exact hsm1 t ht1 y₁ y₃ hy
  have hW : ∀ t ∈ Ioo t₂ (0 : ℝ), ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
      |u (meridional x₁ x₃, t) 1| ≤ meridionalSwirlSup Rstar u t := by
    intro t ht x₁ x₃ hmem
    have htm : t ∈ Ioo (-1 : ℝ) 0 := ⟨ht₂.1.trans ht.1, ht.2⟩
    obtain ⟨B, -, hB⟩ := exists_abs_apply_one_le_of_contDiffOn_ball hu hRpos hR1 htm
    exact abs_apply_one_le_meridionalSwirlSup hB hmem
  have hbound₂ : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₂ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ Mu :=
    fun x h1 h2 t ht => hbound x h1 h2 t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, ht.2⟩
  -- the energy inequality `eq:aniso:closure:energy`, with `C_*` independent of `η`
  obtain ⟨Cstar, hCstar1, hen⟩ := step_closure_energy_inequality hcl hMf haxi hχ hχs hχsupp
    hB1 hRpos ht₂ hAcl hχA hMu hAsub hbound₂ hGnn hG hW
  set η : ℝ := 1 / (16 * Cstar) with hη_def
  have hη : 0 < η ∧ 2 * η < 1 := eta_sixteenth_valid hCstar1
  -- `t_η` from `eq:aniso:closure:small`
  obtain ⟨tG, htG, hGη⟩ := meridionalG_le_of_meridionalSmallness hη.1 hsmall hne
  obtain ⟨tS, htS, hrq⟩ := swirl_hG_of_meridionalSmallness hsmall hη.1 hRρ₀.le
  set tη : ℝ := max t₂ (max tG tS) with htη_def
  have htη : tη ∈ Ioo (-1 : ℝ) 0 :=
    ⟨lt_of_lt_of_le ht₂.1 (le_max_left _ _), max_lt ht₂.2 (max_lt htG.2 htS.2)⟩
  have h₂η : t₂ ≤ tη := le_max_left _ _
  have hGη' : tG ≤ tη := (le_max_left _ _).trans (le_max_right _ _)
  have hSη : tS ≤ tη := (le_max_right _ _).trans (le_max_right _ _)
  -- the swirl bound `eq:aniso:closure:w` by the axis maximum principle
  obtain ⟨Mf₀, hMf₀⟩ := exists_bound_force_swirl_of_forceC2Bounded f hMf
  set Mf : ℝ := max Mf₀ 0 with hMf_def
  have hMfb : ∀ z ∈ unitCylinder, |f z 1| ≤ Mf :=
    fun z hz => (hMf₀ z hz).trans (le_max_left _ _)
  have hrq' : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x₁ x₃ : ℝ,
      meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) Rstar →
        |radialQuotient u (meridional x₁ x₃, t)| ≤ η / (-t) :=
    fun t ht => hrq t ⟨lt_of_le_of_lt hSη ht.1, ht.2⟩
  have hbdry : ∀ x : Vec3, vec3EuclideanNorm x = Rstar → ∀ t ∈ Ioo tη (0 : ℝ),
      |u (x, t) 1| ≤ Mu := by
    intro x hx t ht
    have h := hbound x (by rw [hx]; exact hRmρ.trans hρR) (by rw [hx]; exact hRRp) t
      ⟨lt_of_le_of_lt ((le_max_left _ _).trans h₂η) ht.1, ht.2⟩ 1 (fun _ => 0) (by norm_num)
    simpa [multiPartial] using h
  obtain ⟨Mi, -, hinit⟩ := exists_abs_apply_one_le_of_contDiffOn_ball hu hRpos hR1 htη
  have hsw := swirl_bound u p f hcl haxi hfaxi Mf hMfb Rstar ⟨hRpos, hR1⟩ tη η htη hη.1 hrq'
    Mu hbdry Mi hinit
  set Cη : ℝ := (-tη) ^ η * (max Mu Mi + Mf * (-tη)) with hCη_def
  have hCη : 0 ≤ Cη := by
    have h1 : 0 ≤ (-tη) ^ η := Real.rpow_nonneg (by linarith only [htη.2]) η
    have h2 : 0 ≤ max Mu Mi := hMu.trans (le_max_left _ _)
    have h3 : 0 ≤ Mf * (-tη) := mul_nonneg (le_max_right _ _) (by linarith only [htη.2])
    positivity
  have hWη : ∀ t ∈ Ioo tη (0 : ℝ), meridionalSwirlSup Rstar u t ≤ Cη * (-t) ^ (-η) := by
    intro t ht
    refine meridionalSwirlSup_le hRpos fun x₁ x₃ hmem => ?_
    exact le_mul_rpow_neg_of_weighted_le (le_max_right _ _) ht (hsw t ht x₁ x₃ hmem)
  -- the Grönwall step
  have hχU : tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) ⊆ vec3Ball (0 : Vec3) 1 :=
    hχsupp.trans hB1
  obtain ⟨C', hC', hY⟩ := closure_enstrophy_decay_sixteenth_eta_of_exists_energy_inequality
    hu hχ hχs hχU htη hCη (G := meridionalG ρ₀ u)
    (fun t _ => meridionalSwirlSup_nonneg Rstar u t)
    ⟨Cstar, hCstar1,
      fun t ht => hen t ⟨lt_of_le_of_lt h₂η ht.1, ht.2⟩,
      fun t ht => hGη t ⟨lt_of_le_of_lt hGη' ht.1, ht.2⟩,
      hWη⟩
  -- the `L⁶` step and the smallness hypothesis of the Gustafson–Kang–Tsai criterion
  have hCstar0 : 0 < Cstar := lt_of_lt_of_le one_pos hCstar1
  have hexp : Cstar * η = 1 / 16 := by
    rw [hη_def]
    field_simp
  have hnorm := exists_vec3EuclideanNorm_bound_of_multiPartial_le hMu hbound₂
  have hsmallL : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε :=
    closure_from_annulus_bound (η := η) hρpos hρR hRmρ hRRp.le
      (fun t ht => hu_of_isClassicalSolutionOn_vec3Ball hR1.le hcl t
        ⟨htη.1.trans ht.1, ht.2⟩)
      (fun t ht => hdiv_of_isClassicalSolutionOn_vec3Ball hR1.le hcl t
        ⟨htη.1.trans ht.1, ht.2⟩)
      (fun x h1 h2 t ht => hnorm x h1 h2 t ⟨lt_of_le_of_lt h₂η ht.1, ht.2⟩)
      htη.2 hCstar0 hη_def hC'
      (fun t ht => by
        rw [← cutoffEnstrophy_eq_integral_sq_curlVec, hexp]
        exact hY t ht)
  exact Main.gktCriterion q u Du p f hsol henergy hu hp hf hMf hsmallL

end CIV

