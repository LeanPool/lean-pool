/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.DeterminantBounds

/-!
# High-contrast homogenization: Entry.Multiscale.Global.Containment

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Containment geometry and the first two potential decreases

`p.global.selection`: the containment budget — an adapted cell of a grid of controlled operator
norm lies in the centred cube `□_{2 j_*}` — together with the rounded-grid operator-norm bound,
the definition of the potential `Φ`, and the decreases of the `h`-step and long-step
alternatives.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## §D Containment geometry (`p.global.selection`) -/

/-- `p.global.selection`: an adapted cell of a grid with operator norm `≤ ρ` at generation `j`
lies in
`□_{2 jStar}` once `j + log₃(2 √d ρ) ≤ 2 jStar`. -/
theorem adaptedCell_subset_centeredCube_of_opNorm {d : ℕ} (q : Mat d) (ρ : ℝ) (j : ℤ) (jStar : ℕ)
    (hρ : ‖q‖ ≤ ρ) (hρ0 : 0 < ρ)
    (hj : (j : ℝ) + Real.logb 3 (2 * Real.sqrt d * ρ) ≤ 2 * (jStar : ℝ)) :
    HighContrast.adaptedCell q j ⊆ HighContrast.centeredCube d (2 * (jStar : ℤ)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Recurrence.mem_centeredCube_iff] at hx
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  have hd : 0 < d := i.pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hsd2 : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR.le
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have h3J : (0 : ℝ) < (3 : ℝ) ^ (2 * (jStar : ℤ)) := by positivity
  -- the L2 operator norm controls `vecNormSq` along `matVecMul`
  have hop : vecNormSq (matVecMul q x) ≤ ‖q‖ ^ 2 * vecNormSq x := by
    have h := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) q).le_opNorm (WithLp.toLp 2 x)
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
    rw [Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM, mul_pow,
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
    simp only [Real.norm_eq_abs, sq_abs] at hs
    simpa [vecNormSq, vecDot, Geometry.matVecMul_eq_mulVec, pow_two, Finset.mul_sum] using hs
  -- `x` lies in the cube of generation `j`
  have hxn : vecNormSq x ≤ (d : ℝ) * ((3 : ℝ) ^ j / 2) ^ 2 := by
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin d)),
        x k * x k ≤ ((3 : ℝ) ^ j / 2) ^ 2 := by
      intro k _
      obtain ⟨hlo, hhi⟩ := hx k
      nlinarith only [hlo, hhi]
    have hsum := Finset.sum_le_card_nsmul Finset.univ (fun k => x k * x k) _ hterm
    simpa [vecNormSq, vecDot, Finset.card_univ, nsmul_eq_mul] using hsum
  have hqn : vecNormSq (matVecMul q x) ≤ ρ ^ 2 * ((d : ℝ) * ((3 : ℝ) ^ j / 2) ^ 2) := by
    have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
    have h2 : ‖q‖ ^ 2 ≤ ρ ^ 2 := by nlinarith only [hq0, hρ]
    have hvn : (0 : ℝ) ≤ vecNormSq x := vecNormSq_nonneg x
    have hrhs : (0 : ℝ) ≤ (d : ℝ) * ((3 : ℝ) ^ j / 2) ^ 2 := by positivity
    nlinarith only [hop, h2, hvn, hxn, sq_nonneg ‖q‖, sq_nonneg ρ]
  have hsq : (matVecMul q x i) ^ 2 ≤ (ρ * Real.sqrt (d : ℝ) * (3 : ℝ) ^ j / 2) ^ 2 := by
    have h1 := sq_apply_le_vecNormSq (matVecMul q x) i
    have h2 : (ρ * Real.sqrt (d : ℝ) * (3 : ℝ) ^ j / 2) ^ 2
        = ρ ^ 2 * (Real.sqrt (d : ℝ) ^ 2 * ((3 : ℝ) ^ j / 2) ^ 2) := by ring
    rw [h2, hsd2]
    exact h1.trans hqn
  -- `hj` in multiplicative form
  have hA0 : (0 : ℝ) < 2 * Real.sqrt (d : ℝ) * ρ := by positivity
  have hlogle : Real.logb 3 (2 * Real.sqrt (d : ℝ) * ρ) ≤ 2 * (jStar : ℝ) - (j : ℝ) := by
    linarith only [hj]
  have hAle : 2 * Real.sqrt (d : ℝ) * ρ ≤ (3 : ℝ) ^ (2 * (jStar : ℝ) - (j : ℝ)) := by
    have h := (Real.rpow_le_rpow_left_iff (x := (3 : ℝ))
      (y := Real.logb 3 (2 * Real.sqrt (d : ℝ) * ρ))
      (z := 2 * (jStar : ℝ) - (j : ℝ)) (by norm_num)).2 hlogle
    rwa [Real.rpow_logb (by norm_num) (by norm_num) hA0] at h
  have hcast : (2 * (jStar : ℝ) - (j : ℝ)) = ((2 * (jStar : ℤ) - j : ℤ) : ℝ) := by
    push_cast; ring
  rw [hcast, Real.rpow_intCast] at hAle
  have hmul : (3 : ℝ) ^ (2 * (jStar : ℤ) - j) * (3 : ℝ) ^ j = (3 : ℝ) ^ (2 * (jStar : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hkey : 2 * Real.sqrt (d : ℝ) * ρ * (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (2 * (jStar : ℤ)) := by
    calc 2 * Real.sqrt (d : ℝ) * ρ * (3 : ℝ) ^ j
        ≤ (3 : ℝ) ^ (2 * (jStar : ℤ) - j) * (3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hAle h3j.le
      _ = (3 : ℝ) ^ (2 * (jStar : ℤ)) := hmul
  have hB0 : (0 : ℝ) ≤ ρ * Real.sqrt (d : ℝ) * (3 : ℝ) ^ j / 2 := by positivity
  have hB : ρ * Real.sqrt (d : ℝ) * (3 : ℝ) ^ j / 2 ≤ (3 : ℝ) ^ (2 * (jStar : ℤ)) / 4 := by
    nlinarith only [hkey]
  constructor <;> nlinarith only [hsq, hB, hB0, h3J]

/-- `p.global.selection` (`e.rounded.grid.bounds`): `‖𝒬(m)‖ ≤ 2 (‖m‖ ‖m⁻¹‖)^{1/2}`; restates
`Geometry.opNorm_roundedGrid_le` with `Real.sqrt` unfolded to `rpow`. -/
theorem explicitRoundedGrid_opNorm_le {d : ℕ} (jStar : ℕ) (m : Mat d) (hj : 2 * d ≤ 3 ^ jStar)
    (hm : m.PosDef) :
    ‖Geometry.explicitRoundedGrid jStar m‖ ≤ 2 * (‖m‖ * ‖m⁻¹‖) ^ ((1 : ℝ) / 2)  := by
  simpa [Real.sqrt_eq_rpow] using
    Geometry.opNorm_roundedGrid_le (d := d) (jStar := jStar) (m := m) hj hm

/-! ## §E The potential and its four decreases (`e.global.selection.scalar`, `p.global.selection`)
-/

/-- `e.global.selection.scalar`: the scalar `Φ` at the state `(m, k, n)` on the grid
`𝒬(m)`. -/
@[expose]
noncomputable def potential {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (η a : ℝ)
    (m : Mat d) (k n : ℤ) : ℝ :=
  η * Real.log (1 +
      (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n) / η) +
    a * projectiveDistance m (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) k))

/-- `e.global.selection.h.step`: an `h`-step on a fixed grid with the synchronized
propagation output `e.fixed.geometry.synchronized.propagation` and `x > η` decreases `Φ` by
`c = ½ η log(16/9)` up to `(aC/d) Δ̂_h(n)`. Uses `scalar_growth_bound`, `scalar_contraction`. -/
theorem potential_step_sub_le_of_exp_bound {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (η a c C Q : ℝ)
    (m : Mat d) (k n : ℤ) (h : ℕ) (hd : 0 < d) (hη : η ∈ Set.Ioc (0 : ℝ) 1) (hC : 1 ≤ C)
    (hQ : 0 ≤ Q) (ha : 4 * Q * max 1 C ≤ a * C / d) (hc : c = 1 / 2 * η * Real.log (16 / 9))
    (hx : η < profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n)
    (hx' : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + h) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (n + h))
    (hΔ : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar m) (h : ℤ) n)
    (hprop : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + h) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (n + h) ≤
      1 / 8 * Real.exp (Q * synchCharge P (Geometry.explicitRoundedGrid jStar m) (h : ℤ) n) *
          (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n) +
        C * (Real.exp (Q * synchCharge P (Geometry.explicitRoundedGrid jStar m) (h : ℤ) n) - 1)) :
    potential P γ jStar η a m k (n + h) - potential P γ jStar η a m k n ≤
      -c + a * C / d * synchCharge P (Geometry.explicitRoundedGrid jStar m) (h : ℤ) n := by
  unfold potential
  have hηmem : η ∈ Set.Ioc (0 : ℝ) 1 := hη
  obtain ⟨hη0, _hη1⟩ := hη
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set q := Geometry.explicitRoundedGrid jStar m with hq
  set x := profile P γ q jStar k n + determinantDrift P γ q jStar n with hx_def
  set x' := profile P γ q jStar k (n + h) + determinantDrift P γ q jStar (n + h) with hx'_def
  set Δ := synchCharge P q (h : ℤ) n with hΔ_def
  have hx0 : 0 ≤ x := le_of_lt (lt_trans hη0 (by simpa [q, hx_def] using hx))
  have hx'0 : 0 ≤ x' := by simpa [q, hx'_def] using hx'
  have hΔ0 : 0 ≤ Δ := by simpa [q, Δ, hΔ_def] using hΔ
  have hprop' : x' ≤ Real.exp (Q * Δ) * x / 8 + C * (Real.exp (Q * Δ) - 1) := by
    simpa [q, x, x', Δ, hq, hx_def, hx'_def, hΔ_def, mul_comm, mul_left_comm, mul_assoc,
      div_eq_mul_inv] using hprop
  have hlog_mono : η * Real.log (1 + x' / η) ≤
      η * Real.log (1 + η⁻¹ * (Real.exp (Q * Δ) * x / 8 + C * (Real.exp (Q * Δ) - 1))) := by
    have hleft_pos : 0 < 1 + x' / η := by positivity
    have hdiv_le : x' / η ≤
        (Real.exp (Q * Δ) * x / 8 + C * (Real.exp (Q * Δ) - 1)) / η :=
      div_le_div_of_nonneg_right hprop' (le_of_lt hη0)
    have harg_le : 1 + x' / η ≤
        1 + η⁻¹ * (Real.exp (Q * Δ) * x / 8 + C * (Real.exp (Q * Δ) - 1)) := by
      calc
        1 + x' / η ≤
            1 + (Real.exp (Q * Δ) * x / 8 + C * (Real.exp (Q * Δ) - 1)) / η := by
          simpa [add_comm] using add_le_add_left hdiv_le 1
        _ = 1 + η⁻¹ * (Real.exp (Q * Δ) * x / 8 + C * (Real.exp (Q * Δ) - 1)) := by
          ring
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hleft_pos harg_le) (le_of_lt hη0)
  have hgrowth := scalar_growth_bound η Q C x Δ hηmem hC hQ hx0 hΔ0
  have hcontr := scalar_contraction η x hη0 (by simpa [q, x, hx_def] using hx)
  have hscalar : η * Real.log (1 + x' / η) ≤
      η * Real.log (1 + x / η) - η * Real.log (16 / 9) + Q * (1 + C) * Δ := by
    linarith only [hlog_mono, hgrowth, hcontr]
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hcoef : Q * (1 + C) ≤ a * C / d := by
    have hmax : max (1 : ℝ) C = C := max_eq_right hC
    have h4 : 4 * Q * C ≤ a * C / d := by simpa [hmax] using ha
    have h1C : 1 + C ≤ 2 * C := by linarith only [hC]
    have hle2 : Q * (1 + C) ≤ 2 * (Q * C) := by nlinarith only [hQ, h1C]
    have hle4 : 2 * (Q * C) ≤ 4 * Q * C := by nlinarith only [hQ, hC0]
    linarith only [hle2, hle4, h4]
  have hcoefΔ : Q * (1 + C) * Δ ≤ a * C / d * Δ :=
    mul_le_mul_of_nonneg_right hcoef hΔ0
  have hcpart : -η * Real.log (16 / 9) ≤ -c := by
    rw [hc]
    have hlog0 : 0 ≤ Real.log (16 / 9 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith only [mul_nonneg (le_of_lt hη0) hlog0]
  nlinarith only [hscalar, hcoefΔ, hcpart]

/-- `e.global.selection.long.step`: a `2L` obstruction (`Δ_{n,n+2L} > dεσ`) with the
fixed-span output `e.fixed.geometry.fixed.span.propagation` over `2L` generations. Uses
`scalar_span` and the weight choice. -/
theorem long_step_decrease {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (η a c C Q ε σ H : ℝ) (m : Mat d) (k n : ℤ) (L : ℕ) (hd : 0 < d) (hη : η ∈ Set.Ioc (0 : ℝ) 1)
    (hC : 1 ≤ C) (hQ : 0 ≤ Q) (hL : 1 ≤ L) (_hc : 0 ≤ c) (hε : 0 < ε) (hσ : 0 < σ) (ha1 : 1 ≤ a)
    (ha : 4 * Q * max 1 C ≤ a * C / d)
    (hw : 4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) ≤ a * C * ε * σ)
    (hlogH : 0 ≤ Real.log (1 + C * H))
    (hx0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n)
    (hx1 : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ 1)
    (hx'0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (n + 2 * (L : ℤ)))
    (hΔ : (d : ℝ) * ε * σ < detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)))
    (hspan : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (n + 2 * (L : ℤ)) ≤
      C * (2 * L) *
        (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
          (Real.exp (Q * detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ))) - 1))) :
    potential P γ jStar η a m k (n + 2 * (L : ℤ)) - potential P γ jStar η a m k n ≤
      -c + a * C / d * detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ)) := by
  let x := profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n
  let x' := profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (n + 2 * (L : ℤ))
  let Δ := detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (L : ℤ))
  let M := a * projectiveDistance m (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) k))
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hΔnonneg : 0 ≤ Δ := by
    have hprod : 0 ≤ (d : ℝ) * ε * σ := by positivity
    exact le_trans hprod (le_of_lt hΔ)
  have hx0x : 0 ≤ x := by simpa [x]
  have hx1x : x ≤ 1 := by simpa [x]
  have hx'0x : 0 ≤ x' := by simpa [x']
  have hℓ : (1 : ℝ) ≤ 2 * (L : ℝ) := by
    have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith only [hL']
  have hspan_x : x' ≤ C * (2 * (L : ℝ)) * (x + (Real.exp (Q * Δ) - 1)) := by
    simpa [x, x', Δ, mul_comm, mul_left_comm, mul_assoc] using hspan
  have hηpos : 0 < η := hη.1
  have hspan' : η * Real.log (1 + x' / η) ≤ Real.log (1 + C * (2 * (L : ℝ))) + Q * Δ := by
    obtain ⟨hη0, hη1⟩ := hη
    have hℓ0 : (0 : ℝ) ≤ 2 * (L : ℝ) := le_trans zero_le_one hℓ
    have hCℓ0 : 0 ≤ C * (2 * (L : ℝ)) := mul_nonneg hC0 hℓ0
    have h1 : x' ≤ C * (2 * (L : ℝ)) * Real.exp (Q * Δ) := by
      calc
        x' ≤ C * (2 * (L : ℝ)) * (x + (Real.exp (Q * Δ) - 1)) := hspan_x
        _ ≤ C * (2 * (L : ℝ)) * (1 + (Real.exp (Q * Δ) - 1)) := by
          exact mul_le_mul_of_nonneg_left (by linarith only [hx1x]) hCℓ0
        _ = C * (2 * (L : ℝ)) * Real.exp (Q * Δ) := by ring
    have h2 : x' / η ≤ C * (2 * (L : ℝ)) / η * Real.exp (Q * Δ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hηinv : (0 : ℝ) ≤ η⁻¹ := inv_nonneg.mpr hη0.le
      calc
        x' * η⁻¹ ≤ (C * (2 * (L : ℝ)) * Real.exp (Q * Δ)) * η⁻¹ :=
          mul_le_mul_of_nonneg_right h1 hηinv
        _ = C * (2 * (L : ℝ)) * η⁻¹ * Real.exp (Q * Δ) := by ring
    have hexp1 : (1 : ℝ) ≤ Real.exp (Q * Δ) := Real.one_le_exp (mul_nonneg hQ hΔnonneg)
    have h3 : 1 + x' / η ≤ (1 + C * (2 * (L : ℝ)) / η) * Real.exp (Q * Δ) := by
      have expand : (1 + C * (2 * (L : ℝ)) / η) * Real.exp (Q * Δ) =
          Real.exp (Q * Δ) + C * (2 * (L : ℝ)) / η * Real.exp (Q * Δ) := by ring
      rw [expand]
      linarith only [h2, hexp1]
    have hpos1 : (0 : ℝ) < 1 + x' / η := by
      have hdiv : 0 ≤ x' / η := div_nonneg hx'0x hη0.le
      linarith only [hdiv]
    have hCℓη0 : (0 : ℝ) ≤ C * (2 * (L : ℝ)) / η := div_nonneg hCℓ0 hη0.le
    have hpos2 : (0 : ℝ) < 1 + C * (2 * (L : ℝ)) / η := by
      linarith only [hCℓη0]
    have h4 : Real.log (1 + x' / η) ≤
        Real.log ((1 + C * (2 * (L : ℝ)) / η) * Real.exp (Q * Δ)) :=
      Real.log_le_log hpos1 h3
    have hlogmul : Real.log ((1 + C * (2 * (L : ℝ)) / η) * Real.exp (Q * Δ)) =
        Real.log (1 + C * (2 * (L : ℝ)) / η) + Q * Δ := by
      rw [Real.log_mul hpos2.ne' (Real.exp_ne_zero _), Real.log_exp]
    rw [hlogmul] at h4
    have h5 : η * Real.log (1 + x' / η) ≤
        η * (Real.log (1 + C * (2 * (L : ℝ)) / η) + Q * Δ) :=
      mul_le_mul_of_nonneg_left h4 hη0.le
    have hs : (-1 : ℝ) ≤ C * (2 * (L : ℝ)) / η := by
      linarith only [hCℓη0]
    have hbernoulli : (1 + C * (2 * (L : ℝ)) / η) ^ η ≤
        1 + η * (C * (2 * (L : ℝ)) / η) :=
      rpow_one_add_le_one_add_mul_self hs hη0.le hη1
    have heq : η * (C * (2 * (L : ℝ)) / η) = C * (2 * (L : ℝ)) := by
      field_simp [hη0.ne']
    rw [heq] at hbernoulli
    have h6 : Real.log ((1 + C * (2 * (L : ℝ)) / η) ^ η) ≤
        Real.log (1 + C * (2 * (L : ℝ))) :=
      Real.log_le_log (Real.rpow_pos_of_pos hpos2 η) hbernoulli
    have hrpowlog : Real.log ((1 + C * (2 * (L : ℝ)) / η) ^ η) =
        η * Real.log (1 + C * (2 * (L : ℝ)) / η) :=
      Real.log_rpow hpos2 η
    rw [hrpowlog] at h6
    have h7 : η * (Q * Δ) ≤ Q * Δ := by
      exact mul_le_of_le_one_left (mul_nonneg hQ hΔnonneg) hη1
    have hexpand5 : η * (Real.log (1 + C * (2 * (L : ℝ)) / η) + Q * Δ) =
        η * Real.log (1 + C * (2 * (L : ℝ)) / η) + η * (Q * Δ) := by ring
    rw [hexpand5] at h5
    linarith only [h5, h6, h7]
  have hold_nonneg : 0 ≤ η * Real.log (1 + x / η) := by
    have hxdiv : 0 ≤ x / η := div_nonneg hx0x hηpos.le
    have hlog : 0 ≤ Real.log (1 + x / η) := Real.log_nonneg (by linarith only [hxdiv])
    exact mul_nonneg hηpos.le hlog
  have hlog2CL : Real.log (1 + 2 * C * L) ≤ a * C * ε * σ / 4 - c := by
    linarith only [hw, hlogH, _hc]
  have hQbound : Q ≤ a / (4 * (d : ℝ)) := by
    have hmax : max (1 : ℝ) C = C := max_eq_right hC
    have h4QC : 4 * Q * C ≤ a * C / (d : ℝ) := by simpa [hmax] using ha
    have h4Q : 4 * Q ≤ a / (d : ℝ) := by
      apply (mul_le_mul_iff_of_pos_right hCpos).mp
      calc
        (4 * Q) * C = 4 * Q * C := by ring
        _ ≤ a * C / (d : ℝ) := h4QC
        _ = (a / (d : ℝ)) * C := by ring
    have hdiv4 := div_le_div_of_nonneg_right h4Q (by norm_num : (0 : ℝ) ≤ 4)
    calc
      Q = (4 * Q) / 4 := by ring
      _ ≤ (a / (d : ℝ)) / 4 := hdiv4
      _ = a / (4 * (d : ℝ)) := by field_simp [hdR.ne']
  have hQΔ : Q * Δ ≤ a * C / (4 * d) * Δ := by
    have ha0 : 0 ≤ a := le_trans zero_le_one ha1
    have hdenpos : 0 < 4 * (d : ℝ) := by positivity
    have hQboundC : Q ≤ a * C / (4 * d) := by
      have ha_le_aC : a ≤ a * C := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hC ha0
      exact le_trans hQbound (div_le_div_of_nonneg_right ha_le_aC hdenpos.le)
    exact mul_le_mul_of_nonneg_right hQboundC hΔnonneg
  have hεσbound : a * C * ε * σ / 4 ≤ a * C / (4 * d) * Δ := by
    have haC0 : 0 ≤ a * C := mul_nonneg (le_trans zero_le_one ha1) hC0
    have hmul : a * C * ((d : ℝ) * ε * σ) ≤ a * C * Δ :=
      mul_le_mul_of_nonneg_left (le_of_lt hΔ) haC0
    have hdenpos : 0 ≤ 4 * (d : ℝ) := by positivity
    calc
      a * C * ε * σ / 4 = (a * C * ((d : ℝ) * ε * σ)) / (4 * (d : ℝ)) := by
        field_simp [hdR.ne']
      _ ≤ (a * C * Δ) / (4 * (d : ℝ)) := div_le_div_of_nonneg_right hmul hdenpos
      _ = a * C / (4 * d) * Δ := by field_simp [hdR.ne']
  unfold potential
  change η * Real.log (1 + x' / η) + M - (η * Real.log (1 + x / η) + M) ≤
    -c + a * C / ↑d * Δ
  calc
    η * Real.log (1 + x' / η) + M - (η * Real.log (1 + x / η) + M) ≤
        η * Real.log (1 + x' / η) := by
      have heq : η * Real.log (1 + x' / η) + M - (η * Real.log (1 + x / η) + M) =
          η * Real.log (1 + x' / η) - η * Real.log (1 + x / η) := by ring
      rw [heq]
      exact sub_le_self _ hold_nonneg
    _ ≤ Real.log (1 + C * (2 * (L : ℝ))) + Q * Δ := hspan'
    _ ≤ -c + a * C / d * Δ := by
      have hlogsame : Real.log (1 + C * (2 * (L : ℝ))) = Real.log (1 + 2 * C * L) := by
        have harg : 1 + C * (2 * (L : ℝ)) = 1 + 2 * C * L := by ring
        exact congrArg Real.log harg
      rw [hlogsame]
      have hcoef0 : 0 ≤ a * C / (d : ℝ) :=
        div_nonneg (mul_nonneg (le_trans zero_le_one ha1) hC0) hdR.le
      have hquarter : a * C / (4 * d) * Δ + a * C / (4 * d) * Δ ≤ a * C / d * Δ := by
        have hcoefD0 : 0 ≤ a * C / d * Δ := mul_nonneg hcoef0 hΔnonneg
        have heq : a * C / (4 * d) * Δ + a * C / (4 * d) * Δ =
            (1 / 2) * (a * C / d * Δ) := by
          field_simp [hdR.ne']
          ring
        calc
          a * C / (4 * d) * Δ + a * C / (4 * d) * Δ =
              (1 / 2) * (a * C / d * Δ) := heq
          _ ≤ 1 * (a * C / d * Δ) :=
              mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1) hcoefD0
          _ = a * C / d * Δ := by ring
      calc
        Real.log (1 + 2 * C * L) + Q * Δ ≤
            (a * C * ε * σ / 4 - c) + Q * Δ :=
          by linarith only [hlog2CL]
        _ ≤ (a * C / (4 * d) * Δ - c) + Q * Δ :=
          by linarith only [hεσbound]
        _ ≤ (a * C / (4 * d) * Δ - c) + a * C / (4 * d) * Δ :=
          by linarith only [hQΔ]
        _ = -c + (a * C / (4 * d) * Δ + a * C / (4 * d) * Δ) := by ring
        _ ≤ -c + a * C / d * Δ := by linarith only [hquarter]

end

end HCPolySupport.HighContrast.Multiscale
