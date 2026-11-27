/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.PeriodicLift
public import LeanPool.FunctionSpaces.Analysis.Maximal.FeffermanStein

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Fefferman–Stein inequality for periodic lifts

For functions `g_j` on the torus `𝕋^d`, the maximal functions `M(g_j ∘ π)` of their periodic lifts
on `ℝ^d` satisfy the Fefferman–Stein inequality on the period box `P_0 = (0, 1]^d`
(`Torus.feffermanStein_periodic`): for `1 < p < ∞` and `1 < q ≤ ∞`,

`‖ x ↦ ‖(M(g_j ∘ π)(x))_j‖_{ℓ_q} ‖_{L_p(P_0)} ≤ C ‖ t ↦ ‖(g_j(t))_j‖_{ℓ_q} ‖_{L_p(𝕋^d)}`

with the explicit constant `C = Torus.periodicFSConst d p q`. The proof localises
(`Torus.maximal_comp_proj_le`): at a point of `P_0`, balls of radius `r ≤ 1` lie in the box
`(-1, 2]^d`, so they see only the lift cut off to that box, to which the inequality on `ℝ^d`
(`Rd.feffermanStein`) applies; a ball of radius `r > 1` meets at most `(2r + 2)^d ≤ (4r)^d`
period boxes, so its mean is at most `4^d |B(0,1)|⁻¹ ∫_{𝕋^d} g`. The mean term is bounded by
Minkowski's integral inequality on the probability space `𝕋^d`
(`MeasureTheory.lqNorm_lintegral_le_eLpNorm`).

Lifts of functions that agree almost everywhere have the same maximal function
(`Torus.maximal_enorm_comp_proj_congr_ae`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter Metric Module
open scoped ENNReal TorusHaar

open ENNReal (lqNorm)

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### Localisation of the maximal function -/

/-- **The maximal function of a lift sees only the class of the function**: if `u = v` almost
everywhere on `𝕋^d`, then `M(|u| ∘ π) = M(|v| ∘ π)`, since the lifts agree almost everywhere on
`ℝ^d` (`Torus.ae_comp_proj`). -/
theorem maximal_enorm_comp_proj_congr_ae {E : Type*} [ENorm E] {u v : UnitAddTorus d → E}
    (h : u =ᵐ[volume] v) :
    Rd.maximal (fun y => ‖u (proj y)‖ₑ) = Rd.maximal (fun y => ‖v (proj y)‖ₑ) :=
  Rd.maximal_congr_ae ((ae_comp_proj h).mono fun y hy => by simp only [hy])

/-- **Large balls**: for `r ≥ 1`, `(2r + 2)^d ≤ |B(0,r)| 4^d |B(0,1)|⁻¹`, since
`|B(0,r)| = r^d |B(0,1)|` and `2r + 2 ≤ 4r`. -/
theorem ofReal_two_mul_add_two_pow_le_volume_ball_mul {r : ℝ} (hr : 1 ≤ r) :
    ENNReal.ofReal (2 * r + 2) ^ Fintype.card d ≤
      volume (ball (0 : EuclideanSpace ℝ d) r) *
        (4 ^ Fintype.card d * (volume (ball (0 : EuclideanSpace ℝ d) 1))⁻¹) := by
  have hB0 := Rd.volume_ball_ne_zero (V := EuclideanSpace ℝ d) one_pos
  have hBt := Rd.volume_ball_ne_top (V := EuclideanSpace ℝ d) 1
  rw [Measure.addHaar_ball_of_pos volume 0 (zero_lt_one.trans_le hr), finrank_euclideanSpace,
    mul_comm (4 ^ Fintype.card d), ← mul_assoc, mul_assoc (ENNReal.ofReal _),
    ENNReal.mul_inv_cancel hB0 hBt, mul_one, ← ENNReal.ofReal_pow (by linarith),
    ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) (by linarith) _)

/-- **Localisation of the maximal function of a lift**: at every point `x` of `P_0 = (0, 1]^d`,
`M(g ∘ π)(x) ≤ M(1_{(-1,2]^d} (g ∘ π))(x) + 4^d |B(0,1)|⁻¹ ∫_{𝕋^d} g`. Balls of radius `r ≤ 1`
lie in `(-1, 2]^d`; a ball of radius `r > 1` meets at most `(2r + 2)^d` period boxes
(`Torus.setLIntegral_ball_comp_proj_le`). -/
theorem maximal_comp_proj_le (g : UnitAddTorus d → ℝ≥0∞) {x : EuclideanSpace ℝ d}
    (hx : x ∈ periodBox 0) :
    Rd.maximal (fun y => g (proj y)) x ≤
      Rd.maximal (tripleBox.indicator fun y => g (proj y)) x +
        4 ^ Fintype.card d * (volume (ball (0 : EuclideanSpace ℝ d) 1))⁻¹ * ∫⁻ t, g t := by
  refine Rd.maximal_le_of_forall fun r hr => ?_
  rcases le_or_gt r 1 with hr1 | hr1
  · have heq : ∫⁻ y in ball x r, g (proj y) =
        ∫⁻ y in ball x r, tripleBox.indicator (fun y => g (proj y)) y :=
      setLIntegral_congr_fun measurableSet_ball fun y hy =>
        (indicator_of_mem (ball_subset_tripleBox hx hr1 hy) (fun y => g (proj y))).symm
    rw [heq]
    exact (Rd.setLIntegral_ball_le_mul_maximal hr _ x).trans
      (mul_le_mul_right le_self_add _)
  · calc ∫⁻ y in ball x r, g (proj y)
        ≤ ENNReal.ofReal (2 * r + 2) ^ Fintype.card d * ∫⁻ t, g t :=
          setLIntegral_ball_comp_proj_le g x r
      _ ≤ volume (ball (0 : EuclideanSpace ℝ d) r) *
            (4 ^ Fintype.card d * (volume (ball (0 : EuclideanSpace ℝ d) 1))⁻¹ * ∫⁻ t, g t) := by
          rw [← mul_assoc]
          gcongr
          exact ofReal_two_mul_add_two_pow_le_volume_ball_mul hr1.le
      _ ≤ _ := mul_le_mul_right le_add_self _

/-! ### The inequality -/

/-- The constant `3^{d/p} C_{d,p,q} + 4^d |B(0,1)|⁻¹` of the Fefferman–Stein inequality for
periodic lifts, with the constant `C_{d,p,q} = Rd.feffermanSteinConst` of `ℝ^d` and the volume
`|B(0,1)|` of the unit ball of `ℝ^d`. -/
noncomputable def periodicFSConst (d : Type*) [Fintype d] (p q : ℝ≥0∞) : ℝ≥0∞ :=
  3 ^ ((Fintype.card d : ℝ) / p.toReal) * Rd.feffermanSteinConst (EuclideanSpace ℝ d) p q +
    4 ^ Fintype.card d * (volume (ball (0 : EuclideanSpace ℝ d) 1))⁻¹

/-- The constant of the Fefferman–Stein inequality for periodic lifts is finite for `1 < p < ∞`
and `1 < q ≤ ∞`. -/
theorem periodicFSConst_ne_top {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q) :
    periodicFSConst d p q ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))
      (Rd.feffermanSteinConst_ne_top hp1 hp hq1),
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (ENNReal.inv_ne_top.2 (Rd.volume_ball_ne_zero one_pos))⟩

/-- The pointwise localisation in `ℓ_q`: for `1 ≤ q ≤ ∞`, on `P_0`,
`‖(M(g_j ∘ π)(x))_j‖_{ℓ_q} ≤ ‖(M(1_{(-1,2]^d} (g_j ∘ π))(x))_j‖_{ℓ_q} +
4^d |B(0,1)|⁻¹ ‖(∫_{𝕋^d} g_j)_j‖_{ℓ_q}`. -/
theorem lqNorm_maximal_comp_proj_le {q : ℝ≥0∞} (hq : 1 ≤ q) (g : ℕ → UnitAddTorus d → ℝ≥0∞)
    {x : EuclideanSpace ℝ d} (hx : x ∈ periodBox 0) :
    lqNorm q (fun j => Rd.maximal (fun y => g j (proj y)) x) ≤
      lqNorm q (fun j => Rd.maximal (tripleBox.indicator fun y => g j (proj y)) x) +
        4 ^ Fintype.card d * (volume (ball (0 : EuclideanSpace ℝ d) 1))⁻¹ *
          lqNorm q (fun j => ∫⁻ t, g j t) := by
  rw [← ENNReal.lqNorm_const_mul]
  exact (ENNReal.lqNorm_mono fun j => maximal_comp_proj_le (g j) hx).trans
    (ENNReal.lqNorm_add_le hq _ _)

/-- **The Fefferman–Stein inequality for periodic lifts**: for `1 < p < ∞`, `1 < q ≤ ∞` and
almost everywhere measurable `g_j : 𝕋^d → [0, ∞]`, `j ∈ ℕ`,
`‖ x ↦ ‖(M(g_j ∘ π)(x))_j‖_{ℓ_q} ‖_{L_p(P_0)} ≤ C ‖ t ↦ ‖(g_j(t))_j‖_{ℓ_q} ‖_{L_p(𝕋^d)}` with
`C = Torus.periodicFSConst d p q` and the period box `P_0 = (0, 1]^d`. -/
theorem feffermanStein_periodic {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    (g : ℕ → UnitAddTorus d → ℝ≥0∞) (hg : ∀ j, AEMeasurable (g j) volume) :
    eLpNorm (fun x => lqNorm q (fun j => Rd.maximal (fun y => g j (proj y)) x)) p
        (volume.restrict (periodBox 0)) ≤
      periodicFSConst d p q * eLpNorm (fun t => lqNorm q (fun j => g j t)) p volume := by
  set G : UnitAddTorus d → ℝ≥0∞ := fun t => lqNorm q (fun j => g j t)
  set c : ℝ≥0∞ := 4 ^ Fintype.card d * (volume (ball (0 : EuclideanSpace ℝ d) 1))⁻¹
  set A : EuclideanSpace ℝ d → ℝ≥0∞ := fun x =>
    lqNorm q (fun j => Rd.maximal (tripleBox.indicator fun y => g j (proj y)) x)
  have hgl : ∀ j, AEMeasurable (tripleBox.indicator fun y => g j (proj y)) volume := fun j =>
    ((hg j).comp_quasiMeasurePreserving quasiMeasurePreserving_proj).indicator
      measurableSet_tripleBox
  have hA : Measurable A := measurable_lqNorm_comp (fun j => Rd.measurable_maximal _) q
  have h1 : eLpNorm A p (volume.restrict (periodBox 0)) ≤
      3 ^ ((Fintype.card d : ℝ) / p.toReal) * Rd.feffermanSteinConst (EuclideanSpace ℝ d) p q *
        eLpNorm G p volume := by
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      ((Rd.feffermanStein hp1 hp hq1 _ hgl).trans (le_of_eq ?_))
    have hfun : (fun y => lqNorm q (fun j => tripleBox.indicator (fun y => g j (proj y)) y)) =
        tripleBox.indicator fun y => G (proj y) :=
      funext fun y => ENNReal.lqNorm_indicator q _ _ y
    rw [hfun, eLpNorm_indicator_tripleBox (zero_lt_one.trans hp1).ne' hp
      (aemeasurable_lqNorm_comp hg q)]
    ring
  have h2 : eLpNorm (fun _ : EuclideanSpace ℝ d => c * lqNorm q (fun j => ∫⁻ t, g j t)) p
      (volume.restrict (periodBox 0)) ≤ c * eLpNorm G p volume := by
    rw [eLpNorm_const' _ (zero_lt_one.trans hp1).ne' hp, Measure.restrict_apply_univ,
      volume_periodBox, ENNReal.one_rpow, mul_one, eNorm_eq_self]
    gcongr
    exact lqNorm_lintegral_le_eLpNorm hp1.le hq1.le hg
  calc eLpNorm (fun x => lqNorm q (fun j => Rd.maximal (fun y => g j (proj y)) x)) p
        (volume.restrict (periodBox 0))
      ≤ eLpNorm (A + fun _ => c * lqNorm q (fun j => ∫⁻ t, g j t)) p
          (volume.restrict (periodBox 0)) := by
        refine eLpNorm_mono_eNorm_ae
          (measurable_lqNorm_comp (fun j => Rd.measurable_maximal _) q).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem (measurableSet_periodBox 0)] with x hx
        simp only [eNorm_eq_self, Pi.add_apply]
        exact lqNorm_maximal_comp_proj_le hq1.le g hx
    _ ≤ eLpNorm A p (volume.restrict (periodBox 0)) +
          eLpNorm (fun _ : EuclideanSpace ℝ d => c * lqNorm q (fun j => ∫⁻ t, g j t)) p
            (volume.restrict (periodBox 0)) :=
        eLpNorm_add_le hp1.le
    _ ≤ 3 ^ ((Fintype.card d : ℝ) / p.toReal) * Rd.feffermanSteinConst (EuclideanSpace ℝ d) p q *
          eLpNorm G p volume + c * eLpNorm G p volume := add_le_add h1 h2
    _ = periodicFSConst d p q * eLpNorm G p volume := by
        rw [periodicFSConst, add_mul]

end Torus
