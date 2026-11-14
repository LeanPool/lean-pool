/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderExcess

/-!
# OneStepSchauderInterior

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The ball → window transfer of the interior Schauder atom

`OneStepSchauderExcess.gradLipschitz_le_affineExcessRaw_of_harmonic` gives the
gradient-Lipschitz bound for `y, z` inside **one** Euclidean ball
`euclideanBall a (r/2)` on which the harmonic function is controlled.  The §4
consumer needs the bound on a **window** — a truncated triadic cube — which is
*not* contained in any such ball at the available margin: the sup ↔ `ℓ²` loss is
`√d`, while only one triadic scale (a factor `3`) separates the Hölder window
from the harmonicity domain, so for `d ≥ 3` no single admissible ball covers the
window.  (This is a genuine structural point, not a bookkeeping one: the bound
being propagated is a bound on *differences* of `∇v`, and `∇v` itself is **not**
controlled by the excess — adding a linear function changes `∇v` by a constant
and leaves the excess fixed — so the "far pairs" of the window cannot be handled
by a sup bound.  They must be handled by *chaining*.)

This module supplies the two missing moves.

* `norm_sub_le_of_local_bound` — **local-to-global on a convex set.**  A bound
  `‖G p − G q‖ ≤ L ‖p − q‖` valid only for pairs at sup-distance `< ρ` upgrades,
  on a convex set, to the same bound for *all* pairs: subdivide the segment
  `[p,q]` (which stays in the set) into `N` steps of length `< ρ` and telescope.
  The constant is **unchanged**, and no sign hypothesis on it is needed.
* `affineExcessRaw_le_of_subset_mul` — the volume-ratio comparison of the excess
  minimum on nested windows, `E_raw(W', v) ≤ (|W|/|W'|)^{1/2} E_raw(W, v)`,
  obtained competitor-by-competitor from `Support.normalizedL2On_le_of_subset`
  and passed to the two infima by `le_mul_affineExcessRaw_of_forall`.

Combining them with the atom gives `gradField_lipschitzOn_of_harmonic`: a
gradient-Lipschitz bound for `gradField v` on the whole convex window `W`,
against the excess on the enveloping window `W₂`.  `holderHalf_of_lipschitzOn`
then weakens `α = 1` to the printed `α = 1/2` at the cost of `√(diam W)`
(Hölder monotonicity on a bounded set).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecNormSq euclideanBall euclideanSqDist)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Local-to-global on a convex set -/

private theorem segment_point_mem {W : Set (Vec d)} (hW : Convex ℝ W) {y z : Vec d}
    (hy : y ∈ W) (hz : z ∈ W) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    y + t • (z - y) ∈ W := by
  have hcomb : y + t • (z - y) = (1 - t) • y + t • z := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [hcomb]
  exact hW hy hz (by linarith only [ht1]) ht0 (by ring)

private theorem segment_step_norm (y z : Vec d) (N : ℕ) (k : ℕ) :
    ‖(y + ((k : ℝ) / N) • (z - y)) - (y + (((k : ℕ) + 1 : ℝ) / N) • (z - y))‖
      = (1 / (N : ℝ)) * ‖y - z‖ := by
  have hdiff : (y + ((k : ℝ) / N) • (z - y)) - (y + (((k : ℕ) + 1 : ℝ) / N) • (z - y))
      = ((k : ℝ) / N - ((k : ℝ) + 1) / N) • (z - y) := by
    rw [sub_smul]
    abel
  rw [hdiff, norm_smul]
  have hcoef : (k : ℝ) / N - ((k : ℝ) + 1) / N = -(1 / (N : ℝ)) := by ring
  rw [hcoef, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)),
    norm_sub_rev]

/-- **Local-to-global on a convex set.**  A bound on `‖G p − G q‖` proportional to
`‖p − q‖`, valid only for pairs at sup-distance `< ρ`, holds for *all* pairs of a
convex set, with the **same** constant.  The segment `[p,q]` is subdivided into
`N` steps shorter than `ρ` and the estimate telescopes. -/
theorem norm_sub_le_of_local_bound {W : Set (Vec d)} (hW : Convex ℝ W)
    {G : Vec d → Vec d} {L rho : ℝ} (hrho : 0 < rho)
    (hloc : ∀ p ∈ W, ∀ q ∈ W, ‖p - q‖ < rho → ‖G p - G q‖ ≤ L * ‖p - q‖)
    {y z : Vec d} (hy : y ∈ W) (hz : z ∈ W) : ‖G y - G z‖ ≤ L * ‖y - z‖ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖y - z‖ / rho)
  have hNnn : (0 : ℝ) ≤ ‖y - z‖ / rho := div_nonneg (norm_nonneg _) hrho.le
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt hNnn hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set p : ℕ → Vec d := fun k => y + ((k : ℝ) / N) • (z - y) with hpdef
  have hmem : ∀ k : ℕ, k ≤ N → p k ∈ W := by
    intro k hk
    refine segment_point_mem hW hy hz (by positivity) ?_
    rw [div_le_one hNpos]
    exact_mod_cast hk
  have hshort : ‖y - z‖ / (N : ℝ) < rho := by
    rw [div_lt_iff₀ hNpos]
    have h := (div_lt_iff₀ hrho).mp hN
    calc ‖y - z‖ = ‖y - z‖ / rho * rho := by field_simp
      _ < (N : ℝ) * rho := by
          exact (mul_lt_mul_of_pos_right hN hrho)
      _ = rho * (N : ℝ) := mul_comm _ _
  have hstepbound : ∀ k : ℕ, k ≤ N → k + 1 ≤ N →
      ‖G (p k) - G (p (k + 1))‖ ≤ L * ((1 / (N : ℝ)) * ‖y - z‖) := by
    intro k hk hk1
    have hnormeq : ‖p k - p (k + 1)‖ = (1 / (N : ℝ)) * ‖y - z‖ := by
      have h := segment_step_norm y z N k
      simpa only [hpdef, Nat.cast_add, Nat.cast_one] using h
    have hlt : ‖p k - p (k + 1)‖ < rho := by
      rw [hnormeq, one_div, inv_mul_eq_div]
      exact hshort
    have h := hloc (p k) (hmem k hk) (p (k + 1)) (hmem (k + 1) hk1) hlt
    rwa [hnormeq] at h
  have key : ∀ k : ℕ, k ≤ N → ‖G y - G (p k)‖ ≤ L * ((k : ℝ) / N) * ‖y - z‖ := by
    intro k
    induction k with
    | zero =>
        intro _
        have hp0 : p 0 = y := by
          simp only [hpdef, Nat.cast_zero, zero_div, zero_smul, add_zero]
        rw [hp0, sub_self, norm_zero]
        simp
    | succ k ih =>
        intro hk1
        have hk : k ≤ N := Nat.le_of_succ_le hk1
        have h1 := ih hk
        have h2 := hstepbound k hk hk1
        have htri : ‖G y - G (p (k + 1))‖ ≤ ‖G y - G (p k)‖ + ‖G (p k) - G (p (k + 1))‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (G y) (G (p k)) (G (p (k + 1)))
          simpa using this
        have hsum : L * ((k : ℝ) / N) * ‖y - z‖ + L * ((1 / (N : ℝ)) * ‖y - z‖)
            = L * (((k : ℝ) + 1) / N) * ‖y - z‖ := by
          field_simp
        calc ‖G y - G (p (k + 1))‖
            ≤ ‖G y - G (p k)‖ + ‖G (p k) - G (p (k + 1))‖ := htri
          _ ≤ L * ((k : ℝ) / N) * ‖y - z‖ + L * ((1 / (N : ℝ)) * ‖y - z‖) :=
              add_le_add h1 h2
          _ = L * (((k : ℝ) + 1) / N) * ‖y - z‖ := hsum
          _ = L * (((k + 1 : ℕ) : ℝ) / N) * ‖y - z‖ := by norm_cast
  have hpN : p N = z := by
    simp only [hpdef, div_self hNne, one_smul]
    abel
  have hfin := key N le_rfl
  rw [hpN, div_self hNne, mul_one] at hfin
  exact hfin

/-! ## 2. The volume-ratio comparison of the excess minimum -/

/-- **Window comparison for the excess minimum.**  For `W' ⊆ W` of positive
finite volume, `E_raw(v, W') ≤ (|W|/|W'|)^{1/2} · E_raw(v, W)`.  Competitor by
competitor this is `Support.normalizedL2On_le_of_subset`; the passage to the two
infima is `le_mul_affineExcessRaw_of_forall`. -/
theorem affineExcessRaw_le_of_subset_mul {W W' : Set (Vec d)} {v : Vec d → ℝ}
    (hsub : W' ⊆ W) (hW : 0 < (volume W).toReal) (hW' : 0 < (volume W').toReal)
    (hint : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (v x - affineEval c g x) ^ 2) W volume) :
    affineExcessRaw W' v
      ≤ Real.sqrt ((volume W).toReal / (volume W').toReal) * affineExcessRaw W v :=
  le_mul_affineExcessRaw_of_forall (Real.sqrt_nonneg _) fun c g =>
    le_trans (affineExcessRaw_le_affineDistOn W' v c g)
      (normalizedL2On_le_of_subset hsub hW hW' (hint c g))

/-! ## 3. Hölder monotonicity `α = 1 → α = 1/2` -/

private theorem le_sqrt_mul_rpow_half {t D : ℝ} (ht : 0 ≤ t) (htD : t ≤ D) :
    t ≤ Real.sqrt D * t ^ (1 / 2 : ℝ) := by
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have hmono : Real.sqrt t ≤ Real.sqrt D := Real.sqrt_le_sqrt htD
  have hrw : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
  calc t = Real.sqrt t * Real.sqrt t := hsq.symm
    _ ≤ Real.sqrt D * Real.sqrt t := mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg _)
    _ = Real.sqrt D * t ^ (1 / 2 : ℝ) := by rw [hrw]

/-- **`α = 1 → α = 1/2` on a bounded set.**  A Lipschitz bound with constant `L`
on a set of sup-diameter at most `D` is a `C^{0,1/2}` bound with constant
`L √D`. -/
theorem holderHalf_of_lipschitzOn {U : Set (Vec d)} {G : Vec d → Vec d} {L D : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ p ∈ U, ∀ q ∈ U, ‖G p - G q‖ ≤ L * ‖p - q‖)
    (hdiam : ∀ p ∈ U, ∀ q ∈ U, ‖p - q‖ ≤ D) :
    HolderSeminormBoundOn U (1 / 2 : ℝ) (L * Real.sqrt D) G := by
  intro p hp q hq
  have hstep : ‖p - q‖ ≤ Real.sqrt D * ‖p - q‖ ^ (1 / 2 : ℝ) :=
    le_sqrt_mul_rpow_half (norm_nonneg _) (hdiam p hp q hq)
  calc ‖G p - G q‖ ≤ L * ‖p - q‖ := hlip p hp q hq
    _ ≤ L * (Real.sqrt D * ‖p - q‖ ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hstep hL
    _ = L * Real.sqrt D * ‖p - q‖ ^ (1 / 2 : ℝ) := by ring

/-! ## 4. Ball geometry at the `Vec d` carrier -/

theorem euclideanSqDist_self (p : Vec d) : euclideanSqDist p p = 0 := by
  simp only [euclideanSqDist, sub_self]
  simp [vecNormSq, HCPolySupport.vecDot]

theorem mem_euclideanBall_self {p : Vec d} {rho : ℝ} (h : 0 < rho) : p ∈ euclideanBall p rho := by
  change euclideanSqDist p p < rho ^ 2
  rw [euclideanSqDist_self]
  positivity

/-- The sup-norm ball of radius `s` sits inside the Euclidean ball of radius
`√d · s`: the two-sided norm comparison, in ball form. -/
theorem mem_euclideanBall_of_norm_lt {p q : Vec d} {rho : ℝ}
    (h : Real.sqrt d * ‖q - p‖ < rho) : q ∈ euclideanBall p rho := by
  change euclideanSqDist q p < rho ^ 2
  have h0 : (0 : ℝ) ≤ Real.sqrt d * ‖q - p‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hnorm : ‖(toEuc q : EuclideanSpace ℝ (Fin d)) - toEuc p‖ ≤ Real.sqrt d * ‖q - p‖ := by
    have hmap := norm_toEuc_le (q - p)
    rwa [map_sub] at hmap
  have hsq := norm_sq_toEuc_sub q p
  calc euclideanSqDist q p = ‖(toEuc q : EuclideanSpace ℝ (Fin d)) - toEuc p‖ ^ 2 := hsq.symm
    _ ≤ (Real.sqrt d * ‖q - p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ < rho ^ 2 := by
        exact pow_lt_pow_left₀ h h0 (by norm_num)

/-! ## 5. The gradient-Lipschitz bound on a convex window -/

/-- **The interior Schauder atom on a convex window.**

Hypotheses, in words: `v`'s Euclidean avatar is harmonic on `S`; `W` is a convex
window each of whose points `p` carries an admissible ball
`Metric.ball (toEuc p) R ⊆ S`; the half-balls `euclideanBall p (R/2)` all sit
inside an enveloping window `W₂` whose volume ratio against them is at most
`ratio²`.  Conclusion: `gradField v` is Lipschitz on all of `W` with constant

`4 · schauderConst d · R⁻¹ · R⁻¹ · ratio · E_raw(W₂, v)`.

The factor `4` is `(R/2)⁻¹(R/2)⁻¹ / (R⁻¹R⁻¹)`; the factor `ratio` is the window
transfer; `E_raw` is the §4 excess minimum on `W₂`. -/
theorem gradField_lipschitzOn_of_harmonic [NeZero d] {S : Set (EuclideanSpace ℝ (Fin d))}
    {v : Vec d → ℝ} {W W₂ : Set (Vec d)} {R ratio : ℝ}
    (hharm : HarmonicOnNhd (v ∘ toEuc.symm) S)
    (hWconv : Convex ℝ W) (hR : 0 < R) (hratio0 : 0 ≤ ratio)
    (hballS : ∀ p ∈ W, Metric.ball (toEuc p) R ⊆ S)
    (hsub : ∀ p ∈ W, euclideanBall p (R / 2) ⊆ W₂)
    (hW₂ : 0 < (volume W₂).toReal)
    (hballvol : ∀ p ∈ W, 0 < (volume (euclideanBall p (R / 2))).toReal)
    (hratio : ∀ p ∈ W,
      Real.sqrt ((volume W₂).toReal / (volume (euclideanBall p (R / 2))).toReal) ≤ ratio)
    (hint : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (v x - affineEval c g x) ^ 2) W₂ volume) :
    ∀ p ∈ W, ∀ q ∈ W,
      ‖gradField v p - gradField v q‖
        ≤ (4 * schauderConst d * R⁻¹ * R⁻¹ * (ratio * affineExcessRaw W₂ v)) * ‖p - q‖ := by
  set L : ℝ := 4 * schauderConst d * R⁻¹ * R⁻¹ * (ratio * affineExcessRaw W₂ v) with hLdef
  have hEnn : 0 ≤ affineExcessRaw W₂ v := affineExcessRaw_nonneg W₂ v
  have hL : 0 ≤ L := by
    rw [hLdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (schauderConst_nonneg d)) (inv_nonneg.2 hR.le))
      (inv_nonneg.2 hR.le)) (mul_nonneg hratio0 hEnn)
  set rho : ℝ := R / (4 * (Real.sqrt d + 1)) with hrhodef
  have hden : (0 : ℝ) < 4 * (Real.sqrt d + 1) := by positivity
  have hrho : 0 < rho := by rw [hrhodef]; exact div_pos hR hden
  refine fun p hp q hq => norm_sub_le_of_local_bound hWconv hrho ?_ hp hq
  intro a ha b hb hab
  -- the local step: apply the one-ball atom centred at `a`
  have hharma : HarmonicOnNhd (v ∘ toEuc.symm) (Metric.ball (toEuc a) R) :=
    hharm.mono (hballS a ha)
  have hr2 : (0 : ℝ) < R / 2 := by linarith only [hR]
  have hrR : R / 2 < R := by linarith only [hR]
  have hquarter : (0 : ℝ) < R / 2 / 2 := by linarith only [hR]
  have haball : a ∈ euclideanBall a (R / 2 / 2) := mem_euclideanBall_self hquarter
  have hbball : b ∈ euclideanBall a (R / 2 / 2) := by
    refine mem_euclideanBall_of_norm_lt ?_
    have hsd : Real.sqrt d ≤ Real.sqrt d + 1 := by linarith only [Real.sqrt_nonneg (d : ℝ)]
    have hba : ‖b - a‖ = ‖a - b‖ := norm_sub_rev b a
    have hlt : Real.sqrt d * ‖a - b‖ < Real.sqrt d * rho + rho := by
      have h1 : Real.sqrt d * ‖a - b‖ ≤ Real.sqrt d * rho := by
        rcases eq_or_lt_of_le (Real.sqrt_nonneg (d : ℝ)) with h0 | h0
        · rw [← h0]; simp
        · exact mul_le_mul_of_nonneg_left hab.le (Real.sqrt_nonneg _)
      linarith only [h1, hrho]
    have hkey : Real.sqrt d * rho + rho = R / 4 := by
      rw [hrhodef]
      field_simp
    rw [hba]
    calc Real.sqrt d * ‖a - b‖ < Real.sqrt d * rho + rho := hlt
      _ = R / 4 := hkey
      _ = R / 2 / 2 := by ring
  have hatom := gradLipschitz_le_affineExcessRaw_of_harmonic (v := v) (a := a) hr2 hrR
    hharma haball hbball
  -- the window transfer of the excess
  have hcmp : affineExcessRaw (euclideanBall a (R / 2)) v ≤ ratio * affineExcessRaw W₂ v := by
    have hle := affineExcessRaw_le_of_subset_mul (W := W₂) (W' := euclideanBall a (R / 2))
      (v := v) (hsub a ha) hW₂ (hballvol a ha) hint
    exact hle.trans (mul_le_mul_of_nonneg_right (hratio a ha) hEnn)
  have hcoef : (0 : ℝ) ≤ schauderConst d * (R / 2)⁻¹ * (R / 2)⁻¹ :=
    mul_nonneg (mul_nonneg (schauderConst_nonneg d) (inv_nonneg.2 hr2.le)) (inv_nonneg.2 hr2.le)
  have hLeq : schauderConst d * (R / 2)⁻¹ * (R / 2)⁻¹ * (ratio * affineExcessRaw W₂ v) = L := by
    rw [hLdef]
    field_simp
    ring
  have hstep : schauderConst d * (R / 2)⁻¹ * (R / 2)⁻¹ * affineExcessRaw (euclideanBall a (R / 2)) v
      ≤ L := by
    rw [← hLeq]
    exact mul_le_mul_of_nonneg_left hcmp hcoef
  calc ‖gradField v a - gradField v b‖
      ≤ ‖fderiv ℝ v a - fderiv ℝ v b‖ := norm_gradField_sub_le v a b
    _ ≤ (schauderConst d * (R / 2)⁻¹ * (R / 2)⁻¹
          * affineExcessRaw (euclideanBall a (R / 2)) v) * ‖a - b‖ := hatom
    _ ≤ L * ‖a - b‖ := mul_le_mul_of_nonneg_right hstep (norm_nonneg _)

/-- **The interior Schauder atom, `C^{0,1/2}` form on a convex window.** -/
theorem gradField_holderHalf_of_harmonic [NeZero d] {S : Set (EuclideanSpace ℝ (Fin d))}
    {v : Vec d → ℝ} {W W₂ : Set (Vec d)} {R ratio D : ℝ}
    (hharm : HarmonicOnNhd (v ∘ toEuc.symm) S)
    (hWconv : Convex ℝ W) (hR : 0 < R) (hratio0 : 0 ≤ ratio)
    (hballS : ∀ p ∈ W, Metric.ball (toEuc p) R ⊆ S)
    (hsub : ∀ p ∈ W, euclideanBall p (R / 2) ⊆ W₂)
    (hW₂ : 0 < (volume W₂).toReal)
    (hballvol : ∀ p ∈ W, 0 < (volume (euclideanBall p (R / 2))).toReal)
    (hratio : ∀ p ∈ W,
      Real.sqrt ((volume W₂).toReal / (volume (euclideanBall p (R / 2))).toReal) ≤ ratio)
    (hint : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun x => (v x - affineEval c g x) ^ 2) W₂ volume)
    (hdiam : ∀ p ∈ W, ∀ q ∈ W, ‖p - q‖ ≤ D) :
    HolderSeminormBoundOn W (1 / 2 : ℝ)
      (4 * schauderConst d * R⁻¹ * R⁻¹ * (ratio * affineExcessRaw W₂ v) * Real.sqrt D)
      (gradField v) := by
  have hEnn : 0 ≤ affineExcessRaw W₂ v := affineExcessRaw_nonneg W₂ v
  have hL : (0 : ℝ) ≤ 4 * schauderConst d * R⁻¹ * R⁻¹ * (ratio * affineExcessRaw W₂ v) :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (schauderConst_nonneg d)) (inv_nonneg.2 hR.le))
      (inv_nonneg.2 hR.le)) (mul_nonneg hratio0 hEnn)
  exact holderHalf_of_lipschitzOn hL
    (gradField_lipschitzOn_of_harmonic hharm hWconv hR hratio0 hballS hsub hW₂ hballvol
      hratio hint) hdiam

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
