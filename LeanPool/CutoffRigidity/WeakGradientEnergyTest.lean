/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.WeakH1Mollification
public import LeanPool.CutoffRigidity.GibbsOperatorLocalization

/-! # Testing a genuine weak divergence equation with a localized weak solution

Actual strong mollification justifies the energy test η²g. No smoothness
of g and no membership in a weak derivative domain is assumed by fiat:
the actual coordinate distribution identities are the inputs.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tendsto_integral_mul_of_L2_tendsto {f : ℕ → E → ℝ} {g q : E → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume) (hq : MemLp q 2 volume)
    (hlim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => ∫ x, f n x * q x) atTop (𝓝 (∫ x, g x * q x)) := by
  have hh : Tendsto (fun n => inner ℝ ((hf n).toLp (f n)) (hq.toLp q)) atTop
      (𝓝 (inner ℝ (hg.toLp g) (hq.toLp q))) :=
    hlim.inner (tendsto_const_nhds (x := hq.toLp q))
  simpa only [real_inner_toLp] using hh

/-- The actual coordinate derivative of η²g, with the scalar product
fully expanded for use in energy pairings. -/
theorem coordinateDerivative_sq_cutoff_mul {η g : E → ℝ}
    (hη : Differentiable ℝ η) (hg : Differentiable ℝ g) (j : Fin d) (x : E) :
    coordinateDerivative j (fun y => η y ^ 2 * g y) x =
      η x ^ 2 * coordinateDerivative j g x + 2 * η x * coordinateDerivative j η x * g x := by
  have hm : Differentiable ℝ (fun y => η y * η y) := hη.mul hη
  have he : (fun y => η y ^ 2 * g y) = fun y => (η y * η y) * g y := by
    funext y
    ring
  rw [he, coordinateDerivative_mul_actual hm hg,
    coordinateDerivative_mul_actual hη hη]
  ring

/-- Genuine weak energy testing. The finite sum of L² pairings is kept
explicit, so no extra integrability premise is hidden in an integral. -/
theorem weak_divergence_localized_energy_test {g η : E → ℝ}
    (hgm : Measurable g) (hg : MemLp g 2 volume)
    (K H : Fin d → E →₂[volume] ℝ) (F : E →₂[volume] ℝ)
    (hderiv : ∀ j (ψ : E → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, g x * coordinateDerivative j ψ x) = -(∫ x, K j x * ψ x))
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ tsupport η →
      (∑ j : Fin d, ∫ x, coordinateDerivative j ψ x * H j x) = ∫ x, ψ x * F x) :
    (∑ j : Fin d, ∫ x, K j x * (η x ^ 2 * H j x)) +
      (∑ j : Fin d, ∫ x, g x * (2 * η x * coordinateDerivative j η x * H j x)) =
      ∫ x, g x * (η x ^ 2 * F x) := by
  let φ (n : ℕ) : ContDiffBump (0 : E) :=
    euclideanMollifierBump (differenceStep n) (differenceStep_pos n)
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := differenceStep_tendsto_zero
  let gn (n : ℕ) := bumpMollification (φ n) g
  have hgn (n : ℕ) : ContDiff ℝ 3 (gn n) :=
    (bumpMollification_contDiff (φ n) (hg.locallyIntegrable (by norm_num))).of_le (by norm_num)
  have hgnLp (n : ℕ) : MemLp (gn n) 2 volume :=
    (bumpMollification_L2_contraction (φ n) hgm hg).1
  have hgnLim : Tendsto (fun n => (hgnLp n).toLp (gn n)) atTop (𝓝 (hg.toLp g)) :=
    bumpMollificationLp_tendsto φ hφ g hgm hg
  have hDpoint (n : ℕ) (j : Fin d) : coordinateDerivative j (gn n) =
      bumpMollification (φ n) (fun x => K j x) := by
    funext x
    exact coordinateDerivative_bumpMollification_of_weak_derivative (φ n)
      (hg.locallyIntegrable (by norm_num)) ((Lp.memLp (K j)).locallyIntegrable (by norm_num))
      j (hderiv j) x
  have hDnLp (n : ℕ) (j : Fin d) : MemLp (coordinateDerivative j (gn n)) 2 volume := by
    rw [hDpoint]
    exact (bumpMollification_L2_contraction (φ n) (Lp.stronglyMeasurable (K j)).measurable
      (Lp.memLp (K j))).1
  have hDnLim (j : Fin d) : Tendsto (fun n => (hDnLp n j).toLp
      (coordinateDerivative j (gn n))) atTop (𝓝 ((Lp.memLp (K j)).toLp (fun x => K j x))) := by
    simpa only [hDpoint, bumpMollificationLp] using
      bumpMollificationLp_tendsto φ hφ (fun x => K j x)
        (Lp.stronglyMeasurable (K j)).measurable (Lp.memLp (K j))
  have hηsqc : HasCompactSupport (fun x => η x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hηc.mul_right (f' := η)
  have hηsqCont : Continuous (fun x => η x ^ 2) := by
    simpa only [Pi.mul_def, pow_two] using hη.continuous.mul hη.continuous
  have hηsq : MemLp (fun x => η x ^ 2) ⊤ volume :=
    hηsqCont.memLp_of_hasCompactSupport hηsqc
  have hA (j : Fin d) : MemLp (fun x => η x ^ 2 * H j x) 2 volume :=
    hηsq.fun_mul (Lp.memLp (H j))
  have hB (j : Fin d) : MemLp
      (fun x => 2 * η x * coordinateDerivative j η x * H j x) 2 volume := by
    have hD := (c1_coordinateDerivative_of_c2 (hη.of_le (by norm_num)) j).continuous
    have hc : Continuous (fun x => 2 * η x * coordinateDerivative j η x) := by fun_prop
    have hs : HasCompactSupport (fun x => 2 * η x * coordinateDerivative j η x) := by
      have hh := hηc.comp_left (g := fun r : ℝ => 2 * r) (by simp)
      simpa only [Pi.mul_def, Function.comp_def] using hh.mul_right (f' := coordinateDerivative j η)
    exact (hc.memLp_of_hasCompactSupport hs : MemLp _ ⊤ volume).fun_mul (Lp.memLp (H j))
  have hC : MemLp (fun x => η x ^ 2 * F x) 2 volume := hηsq.fun_mul (Lp.memLp F)
  have hAlim := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_integral_mul_of_L2_tendsto (fun n => hDnLp n j) (Lp.memLp (K j)) (hA j) (hDnLim j))
  have hBlim := tendsto_finsetSum Finset.univ (fun j _ =>
    tendsto_integral_mul_of_L2_tendsto hgnLp hg (hB j) hgnLim)
  have hClim := tendsto_integral_mul_of_L2_tendsto hgnLp hg hC hgnLim
  have hEq (n : ℕ) :
      (∑ j : Fin d, ∫ x, coordinateDerivative j (gn n) x * (η x ^ 2 * H j x)) +
      (∑ j : Fin d, ∫ x, gn n x * (2 * η x * coordinateDerivative j η x * H j x)) =
      ∫ x, gn n x * (η x ^ 2 * F x) := by
    let ψ (x : E) := η x ^ 2 * gn n x
    have hψ : ContDiff ℝ 3 ψ := (hη.pow 2).mul (hgn n)
    have hψc : HasCompactSupport ψ := by
      simpa only [ψ, Pi.mul_def] using
        hηsqc.mul_right (f' := gn n)
    have hψsupp : tsupport ψ ⊆ tsupport η := by
      have hs : tsupport (fun x => η x ^ 2) ⊆ tsupport η := by
        simpa only [Pi.mul_def, pow_two] using (tsupport_mul_subset_left (f := η) (g := η))
      exact (tsupport_mul_subset_left (f := fun x => η x ^ 2) (g := gn n)).trans hs
    have he := hweak ψ hψ hψc hψsupp
    have hterm (j : Fin d) : (∫ x, coordinateDerivative j ψ x * H j x) =
        (∫ x, coordinateDerivative j (gn n) x * (η x ^ 2 * H j x)) +
        (∫ x, gn n x * (2 * η x * coordinateDerivative j η x * H j x)) := by
      have hp (x : E) : coordinateDerivative j ψ x * H j x =
          coordinateDerivative j (gn n) x * (η x ^ 2 * H j x) +
          gn n x * (2 * η x * coordinateDerivative j η x * H j x) := by
        rw [coordinateDerivative_sq_cutoff_mul (hη.differentiable (by norm_num))
          ((hgn n).differentiable (by norm_num))]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hp)]
      simpa only [Pi.mul_def] using integral_add
        ((hDnLp n j).integrable_mul (hA j)) ((hgnLp n).integrable_mul (hB j))
    simp_rw [hterm, Finset.sum_add_distrib] at he
    refine he.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
    intro x
    dsimp only [ψ]
    ring
  exact tendsto_nhds_unique (hAlim.add hBlim) (hClim.congr' (Filter.Eventually.of_forall fun n =>
    (hEq n).symm))

/-- The same actual energy test with raw L² representatives for the
coefficients. Their canonical L² classes introduce no pointwise choices. -/
theorem weak_divergence_localized_energy_test_raw {g η F : E → ℝ}
    (hgm : Measurable g) (hg : MemLp g 2 volume)
    (K : Fin d → E →₂[volume] ℝ) (H : Fin d → E → ℝ)
    (hH : ∀ j, MemLp (H j) 2 volume) (hF : MemLp F 2 volume)
    (hderiv : ∀ j (ψ : E → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ x, g x * coordinateDerivative j ψ x) = -(∫ x, K j x * ψ x))
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ tsupport η →
      (∑ j : Fin d, ∫ x, coordinateDerivative j ψ x * H j x) = ∫ x, ψ x * F x) :
    (∑ j : Fin d, ∫ x, K j x * (η x ^ 2 * H j x)) +
      (∑ j : Fin d, ∫ x, g x * (2 * η x * coordinateDerivative j η x * H j x)) =
      ∫ x, g x * (η x ^ 2 * F x) := by
  have hi := weak_divergence_localized_energy_test hgm hg K
    (fun j => (hH j).toLp (H j)) (hF.toLp F) hderiv hη hηc
  have hpair (j : Fin d) (a : E → ℝ) :
      (∫ x, a x * ((hH j).toLp (H j)) x) = ∫ x, a x * H j x := by
    apply integral_congr_ae
    filter_upwards [(hH j).coeFn_toLp] with x hx
    rw [hx]
  have hFpair (a : E → ℝ) :
      (∫ x, a x * (hF.toLp F) x) = ∫ x, a x * F x := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    rw [hx]
  have hw : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ tsupport η →
      (∑ j : Fin d, ∫ x, coordinateDerivative j ψ x * ((hH j).toLp (H j)) x) =
      ∫ x, ψ x * (hF.toLp F) x := by
    intro ψ hψ hψc hψs
    simp_rw [hpair, hFpair]
    exact hweak ψ hψ hψc hψs
  have he := hi hw
  simp_rw [← mul_assoc, hpair, hFpair] at he
  simpa only [mul_assoc] using he

end CutoffRigidity
