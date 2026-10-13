/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.WeakGradientLocality
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ

/-!
# HarmonicityTransferTests

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Weak harmonicity against smooth tests

`Support.IsWeaklyHarmonicOn W v` is stated against *every* `H¹₀(W)` competitor,
while every construction that produces harmonicity — in particular the odd
reflection of §4.3 — produces it against *smooth compactly supported* tests.
This file supplies the two bridges between the two formulations, both of which
run through the `H10Function` package's own `L²` approximation data:

* `isWeaklyHarmonicOn_of_contDiff_tests` — smooth tests suffice (the direction
  a construction needs);
* `integral_vecDot_euclideanGradient_eq_zero` — a *smooth* function that
  happens to lie in `H¹₀(W)` may be used as a competitor with its **classical**
  gradient (the direction a consumer needs; the identification of the
  `H10Function`'s recorded gradient with `euclideanGradient` is the a.e.
  uniqueness of weak derivatives on an open set, CoarseGraining's
  `HasWeakPartialDerivOn.ae_eq`).

Both are proved by testing coordinate by coordinate and passing to the limit
through Hölder's inequality at the pair `(2, 2)`, so the only analytic input is
`tendsto_setIntegral_mul_of_tendsto_eLpNormTwo`, the `L²` continuity of the
tested integral, which is proved here.

## References

* CoarseGraining, `Homogenization/Sobolev/WeakDerivatives.lean`
  (`HasWeakPartialDerivOn.ae_eq`, `HasWeakPartialDerivOn.of_contDiff`),
  `Homogenization/Sobolev/H1/Definitions.lean` (the `H10Function` package).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. `L²` continuity of the tested integral -/

/-- **`L²` continuity of the tested integral.**  If `f n → g` in `L²(W)` and
`h ∈ L²(W)`, the paired integrals converge.  (This is the `p = 2`
specialization of the graph-closure engine of `OddReflectionGlue`, restated
publicly here because the tested integral of a *gradient* pairing needs it once
per coordinate.) -/
theorem tendsto_setIntegral_mul_of_tendsto_eLpNormTwo {W : Set (Vec d)}
    {h : Vec d → ℝ} {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h 2 (volume.restrict W))
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W))
    (htend : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 (volume.restrict W))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in W, f n x * h x ∂volume) atTop
      (nhds (∫ x in W, g x * h x ∂volume)) := by
  set μ : Measure (Vec d) := volume.restrict W with hμ
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := fun n => (hf n).integrable_mul hh
  have hgh_int : Integrable (fun x => g x * h x) μ := hg.integrable_mul hh
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ) = ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  set B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (fun x => f n x - g x) 2 μ * eLpNorm h 2 μ with hB
  have hBtend : Tendsto (fun n => (B n).toReal) atTop (nhds 0) := by
    have hprod : Tendsto B atTop (nhds (0 * eLpNorm h 2 μ)) := by
      refine ENNReal.Tendsto.mul (by simpa [μ] using htend) (Or.inr hh.eLpNorm_lt_top.ne)
        tendsto_const_nhds (Or.inr (by simp))
    rw [zero_mul] at hprod
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    simpa using! hreal
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hbound : ∀ᵐ x ∂μ, ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Eventually.of_forall fun x => by rw [nnnorm_mul]; simp
  have hHolder : eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have hh' := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := 1)
      (fun x y => x * y) 1 continuous_mul ((hf n).sub hg).aestronglyMeasurable
      hh.aestronglyMeasurable hbound
    simpa [B] using! hh'
  calc ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm _
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
        have hm : AEStronglyMeasurable (fun x => (f n x - g x) * h x) μ :=
          ((hf n).sub hg).aestronglyMeasurable.mul hh.aestronglyMeasurable
        rw [eLpNorm_one_eq_lintegral_enorm hm]
        simp_rw [ofReal_norm]
    _ ≤ (B n).toReal := by
        refine ENNReal.toReal_mono ?_ hHolder
        exact ENNReal.mul_ne_top ((hf n).sub hg).eLpNorm_lt_top.ne hh.eLpNorm_lt_top.ne

/-! ## 2. Coordinate splitting of the tested integral -/

/-- A smooth compactly supported function's coordinate derivative is in
`L²(W)` for every `W`. -/
theorem memLp_two_fderiv_apply_restrict {W : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (j : Fin d) :
    MemLp (fun y => (fderiv ℝ f y) (basisVec j)) 2 (volume.restrict W) := by
  have hcont : Continuous fun y => (fderiv ℝ f y) (basisVec j) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsupp : HasCompactSupport fun y => (fderiv ℝ f y) (basisVec j) := by
    simpa only using hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  exact (hcont.memLp_of_hasCompactSupport hsupp).restrict W

/-- The tested integral splits into its `d` coordinate pairings. -/
private theorem integral_vecDot_split {W : Set (Vec d)} (w : H1Function W)
    (G : Vec d → Vec d) (hG : ∀ j, MemLp (fun y => G y j) 2 (volume.restrict W)) :
    ∫ y in W, vecDot (w.grad y) (G y) ∂volume =
      ∑ j : Fin d, ∫ y in W, G y j * w.grad y j ∂volume := by
  have hint : ∀ j : Fin d,
      Integrable (fun y => G y j * w.grad y j) (volume.restrict W) := fun j =>
    (hG j).integrable_mul (w.gradMemL2 j)
  rw [← integral_finsetSum _ fun j _ => hint j]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show vecDot (w.grad y) (G y) = ∑ j : Fin d, G y j * w.grad y j
  rw [vecDot]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ## 3. Smooth tests suffice -/

/-- **Smooth tests suffice for weak harmonicity.**

An `H¹(W)` function whose Dirichlet first variation vanishes against every
*smooth compactly supported* test supported in `W` is weakly harmonic on `W`,
i.e. the first variation vanishes against every `H¹₀(W)` competitor.  The proof
tests against the `H10Function` package's own smooth approximants and passes to
the limit coordinatewise. -/
theorem isWeaklyHarmonicOn_of_contDiff_tests {W : Set (Vec d)} (w : H1Function W)
    (h : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ y in W, vecDot (w.grad y) (euclideanGradient φ y) ∂volume = 0) :
    IsWeaklyHarmonicOn W w := by
  intro φ
  have happroxL2 : ∀ (n : ℕ) (j : Fin d),
      MemLp (fun y => euclideanGradient (φ.approx n) y j) 2 (volume.restrict W) :=
    fun n j => memLp_two_fderiv_apply_restrict (φ.approx_smooth n) (φ.approx_hasCompactSupport n) j
  have hsum : ∀ n : ℕ,
      (∑ j : Fin d,
        ∫ y in W, euclideanGradient (φ.approx n) y j * w.grad y j ∂volume) = 0 := by
    intro n
    rw [← integral_vecDot_split w (euclideanGradient (φ.approx n)) (happroxL2 n)]
    exact h (φ.approx n) (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
      (φ.approx_support_subset n)
  have hlim := integral_vecDot_split w φ.toH1Function.grad φ.toH1Function.gradMemL2
  have hconv : ∀ j : Fin d, Tendsto
      (fun n => ∫ y in W, euclideanGradient (φ.approx n) y j * w.grad y j ∂volume)
      atTop (nhds (∫ y in W, φ.toH1Function.grad y j * w.grad y j ∂volume)) := by
    intro j
    exact tendsto_setIntegral_mul_of_tendsto_eLpNormTwo (w.gradMemL2 j)
      (fun n => happroxL2 n j) (φ.toH1Function.gradMemL2 j) (φ.tendsto_approx_grad j)
  have htot : Tendsto
      (fun n => ∑ j : Fin d,
        ∫ y in W, euclideanGradient (φ.approx n) y j * w.grad y j ∂volume) atTop
      (nhds (∑ j : Fin d, ∫ y in W, φ.toH1Function.grad y j * w.grad y j ∂volume)) :=
    tendsto_finsetSum _ fun j _ => hconv j
  have hconst := htot.congr fun n => hsum n
  rw [hlim]
  exact tendsto_nhds_unique hconst tendsto_const_nhds

/-! ## 4. Smooth `H¹₀` competitors carry their classical gradient -/

/-- **A smooth `H¹₀(W)` competitor may be tested with its classical gradient.**

If `ψ` is smooth and lies in `H¹₀(W)`, then weak harmonicity of `v` on `W`
gives the vanishing of the first variation against `euclideanGradient ψ`.  The
`H10Function` witness of `MemH10 W ψ` carries *some* weak gradient of `ψ`; on
the open set `W` it agrees a.e. with the classical one by uniqueness of weak
derivatives, and both are locally integrable there. -/
theorem integral_vecDot_euclideanGradient_eq_zero {W : Set (Vec d)} (hWopen : IsOpen W)
    [IsFiniteMeasure (volume.restrict W)] {v : H1Function W}
    (hv : IsWeaklyHarmonicOn W v) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hmem : MemH10 W ψ) :
    ∫ y in W, vecDot (v.grad y) (euclideanGradient ψ y) ∂volume = 0 := by
  obtain ⟨w, hw⟩ := hmem
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hcont : ∀ j : Fin d, Continuous fun y => euclideanGradient ψ y j := fun j =>
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hae : ∀ j : Fin d, (fun y => w.toH1Function.grad y j)
      =ᵐ[volume.restrict W] fun y => euclideanGradient ψ y j := by
    intro j
    refine HasWeakPartialDerivOn.ae_eq (u := ψ) (i := j) hWopen ?_ ?_ ?_ ?_
    · have hI : IntegrableOn (fun y => w.toH1Function.grad y j) W volume :=
        (w.toH1Function.gradMemL2 j).integrable (by norm_num)
      exact hI.locallyIntegrableOn
    · exact (hcont j).locallyIntegrable.locallyIntegrableOn W
    · rw [← hw]
      exact w.toH1Function.hasWeakGradient j
    · exact HasWeakPartialDerivOn.of_contDiff hψ1
  have haeAll : ∀ᵐ y ∂(volume.restrict W),
      ∀ j : Fin d, w.toH1Function.grad y j = euclideanGradient ψ y j :=
    ae_all_iff.2 hae
  have hEq : ∫ y in W, vecDot (v.grad y) (euclideanGradient ψ y) ∂volume =
      ∫ y in W, vecDot (v.grad y) (w.toH1Function.grad y) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [haeAll] with y hy
    have hvec : euclideanGradient ψ y = w.toH1Function.grad y := by
      funext j
      exact (hy j).symm
    rw [hvec]
  rw [hEq]
  exact hv w

end

end Algsuperdiff.Section4.Provider.ExcessDecay
