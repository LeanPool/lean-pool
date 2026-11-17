/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Operator.Coordinates
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.Kernel
public import LeanPool.KLS.FunctionalInequalities.Probability.Stein.IdentityExtension
public import LeanPool.KLS.FunctionalInequalities.Energy.DualNorm

/-!
# Stein kernels bound the `H^{-1}` norm of linear functions

Letwin, arXiv:2607.24164v1, Lemma 2.9 in generic form: if `τ` is an a.e. symmetric Stein kernel of
`μ ≪ volume` with `|τ|_HS ∈ L²(μ)` and finite second moment, then for every `v` the linear function
`⟪·, v⟫` has finite `H^{-1}(μ)` norm with `‖⟪·, v⟫‖²_{H^{-1}} ≤ ∫ ‖τ(x) v‖² dμ` (A.7 plus
Cauchy–Schwarz
on every unit-energy test).
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace FunctionalInequalities.Probability.Stein

/-- The linear function `⟪·, v⟫` as an element of `L²(μ)`. -/
def linearLp {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ2 :
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
  (hμ2.inner_const (𝕜 := ℝ) v).toLp (fun x => ⟪x, v⟫)

/--
**Letwin Lemma 2.9 (generic form)**: for a Stein kernel of `μ ≪ volume` with finite second moment,
`q = ⟪·, v⟫` is centered, `‖q‖_{H^{-1}}` is finite, equals the real signed supremum, and
`‖q‖²_{H^{-1}} ≤ ∫ ‖τ(x) v‖² dμ`. -/
theorem linear_dual_bound_of_ac {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → KernelMatrix n) (hK : IsSteinKernel μ τ)
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume)
    (hμ2 :
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hSym : SymmetricAE μ τ)
    (hHS : MemLp (fun x => hsNorm (τ x)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    let q := linearLp μ hμ2 v
    (∫ x, q x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) = 0 ∧
      Energy.Dual.dualNorm μ q ≠ ⊤ ∧
        (Energy.Dual.dualNorm μ q).toReal = sSup (Energy.Dual.signedPairings μ q) ∧
          (Energy.Dual.dualNorm μ q).toReal ^ 2 ≤
            ∫ x, ‖action (τ x) v‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  dsimp only
  let q := linearLp μ hμ2 v
  have hlin :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪x, v⟫) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [id_eq] using hμ2.inner_const (𝕜 := ℝ) v
  have hτv := action_memLp hK.measurable_entries hHS v
  let ρ : ℝ :=
    (eLpNorm (fun x => action (τ x) v) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal
  have hρ : 0 ≤ ρ := ENNReal.toReal_nonneg
  have hpair (t : Energy.Dual.UnitEnergyTest μ) : Energy.Dual.pairing μ q t ≤ ρ := by
    have heq :
      Energy.Dual.pairing μ q t =
        ∫ x, ⟪x, v⟫ * t.fn x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [Energy.Dual.pairing, q, linearLp, Real.inner_apply, id_eq] using
        (L2.integral_inner_toLp hlin t.memLp).symm
    have hstein :=
      extended_identity_of_ac μ τ hK hac hμ2 hSym hHS t.fn t.locallyLipschitz t.memLp t.gradLp v
    have hcs := L2.abs_integral_inner_le hτv t.gradLp
    have hunit :
      (eLpNorm (gradient t.fn) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal ≤ 1 := by
      simpa only [Lp.norm_toLp] using t.energy
    calc
      Energy.Dual.pairing μ q t ≤ |Energy.Dual.pairing μ q t| := le_abs_self _
      _ = |∫ x, ⟪action (τ x) v, gradient t.fn x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| := by
        rw [heq, hstein]
      _ ≤ ρ * (eLpNorm (gradient t.fn) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal := hcs
      _ ≤ ρ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hρ
  have hbound : Energy.Dual.dualNorm μ q ≤ ENNReal.ofReal ρ :=
    iSup_le fun t => ENNReal.ofReal_le_ofReal (hpair t)
  have hfinite : Energy.Dual.dualNorm μ q ≠ ⊤ :=
    (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top).ne
  have hreal : (Energy.Dual.dualNorm μ q).toReal ≤ ρ := by
    have h := (ENNReal.toReal_le_toReal hfinite (by simp)).mpr hbound
    simpa only [ENNReal.toReal_ofReal hρ] using h
  have hρsq : ρ ^ 2 = ∫ x, ‖action (τ x) v‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    (L2.integral_norm_sq_eq_eLpNorm_sq hτv).symm
  have hmean : ∫ x, q x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
    have heq : q =ᵐ[(μ : Measure (EuclideanSpace ℝ (Fin n)))] fun x => ⟪x, v⟫ := by
      exact hlin.coeFn_toLp
    rw [integral_congr_ae heq]
    have h := integral_inner (𝕜 := ℝ) hK.integrable_id v
    simpa only [id_eq, hK.mean_zero, inner_zero_right, real_inner_comm] using h
  refine ⟨hmean, hfinite, Energy.Dual.toReal_dualNorm_eq_signed_sSup μ q hfinite, ?_⟩
  rw [← hρsq]
  have hn : 0 ≤ (Energy.Dual.dualNorm μ q).toReal := ENNReal.toReal_nonneg
  nlinarith

end FunctionalInequalities.Probability.Stein

end
