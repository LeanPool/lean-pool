/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.CutoffTest
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.CaccioppoliAbsorbed

/-!
# WeightedEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Weighted energy inequality for a localized solution

The decay estimates of this directory rest on the Caccioppoli inequality
obtained by testing `-div (a grad u) = g` with `zeta ^ 2 * u`, where `zeta` is
a smooth compactly supported weight whose topological support lies in the
domain.  Unlike the De Giorgi cutoff test, no level truncation is involved:
the estimate is applied to the solution itself, and the mass term produced by
the forcing is what drives the decay.  The Young inequality for the flux
cross term is the one already used by the level-set estimate,
`DivergenceFormProcess.Form.cutoff_flux_young`.

## Main results

- `DivergenceFormProcess.Decay.weightedEnergy_identity`: the exact identity
  produced by the test `zeta ^ 2 * u`.
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-- The square of an `H¹` value against an essentially bounded weight is
integrable. -/
theorem integrable_sq_mul_memLpTop {u : H1Function U} {F : Vec d → ℝ}
    (hF : MemLp F ∞ (volumeMeasureOn U)) :
    Integrable (fun x => u.toFun x ^ 2 * F x) (volumeMeasureOn U) := by
  have hFu : MemScalarL2 U (fun x => u.toFun x * F x) := by
    simpa only [MemScalarL2, volumeMeasureOn, mul_comm] using u.memL2.fun_mul hF
  apply (hFu.integrable_mul u.memL2).congr
  filter_upwards with x
  simp only [Pi.mul_apply]
  ring

section Weight

variable {zeta : Vec d → ℝ}

/-- The square of a smooth compactly supported weight is a smooth compactly
supported multiplier. -/
theorem sq_weight_smooth (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hzetaCompact : HasCompactSupport zeta) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => zeta x ^ 2) ∧
      HasCompactSupport (fun x => zeta x ^ 2) :=
  ⟨by simpa only [pow_two] using hzeta.mul hzeta,
    by simpa only [pow_two] using! hzetaCompact.mul_left (f := zeta)⟩

/-- Squaring does not enlarge the topological support. -/
theorem tsupport_sq_weight_subset {V : Set (Vec d)} (hzetaU : tsupport zeta ⊆ V) :
    tsupport (fun x => zeta x ^ 2) ⊆ V := by
  have hsupp : Function.support (fun x => zeta x ^ 2) = Function.support zeta := by
    ext x
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
      not_false_eq_true]
  exact (closure_mono hsupp.subset).trans hzetaU

/-- The squared weight is admissible whenever the weight is supported in the
domain. -/
theorem isAdmissibleMultiplier_sq_of_tsupport_subset
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hzetaCompact : HasCompactSupport zeta)
    (hzetaU : tsupport zeta ⊆ U) :
    IsAdmissibleMultiplier U u (fun x => zeta x ^ 2) :=
  isAdmissibleMultiplier_of_tsupport_subset hU u
    (sq_weight_smooth hzeta hzetaCompact).1
    (sq_weight_smooth hzeta hzetaCompact).2
    (tsupport_sq_weight_subset hzetaU)

/-- The squared weight is admissible for a factor with zero trace. -/
theorem isAdmissibleMultiplier_sq_of_zeroTrace (z : H10Function U)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hzetaCompact : HasCompactSupport zeta) :
    IsAdmissibleMultiplier U z.toH1Function (fun x => zeta x ^ 2) :=
  isAdmissibleMultiplier_of_zeroTrace z
    (sq_weight_smooth hzeta hzetaCompact).1
    (sq_weight_smooth hzeta hzetaCompact).2

/-- The Fréchet derivative of the squared weight in a coordinate direction. -/
private theorem fderiv_sq_weight (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y => zeta y ^ 2) x) (basisVec i) =
      2 * zeta x * (fderiv ℝ zeta x) (basisVec i) := by
  have hdiff : DifferentiableAt ℝ zeta x := hzeta.differentiable (by simp) x
  rw [show (fun y => zeta y ^ 2) = zeta * zeta by
    funext y; simp only [pow_two, Pi.mul_apply]]
  rw [fderiv_mul hdiff hdiff]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Testing `-div (a grad u) = g` with `zeta ^ 2 * u` gives the exact energy
identity.  No ellipticity estimate is used here. -/
theorem weightedEnergy_identity {a : CoeffField d} {g : Vec d → ℝ}
    {u : H1Function U} (hsol : IsScalarForcedWeakSolution a U g u)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hadm : IsAdmissibleMultiplier U u (fun x => zeta x ^ 2)) :
    (∫ x in U,
        zeta x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (u.grad x) +
          2 * zeta x * u.toFun x *
            vecDot (matVecMul (a x) (u.grad x))
              (fun i => (fderiv ℝ zeta x) (basisVec i))
        ∂volume) =
      ∫ x in U, g x * (zeta x ^ 2 * u.toFun x) ∂volume := by
  obtain ⟨w, hwval, hwgrad⟩ := hadm
  have hweak := hsol.2 w
  calc
    (∫ x in U,
        zeta x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (u.grad x) +
          2 * zeta x * u.toFun x *
            vecDot (matVecMul (a x) (u.grad x))
              (fun i => (fderiv ℝ zeta x) (basisVec i))
        ∂volume) =
        ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (w.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hwgrad] with x hx
      rw [hx]
      have hpt : ∀ i : Fin d,
          matVecMul (a x) (u.grad x) i *
              (zeta x ^ 2 * u.grad x i +
                u.toFun x * (fderiv ℝ (fun y => zeta y ^ 2) x) (basisVec i)) =
            zeta x ^ 2 * (matVecMul (a x) (u.grad x) i * u.grad x i) +
              2 * zeta x * u.toFun x *
                (matVecMul (a x) (u.grad x) i *
                  (fderiv ℝ zeta x) (basisVec i)) := by
        intro i
        rw [fderiv_sq_weight hzeta x i]
        ring
      simp only [vecDot, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hpt i)]
      simp only [Finset.sum_add_distrib]
    _ = ∫ x in U, g x * w.toH1Function.toFun x ∂volume := hweak
    _ = ∫ x in U, g x * (zeta x ^ 2 * u.toFun x) ∂volume := by
      rw [hwval]

end Weight

end DivergenceFormProcess.Decay
