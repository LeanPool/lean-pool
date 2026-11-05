/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.DeGiorgiOneSided
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.DivergenceLevelEnergy

/-!
# DivergenceDeGiorgiBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

namespace DivergenceFormProcess.Regularity

open HCPolySupport MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

private theorem weakSolution_neg
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {u : H10Function U} {g : Vec d → Vec d}
    (hsol : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    IsZeroTraceDirichletRhsWeakSolution a U (-u) (fun x => -g x) := by
  intro φ
  have hbase := hsol φ
  change
    ∫ x in U, vecDot (matVecMul (a x) ((-u.toH1Function).grad x))
        (φ.toH1Function.grad x) ∂volume = _
  calc
    ∫ x in U, vecDot (matVecMul (a x) ((-u.toH1Function).grad x))
        (φ.toH1Function.grad x) ∂volume =
        -∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [H1Function.neg_grad, matVecMul_neg, vecDot_neg_left]
    _ = -∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂volume := by
      rw [hbase]
    _ = ∫ x in U, vecDot (-g x) (φ.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [vecDot_neg_left]

private theorem vecNormSq_neg (d : ℕ) (v : Vec d) :
    vecNormSq (-v) = vecNormSq v := by
  simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]

/-- **The De Giorgi constant of the dimension.**  In every dimension at least
two there is one nonnegative constant with the following property: on every
axis cube, for every coefficient field elliptic there, every measurable
zero-trace weak solution with a divergence forcing bounded by `M` obeys the
De Giorgi bound with that constant.  The constant stands outside the cube, its
side length, the coefficient field, both ellipticity constants, the solution,
the forcing and its bound, so it depends on the dimension alone. -/
theorem exists_deGiorgi_bound_constant {d : ℕ} (hd : 2 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L →
        ∀ (a : CoeffField d) (lam Lam : ℝ), 0 < lam →
          IsEllipticFieldOn lam Lam (axisCube z L) a →
          ∀ (u : H10Function (axisCube z L)) (g : Vec d → Vec d),
            IsZeroTraceDirichletRhsWeakSolution a (axisCube z L) u g →
            Measurable u.toH1Function.toFun →
            MemVectorL2 (axisCube z L) g →
            ∀ M : ℝ, 0 ≤ M →
              (∀ᵐ x ∂volumeMeasureOn (axisCube z L),
                Real.sqrt (vecNormSq (g x)) ≤ M) →
              ∀ᵐ x ∂volumeMeasureOn (axisCube z L),
                |u.toH1Function.toFun x| ≤
                  Cd * L * ((Real.sqrt d / lam) * M) := by
  obtain ⟨Cd, hCd, hcore⟩ := deGiorgi_one_sided_core_of_two_le hd
  refine ⟨Cd, hCd, ?_⟩
  have bound : ∀ (z : Vec d) (L : ℝ), 0 < L →
      ∀ (a : CoeffField d) (lam Lam : ℝ), 0 < lam →
        IsEllipticFieldOn lam Lam (axisCube z L) a →
        ∀ (v : H10Function (axisCube z L)) (q : Vec d → Vec d),
          IsZeroTraceDirichletRhsWeakSolution a (axisCube z L) v q →
          Measurable v.toH1Function.toFun →
          MemVectorL2 (axisCube z L) q →
          ∀ M : ℝ, 0 ≤ M →
            (∀ᵐ x ∂volumeMeasureOn (axisCube z L),
              Real.sqrt (vecNormSq (q x)) ≤ M) →
            ∀ᵐ x ∂volumeMeasureOn (axisCube z L),
              v.toH1Function.toFun x ≤ Cd * L * ((Real.sqrt d / lam) * M) := by
    intro z L hL a lam Lam hlam hEll v q hsolv hvMeas hq M hM hqBound
    have hdiff : MemH10 (axisCube z L)
        (fun x => v.toH1Function.toFun x -
          (0 : H1Function (axisCube z L)).toFun x) := by
      simpa only [H1Function.zero_toFun, Pi.zero_apply, sub_zero] using v.memH10
    have hbound := hcore z L hL v.toH1Function 0 hvMeas measurable_zero
      hdiff 0 ((Real.sqrt d / lam) * M)
    have hE : 0 ≤ (Real.sqrt d / lam) * M :=
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hlam.le) hM
    have hmedian :
        volume {x | x ∈ axisCube z L ∧ 0 < v.toH1Function.toFun x} +
            volume {x | x ∈ axisCube z L ∧
              0 < (0 : H1Function (axisCube z L)).toFun x} ≤
          volume (axisCube z L) := by
      simpa only [H1Function.zero_toFun, Pi.zero_apply, lt_self_iff_false,
        and_false, Set.ofPred_false, measure_empty, add_zero] using
        (measure_mono (show
          {x | x ∈ axisCube z L ∧ 0 < v.toH1Function.toFun x} ⊆ axisCube z L from
            fun _ hx => hx.1))
    have henergy : ∀ k : ℝ, 0 ≤ k →
        (∑ i : Fin d, (eLpNorm
            ({x | x ∈ axisCube z L ∧ 0 + k < v.toH1Function.toFun x}.indicator
              (fun x => v.toH1Function.grad x i)) 2
            (volumeMeasureOn (axisCube z L))).toReal) +
          ∑ i : Fin d, (eLpNorm
            ({x | x ∈ axisCube z L ∧
                0 + k < (0 : H1Function (axisCube z L)).toFun x}.indicator
              (fun x => (0 : H1Function (axisCube z L)).grad x i)) 2
            (volumeMeasureOn (axisCube z L))).toReal ≤
          ((Real.sqrt d / lam) * M) * Real.sqrt
            ((volume {x | x ∈ axisCube z L ∧
              0 + k < v.toH1Function.toFun x}).toReal +
            (volume {x | x ∈ axisCube z L ∧
              0 + k < (0 : H1Function (axisCube z L)).toFun x}).toReal) := by
      intro k hk
      have hlevel :=
        HCPolySupport.IsZeroTraceDirichletRhsWeakSolution.levelEnergy_sumCoordNorm_le
          (isOpenBoundedConvexDomain_axisCube z L) hlam hEll hsolv hvMeas hq hM hk hqBound
      simpa only [zero_add, H1Function.zero_toFun, Pi.zero_apply,
        H1Function.zero_grad, Pi.zero_apply, hk.not_gt, and_false, Set.ofPred_false,
        Set.indicator_zero, eLpNorm_fun_zero, ENNReal.toReal_zero,
        Finset.sum_const_zero, measure_empty, add_zero] using hlevel
    simpa only [zero_add] using hbound hE hmedian henergy
  intro z L hL a lam Lam hlam hEll u g hsol huMeas hg M hM hgBound
  have hup := bound z L hL a lam Lam hlam hEll u g hsol huMeas hg M hM hgBound
  have hnegSol := weakSolution_neg hsol
  have hnegMeas : Measurable (-u).toH1Function.toFun := by
    change Measurable (-u.toH1Function).toFun
    simpa only [H1Function.neg_toFun] using! huMeas.neg
  have hgNeg : MemVectorL2 (axisCube z L) (fun x => -g x) := by
    simpa only [Pi.neg_apply] using! hg.neg
  have hgNegBound : ∀ᵐ x ∂volumeMeasureOn (axisCube z L),
      Real.sqrt (vecNormSq (-g x)) ≤ M := by
    filter_upwards [hgBound] with x hx
    rwa [vecNormSq_neg]
  have hdown := bound z L hL a lam Lam hlam hEll (-u) (fun x => -g x) hnegSol
    hnegMeas hgNeg M hM hgNegBound
  filter_upwards [hup, hdown] with x hx hnx
  apply abs_le.mpr
  constructor
  · have hnx' : -u.toH1Function.toFun x ≤
        Cd * L * ((Real.sqrt d / lam) * M) := by
      change (-u.toH1Function).toFun x ≤ _ at hnx
      simpa only [H1Function.neg_toFun] using hnx
    exact neg_le.mp hnx'
  · exact hx

end
end DivergenceFormProcess.Regularity
