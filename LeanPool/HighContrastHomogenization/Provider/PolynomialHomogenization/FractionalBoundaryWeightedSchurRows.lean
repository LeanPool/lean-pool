/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightAlgebra
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalBoundaryWeightedRieszKernel

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.FractionalBoundaryWeightedSchurRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur rows for the fractional boundary kernel
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The boundary-weighted fractional Riesz kernel used in the Schur test. -/
@[expose]
noncomputable def fractionalBoundarySchurKernel
    (U : Set (Vec d)) (s : ℝ) (x y : Vec d) : ℝ≥0∞ :=
  euclideanBoundaryWeight U s x *
    ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ)))

theorem measurable_fractionalBoundarySchurKernel (U : Set (Vec d)) (s : ℝ) :
    Measurable (Function.uncurry (fractionalBoundarySchurKernel U s)) := by
  have hdist : Measurable (fun z : Vec d × Vec d => euclideanDist z.1 z.2) := by
    have hsub : Measurable (fun z : Vec d × Vec d => z.1 - z.2) :=
      measurable_fst.sub measurable_snd
    unfold euclideanDist euclideanNorm
    exact (continuous_vecNormSq.measurable.comp hsub).sqrt
  exact (measurable_euclideanBoundaryWeight U s).comp measurable_fst |>.mul
    ((hdist.pow measurable_const).ennreal_ofReal)

/-- For `0<s<a` and `s+a<1`, the row and column integrals of the
boundary-weighted fractional kernel are bounded by the same auxiliary
boundary weight, with structural finite constants. -/
theorem exists_fractionalBoundarySchur_row_column
    (hd : 1 ≤ d) {rho Rad s a : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad) (hs : 0 < s)
    (hsa : s < a) (hsa1 : s + a < 1) :
    ∃ A B : ℝ≥0∞, A ≠ ⊤ ∧ B ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad →
          (∀ x ∈ U,
            (∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
                euclideanBoundaryWeight U a y ∂volume) ≤
              A * euclideanBoundaryWeight U a x) ∧
          (∀ y ∈ U,
            (∫⁻ x in U, fractionalBoundarySchurKernel U s x y *
                euclideanBoundaryWeight U a x ∂volume) ≤
              B * euclideanBoundaryWeight U a y) := by
  have ha0 : 0 < a := hs.trans hsa
  have ha1 : a < 1 := by linarith only [hs, hsa1]
  have hspa : s < s + a := lt_add_of_pos_right s ha0
  obtain ⟨A, hAtop, hA⟩ :=
    exists_bound_lintegral_fractionalBoundaryRieszKernel
      hd hrho hRad hs hsa ha1
  obtain ⟨B, hBtop, hB⟩ :=
    exists_bound_lintegral_fractionalBoundaryRieszKernel
      hd hrho hRad hs hspa hsa1
  refine ⟨A, B, hAtop, hBtop, ?_⟩
  intro U hU hsand
  constructor
  · intro x hx
    have hdelta : 0 < euclideanBoundaryDistance U x :=
      euclideanBoundaryDistance_pos hd hU hx
    have hbase := hA U hU hsand x hx
    rw [show (∫⁻ y in U, fractionalBoundarySchurKernel U s x y *
          euclideanBoundaryWeight U a y ∂volume) =
        euclideanBoundaryWeight U s x *
          ∫⁻ y in U, ENNReal.ofReal
              (euclideanDist x y ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U a y ∂volume by
      rw [← lintegral_const_mul'
        (euclideanBoundaryWeight U s x) _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun y => ?_
      unfold fractionalBoundarySchurKernel
      ring]
    calc
      euclideanBoundaryWeight U s x *
          (∫⁻ y in U, ENNReal.ofReal
              (euclideanDist x y ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U a y ∂volume) ≤
          euclideanBoundaryWeight U s x *
            (A * ENNReal.ofReal
              (euclideanBoundaryDistance U x ^ (s - a))) :=
        mul_le_mul_right hbase _
      _ = A * euclideanBoundaryWeight U a x := by
        calc
          euclideanBoundaryWeight U s x *
              (A * ENNReal.ofReal
                (euclideanBoundaryDistance U x ^ (s - a))) =
              A * (euclideanBoundaryWeight U s x *
                ENNReal.ofReal
                  (euclideanBoundaryDistance U x ^ (s - a))) := by
            ac_rfl
          _ = A * euclideanBoundaryWeight U a x := by
            rw [euclideanBoundaryWeight_mul_ofReal_rpow_sub hdelta s a]
  · intro y hy
    have hdelta : 0 < euclideanBoundaryDistance U y :=
      euclideanBoundaryDistance_pos hd hU hy
    have hbase := hB U hU hsand y hy
    calc
      (∫⁻ x in U, fractionalBoundarySchurKernel U s x y *
          euclideanBoundaryWeight U a x ∂volume) =
          ∫⁻ x in U, ENNReal.ofReal
              (euclideanDist y x ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U (s + a) x ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [self_mem_ae_restrict
          (measurableSet_of_isOpenBoundedConvexDomain hU)] with x hx
        have hmul := euclideanBoundaryWeight_mul
          (euclideanBoundaryDistance_pos hd hU hx) s a
        unfold fractionalBoundarySchurKernel
        rw [euclideanDist_comm x y]
        calc
          (euclideanBoundaryWeight U s x *
              ENNReal.ofReal (euclideanDist y x ^ (s - (d : ℝ)))) *
              euclideanBoundaryWeight U a x =
              ENNReal.ofReal (euclideanDist y x ^ (s - (d : ℝ))) *
                (euclideanBoundaryWeight U s x *
                  euclideanBoundaryWeight U a x) := by
            ac_rfl
          _ = ENNReal.ofReal (euclideanDist y x ^ (s - (d : ℝ))) *
              euclideanBoundaryWeight U (s + a) x := by rw [hmul]
      _ ≤ B * ENNReal.ofReal
          (euclideanBoundaryDistance U y ^ (s - (s + a))) := hbase
      _ = B * euclideanBoundaryWeight U a y := by
        congr 1
        unfold euclideanBoundaryWeight
        congr 2
        ring

end

end HighContrast
end HCPolySupport
