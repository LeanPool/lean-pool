/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import LeanPool.KLS.FunctionalInequalities.L2.Pairing
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus

/-!
# Compact-test dual bound from a latent source identity
-/

@[expose] public section

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff

section CompactSourceDualBound

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.Stein

/--
Squared dual bound from a source identity: for a latent L2 field paired with compactly supported
smooth tests through a
measurable pushforward onto an actual probability law, the linear pairing squared is bounded by the
field's L2 norm
squared times `∫ ‖Dh‖²`. Arbitrary latent measure space; all Euclidean dimensions. -/
theorem compact_linear_pairing_sq_le_of_source_identity {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (Z F : Ω → EuclideanSpace ℝ (Fin n)) (hZ : Measurable Z)
    (hmap : P.map Z = (mu : Measure (EuclideanSpace ℝ (Fin n)))) (hF : MemLp F 2 P)
    (v : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h)
    (hid :
      (∫ x, ⟪x, v⟫ * h x ∂(mu : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ w, ⟪F w, gradient h (Z w)⟫ ∂P) :
    (∫ x, ⟪x, v⟫ * h x ∂(mu : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
      (∫ w, ‖F w‖ ^ 2 ∂P) *
        ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(mu : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgc := continuous_gradient hh1
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support (hasCompactSupport_gradient hhc)
  have hg : MemLp (gradient h) 2 (mu : Measure (EuclideanSpace ℝ (Fin n))) :=
    MemLp.of_bound hgc.aestronglyMeasurable C (ae_of_all _ hC)
  have hMP : MeasurePreserving Z P (mu : Measure (EuclideanSpace ℝ (Fin n))) := ⟨hZ, hmap⟩
  have hG := hg.comp_measurePreserving hMP
  have hCS := FunctionalInequalities.L2.abs_integral_inner_le hF hG
  have hEnergy :
    (∫ w, ‖gradient h (Z w)‖ ^ 2 ∂P) =
      ∫ x, ‖gradient h x‖ ^ 2 ∂(mu : Measure (EuclideanSpace ℝ (Fin n))) := by
    change (∫ w, ‖(gradient h ∘ Z) w‖ ^ 2 ∂P) = _
    rw [FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hG,
      FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hg,
      eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hMP]
  have hNorm (x : EuclideanSpace ℝ (Fin n)) : ‖gradient h x‖ = ‖fderiv ℝ h x‖ :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map _
  rw [hid]
  calc
    _ = |∫ w, ⟪F w, gradient h (Z w)⟫ ∂P| ^ 2 := (sq_abs _).symm
    _ ≤ ((eLpNorm F 2 P).toReal * (eLpNorm (gradient h ∘ Z) 2 P).toReal) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).2 hCS
    _ = (∫ w, ‖F w‖ ^ 2 ∂P) * ∫ w, ‖gradient h (Z w)‖ ^ 2 ∂P := by
      rw [mul_pow, ← FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hF, ←
        FunctionalInequalities.L2.integral_norm_sq_eq_eLpNorm_sq hG]
      rfl
    _ = _ := by rw [hEnergy]; simp_rw [hNorm]

end FunctionalInequalities.Probability.Stein

end CompactSourceDualBound
