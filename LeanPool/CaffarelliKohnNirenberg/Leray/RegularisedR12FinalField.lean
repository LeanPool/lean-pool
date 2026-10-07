/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalFourier
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial

/-!
# Space-time fields from continuous paths of frequency fields

A continuous path `t ↦ G t` of square-integrable frequency fields, weighted
by the inverse Bessel weight of order four and a multiplier of at most
quadratic growth, defines a continuous space-time field through the inverse
Fourier integral. Its spatial partial derivatives multiply the frequency field
by `2πi ξ_j`, and it is bounded on every time set where the path is bounded.
These fields realize the velocity and pressure of `thm:regularised` (R2).
-/

public section

open MeasureTheory FourierTransform Complex
open scoped ENNReal FourierTransform Real

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

section SpaceTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The real space-time field `c (W_M (G t) x)`. -/
@[expose]
def regR12SpaceTimeField (c : E →L[ℝ] ℝ) (M : L2Vec3 → ℂ)
    (G : ℝ → Lp E 2 (volume : Measure L2Vec3)) : ParabolicPoint → ℝ :=
  fun z => c (regR12WeightedField M (G z.2) (WithLp.toLp 2 z.1))

/-- The frequency multiplier of the coordinate partial derivative `∂_j`. -/
@[expose]
def regR12CoordSymbol (j : Fin 3) : L2Vec3 → ℂ :=
  regR12DirSymbol (WithLp.toLp 2 (basisVec j))

theorem regR12CoordSymbol_continuous (j : Fin 3) : Continuous (regR12CoordSymbol j) :=
  regR12DirSymbol_continuous _

theorem regR12CoordSymbol_norm_le (j : Fin 3) (ξ : L2Vec3) :
    ‖regR12CoordSymbol j ξ‖ ≤ 2 * π * ‖ξ‖ := by
  have h := regR12DirSymbol_norm_le (WithLp.toLp 2 (basisVec j)) ξ
  have hn : ‖(WithLp.toLp 2 (basisVec j) : L2Vec3)‖ = 1 := by
    rw [← vec3EuclideanNorm_eq_l2]
    simp [vec3EuclideanNorm, basisVec, Pi.single_apply]
  rw [hn, mul_one] at h
  exact h

variable (c : E →L[ℝ] ℝ) (M : L2Vec3 → ℂ) (hM : AEStronglyMeasurable M) (C : ℝ) (hC : 0 ≤ C)
  (hMC : ∀ ξ, ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2))
  (G : ℝ → Lp E 2 (volume : Measure L2Vec3))

include hM hC hMC in
/-- The space-time field is continuous for the product topology. -/
theorem regR12SpaceTimeField_continuous (hG : Continuous G) :
    Continuous (fun z : Vec3 × ℝ => c (regR12WeightedField M (G z.2) (WithLp.toLp 2 z.1))) := by
  have hW : Continuous (fun p : Lp E 2 (volume : Measure L2Vec3) × L2Vec3 =>
      regR12WeightedField M p.1 p.2) := regR12WeightedField_continuous M hM C hC hMC
  have hpair : Continuous (fun z : Vec3 × ℝ =>
      ((G z.2, WithLp.toLp 2 z.1) : Lp E 2 (volume : Measure L2Vec3) × L2Vec3)) :=
    (hG.comp continuous_snd).prodMk ((PiLp.continuous_toLp 2 _).comp continuous_fst)
  have h3 := hW.comp hpair
  exact c.continuous.comp h3

include hM hC hMC in
/-- The space-time field is bounded by the norm of the frequency path. -/
theorem regR12SpaceTimeField_abs_le (z : ParabolicPoint) :
    |regR12SpaceTimeField c M G z| ≤
      ‖c‖ * (C * (eLpNorm regR12Kernel 2 volume).toReal * ‖G z.2‖) := by
  rw [← Real.norm_eq_abs]
  exact (c.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (regR12WeightedField_norm_le M hM C hC hMC _ _) (norm_nonneg c))

include hM hC hMC in
/-- The spatial slices of the space-time field are differentiable, with the
coordinate partial derivatives given by multiplication by `2πi ξ_j`. -/
theorem regR12SpaceTimeField_spatialPartial
    (hMC1 : ∀ ξ, ‖ξ‖ * ‖M ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2)) (z : ParabolicPoint) :
    DifferentiableAt ℝ (fun x : Vec3 => regR12SpaceTimeField c M G (x, z.2)) z.1 ∧
      ∀ j : Fin 3, spatialPartial (regR12SpaceTimeField c M G) j z =
        regR12SpaceTimeField c (fun ξ => regR12CoordSymbol j ξ * M ξ) G z := by
  let L : Vec3 →L[ℝ] L2Vec3 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hL : ∀ x, L x = WithLp.toLp 2 x := fun _ => rfl
  obtain ⟨hd, -⟩ := regR12WeightedField_fderiv_apply M hM C hC hMC hMC1 (G z.2)
    (L z.1) (L z.1)
  have hcomp : HasFDerivAt (fun x : Vec3 => regR12SpaceTimeField c M G (x, z.2))
      (c.comp ((fderiv ℝ (regR12WeightedField M (G z.2)) (L z.1)).comp L)) z.1 :=
    c.hasFDerivAt.comp z.1 (hd.comp z.1 L.hasFDerivAt)
  refine ⟨hcomp.differentiableAt, fun j => ?_⟩
  unfold spatialPartial
  rw [hcomp.fderiv]
  obtain ⟨-, hformula⟩ := regR12WeightedField_fderiv_apply M hM C hC hMC hMC1 (G z.2)
    (L z.1) (L (basisVec j))
  simp only [ContinuousLinearMap.comp_apply]
  rw [hformula]
  rfl

end SpaceTime

/-- Continuity for the product topology gives continuity for the parabolic
topology of ParabolicPoint. -/
theorem regR12_continuousOn_of_prod {F : ParabolicPoint → ℝ} {S : Set (Vec3 × ℝ)}
    (hF : ContinuousOn (fun z : Vec3 × ℝ => F ((z.1, z.2) : ParabolicPoint)) S) :
    ContinuousOn F (S : Set ParabolicPoint) := by
  exact hF.comp parabolicHomeomorph.continuous.continuousOn (fun _ hz => hz)

end CKN.Leray
