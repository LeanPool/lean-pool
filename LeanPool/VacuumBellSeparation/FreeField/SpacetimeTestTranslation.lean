/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation of the actual compact spacetime test functions

Translation by a sends F(x) to F(x-a). Its physical mass-shell Fourier
transform gains the phase exp(i(omega(p) a.time - p dot a.space)). The
modulus-one phase cancels from the physical one-particle inner product.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- Spacetime translate. -/
def spacetimeTranslate (a : Spacetime) (F : RealTestFunction) : RealTestFunction :=
  ⟨fun x => F.1 (x - a), F.2.1.comp (contDiff_id.sub contDiff_const),
    F.2.2.comp_homeomorph (Homeomorph.subRight a)⟩

theorem tsupport_spacetimeTranslate (a : Spacetime) (F : RealTestFunction) :
    tsupport (spacetimeTranslate a F).1 = (fun x => x - a) ⁻¹' tsupport F.1 :=
  tsupport_comp_eq_preimage F.1 (Homeomorph.subRight a)

theorem spacetimeTranslate_add (a : Spacetime) (F G : RealTestFunction) :
    spacetimeTranslate a (F + G) = spacetimeTranslate a F + spacetimeTranslate a G := by
  apply Subtype.ext
  rfl

theorem spacetimeTranslate_cancel_neg (a : Spacetime) (F : RealTestFunction) :
    spacetimeTranslate a (spacetimeTranslate (-a) F) = F := by
  apply Subtype.ext
  funext x
  simp only [spacetimeTranslate, sub_neg_eq_add, sub_add_cancel]

/-- Spacetime translation phase given by `Complex.exp (Complex.I * ((dispersion m p * a.1 - ⟪p,
a.2⟫_ℝ : ℝ) : ℂ))`. -/
def spacetimeTranslationPhase (m : ℝ) (a : Spacetime)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (Complex.I * ((dispersion m p * a.1 - ⟪p, a.2⟫_ℝ : ℝ) : ℂ))

theorem norm_spacetimeTranslationPhase (m : ℝ) (a : Spacetime)
    (p : EuclideanSpace ℝ (Fin 3)) : ‖spacetimeTranslationPhase m a p‖ = 1 := by
  rw [spacetimeTranslationPhase, Complex.norm_exp]
  simp

theorem oneParticle_spacetimeTranslate (m : ℝ) (a : Spacetime)
    (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (spacetimeTranslate a F) p =
      spacetimeTranslationPhase m a p * oneParticle m F p := by
  have harg (x : Spacetime) :
      dispersion m p * (x + a).1 - ⟪p, (x + a).2⟫_ℝ =
        (dispersion m p * x.1 - ⟪p, x.2⟫_ℝ) +
          (dispersion m p * a.1 - ⟪p, a.2⟫_ℝ) := by
    change dispersion m p * (x.1 + a.1) - ⟪p, x.2 + a.2⟫_ℝ = _
    rw [inner_add_right]
    ring
  have : (volume : Measure Spacetime).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  unfold oneParticle
  rw [← integral_add_right_eq_self
    (fun x : Spacetime =>
      Complex.exp (Complex.I * ((dispersion m p * x.1 - ⟪p, x.2⟫_ℝ : ℝ) : ℂ)) *
        ((spacetimeTranslate a F).1 x : ℂ)) a]
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change Complex.exp (Complex.I *
      ((dispersion m p * (x + a).1 - ⟪p, (x + a).2⟫_ℝ : ℝ) : ℂ)) *
      (F.1 ((x + a) - a) : ℂ) = _
  rw [add_sub_cancel_right, harg, Complex.ofReal_add, mul_add, Complex.exp_add]
  unfold spacetimeTranslationPhase
  ring

theorem oneParticleInner_spacetimeTranslate (m : ℝ) (a : Spacetime)
    (F G : RealTestFunction) :
    oneParticleInner m (spacetimeTranslate a F) (spacetimeTranslate a G) =
      oneParticleInner m F G := by
  unfold oneParticleInner
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun p => ?_
  change conj (oneParticle m (spacetimeTranslate a F) p) *
      oneParticle m (spacetimeTranslate a G) p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
    conj (oneParticle m F p) * oneParticle m G p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)
  rw [oneParticle_spacetimeTranslate, oneParticle_spacetimeTranslate, map_mul]
  have hc : conj (spacetimeTranslationPhase m a p) * spacetimeTranslationPhase m a p = 1 := by
    rw [Complex.conj_mul', norm_spacetimeTranslationPhase]
    norm_num
  calc
    _ = (conj (spacetimeTranslationPhase m a p) * spacetimeTranslationPhase m a p) *
        (conj (oneParticle m F p) * oneParticle m G p *
          ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hc, one_mul]

end VacuumBellSeparation
