/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedComplexLinearVolterraUniqueness
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLinearLocalMapPhysical
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalComplexShiftMild

/-!
# Physical agreement after a complete Sobolev restart

The complete Sobolev solution of the equation linearized around the global
physical trajectory realizes that same global trajectory on its interval.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A fixed point of the complete Sobolev linear equation after any
nonnegative restart time represents the global complex physical mild curve. -/
theorem regularisedBesselLinearFixedPoint_physical_eq_global_shift
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (k : ℕ)
    (b₀ : RealVectorL2) (hbJ : RegularizedMildJData b₀)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (b : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2)
    (hb : regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) b =
        complexifyVectorL2 (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a))
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2))
    (hfix : regularisedBesselLinearLocalMap ρ ε hε k b T hT
      (regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T)
      ‖b₀‖ (norm_nonneg b₀)
      (regularisedGlobalComplexShiftPath_norm_le_initial
        ρ ε hε b₀ hbJ a T ha) v = v)
    (t : RegularizedMildTimeInterval T) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ)
      (by positivity) (v t) =
        complexifyVectorL2
          (regularizedGlobalMildCurve ρ ε hε b₀ hbJ (a + t.1)) := by
  let E := regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
  let g := regularisedGlobalComplexShiftPath ρ ε hε b₀ hbJ a T
  let w : C(RegularizedMildTimeInterval T, ComplexVectorL2) :=
    ⟨fun q => E (v q), E.continuous.comp v.continuous⟩
  have hw (q : RegularizedMildTimeInterval T) :
      w q = heatSemigroup q.1 q.2.1
          (complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a)) -
        ∫ τ in (0 : ℝ)..T,
          if h : 0 < τ ∧ τ < q.1 then
            stokesL2Operator h.1
              (regularisedTensorPhysicalMap ρ ε hε
                (g (regularizedMildTimeClamp T hT (q.1 - τ)))
                (w (regularizedMildTimeClamp T hT (q.1 - τ))))
          else 0 := by
    have hfixq := congrArg
      (fun z : C(RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2) => z q)
      hfix
    have hphysical := regularisedBesselLinearLocalMap_physical
      ρ ε hε k b T hT g ‖b₀‖ (norm_nonneg b₀)
        (regularisedGlobalComplexShiftPath_norm_le_initial
          ρ ε hε b₀ hbJ a T ha) v q
    change E (regularisedBesselLinearLocalMap ρ ε hε k b T hT g
      ‖b₀‖ (norm_nonneg b₀)
      (regularisedGlobalComplexShiftPath_norm_le_initial
        ρ ε hε b₀ hbJ a T ha) v q) = _ at hphysical
    rw [hfixq] at hphysical
    rw [hb] at hphysical
    change w q = _ at hphysical
    exact hphysical
  have hg (q : RegularizedMildTimeInterval T) :
      g q = heatSemigroup q.1 q.2.1
          (complexifyVectorL2
            (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a)) -
        ∫ τ in (0 : ℝ)..T,
          if h : 0 < τ ∧ τ < q.1 then
            stokesL2Operator h.1
              (regularisedTensorPhysicalMap ρ ε hε
                (g (regularizedMildTimeClamp T hT (q.1 - τ)))
                (g (regularizedMildTimeClamp T hT (q.1 - τ))))
          else 0 := by
    exact regularisedGlobalComplexShiftPath_linearMild
      ρ ε hε b₀ hbJ a T ha hT q
  have hEq := regularisedComplexLinearVolterra_unique ρ ε hε T hT g
    (complexifyVectorL2 (regularizedGlobalMildCurve ρ ε hε b₀ hbJ a))
    w g hw hg
  have hAt := congrArg
    (fun z : C(RegularizedMildTimeInterval T, ComplexVectorL2) => z t) hEq
  exact hAt

end CKN.Leray

end
