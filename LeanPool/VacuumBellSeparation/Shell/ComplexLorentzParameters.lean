/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.LorentzParameterFamily
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Coordinates and actual derivatives of the Lorentz factors

These explicit complex formulas are identified with the complexification
of the original real spacetime maps. Their derivatives are real
parameter derivatives; the spacetime argument remains complex.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Complex Lorentz parameter action. -/
noncomputable def complexLorentzParameterAction (j : Fin 6) (s : ℝ)
    (z : ComplexSpacetime) : ComplexSpacetime :=
  ![((Real.cosh s : ℂ) * z.1 + (Real.sinh s : ℂ) * z.2 0,
      ![(Real.sinh s : ℂ) * z.1 + (Real.cosh s : ℂ) * z.2 0, z.2 1, z.2 2]),
    ((Real.cosh s : ℂ) * z.1 + (Real.sinh s : ℂ) * z.2 1,
      ![z.2 0, (Real.sinh s : ℂ) * z.1 + (Real.cosh s : ℂ) * z.2 1, z.2 2]),
    (z.1, ![(Real.cos s : ℂ) * z.2 0 - (Real.sin s : ℂ) * z.2 1,
      (Real.sin s : ℂ) * z.2 0 + (Real.cos s : ℂ) * z.2 1, z.2 2]),
    (z.1, ![(Real.cos s : ℂ) * z.2 0 - (Real.sin s : ℂ) * z.2 2,
      z.2 1, (Real.sin s : ℂ) * z.2 0 + (Real.cos s : ℂ) * z.2 2]),
    (z.1, ![z.2 0, (Real.cos s : ℂ) * z.2 1 - (Real.sin s : ℂ) * z.2 2,
      (Real.sin s : ℂ) * z.2 1 + (Real.cos s : ℂ) * z.2 2]),
    ((Real.cosh s : ℂ) * z.1 + (Real.sinh s : ℂ) * z.2 2,
      ![z.2 0, z.2 1, (Real.sinh s : ℂ) * z.1 + (Real.cosh s : ℂ) * z.2 2])] j

theorem complexified_lorentzParameterFactor (j : Fin 6) (s : ℝ)
    (z : ComplexSpacetime) :
    complexifiedSpacetimeMap (lorentzParameterFactor j s) z =
      complexLorentzParameterAction j s z := by
  fin_cases j <;> apply Prod.ext
  all_goals
    try (ext i; fin_cases i)
  all_goals
    simp [lorentzParameterFactor, complexLorentzParameterAction,
      complexifiedSpacetimeMap_apply, complexSpacetimeOfReal, Fin.sum_univ_three,
      coordinateBoost2, coordinateBoost3, spatialLorentzConjugate_apply,
      coordinateLorentzRotation13_eq, coordinateLorentzRotation23_eq,
      boost_apply, boostCLM_apply, spatialRotation_apply,
      spatialPlaneRotation_apply, spatialPlaneRotation13_apply, spatialPlaneRotation23_apply,
      spatialCoordinatePermutation, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft', Equiv.swap_apply_def, coordDir_zero, coordDir_succ,
      e₁, EuclideanSpace.inner_single_left, PiLp.single_apply, Complex.ofReal_add,
      Complex.ofReal_sub]
  all_goals ring

/-- Lorentz parameter generator. -/
noncomputable def lorentzParameterGenerator (j : Fin 6) (z : ComplexSpacetime) :
    ComplexSpacetime :=
  ![(z.2 0, ![z.1, 0, 0]), (z.2 1, ![0, z.1, 0]),
    (0, ![-z.2 1, z.2 0, 0]), (0, ![-z.2 2, 0, z.2 0]),
    (0, ![0, -z.2 2, z.2 1]), (z.2 2, ![0, 0, z.1])] j

theorem contDiff_complexLorentzParameterAction (j : Fin 6) :
    ContDiff ℝ ⊤ (fun q : ℝ × ComplexSpacetime =>
      complexLorentzParameterAction j q.1 q.2) := by
  have hz₀ : ContDiff ℝ ⊤ (fun q : ℝ × ComplexSpacetime => q.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hz (i : Fin 3) : ContDiff ℝ ⊤ (fun q : ℝ × ComplexSpacetime => q.2.2 i) :=
    (contDiff_apply ℝ (fun _ : Fin 3 => ℂ) i).comp (contDiff_snd.comp contDiff_snd)
  have hc : ContDiff ℝ ⊤ (fun q : ℝ × ComplexSpacetime => (Real.cosh q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cosh.comp contDiff_fst)
  have hs : ContDiff ℝ ⊤ (fun q : ℝ × ComplexSpacetime => (Real.sinh q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sinh.comp contDiff_fst)
  have hco : ContDiff ℝ ⊤ (fun q : ℝ × ComplexSpacetime => (Real.cos q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp contDiff_fst)
  have hsi : ContDiff ℝ ⊤ (fun q : ℝ × ComplexSpacetime => (Real.sin q.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_fst)
  fin_cases j
  · apply ContDiff.prodMk
    · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
          using (hc.mul hz₀).add (hs.mul (hz 0))
    · apply contDiff_pi.mpr
      intro i
      fin_cases i
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hs.mul hz₀).add (hc.mul (hz 0))
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 1
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 2
  · apply ContDiff.prodMk
    · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
          using (hc.mul hz₀).add (hs.mul (hz 1))
    · apply contDiff_pi.mpr
      intro i
      fin_cases i
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 0
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hs.mul hz₀).add (hc.mul (hz 1))
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 2
  · apply ContDiff.prodMk
    · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def] using hz₀
    · apply contDiff_pi.mpr
      intro i
      fin_cases i
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hco.mul (hz 0)).sub (hsi.mul (hz 1))
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hsi.mul (hz 0)).add (hco.mul (hz 1))
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 2
  · apply ContDiff.prodMk
    · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def] using hz₀
    · apply contDiff_pi.mpr
      intro i
      fin_cases i
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hco.mul (hz 0)).sub (hsi.mul (hz 2))
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 1
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hsi.mul (hz 0)).add (hco.mul (hz 2))
  · apply ContDiff.prodMk
    · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def] using hz₀
    · apply contDiff_pi.mpr
      intro i
      fin_cases i
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 0
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hco.mul (hz 1)).sub (hsi.mul (hz 2))
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hsi.mul (hz 1)).add (hco.mul (hz 2))
  · apply ContDiff.prodMk
    · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
        Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
          using (hc.mul hz₀).add (hs.mul (hz 2))
    · apply contDiff_pi.mpr
      intro i
      fin_cases i
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 0
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using hz 1
      · simpa only [complexLorentzParameterAction, Matrix.cons_val_zero, Matrix.cons_val_zero',
          Matrix.cons_val_succ, Matrix.cons_val_succ', Pi.add_def, Pi.mul_def, Pi.sub_def]
            using (hs.mul hz₀).add (hc.mul (hz 2))

theorem hasDerivAt_complexLorentzParameterAction_zero (j : Fin 6)
    (z : ComplexSpacetime) :
    HasDerivAt (fun s : ℝ => complexLorentzParameterAction j s z)
      (lorentzParameterGenerator j z) 0 := by
  have hc : HasDerivAt (fun s : ℝ => (Real.cosh s : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cosh 0).ofReal_comp
  have hs : HasDerivAt (fun s : ℝ => (Real.sinh s : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_sinh 0).ofReal_comp
  have hco : HasDerivAt (fun s : ℝ => (Real.cos s : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).ofReal_comp
  have hsi : HasDerivAt (fun s : ℝ => (Real.sin s : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).ofReal_comp
  have hb (x y : ℂ) : HasDerivAt
      (fun s : ℝ => (Real.cosh s : ℂ) * x + (Real.sinh s : ℂ) * y) y 0 := by
    simpa only [Pi.add_def, zero_mul, one_mul, zero_add, add_zero]
      using (hc.mul_const x).add (hs.mul_const y)
  have hb' (x y : ℂ) : HasDerivAt
      (fun s : ℝ => (Real.sinh s : ℂ) * x + (Real.cosh s : ℂ) * y) x 0 := by
    simpa only [Pi.add_def, zero_mul, one_mul, zero_add, add_zero]
      using (hs.mul_const x).add (hc.mul_const y)
  have hr (x y : ℂ) : HasDerivAt
      (fun s : ℝ => (Real.cos s : ℂ) * x - (Real.sin s : ℂ) * y) (-y) 0 := by
    simpa only [Pi.sub_def, zero_mul, one_mul, zero_sub]
      using (hco.mul_const x).sub (hsi.mul_const y)
  have hr' (x y : ℂ) : HasDerivAt
      (fun s : ℝ => (Real.sin s : ℂ) * x + (Real.cos s : ℂ) * y) x 0 := by
    simpa only [Pi.add_def, zero_mul, one_mul, zero_add, add_zero]
      using (hsi.mul_const x).add (hco.mul_const y)
  fin_cases j <;> apply HasDerivAt.prodMk
  all_goals
    first
    | exact hb _ _
    | exact hasDerivAt_const 0 _
    | (apply hasDerivAt_pi.mpr; intro i; fin_cases i <;>
        first | exact hb' _ _ | exact hr _ _ | exact hr' _ _ |
          exact hasDerivAt_const 0 _)

end VacuumBellSeparation
