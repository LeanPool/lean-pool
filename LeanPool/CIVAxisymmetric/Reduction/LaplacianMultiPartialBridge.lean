/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Reduction.AxisDeriv

/-!
# Bridge from `spatialPartial`/`spatialSecondPartial` to `multiPartial`

These lemmas translate the momentum equation (`eq:nse:forced`) from the
`spatialPartial`/`spatialSecondPartial`/`timePartial` operators used in the
classical formulation into the `multiPartial` language of `AnalyticBoundOn`,
`eq:analytic:interior:force` — the shape the real-analytic estimates behind
`thm:analytic:interior` (Kahane 1969) need to state the induction on derivative order.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



theorem spatialPartial_eq_multiPartial_single (g : ParabolicPoint → ℝ) (i : Fin 3) (x : Vec3)
    (t : ℝ) :
    spatialPartial g i (x, t) = multiPartial g (Pi.single i 1) (x, t) := by
  set G : Vec3 → ℝ := fun y => g (y, t)
  have h_spatial : spatialPartial g i (x, t) = axisDeriv i G x := by
    have h_iter := slice_spatialPartial_iterate g i 1 t
    rw [Function.iterate_one] at h_iter
    exact congr_fun h_iter x
  have h_multi : multiPartial g (Pi.single i 1) (x, t) = axisDeriv i G x := by
    have h_slice := multiPartial_slice g (Pi.single i 1) t
    have h_eq := congr_fun h_slice x
    fin_cases i <;> simpa [G] using h_eq
  rw [h_multi, h_spatial]

theorem spatialSecondPartial_eq_multiPartial_single (g : ParabolicPoint → ℝ) (j : Fin 3) (x : Vec3)
    (t : ℝ) :
    spatialSecondPartial g j j (x, t) = multiPartial g (Pi.single j 2) (x, t) := by
  set G : Vec3 → ℝ := fun y => g (y, t)
  unfold spatialSecondPartial
  have h_outer : spatialPartial (fun w => spatialPartial g j w) j (x, t) =
      axisDeriv j (fun y => spatialPartial g j (y, t)) x := by
    have h_iter := slice_spatialPartial_iterate (fun w => spatialPartial g j w) j 1 t
    rw [Function.iterate_one] at h_iter
    exact congr_fun h_iter x
  have h_inner : (fun y : Vec3 => spatialPartial g j (y, t)) = axisDeriv j G := by
    have h_iter := slice_spatialPartial_iterate g j 1 t
    rw [Function.iterate_one] at h_iter
    exact h_iter
  have h_multi : multiPartial g (Pi.single j 2) (x, t) = axisDeriv j (axisDeriv j G) x := by
    have h_slice := multiPartial_slice g (Pi.single j 2) t
    have h_eq := congr_fun h_slice x
    fin_cases j <;> simpa [G] using h_eq
  rw [h_outer, h_inner, h_multi]

theorem sum_spatialSecondPartial_eq_sum_multiPartial (g : ParabolicPoint → ℝ) (x : Vec3) (t : ℝ) :
    ∑ j : Fin 3, spatialSecondPartial g j j (x, t) =
      ∑ j : Fin 3, multiPartial g (Pi.single j 2) (x, t) := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact spatialSecondPartial_eq_multiPartial_single g j x t

theorem laplacian_eq_of_isClassicalSolutionOn {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {S : Set ParabolicPoint} (hsol : IsClassicalSolutionOn u p f S)
    (x : Vec3) (t : ℝ) (hz : (x, t) ∈ S) (i : Fin 3) :
    ∑ j : Fin 3, multiPartial (fun w => u w i) (Pi.single j 2) (x, t) =
      timePartial (fun w => u w i) (x, t) +
        ∑ j : Fin 3, u (x, t) j * multiPartial (fun w => u w i) (Pi.single j 1) (x, t) +
          multiPartial p (Pi.single i 1) (x, t) - f (x, t) i := by
  have hmom := hsol.2.2.2.1 (x, t) hz i
  have h_laplacian : ∑ j : Fin 3, spatialSecondPartial (fun w => u w i) j j (x, t) =
      ∑ j : Fin 3, multiPartial (fun w => u w i) (Pi.single j 2) (x, t) :=
    sum_spatialSecondPartial_eq_sum_multiPartial (fun w => u w i) x t
  have h_spatial (j : Fin 3) : spatialPartial (fun w => u w i) j (x, t) =
      multiPartial (fun w => u w i) (Pi.single j 1) (x, t) :=
    spatialPartial_eq_multiPartial_single (fun w => u w i) j x t
  have h_pressure : spatialPartial p i (x, t) = multiPartial p (Pi.single i 1) (x, t) :=
    spatialPartial_eq_multiPartial_single p i x t
  have h_sum_spatial : (∑ j : Fin 3, u (x, t) j * spatialPartial (fun w => u w i) j (x, t)) =
      (∑ j : Fin 3, u (x, t) j * multiPartial (fun w => u w i) (Pi.single j 1) (x, t)) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h_spatial j]
  rw [h_laplacian, h_pressure, h_sum_spatial] at hmom
  linarith only [hmom]

end CIV
