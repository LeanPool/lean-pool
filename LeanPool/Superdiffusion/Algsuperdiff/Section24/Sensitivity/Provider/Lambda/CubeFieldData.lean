/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Lambda.WitnessBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.VectorMemLp
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge.BesovCongr
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.UnitCubeWeakIBP
public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz.UnitCube
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.BasicLemmas

/-!
# CubeFieldData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The frozen perturbation restricted to a sub-cube

The `p = 0` descendant-cube `D_h` bound applies the splitting identity, the weak
integration by parts and the Besov product estimate on a *sub-cube* `R` of the
frozen unit-cube carrier.  Every analytic datum needed there is the restriction
of a datum of the frozen `UnitCubeSkewW2Infinity` structure:

* the weak first-derivative data `unitCubeDerivData h` is a single global
  function of `x`; its `L^∞` memberships restrict by measure monotonicity and
  its weak-derivative property restricts by `HasWeakPartialDerivOn.restrict`;
* the entrywise Lipschitz representatives supplied by
  `Provider.DhBound.Lipschitz.UnitCube` are *globally* Lipschitz functions on
  `Vec d`, so the Lipschitz hypothesis of the Besov product estimate holds on
  every sub-cube verbatim;
* the frozen `L^∞` bound `gradientW1Infinity` is an a.e. bound on the whole
  carrier, hence on every sub-cube.

Every declaration is an internal helper for the Section 2.4 sensitivity
providers.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Lambda

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
open Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Lipschitz
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Restriction of the frozen weak-derivative data -/

/-- The `L^∞` memberships of the frozen first derivative restrict to any
sub-carrier. -/
theorem memLp_firstDeriv_restrict (h : UnitCubeSkewW2Infinity d)
    {V : Set (Vec d)}
    (hsub : V ⊆ ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (k i j : Fin d) :
    MemLp (fun x => unitCubeDerivData h k x i j) ∞ (volumeMeasureOn V) :=
  (h.firstDeriv_memLp k i j).mono_measure
    (MeasureTheory.Measure.restrict_mono hsub le_rfl)

/-- The frozen weak-derivative identity restricts to any open sub-carrier. -/
theorem hasWeakPartialDeriv_value_restrict (h : UnitCubeSkewW2Infinity d)
    {V : Set (Vec d)} (hV : IsOpen V)
    (hsub : V ⊆ ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (k i j : Fin d) :
    HasWeakPartialDerivOn V k
      (fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j)
      (fun x => unitCubeDerivData h k x i j) :=
  (h.hasWeakPartialDeriv_value k i j).restrict hV hsub

/-! ## Globally Lipschitz representatives of the first derivative -/

/-- The entrywise globally Lipschitz representative of the frozen
first-derivative field. -/
def fluxDerivRep (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) : Vec d → ℝ :=
  (exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv h k i j).choose

theorem fluxDerivRep_lipschitz (h : UnitCubeSkewW2Infinity d) (k i j : Fin d)
    (x y : Vec d) :
    |fluxDerivRep h k i j x - fluxDerivRep h k i j y| ≤
      (d : ℝ) * h.gradientW1Infinity * ‖x - y‖ := by
  simpa [Real.norm_eq_abs] using!
    (exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv h k i j).choose_spec.1 x y

theorem fluxDerivRep_ae_eq (h : UnitCubeSkewW2Infinity d) (k i j : Fin d) :
    (fun x => fluxDerivRep h k i j x)
      =ᵐ[volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))]
      fun x => unitCubeDerivData h k x i j :=
  (exists_lipschitz_ae_eq_unitCubeSkewW2Infinity_firstDeriv h k i j).choose_spec.2

/-- The globally Lipschitz representative of the weak divergence `∇·h`. -/
def fluxDivRep (h : UnitCubeSkewW2Infinity d) : Vec d → Vec d :=
  fun x j => ∑ i : Fin d, fluxDerivRep h i i j x

theorem matWeakDiv_unitCubeDerivData_apply' (h : UnitCubeSkewW2Infinity d)
    (x : Vec d) (j : Fin d) :
    matWeakDiv (unitCubeDerivData h) x j =
      ∑ i : Fin d, unitCubeDerivData h i x i j := rfl

theorem fluxDivRep_lipschitz (h : UnitCubeSkewW2Infinity d) (x y : Vec d) :
    ‖fluxDivRep h x - fluxDivRep h y‖ ≤
      ((d : ℝ) ^ 2 * h.gradientW1Infinity) * ‖x - y‖ := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hB : 0 ≤ ((d : ℝ) ^ 2 * h.gradientW1Infinity) * ‖x - y‖ := by positivity
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  calc ‖(fluxDivRep h x - fluxDivRep h y) j‖
      = |∑ i : Fin d, (fluxDerivRep h i i j x - fluxDerivRep h i i j y)| := by
        rw [Real.norm_eq_abs]
        congr 1
        show (∑ i : Fin d, fluxDerivRep h i i j x) -
            ∑ i : Fin d, fluxDerivRep h i i j y =
          ∑ i : Fin d, (fluxDerivRep h i i j x - fluxDerivRep h i i j y)
        rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin d, |fluxDerivRep h i i j x - fluxDerivRep h i i j y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (d : ℝ) * h.gradientW1Infinity * ‖x - y‖ :=
        Finset.sum_le_sum fun i _ => fluxDerivRep_lipschitz h i i j x y
    _ = ((d : ℝ) ^ 2 * h.gradientW1Infinity) * ‖x - y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## Transfer to a sub-cube -/

variable {R : TriadicCube d}

/-- The Lipschitz representative of `∇·h` agrees a.e. with the weak divergence
on every sub-cube of the frozen carrier. -/
theorem fluxDivRep_ae_eq_cube (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    fluxDivRep h =ᵐ[normalizedCubeMeasure R] matWeakDiv (unitCubeDerivData h) := by
  classical
  have hall : ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain R : Domain d) : Set (Vec d)),
      ∀ k i j : Fin d, fluxDerivRep h k i j x = unitCubeDerivData h k x i j := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact ae_restrict_of_ae_restrict_of_subset hsub (fluxDerivRep_ae_eq h k i j)
  refine ae_cubeDomain_iff_normalizedCubeMeasure R ?_
  filter_upwards [hall] with x hx
  funext j
  show (∑ i : Fin d, fluxDerivRep h i i j x) =
    ∑ i : Fin d, unitCubeDerivData h i x i j
  exact Finset.sum_congr rfl fun i _ => hx i i j

/-! ## `L^∞` bounds on a sub-cube -/

theorem toReal_eLpNorm_matrixDerivativeNorm_le_grad (h : UnitCubeSkewW2Infinity d) :
    ENNReal.toReal
        (eLpNorm (fun x => matrixDerivativeNorm (h.firstDeriv x)) ∞
          (volumeMeasureOn
            ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))) ≤
      h.gradientW1Infinity := by
  unfold UnitCubeSkewW2Infinity.gradientW1Infinity
  exact le_max_right _ _

theorem ae_abs_unitCubeDerivData_le_grad (h : UnitCubeSkewW2Infinity d)
    (k i j : Fin d) :
    ∀ᵐ x ∂ volumeMeasureOn
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)),
      |unitCubeDerivData h k x i j| ≤ h.gradientW1Infinity := by
  filter_upwards [ae_abs_apply_le_toReal_eLpNorm_matrixDerivativeNorm
    (D := h.firstDeriv) (fun k' i' j' => h.firstDeriv_memLp k' i' j') k i j] with x hx
  exact hx.trans (toReal_eLpNorm_matrixDerivativeNorm_le_grad h)

theorem ae_norm_matWeakDiv_le_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    ∀ᵐ x ∂ normalizedCubeMeasure R,
      ‖matWeakDiv (unitCubeDerivData h) x‖ ≤ (d : ℝ) * h.gradientW1Infinity := by
  classical
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  have hall : ∀ᵐ x ∂ volumeMeasureOn ((cubeDomain R : Domain d) : Set (Vec d)),
      ∀ k i j : Fin d, |unitCubeDerivData h k x i j| ≤ h.gradientW1Infinity := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact ae_restrict_of_ae_restrict_of_subset hsub
      (ae_abs_unitCubeDerivData_le_grad h k i j)
  refine ae_normalizedCubeMeasure_of_ae_cubeDomain R ?_
  filter_upwards [hall] with x hx
  have hB : (0 : ℝ) ≤ (d : ℝ) * h.gradientW1Infinity := by positivity
  rw [pi_norm_le_iff_of_nonneg hB]
  intro j
  rw [Real.norm_eq_abs, matWeakDiv_unitCubeDerivData_apply']
  calc |∑ i : Fin d, unitCubeDerivData h i x i j|
      ≤ ∑ i : Fin d, |unitCubeDerivData h i x i j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, h.gradientW1Infinity :=
        Finset.sum_le_sum fun i _ => hx i i j
    _ = (d : ℝ) * h.gradientW1Infinity := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem cubeLpNorm_infty_matWeakDiv_le_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    cubeLpNorm R ∞ (matWeakDiv (unitCubeDerivData h)) ≤
      (d : ℝ) * h.gradientW1Infinity := by
  have hg : 0 ≤ h.gradientW1Infinity := gradientW1Infinity_nonneg h
  exact cubeLpNorm_infty_le_of_ae_bound R _ (by positivity)
    (ae_norm_matWeakDiv_le_cube h R hsub)

theorem cubeLpNorm_infty_fluxDivRep_le_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    cubeLpNorm R ∞ (fluxDivRep h) ≤ (d : ℝ) * h.gradientW1Infinity := by
  rw [cubeLpNorm_congr_ae R ∞ (fluxDivRep_ae_eq_cube h R hsub)]
  exact cubeLpNorm_infty_matWeakDiv_le_cube h R hsub

/-! ## `L^∞` memberships on a sub-cube -/

theorem memLp_unitCubeDerivData_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (k i j : Fin d) (r : ℝ≥0∞) :
    MemLp (fun x => unitCubeDerivData h k x i j) r (normalizedCubeMeasure R) :=
  (memLp_normalizedCubeMeasure_of_memLp_cubeDomain (r := ∞) R
    (memLp_firstDeriv_restrict h hsub k i j)).mono_exponent le_top

theorem memLp_matWeakDiv_cube (h : UnitCubeSkewW2Infinity d) (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
    (r : ℝ≥0∞) :
    MemLp (matWeakDiv (unitCubeDerivData h)) r (normalizedCubeMeasure R) := by
  classical
  refine memLp_vec_of_components fun j => ?_
  have : MemLp (fun x => ∑ i : Fin d, unitCubeDerivData h i x i j) r
      (normalizedCubeMeasure R) :=
    memLp_finsetSum (s := Finset.univ)
      (f := fun i => fun x => unitCubeDerivData h i x i j)
      fun i _ => memLp_unitCubeDerivData_cube h R hsub i i j r
  simpa [matWeakDiv_unitCubeDerivData_apply'] using this

theorem memLp_fluxDivRep_top_cube (h : UnitCubeSkewW2Infinity d)
    (R : TriadicCube d)
    (hsub : ((cubeDomain R : Domain d) : Set (Vec d)) ⊆
      ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :
    MemLp (fluxDivRep h) ∞ (normalizedCubeMeasure R) :=
  (memLp_matWeakDiv_cube h R hsub ∞).ae_eq (fluxDivRep_ae_eq_cube h R hsub).symm

end

end Algsuperdiff.Section24.Sensitivity.Provider.Lambda
