/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.ColourSeparation

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeCellSeparation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Colour separation of the standard aligned cubes

The concentration-for-sums condition supplied by unit range of dependence is a
statement about a family of observables indexed by the standard aligned cubes
`z + □_n`, `z ∈ 3^n ℤ^d ∩ □_m`, of `e.coarse.ellipticity`.  Neighbouring
cubes of that family touch, so unit range does not apply to the family as a
whole.  It applies after a triadic colouring: two distinct cubes of the same
scale whose indices agree modulo three are separated in `ℓ^∞`-distance by more
than one, so the local sigma-fields they carry are independent.

This file records that geometry for the standard cubes, in the two forms the
concentration argument consumes: measurability of the cubes, and pairwise unit
separation of a same-colour family.  The colour classes need no new carrier: the
residue map `w ↦ (w i mod 3)_i` takes values in `(ZMod 3)^d`, and the partition
of a finite index family into its colour classes is the one already used by the
finite-range averaging estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The standard aligned cubes are measurable -/

/-- A standard aligned cube is a measurable subset of `ℝ^d`. -/
theorem measurableSet_standardCell (d : ℕ) (k : ℤ) (w : Fin d → ℤ) :
    MeasurableSet (standardCell d k w) :=
  (isOpenBoundedConvexDomain_openCubeSet
    (translateCube w (originCube d k))).isOpen.measurableSet

/-! ## Same-colour cubes are unit separated -/

/-- **Two standard aligned cubes at a nonnegative scale whose indices differ by
a nonzero multiple of three in some coordinate are `ℓ^∞`-separated by at least
one.**  In fact they are separated by at least two; the unit-range assumption
asks only for one. -/
theorem unitSeparated_standardCell_of_dvd_sub {k : ℤ} (hk : 0 ≤ k)
    {w w' : Fin d → ℤ} {i₀ : Fin d} (hne : w i₀ ≠ w' i₀)
    (hdvd : (3 : ℤ) ∣ (w i₀ - w' i₀)) :
    UnitSeparated (standardCell d k w) (standardCell d k w') := by
  have hstep : (3 : ℤ) ≤ |w i₀ - w' i₀| :=
    Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs 3 _).mpr hdvd)
  have h3k : (1 : ℝ) ≤ (3 : ℝ) ^ k := by
    calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℤ) := by norm_num
      _ ≤ (3 : ℝ) ^ k := zpow_le_zpow_right₀ (by norm_num) hk
  intro x y hx hy
  rw [Recurrence.mem_standardCell_iff] at hx hy
  obtain ⟨hx1, hx2⟩ := hx i₀
  obtain ⟨hy1, hy2⟩ := hy i₀
  set T : ℝ := (3 : ℝ) ^ k with hTdef
  clear_value T
  have hcoord : (1 : ℝ) ≤ |x i₀ - y i₀| := by
    rcases abs_cases (w i₀ - w' i₀) with ⟨habs, _⟩ | ⟨habs, _⟩
    · have hZ : (3 : ℤ) ≤ w i₀ - w' i₀ := by omega
      have hR : (3 : ℝ) ≤ (w i₀ : ℝ) - (w' i₀ : ℝ) := by exact_mod_cast hZ
      have hgap : (1 : ℝ) ≤ x i₀ - y i₀ := by nlinarith only [hx1, hy2, hR, h3k]
      exact le_trans hgap (le_abs_self _)
    · have hZ : w i₀ - w' i₀ ≤ -3 := by omega
      have hR : (w i₀ : ℝ) - (w' i₀ : ℝ) ≤ -3 := by exact_mod_cast hZ
      have hgap : x i₀ - y i₀ ≤ -1 := by nlinarith only [hx2, hy1, hR, h3k]
      exact le_trans (by linarith only [hgap]) (neg_le_abs _)
  have hsup : Source.AKL.supDist x y = ‖x - y‖ := rfl
  have hpi : ‖(x - y) i₀‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) i₀
  rw [hsup]
  have hval : ‖(x - y) i₀‖ = |x i₀ - y i₀| := by
    simp [Real.norm_eq_abs]
  rw [hval] at hpi
  linarith only [hcoord, hpi]

/-- **Two distinct standard aligned cubes of the same colour are
`ℓ^∞`-separated by at least one.**  The colour of a cube is the residue of its
index modulo three. -/
theorem unitSeparated_standardCell_of_intCast_eq {k : ℤ} (hk : 0 ≤ k)
    {w w' : Fin d → ℤ} (hne : w ≠ w')
    (hcol : (fun i => ((w i : ZMod 3))) = fun i => ((w' i : ZMod 3))) :
    UnitSeparated (standardCell d k w) (standardCell d k w') := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  refine unitSeparated_standardCell_of_dvd_sub hk hi₀ ?_
  have hres : ((w i₀ : ZMod 3)) = ((w' i₀ : ZMod 3)) := congrFun hcol i₀
  have hmod := (ZMod.intCast_eq_intCast_iff' (w i₀) (w' i₀) 3).mp hres
  omega

end

end Quenched
end HighContrast
end HCPolySupport
