/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CoefficientFamily

/-!
# SubConstFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The triadic coefficient family of `a_L − C` at a constant skew matrix `C`

ABK26, Section 4.1 abbreviates,

```
  ã_{L,m}  :=  a_L − (k_L − k_m)_{□_m}
```

and then reads the response functional `J(z+□_n, …; ã_{L,m})` at *every* cube
`z + □_n` of the scale-`n` lattice.  The subtracted matrix is a **constant**:
the average is taken over the fixed cube `□_m`, not over the moving cube `z +
□_n`.  Consequently `ã_{L,m}` is a single coefficient field on all of space,
and it carries a genuine Chapter 2 *triadic coefficient family* — one
coefficient object per cube, all with the same representative.

This is what `Support.fluxCorrectedCoeffOn` is not: there the average is taken
over the very cube that carries the object, so the field moves with the cube and
no family exists.  The two constructions share their ellipticity mechanism, and
this module re-derives it at a free constant.

## The ellipticity mechanism

`a_L = ν Id + k_L` with `k_L` antisymmetric, so `symmPart a_L = ν Id`
(`Cutoff.symmPart_coefficientCutoff`).  Subtracting an antisymmetric constant
`C` does not move the symmetric part, so `symmPart (a_L − C) = ν Id` still, and
the *lower* ellipticity constant is still the molecular diffusivity `ν`.  The
upper constant comes from the entry envelope
`Cutoff.coefficientCutoffCubeEntryBound M L ω Q + matAbsSum C`, fed to the
public certificate `Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound`.

Both helpers of the two existing instances of this mechanism
(`Cutoff.coefficientCutoffCoeffOn`, `Support.fluxCorrectedCoeffOn`) are
`private` in their own files, so they are re-derived here rather than reused;
the de-privatisation is a queued cleanup item elsewhere and is deliberately not
performed by this module, which edits no existing file.

## What is proved

* `subConstCutoffField` — the field `a_L − C` on all of space, and its
  symmetric part.
* `subConstCutoffCoeffOn` — its Chapter 2 coefficient object on one triadic
  cube, at the lower constant `ν`.
* `subConstCutoffTriadicCoeffFamily` — the triadic family.  Compatibility is
  reflexivity, exactly as for `Cutoff.coefficientCutoffTriadicCoeffFamily`,
  because every cube receives the same representative.

## References

* ABK26, (`ã_{L,m} := a_L − (k_L − k_m)_{□_m}`), (the "differ by a constant
  anti-symmetric matrix" observation).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## The `ℓ¹` entry mass of a constant matrix -/

/-- The `ℓ¹` entry mass of a matrix.  It dominates every entry, and is the only
new ingredient the ellipticity of `a_L − C` needs. -/
noncomputable def matAbsSum (C : Mat d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, |C i j|

theorem abs_le_matAbsSum (C : Mat d) (i j : Fin d) : |C i j| ≤ matAbsSum C := by
  have hinner : |C i j| ≤ ∑ j' : Fin d, |C i j'| :=
    Finset.single_le_sum (f := fun j' : Fin d => |C i j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  have houter : (∑ j' : Fin d, |C i j'|) ≤ matAbsSum C :=
    Finset.single_le_sum
      (f := fun i' : Fin d => ∑ j' : Fin d, |C i' j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i)
  exact hinner.trans houter

/-! ## The field `a_L − C` -/

/-- The manuscript's `ã_{L,m} = a_L − (k_L − k_m)_{□_m}`, written at a free
constant `C`: a single coefficient field on all of space. -/
noncomputable def subConstCutoffField (M : ABKModel d) (L : ℤ) (C : Mat d)
    (omega : Cutoff.CutoffSample d) : CoeffField d :=
  fun x => Cutoff.coefficientCutoff M.nu L omega x - C

@[simp]
theorem subConstCutoffField_apply (M : ABKModel d) (L : ℤ) (C : Mat d)
    (omega : Cutoff.CutoffSample d) (x : Vec d) :
    subConstCutoffField M L C omega x =
      Cutoff.coefficientCutoff M.nu L omega x - C :=
  rfl

/-- Subtracting an antisymmetric constant does not move the symmetric part: it
is still exactly `ν Id`.  This is the whole content of the ellipticity of
`ã_{L,m}`. -/
theorem symmPart_subConstCutoffField (M : ABKModel d) (L : ℤ) (C : Mat d)
    (hC : matTranspose C = -C) (omega : Cutoff.CutoffSample d) (x : Vec d) :
    symmPart (subConstCutoffField M L C omega x) = M.nu • (1 : Mat d) := by
  ext i j
  have hA := congrFun (congrFun
    (Cutoff.symmPart_coefficientCutoff M.nu L omega x) i) j
  have hCji : C j i = -C i j := by
    simpa only [Matrix.transpose_apply, Matrix.neg_apply]
      using! congrFun (congrFun hC i) j
  simp only [symmPart, subConstCutoffField, Matrix.sub_apply] at hA ⊢
  linarith only [hA, hCji]

/-! ## The ellipticity constants on one cube -/

/-- The uniform entry envelope of `a_L − C` on `Q`. -/
noncomputable def subConstCutoffEntryBound (M : ABKModel d) (L : ℤ) (C : Mat d)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) : ℝ :=
  Cutoff.coefficientCutoffCubeEntryBound M L omega Q + matAbsSum C

/-- The upper ellipticity constant of `a_L − C` on `Q`, produced by the proved
skew-plus-entry-bound certificate. -/
noncomputable def subConstCutoffEllipticityUpper (M : ABKModel d) (L : ℤ)
    (C : Mat d) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) : ℝ :=
  ((d : ℝ) * (d : ℝ) * (subConstCutoffEntryBound M L C omega Q) ^ 2 + M.nu ^ 2) /
    M.nu

theorem abs_subConstCutoffField_entry_le (M : ABKModel d) (L : ℤ) (C : Mat d)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) (i j : Fin d) :
    |subConstCutoffField M L C omega x i j| ≤
      subConstCutoffEntryBound M L C omega Q := by
  have h1 := Cutoff.abs_coefficientCutoff_entry_le_cubeEntryBound M L omega Q hx i j
  have h2 := abs_le_matAbsSum C i j
  calc
    |subConstCutoffField M L C omega x i j| =
        |Cutoff.coefficientCutoff M.nu L omega x i j - C i j| := rfl
    _ ≤ |Cutoff.coefficientCutoff M.nu L omega x i j| + |C i j| := abs_sub _ _
    _ ≤ subConstCutoffEntryBound M L C omega Q := add_le_add h1 h2

theorem isEllipticMatrix_subConstCutoffField (M : ABKModel d) (L : ℤ) (C : Mat d)
    (hC : matTranspose C = -C) (omega : Cutoff.CutoffSample d) (Q : TriadicCube d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    IsEllipticMatrix M.nu (subConstCutoffEllipticityUpper M L C omega Q)
      (subConstCutoffField M L C omega x) :=
  Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
    (symmPart_subConstCutoffField M L C hC omega x)
    (fun i j => abs_subConstCutoffField_entry_le M L C omega Q hx i j)

theorem cubeCenter_mem_openCubeSet (Q : TriadicCube d) :
    cubeCenter Q ∈ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.mem_ball_self (cubeRadius_pos Q)

/-! ## The coefficient object and the triadic family -/

/-- The Chapter 2 coefficient object of `ã_{L,m} = a_L − C` on the cube `Q`.
The lower ellipticity constant is still the molecular diffusivity `ν`, because
the subtracted matrix is antisymmetric. -/
noncomputable def subConstCutoffCoeffOn (M : ABKModel d) (L : ℤ) (C : Mat d)
    (hC : matTranspose C = -C) (omega : Cutoff.CutoffSample d)
    (Q : TriadicCube d) : CoeffOn (cubeDomain Q) where
  toCoeffField := subConstCutoffField M L C omega
  lam := M.nu
  Lam := subConstCutoffEllipticityUpper M L C omega Q
  lam_pos := M.nu_pos
  lam_le_Lam :=
    (isEllipticMatrix_subConstCutoffField M L C hC omega Q
      (cubeCenter_mem_openCubeSet Q)).2.1
  aeStronglyMeasurable := by
    classical
    intro i j
    have hmeas : Measurable (fun x : Vec d =>
        restrictCoeffField (openCubeSet Q) (subConstCutoffField M L C omega) x i j) := by
      have hEq : (fun x : Vec d =>
          restrictCoeffField (openCubeSet Q) (subConstCutoffField M L C omega) x i j) =
          fun x => if x ∈ openCubeSet Q then
            subConstCutoffField M L C omega x i j else 0 := by
        funext x
        by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
      rw [hEq]
      exact (((Cutoff.coefficientCutoff M.nu L omega).entry_measurable i j).sub
        measurable_const).ite (measurableSet_openCubeSet Q) measurable_const
    exact hmeas.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact isEllipticMatrix_subConstCutoffField M L C hC omega Q hx

@[simp]
theorem subConstCutoffCoeffOn_toCoeffField (M : ABKModel d) (L : ℤ) (C : Mat d)
    (hC : matTranspose C = -C) (omega : Cutoff.CutoffSample d)
    (Q : TriadicCube d) :
    (subConstCutoffCoeffOn M L C hC omega Q).toCoeffField =
      subConstCutoffField M L C omega :=
  rfl

/-- **The triadic coefficient family of `ã_{L,m}`.**  Every cube receives the
same literal representative `a_L − C`; only the locally derived upper
ellipticity witness changes with the cube, so compatibility is reflexivity. -/
noncomputable def subConstCutoffTriadicCoeffFamily (M : ABKModel d) (L : ℤ)
    (C : Mat d) (hC : matTranspose C = -C) (omega : Cutoff.CutoffSample d) :
    TriadicCoeffFamily d where
  coeffOn := subConstCutoffCoeffOn M L C hC omega
  restrictsTo_of_subset := by
    intro Q R _
    exact Filter.EventuallyEq.rfl

@[simp]
theorem subConstCutoffTriadicCoeffFamily_coeffOn_toCoeffField (M : ABKModel d)
    (L : ℤ) (C : Mat d) (hC : matTranspose C = -C)
    (omega : Cutoff.CutoffSample d) (Q : TriadicCube d) :
    ((subConstCutoffTriadicCoeffFamily M L C hC omega).coeffOn Q).toCoeffField =
      subConstCutoffField M L C omega :=
  rfl

end

end Algsuperdiff.Section4.Provider.Annular
