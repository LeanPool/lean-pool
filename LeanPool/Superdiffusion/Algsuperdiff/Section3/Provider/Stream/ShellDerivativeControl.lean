/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Scaling

/-!
# ShellDerivativeControl

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Derivative-level local cube controls for shell fields

`Algsuperdiff.Section3.Cutoff.localCubeControl` measures the exact value
supremum `‖j‖_{L∞(cu_ell)}` of a shell field on the open origin cube of scale
`ell`.  ABK26's stream estimates additionally need the two derivative
suprema `‖∇j‖_{L∞(cu_ell)}` and `‖∇²j‖_{L∞(cu_ell)}`.  This module supplies
them in exactly the norms fixed by the frozen J2 observable
(`ShellField.unitCubeDerivNorm` and `ShellField.unitCubeSecondDerivNorm`),
together with their sharp characterizations, monotonicity in the cube scale,
and the exact triadic scaling identities.

The two gauges are *raw* suprema: `localCubeDerivNorm ell j` is literally
`‖∇j‖_{L∞(cu_ell)}` and `localCubeSecondDerivNorm ell j` is literally
`‖∇²j‖_{L∞(cu_ell)}`, with no scale normalization folded in.  The chain-rule
factors of the frozen `spatialScale` action are divided out explicitly in the
definitions.  Consequently the amplitudes in the triadic scaling identities
are the manuscript's `3^{(γ-1)k}` and `3^{(γ-2)k}` rather than `3^{γk}`.

Note that `cubeScaleFactor (originCube d ell)` is by definition `(3 : ℝ) ^ ell`,
so the definitions below use exactly the cube-scale convention of
`Algsuperdiff.Section3.Cutoff.localCubeControl`.

## Main definitions

* `localCubeDerivNorm`: `‖∇j‖_{L∞(cu_ell)}`.
* `localCubeSecondDerivNorm`: `‖∇²j‖_{L∞(cu_ell)}`.

## Main results

* `matrixDerivativeNorm_deriv_le_localCubeDerivNorm`,
  `localCubeDerivNorm_le_of_forall` and their second-derivative analogues:
  each gauge is the least nonnegative pointwise bound on its open cube.
* `localCubeDerivNorm_triadicScale`, `localCubeSecondDerivNorm_triadicScale`:
  the exact scaling identities, mirroring
  `Algsuperdiff.Section3.Cutoff.localCubeControl_triadicScale`.

## References

* ABK26, `e.jk.O`, `e.nabla.jk.O`.
* ABK26, `e.kn.reg.ass.with.gamma`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Set
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Exact positive homogeneity of the J2 matrix norms -/

private theorem matrixOperatorNorm_smul (c : ℝ) (A : Mat d) :
    matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A := by
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • A)‖ =
    |c| * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- Sharp characterization of the exact induced first-derivative norm: it is
the least nonnegative bound on the Euclidean unit ball. -/
theorem matrixDerivativeNorm_le_iff (D : ShellField.MatrixDerivative d) (C : ℝ) :
    ShellField.matrixDerivativeNorm D ≤ C ↔
      0 ≤ C ∧ ∀ v : Vec d, vecNorm v ≤ 1 → matrixOperatorNorm (D v) ≤ C := by
  constructor
  · intro h
    refine ⟨(ShellField.matrixDerivativeNorm_nonneg D).trans h, ?_⟩
    intro v hv
    exact (ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D v hv).trans h
  · rintro ⟨hC, h⟩
    change sSup (Set.range fun o : Option {v : Vec d // vecNorm v ≤ 1} =>
      match o with
      | none => (0 : ℝ)
      | some v => matrixOperatorNorm (D v.1)) ≤ C
    refine csSup_le (Set.range_nonempty _) ?_
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact hC
    | some v => exact h v.1 v.2

/-- The exact induced first-derivative norm is positively homogeneous. -/
theorem matrixDerivativeNorm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c)
    (D : ShellField.MatrixDerivative d) :
    ShellField.matrixDerivativeNorm (c • D) =
      c * ShellField.matrixDerivativeNorm D := by
  have hpt : ∀ v : Vec d,
      matrixOperatorNorm ((c • D) v) = c * matrixOperatorNorm (D v) := by
    intro v
    change matrixOperatorNorm (c • D v) = c * matrixOperatorNorm (D v)
    rw [matrixOperatorNorm_smul, abs_of_nonneg hc]
  refine le_antisymm ?_ ?_
  · rw [matrixDerivativeNorm_le_iff]
    refine ⟨mul_nonneg hc (ShellField.matrixDerivativeNorm_nonneg D), ?_⟩
    intro v hv
    rw [hpt v]
    exact mul_le_mul_of_nonneg_left
      (ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D v hv) hc
  · rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0, zero_mul]
      exact ShellField.matrixDerivativeNorm_nonneg _
    · have hkey : ShellField.matrixDerivativeNorm D ≤
          c⁻¹ * ShellField.matrixDerivativeNorm (c • D) := by
        rw [matrixDerivativeNorm_le_iff]
        refine ⟨mul_nonneg (inv_nonneg.2 hc)
          (ShellField.matrixDerivativeNorm_nonneg _), ?_⟩
        intro v hv
        rw [le_inv_mul_iff₀ hcpos, ← hpt v]
        exact ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm (c • D) v hv
      calc
        c * ShellField.matrixDerivativeNorm D ≤
            c * (c⁻¹ * ShellField.matrixDerivativeNorm (c • D)) :=
          mul_le_mul_of_nonneg_left hkey hc
        _ = ShellField.matrixDerivativeNorm (c • D) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]

/-- The exact twice-induced second-derivative norm is positively
homogeneous. -/
theorem matrixSecondDerivativeNorm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c)
    (H : ShellField.MatrixSecondDerivative d) :
    ShellField.matrixSecondDerivativeNorm (c • H) =
      c * ShellField.matrixSecondDerivativeNorm H := by
  have hpt : ∀ u : Vec d,
      ShellField.matrixDerivativeNorm ((c • H) u) =
        c * ShellField.matrixDerivativeNorm (H u) := by
    intro u
    change ShellField.matrixDerivativeNorm (c • H u) = _
    exact matrixDerivativeNorm_smul_of_nonneg hc (H u)
  refine le_antisymm ?_ ?_
  · rw [ShellField.matrixSecondDerivativeNorm_le_iff]
    refine ⟨mul_nonneg hc (ShellField.matrixSecondDerivativeNorm_nonneg H), ?_⟩
    intro u hu
    rw [hpt u]
    exact mul_le_mul_of_nonneg_left
      (ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H u hu) hc
  · rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0, zero_mul]
      exact ShellField.matrixSecondDerivativeNorm_nonneg _
    · have hkey : ShellField.matrixSecondDerivativeNorm H ≤
          c⁻¹ * ShellField.matrixSecondDerivativeNorm (c • H) := by
        rw [ShellField.matrixSecondDerivativeNorm_le_iff]
        refine ⟨mul_nonneg (inv_nonneg.2 hc)
          (ShellField.matrixSecondDerivativeNorm_nonneg _), ?_⟩
        intro u hu
        rw [le_inv_mul_iff₀ hcpos, ← hpt u]
        exact ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm
          (c • H) u hu
      calc
        c * ShellField.matrixSecondDerivativeNorm H ≤
            c * (c⁻¹ * ShellField.matrixSecondDerivativeNorm (c • H)) :=
          mul_le_mul_of_nonneg_left hkey hc
        _ = ShellField.matrixSecondDerivativeNorm (c • H) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]

/-! ## The open-unit-cube supremum toolkit -/

private theorem unitOpenCubeSup_bddAbove {f : Vec d → ℝ} (hf : Continuous f)
    (hfn : ∀ x : Vec d, 0 ≤ f x) :
    BddAbove (Set.range fun o : Option (ShellField.UnitOpenCubePoint d) =>
      match o with
      | none => (0 : ℝ)
      | some x => f x.1) := by
  have hK : IsCompact (Metric.closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))) :=
    isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have hx : x.1 ∈ Metric.closedBall
          (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0)) := by
        apply Metric.ball_subset_closedBall
        rw [ball_cubeCenter_eq_openCubeSet]
        exact x.2
      have hfx : f x.1 ≤ C := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hfn x.1)] using hC x.1 hx
      exact hfx.trans (le_max_right _ _)

private theorem le_unitOpenCubeSup {f : Vec d → ℝ} (hf : Continuous f)
    (hfn : ∀ x : Vec d, 0 ≤ f x) (x : ShellField.UnitOpenCubePoint d) :
    f x.1 ≤ sSup (Set.range fun o : Option (ShellField.UnitOpenCubePoint d) =>
      match o with
      | none => (0 : ℝ)
      | some y => f y.1) :=
  le_csSup (unitOpenCubeSup_bddAbove hf hfn) ⟨some x, rfl⟩

private theorem unitOpenCubeSup_le {f : Vec d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : ShellField.UnitOpenCubePoint d, f x.1 ≤ C) :
    sSup (Set.range fun o : Option (ShellField.UnitOpenCubePoint d) =>
      match o with
      | none => (0 : ℝ)
      | some y => f y.1) ≤ C := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact hC
  | some x => exact h x

/-- The J2 first-derivative unit-cube norm dominates the exact induced
derivative norm at every point of the literal open unit cube. -/
theorem matrixDerivativeNorm_deriv_le_unitCubeDerivNorm (j : ShellField d)
    {y : Vec d} (hy : y ∈ openCubeSet (originCube d 0)) :
    ShellField.matrixDerivativeNorm (ShellField.deriv j y) ≤
      ShellField.unitCubeDerivNorm j := by
  change _ ≤ sSup (Set.range fun o : Option (ShellField.UnitOpenCubePoint d) =>
    match o with
    | none => (0 : ℝ)
    | some z => ShellField.matrixDerivativeNorm (ShellField.deriv j z.1))
  exact le_unitOpenCubeSup
    (ShellField.matrixDerivativeNorm_continuous.comp (ShellField.deriv j).continuous)
    (fun z => ShellField.matrixDerivativeNorm_nonneg (ShellField.deriv j z))
    ⟨y, hy⟩

/-- Sharp characterization of the J2 first-derivative unit-cube norm. -/
theorem unitCubeDerivNorm_le_iff (j : ShellField d) (C : ℝ) :
    ShellField.unitCubeDerivNorm j ≤ C ↔
      0 ≤ C ∧ ∀ y ∈ openCubeSet (originCube d 0),
        ShellField.matrixDerivativeNorm (ShellField.deriv j y) ≤ C := by
  constructor
  · intro h
    refine ⟨(ShellField.unitCubeDerivNorm_nonneg j).trans h, ?_⟩
    intro y hy
    exact (matrixDerivativeNorm_deriv_le_unitCubeDerivNorm j hy).trans h
  · rintro ⟨hC, h⟩
    change sSup (Set.range fun o : Option (ShellField.UnitOpenCubePoint d) =>
      match o with
      | none => (0 : ℝ)
      | some z => ShellField.matrixDerivativeNorm (ShellField.deriv j z.1)) ≤ C
    exact unitOpenCubeSup_le
      (f := fun y : Vec d => ShellField.matrixDerivativeNorm (ShellField.deriv j y))
      hC (fun z => h z.1 z.2)

/-- The J2 second-derivative unit-cube norm dominates the exact twice-induced
derivative norm at every point of the literal open unit cube. -/
theorem matrixSecondDerivativeNorm_secondDeriv_le_unitCubeSecondDerivNorm
    (j : ShellField d) {y : Vec d} (hy : y ∈ openCubeSet (originCube d 0)) :
    ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j y) ≤
      ShellField.unitCubeSecondDerivNorm j :=
  ((ShellField.unitCubeSecondDerivNorm_le_iff j
    (ShellField.unitCubeSecondDerivNorm j)).1 le_rfl).2 ⟨y, hy⟩

/-- Sharp characterization of the J2 second-derivative unit-cube norm, stated
on unbundled cube points. -/
theorem unitCubeSecondDerivNorm_le_iff' (j : ShellField d) (C : ℝ) :
    ShellField.unitCubeSecondDerivNorm j ≤ C ↔
      0 ≤ C ∧ ∀ y ∈ openCubeSet (originCube d 0),
        ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j y) ≤ C := by
  rw [ShellField.unitCubeSecondDerivNorm_le_iff]
  constructor
  · rintro ⟨hC, h⟩
    exact ⟨hC, fun y hy => h ⟨y, hy⟩⟩
  · rintro ⟨hC, h⟩
    exact ⟨hC, fun z => h z.1 z.2⟩

/-! ## Amplitude scaling of the unit-cube derivative norms -/

/-- Amplitude scaling acts on the J2 first-derivative unit-cube norm by the
exact factor. -/
theorem unitCubeDerivNorm_scale_of_nonneg {c : ℝ} (hc : 0 ≤ c) (j : ShellField d) :
    ShellField.unitCubeDerivNorm (ShellField.scale c j) =
      c * ShellField.unitCubeDerivNorm j := by
  have hpt : ∀ x : Vec d,
      ShellField.matrixDerivativeNorm (ShellField.deriv (ShellField.scale c j) x) =
        c * ShellField.matrixDerivativeNorm (ShellField.deriv j x) := by
    intro x
    rw [ShellField.scale_deriv]
    exact matrixDerivativeNorm_smul_of_nonneg hc _
  refine le_antisymm ?_ ?_
  · rw [unitCubeDerivNorm_le_iff]
    refine ⟨mul_nonneg hc (ShellField.unitCubeDerivNorm_nonneg j), ?_⟩
    intro y hy
    rw [hpt y]
    exact mul_le_mul_of_nonneg_left
      (matrixDerivativeNorm_deriv_le_unitCubeDerivNorm j hy) hc
  · rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0, zero_mul]
      exact ShellField.unitCubeDerivNorm_nonneg _
    · have hkey : ShellField.unitCubeDerivNorm j ≤
          c⁻¹ * ShellField.unitCubeDerivNorm (ShellField.scale c j) := by
        rw [unitCubeDerivNorm_le_iff]
        refine ⟨mul_nonneg (inv_nonneg.2 hc) (ShellField.unitCubeDerivNorm_nonneg _), ?_⟩
        intro y hy
        rw [le_inv_mul_iff₀ hcpos, ← hpt y]
        exact matrixDerivativeNorm_deriv_le_unitCubeDerivNorm (ShellField.scale c j) hy
      calc
        c * ShellField.unitCubeDerivNorm j ≤
            c * (c⁻¹ * ShellField.unitCubeDerivNorm (ShellField.scale c j)) :=
          mul_le_mul_of_nonneg_left hkey hc
        _ = ShellField.unitCubeDerivNorm (ShellField.scale c j) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]

/-- Amplitude scaling acts on the J2 second-derivative unit-cube norm by the
exact factor. -/
theorem unitCubeSecondDerivNorm_scale_of_nonneg {c : ℝ} (hc : 0 ≤ c)
    (j : ShellField d) :
    ShellField.unitCubeSecondDerivNorm (ShellField.scale c j) =
      c * ShellField.unitCubeSecondDerivNorm j := by
  have hpt : ∀ x : Vec d,
      ShellField.matrixSecondDerivativeNorm
          (ShellField.secondDeriv (ShellField.scale c j) x) =
        c * ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j x) := by
    intro x
    rw [ShellField.scale_secondDeriv]
    exact matrixSecondDerivativeNorm_smul_of_nonneg hc _
  refine le_antisymm ?_ ?_
  · rw [unitCubeSecondDerivNorm_le_iff']
    refine ⟨mul_nonneg hc (ShellField.unitCubeSecondDerivNorm_nonneg j), ?_⟩
    intro y hy
    rw [hpt y]
    exact mul_le_mul_of_nonneg_left
      (matrixSecondDerivativeNorm_secondDeriv_le_unitCubeSecondDerivNorm j hy) hc
  · rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0, zero_mul]
      exact ShellField.unitCubeSecondDerivNorm_nonneg _
    · have hkey : ShellField.unitCubeSecondDerivNorm j ≤
          c⁻¹ * ShellField.unitCubeSecondDerivNorm (ShellField.scale c j) := by
        rw [unitCubeSecondDerivNorm_le_iff']
        refine ⟨mul_nonneg (inv_nonneg.2 hc)
          (ShellField.unitCubeSecondDerivNorm_nonneg _), ?_⟩
        intro y hy
        rw [le_inv_mul_iff₀ hcpos, ← hpt y]
        exact matrixSecondDerivativeNorm_secondDeriv_le_unitCubeSecondDerivNorm
          (ShellField.scale c j) hy
      calc
        c * ShellField.unitCubeSecondDerivNorm j ≤
            c * (c⁻¹ * ShellField.unitCubeSecondDerivNorm (ShellField.scale c j)) :=
          mul_le_mul_of_nonneg_left hkey hc
        _ = ShellField.unitCubeSecondDerivNorm (ShellField.scale c j) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]

/-! ## Local cube derivative gauges -/

/-- The exact `L∞` norm of the shell's first derivative on the open origin
cube of scale `ell`: the manuscript's `‖∇j‖_{L∞(cu_ell)}`.  The chain-rule
factor of the frozen `spatialScale` action is divided out, so this is the raw
supremum with no scale normalization. -/
def localCubeDerivNorm (ell : ℤ) (j : ShellField d) : ℝ :=
  ((3 : ℝ) ^ ell)⁻¹ *
    ShellField.unitCubeDerivNorm (ShellField.spatialScale ((3 : ℝ) ^ ell) j)

/-- The exact `L∞` norm of the shell's second derivative on the open origin
cube of scale `ell`: the manuscript's `‖∇²j‖_{L∞(cu_ell)}`. -/
def localCubeSecondDerivNorm (ell : ℤ) (j : ShellField d) : ℝ :=
  (((3 : ℝ) ^ ell)⁻¹) ^ 2 *
    ShellField.unitCubeSecondDerivNorm (ShellField.spatialScale ((3 : ℝ) ^ ell) j)

private theorem three_zpow_pos (ell : ℤ) : (0 : ℝ) < (3 : ℝ) ^ ell :=
  zpow_pos (by norm_num) ell

theorem localCubeDerivNorm_nonneg (ell : ℤ) (j : ShellField d) :
    0 ≤ localCubeDerivNorm ell j :=
  mul_nonneg (inv_nonneg.2 (three_zpow_pos ell).le)
    (ShellField.unitCubeDerivNorm_nonneg _)

theorem localCubeSecondDerivNorm_nonneg (ell : ℤ) (j : ShellField d) :
    0 ≤ localCubeSecondDerivNorm ell j :=
  mul_nonneg (sq_nonneg _) (ShellField.unitCubeSecondDerivNorm_nonneg _)

theorem measurable_localCubeDerivNorm (ell : ℤ) :
    Measurable (localCubeDerivNorm (d := d) ell) :=
  measurable_const.mul
    (ShellField.unitCubeDerivNorm_measurable.comp
      (ShellField.measurable_spatialScale _))

theorem measurable_localCubeSecondDerivNorm (ell : ℤ) :
    Measurable (localCubeSecondDerivNorm (d := d) ell) :=
  measurable_const.mul
    (ShellField.unitCubeSecondDerivNorm_measurable.comp
      (ShellField.measurable_spatialScale _))

private theorem spatialScale_one (j : ShellField d) :
    ShellField.spatialScale 1 j = j :=
  ShellField.ext (fun x => by rw [ShellField.spatialScale_apply, one_smul])

@[simp] theorem localCubeDerivNorm_zero (j : ShellField d) :
    localCubeDerivNorm 0 j = ShellField.unitCubeDerivNorm j := by
  rw [localCubeDerivNorm, zpow_zero, inv_one, one_mul, spatialScale_one]

@[simp] theorem localCubeSecondDerivNorm_zero (j : ShellField d) :
    localCubeSecondDerivNorm 0 j = ShellField.unitCubeSecondDerivNorm j := by
  rw [localCubeSecondDerivNorm, zpow_zero, inv_one, one_pow, one_mul, spatialScale_one]

private theorem matrixDerivativeNorm_deriv_spatialScale {r : ℝ} (hr : 0 ≤ r)
    (j : ShellField d) (y : Vec d) :
    ShellField.matrixDerivativeNorm (ShellField.deriv (ShellField.spatialScale r j) y) =
      r * ShellField.matrixDerivativeNorm (ShellField.deriv j (r • y)) := by
  rw [ShellField.spatialScale_deriv, matrixDerivativeNorm_smul_of_nonneg hr]

private theorem matrixSecondDerivativeNorm_secondDeriv_spatialScale {r : ℝ}
    (hr : 0 ≤ r ^ 2) (j : ShellField d) (y : Vec d) :
    ShellField.matrixSecondDerivativeNorm
        (ShellField.secondDeriv (ShellField.spatialScale r j) y) =
      r ^ 2 * ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j (r • y)) := by
  rw [ShellField.spatialScale_secondDeriv, matrixSecondDerivativeNorm_smul_of_nonneg hr]

private theorem smul_mem_openCubeSet {ell : ℤ} {y : Vec d}
    (hy : y ∈ openCubeSet (originCube d 0)) :
    ((3 : ℝ) ^ ell) • y ∈ openCubeSet (originCube d ell) := by
  rw [openCubeSet_originCube_eq_smul_originCube_zero, cubeScaleFactor_originCube,
    Set.mem_smul_set]
  exact ⟨y, hy, rfl⟩

private theorem inv_smul_mem_openCubeSet_zero {ell : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) :
    ((3 : ℝ) ^ ell)⁻¹ • x ∈ openCubeSet (originCube d 0) := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ ell := three_zpow_pos ell
  rw [openCubeSet_originCube_eq_smul_originCube_zero, cubeScaleFactor_originCube,
    Set.mem_smul_set] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [← hxy, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
  exact hy

/-- The first-derivative gauge dominates the exact induced derivative norm at
every point of the open origin cube of scale `ell`. -/
theorem matrixDerivativeNorm_deriv_le_localCubeDerivNorm (ell : ℤ)
    (j : ShellField d) {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) :
    ShellField.matrixDerivativeNorm (ShellField.deriv j x) ≤
      localCubeDerivNorm ell j := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ ell := three_zpow_pos ell
  have hcancel : ((3 : ℝ) ^ ell) • (((3 : ℝ) ^ ell)⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  have hpt := matrixDerivativeNorm_deriv_le_unitCubeDerivNorm
    (ShellField.spatialScale ((3 : ℝ) ^ ell) j) (inv_smul_mem_openCubeSet_zero hx)
  rw [matrixDerivativeNorm_deriv_spatialScale hr.le, hcancel] at hpt
  rw [localCubeDerivNorm, le_inv_mul_iff₀ hr]
  exact hpt

/-- Minimality of the first-derivative gauge. -/
theorem localCubeDerivNorm_le_of_forall (ell : ℤ) (j : ShellField d) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x ∈ openCubeSet (originCube d ell),
      ShellField.matrixDerivativeNorm (ShellField.deriv j x) ≤ C) :
    localCubeDerivNorm ell j ≤ C := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ ell := three_zpow_pos ell
  have hsup : ShellField.unitCubeDerivNorm
      (ShellField.spatialScale ((3 : ℝ) ^ ell) j) ≤ (3 : ℝ) ^ ell * C := by
    rw [unitCubeDerivNorm_le_iff]
    refine ⟨mul_nonneg hr.le hC, ?_⟩
    intro y hy
    rw [matrixDerivativeNorm_deriv_spatialScale hr.le]
    exact mul_le_mul_of_nonneg_left (h _ (smul_mem_openCubeSet hy)) hr.le
  rw [localCubeDerivNorm, inv_mul_le_iff₀ hr]
  exact hsup

/-- The second-derivative gauge dominates the exact twice-induced derivative
norm at every point of the open origin cube of scale `ell`. -/
theorem matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm (ell : ℤ)
    (j : ShellField d) {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) :
    ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j x) ≤
      localCubeSecondDerivNorm ell j := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ ell := three_zpow_pos ell
  have hr2 : (0 : ℝ) < ((3 : ℝ) ^ ell) ^ 2 := by positivity
  have hcancel : ((3 : ℝ) ^ ell) • (((3 : ℝ) ^ ell)⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  have hpt := matrixSecondDerivativeNorm_secondDeriv_le_unitCubeSecondDerivNorm
    (ShellField.spatialScale ((3 : ℝ) ^ ell) j) (inv_smul_mem_openCubeSet_zero hx)
  rw [matrixSecondDerivativeNorm_secondDeriv_spatialScale hr2.le, hcancel] at hpt
  rw [localCubeSecondDerivNorm, inv_pow, le_inv_mul_iff₀ hr2]
  exact hpt

/-- Minimality of the second-derivative gauge. -/
theorem localCubeSecondDerivNorm_le_of_forall (ell : ℤ) (j : ShellField d) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x ∈ openCubeSet (originCube d ell),
      ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j x) ≤ C) :
    localCubeSecondDerivNorm ell j ≤ C := by
  have hr : (0 : ℝ) < (3 : ℝ) ^ ell := three_zpow_pos ell
  have hr2 : (0 : ℝ) < ((3 : ℝ) ^ ell) ^ 2 := by positivity
  have hsup : ShellField.unitCubeSecondDerivNorm
      (ShellField.spatialScale ((3 : ℝ) ^ ell) j) ≤ ((3 : ℝ) ^ ell) ^ 2 * C := by
    rw [unitCubeSecondDerivNorm_le_iff']
    refine ⟨mul_nonneg hr2.le hC, ?_⟩
    intro y hy
    rw [matrixSecondDerivativeNorm_secondDeriv_spatialScale hr2.le]
    exact mul_le_mul_of_nonneg_left (h _ (smul_mem_openCubeSet hy)) hr2.le
  rw [localCubeSecondDerivNorm, inv_pow, inv_mul_le_iff₀ hr2]
  exact hsup

/-! ## Monotonicity in the cube scale -/

private theorem openCubeSet_originCube_mono {ell ell' : ℤ} (h : ell ≤ ell') :
    openCubeSet (originCube d ell) ⊆ openCubeSet (originCube d ell') := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  have hpow : (3 : ℝ) ^ ell ≤ (3 : ℝ) ^ ell' :=
    zpow_le_zpow_right₀ (by norm_num) h
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  exact ⟨by linarith, by linarith⟩

/-- The first-derivative gauge is monotone in the cube scale, since larger
scales mean larger cubes. -/
theorem localCubeDerivNorm_mono {ell ell' : ℤ} (h : ell ≤ ell') (j : ShellField d) :
    localCubeDerivNorm ell j ≤ localCubeDerivNorm ell' j := by
  refine localCubeDerivNorm_le_of_forall ell j (localCubeDerivNorm_nonneg ell' j) ?_
  intro x hx
  exact matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell' j
    (openCubeSet_originCube_mono h hx)

/-- The second-derivative gauge is monotone in the cube scale. -/
theorem localCubeSecondDerivNorm_mono {ell ell' : ℤ} (h : ell ≤ ell')
    (j : ShellField d) :
    localCubeSecondDerivNorm ell j ≤ localCubeSecondDerivNorm ell' j := by
  refine localCubeSecondDerivNorm_le_of_forall ell j
    (localCubeSecondDerivNorm_nonneg ell' j) ?_
  intro x hx
  exact matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm ell' j
    (openCubeSet_originCube_mono h hx)

/-! ## Exact triadic scaling -/

private theorem spatialScale_triadicScale (gamma : ℝ) (ell k : ℤ)
    (j : ShellField d) :
    ShellField.spatialScale ((3 : ℝ) ^ ell) (ShellField.triadicScale gamma k j) =
      ShellField.scale (Real.rpow 3 (gamma * (k : ℝ)))
        (ShellField.spatialScale ((3 : ℝ) ^ (ell - k)) j) := by
  refine ShellField.ext (fun x => ?_)
  simp only [ShellField.spatialScale_apply, ShellField.triadicScale_apply,
    ShellField.scale_apply]
  have hscale : ((3 : ℝ) ^ k)⁻¹ * (3 : ℝ) ^ ell = (3 : ℝ) ^ (ell - k) := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rw [smul_smul, hscale]

private theorem rpow_three_sub_one_mul (a : ℝ) (k : ℤ) :
    Real.rpow 3 ((a - 1) * (k : ℝ)) =
      Real.rpow 3 (a * (k : ℝ)) * ((3 : ℝ) ^ k)⁻¹ := by
  show (3 : ℝ) ^ ((a - 1) * (k : ℝ)) = (3 : ℝ) ^ (a * (k : ℝ)) * ((3 : ℝ) ^ k)⁻¹
  rw [show (a - 1) * (k : ℝ) = a * (k : ℝ) - (k : ℝ) by ring,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_intCast, div_eq_mul_inv]

private theorem rpow_three_sub_two_mul (a : ℝ) (k : ℤ) :
    Real.rpow 3 ((a - 2) * (k : ℝ)) =
      Real.rpow 3 (a * (k : ℝ)) * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ := by
  show (3 : ℝ) ^ ((a - 2) * (k : ℝ)) =
    (3 : ℝ) ^ (a * (k : ℝ)) * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹
  rw [show (a - 2) * (k : ℝ) = a * (k : ℝ) - (k : ℝ) - (k : ℝ) by ring,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
    Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_intCast,
    div_eq_mul_inv, div_eq_mul_inv]

private theorem inv_zpow_three_split (ell k : ℤ) :
    ((3 : ℝ) ^ ell)⁻¹ = ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ (ell - k))⁻¹ := by
  rw [← mul_inv, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
    show k + (ell - k) = ell by ring]

/-- The exact first-derivative scaling identity: the triadically scaled shell
`3^{γk} j(3^{-k}·)` has first-derivative gauge `3^{(γ-1)k}` times the gauge of
the original shell at the shifted cube scale `ell - k`.  This is the
derivative analogue of
`Algsuperdiff.Section3.Cutoff.localCubeControl_triadicScale`; the extra factor
`3^{-k}` is the chain rule. -/
theorem localCubeDerivNorm_triadicScale (gamma : ℝ) (ell k : ℤ) (j : ShellField d) :
    localCubeDerivNorm ell (ShellField.triadicScale gamma k j) =
      Real.rpow 3 ((gamma - 1) * (k : ℝ)) * localCubeDerivNorm (ell - k) j := by
  rw [localCubeDerivNorm, localCubeDerivNorm, spatialScale_triadicScale,
    unitCubeDerivNorm_scale_of_nonneg (c := Real.rpow 3 (gamma * (k : ℝ)))
      (Real.rpow_nonneg (by norm_num) _),
    rpow_three_sub_one_mul, inv_zpow_three_split ell k]
  ring

/-- The exact second-derivative scaling identity, with the two chain-rule
factors producing the exponent `γ - 2`. -/
theorem localCubeSecondDerivNorm_triadicScale (gamma : ℝ) (ell k : ℤ)
    (j : ShellField d) :
    localCubeSecondDerivNorm ell (ShellField.triadicScale gamma k j) =
      Real.rpow 3 ((gamma - 2) * (k : ℝ)) * localCubeSecondDerivNorm (ell - k) j := by
  rw [localCubeSecondDerivNorm, localCubeSecondDerivNorm, spatialScale_triadicScale,
    unitCubeSecondDerivNorm_scale_of_nonneg (c := Real.rpow 3 (gamma * (k : ℝ)))
      (Real.rpow_nonneg (by norm_num) _),
    rpow_three_sub_two_mul, inv_zpow_three_split ell k]
  ring

end

end Algsuperdiff.Section3.Provider.Stream
