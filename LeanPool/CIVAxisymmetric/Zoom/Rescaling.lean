/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.Meridional
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Statements.Dr
public import LeanPool.CIVAxisymmetric.Statements.Dz
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Rescaling

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The zoom-in map of `eq:aniso:zoom:finite:variables`. -/
@[expose] def zoomPoint (lam h zc : ℝ) (p : (ℝ × ℝ) × ℝ) : ParabolicPoint :=
  (meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2), lam ^ 2 * p.2)

/-- `V_n`, the radial component of the rescaled velocity, of
`eq:aniso:zoom:fields`. -/
@[expose] def zoomV (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam * u (zoomPoint lam h zc p) 0

/-- `W_n`, the vertical component of the rescaled velocity, of
`eq:aniso:zoom:fields`. -/
@[expose] def zoomW (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam * lam ^ (2 * h) * u (zoomPoint lam h zc p) 2

/-- `S_n`, the swirl component of the rescaled velocity, of
`eq:aniso:zoom:fields`. -/
@[expose] def zoomS (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam * lam ^ (2 * h) * u (zoomPoint lam h zc p) 1

/-- The time sign is `lam ^ 2 * p.2` with `p.2 = τ < 0`, so the selected time
`τ = -1` maps to `t = -lam²`. This is the paper's convention and the corrected sign;
do not change it. -/
theorem zoomPoint_mem_unitCylinder_iff (lam h zc : ℝ) (p : (ℝ × ℝ) × ℝ) :
    zoomPoint lam h zc p ∈ unitCylinder ↔
      (lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2 < 1 ∧
        lam ^ 2 * p.2 ∈ Ioo (-1 : ℝ) 0 := by
  constructor
  · intro hmem
    rcases hmem with ⟨hball, htime⟩
    have hball_norm : vec3EuclideanNorm (meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) *
      p.1.2)) < 1 := by
      simpa [unitCylinder, spaceTimeSet, zoomPoint, mem_vec3Ball, sub_zero] using hball
    have hsum : vec3EuclideanNorm (meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2)) =
        Real.sqrt ((lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2) := by
      rw [vec3EuclideanNorm]
      simp [meridional, Fin.sum_univ_three]
    rw [hsum] at hball_norm
    have hsq : (lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2 < 1 := by
      have htemp := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mp hball_norm
      simpa [sq] using htemp
    exact ⟨hsq, htime⟩
  · intro ⟨hsq, htime⟩
    have hball_norm : Real.sqrt ((lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2) < 1 := by
      apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
      simpa [sq] using hsq
    have hsum : vec3EuclideanNorm (meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2)) =
        Real.sqrt ((lam * p.1.1) ^ 2 + (zc + lam ^ (1 - 2 * h) * p.1.2) ^ 2) := by
      rw [vec3EuclideanNorm]
      simp [meridional, Fin.sum_univ_three]
    have hball_norm' : vec3EuclideanNorm (meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) *
      p.1.2)) < 1 := by
      rw [hsum]
      exact hball_norm
    have hball : meridional (lam * p.1.1) (zc + lam ^ (1 - 2 * h) * p.1.2) ∈ vec3Ball (0 : Vec3)
      1 := by
      rwa [mem_vec3Ball, sub_zero]
    have hunit : zoomPoint lam h zc p ∈ unitCylinder := by
      rw [unitCylinder, spaceTimeSet, zoomPoint]
      exact Set.mem_prod.mpr ⟨hball, htime⟩
    exact hunit

/-- `zoomPoint` is affine in `p` (with `lam`, `h`, `zc` fixed), hence continuous.
`ParabolicPoint` carries the parabolic metric rather than the product one (design
note R2), so the statement is given on the explicit product carrier `Vec3 × ℝ`:
naming the codomain `Y := Vec3 × ℝ` fixes the `TopologicalSpace` instance to the
product one before `zoomPoint`'s own `ParabolicPoint`-typed body is elaborated,
since a bare type ascription on the body is defeq-transparent and would leave the
`ParabolicPoint` instance in place. -/
theorem continuous_zoomPoint (lam h zc : ℝ) :
    Continuous (Y := Vec3 × ℝ) (fun p : (ℝ × ℝ) × ℝ => zoomPoint lam h zc p) := by
  unfold zoomPoint
  apply Continuous.prodMk
  · -- spatial component: p ↦ meridional (lam * p.1.1) (zc + lam^(1-2h) * p.1.2)
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simp only [meridional]
      exact Continuous.mul continuous_const (continuous_fst.comp continuous_fst)
    · simp only [meridional]
      exact continuous_const
    · simp only [meridional]
      refine Continuous.add continuous_const ?_
      exact Continuous.mul continuous_const (continuous_snd.comp continuous_fst)
  · -- time component: lam^2 * p.2
    exact Continuous.mul continuous_const continuous_snd

/-- `zoomPoint` is affine, hence smooth. `ParabolicPoint` carries the parabolic
metric rather than the product one (design note R2), so the statement is given
on the explicit product carrier `Vec3 × ℝ`, naming the codomain `F := Vec3 × ℝ`
for the same reason as `continuous_zoomPoint`. -/
theorem contDiff_zoomPoint (lam h zc : ℝ) :
    ContDiff ℝ (F := Vec3 × ℝ) (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => zoomPoint lam h zc p) := by
  unfold zoomPoint
  apply ContDiff.prodMk
  · -- spatial component
    have hx : ContDiff ℝ (⊤ : ℕ∞) (fun (p : (ℝ × ℝ) × ℝ) => lam * p.1.1) :=
      ContDiff.mul contDiff_const (contDiff_fst.comp contDiff_fst)
    have hz : ContDiff ℝ (⊤ : ℕ∞) (fun (p : (ℝ × ℝ) × ℝ) => zc + lam ^ (1 - 2 * h) * p.1.2) :=
      ContDiff.add contDiff_const (ContDiff.mul contDiff_const (contDiff_snd.comp contDiff_fst))
    refine (contDiff_pi (ι := Fin 3)).2 ?_
    intro i
    fin_cases i
    · simpa [meridional] using hx
    · simpa [meridional] using contDiff_const
    · simpa [meridional] using hz
  · -- time part: lam^2 * p.2
    exact ContDiff.mul contDiff_const contDiff_snd

end CIV
