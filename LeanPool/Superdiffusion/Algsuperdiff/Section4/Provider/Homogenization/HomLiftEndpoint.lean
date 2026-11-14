/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomLiftTelescope

/-!
# HomLiftEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the `L^∞` endpoint of the Hölder lifting

## What this module proves

Step 3 of Theorem B asserts

```text
  3^{-m} ‖u - v‖_{L^∞(□_m)} ≤ C 3^{-ms} ‖∇u - ∇v‖_{W_hat^{-s,∞}(□_m)}
```

for the Dirichlet pair `u, v` of the manuscript, whose difference satisfies `u
- v ∈ H^1_0(□_m)`.

Once the Hölder lifting of `HomLiftTelescope` has produced
`[w]_{C^{0,1-s}(□_m)} ≤ K`, the `L^∞` endpoint is elementary: `w` vanishes on
`∂□_m`, every point of `□_m` is within sup-distance `3^m` of a boundary
point, and therefore

```text
  3^{-m} |w(x)| ≤ 3^{-m} K (3^m)^{1-s} = K 3^{-ms}   for every x ∈ □_m,
```

with constant exactly `1`.  This is `linfty_of_holder_of_boundary_zero_cube`.

## The boundary carrier

The zero boundary value is carried literally: `w` vanishes on
`cubeFaceSet Q = closedCubeSet Q \ openCubeSet Q`.  This is the pointwise
form of `u - v ∈ H^1_0(□_m)` for the *continuous representative* the Hölder
bound produces, and it is stated as an explicit hypothesis rather than
derived from an `H^1_0` witness: the trace theorem that turns
`u - v ∈ H^1_0` into pointwise vanishing on `∂□_m` is not in the tree.

## Main results

* `closedCubeSet`, `cubeFaceSet` — the closed realization of a triadic cube
  and its topological boundary.
* `norm_sub_le_cubeScaleFactor` — the sup-diameter of a triadic cube is its
  side length `3^{scale}` (the `hdiam` hypothesis of the lifting).
* `linfty_of_holder_of_boundary_zero_cube` — the endpoint display, at
  constant `1`.
* `ae_linfty_of_holder_of_boundary_zero_cube` — the same, in the `∀ᵐ x` form
  the frozen statement literally uses.

## References

* ABK26, Theorem B Step 3.
* ABK26 (the `W^{-s,∞} ↔ Hölder` remark, "for functions vanishing on
  the boundary").
-/

open HCPolySupport MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The closed cube and its faces -/

/-- The **closed** realization of a triadic cube: `openCubeSet` with both
inequalities relaxed.  `CoarseGraining` carries the open and half-open realizations only;
the closed one is what the boundary argument needs. -/
def closedCubeSet (Q : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i, ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤ x i ∧
      x i ≤ ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q }

/-- The face set of a triadic cube: the closed realization minus the open
one. -/
def cubeFaceSet (Q : TriadicCube d) : Set (Vec d) :=
  closedCubeSet Q \ openCubeSet Q

theorem openCubeSet_subset_closedCubeSet (Q : TriadicCube d) :
    openCubeSet Q ⊆ closedCubeSet Q := by
  intro x hx i
  exact ⟨(hx i).1.le, (hx i).2.le⟩

theorem cubeScaleFactor_pos (Q : TriadicCube d) : 0 < cubeScaleFactor Q :=
  zpow_pos (by norm_num) _

/-- The side length as a real power of `3` at the cube's scale. -/
theorem three_rpow_scale_eq (Q : TriadicCube d) :
    (3 : ℝ) ^ ((Q.scale : ℤ) : ℝ) = cubeScaleFactor Q := by
  rw [three_rpow_intCast, natCast_three]
  rfl

/-! ## 2. The sup-diameter of a triadic cube -/

/-- **The diameter estimate.**  In the ambient sup norm of `Vec d`, two points
of the closed triadic cube `Q` are at distance at most the side length
`3^{Q.scale}`.  This is the `hdiam` hypothesis of the Hölder lifting. -/
theorem norm_sub_le_cubeScaleFactor (Q : TriadicCube d) :
    ∀ x ∈ closedCubeSet Q, ∀ y ∈ closedCubeSet Q,
      ‖x - y‖ ≤ (3 : ℝ) ^ ((Q.scale : ℤ) : ℝ) := by
  intro x hx y hy
  rw [three_rpow_scale_eq]
  refine (pi_norm_le_iff_of_nonneg (cubeScaleFactor_pos Q).le).mpr ?_
  intro i
  have hxi := hx i
  have hyi := hy i
  have hgap :
      ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q -
          ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q = cubeScaleFactor Q := by
    ring
  have : |x i - y i| ≤ cubeScaleFactor Q := by
    rw [abs_le]
    constructor
    · linarith only [hxi.1, hyi.2, hgap]
    · linarith only [hxi.2, hyi.1, hgap]
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using this

/-! ## 3. The boundary point -/

/-- Every point of the open cube has a face point of the same cube at
sup-distance at most the side length: move one coordinate to the upper face
and leave the others alone. -/
theorem exists_face_point [NeZero d] (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) :
    ∃ y ∈ cubeFaceSet Q, ‖x - y‖ ≤ (3 : ℝ) ^ ((Q.scale : ℤ) : ℝ) := by
  classical
  have hpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨i₀⟩ : Nonempty (Fin d) := ⟨⟨0, hpos⟩⟩
  have hf : 0 < cubeScaleFactor Q := cubeScaleFactor_pos Q
  refine ⟨Function.update x i₀ (((Q.index i₀ : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q),
    ⟨?_, ?_⟩, ?_⟩
  · intro i
    by_cases hi : i = i₀
    · subst hi
      rw [Function.update_self]
      refine ⟨?_, le_rfl⟩
      exact (mul_lt_mul_of_pos_right
        (show ((Q.index i : ℝ) - (1 / 2 : ℝ)) < ((Q.index i : ℝ) + (1 / 2 : ℝ)) by
          linarith only [(by norm_num : (0 : ℝ) < 1)]) hf).le
    · rw [Function.update_of_ne hi]
      exact ⟨(hx i).1.le, (hx i).2.le⟩
  · intro hmem
    have hlt := (hmem i₀).2
    rw [Function.update_self] at hlt
    exact lt_irrefl _ hlt
  · rw [three_rpow_scale_eq]
    refine (pi_norm_le_iff_of_nonneg hf.le).mpr ?_
    intro i
    by_cases hi : i = i₀
    · subst hi
      have hupd :
          (Function.update x i (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) i
            = ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q :=
        Function.update_self i _ x
      have hlow := (hx i).1
      have hhigh := (hx i).2
      have hgap :
          ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q -
              ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q = cubeScaleFactor Q := by
        ring
      have hbd :
          |x i - ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q| ≤ cubeScaleFactor Q := by
        rw [abs_le]
        exact ⟨by linarith only [hlow, hgap], by linarith only [hhigh, hf]⟩
      simpa only [Pi.sub_apply, Real.norm_eq_abs, hupd] using hbd
    · have hupd :
          (Function.update x i₀ (((Q.index i₀ : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) i
            = x i := Function.update_of_ne hi _ x
      simp only [Pi.sub_apply, Real.norm_eq_abs, hupd, sub_self, abs_zero]
      exact hf.le

/-! ## 4. The `L^∞` endpoint -/

/-- **The `L^∞` endpoint of the lifting**.

If `w` obeys the Hölder bound `[w]_{C^{0,1-s}} ≤ K` on the closed cube and
vanishes on the cube's faces, then

```text
  3^{-scale} |w(x)| ≤ K · 3^{-scale·s}   for every x in the open cube.
```

The constant is exactly `1`: the volume-normalized `L^∞` gauge on the left
and the Hölder seminorm on the right differ by exactly the factor
`(3^{scale})^{1-s}` supplied by the cube's diameter. -/
theorem linfty_of_holder_of_boundary_zero_cube [NeZero d] (Q : TriadicCube d)
    {w : Vec d → ℝ} {s K : ℝ} (hs1 : s < 1) (hK : 0 ≤ K)
    (hHol : HolderSeminormBoundOn (closedCubeSet Q) (1 - s) K w)
    (hzero : ∀ y ∈ cubeFaceSet Q, w y = 0) :
    ∀ x ∈ openCubeSet Q,
      (3 : ℝ) ^ (-((Q.scale : ℤ) : ℝ)) * |w x| ≤
        K * (3 : ℝ) ^ (-((Q.scale : ℤ) : ℝ) * s) := by
  intro x hx
  obtain ⟨y, hy, hdist⟩ := exists_face_point Q hx
  have hxc : x ∈ closedCubeSet Q := openCubeSet_subset_closedCubeSet Q hx
  have hyc : y ∈ closedCubeSet Q := hy.1
  have h1s : (0 : ℝ) < 1 - s := by linarith only [hs1]
  have hHxy := hHol x hxc y hyc
  rw [Real.norm_eq_abs, hzero y hy, sub_zero] at hHxy
  have hmono : ‖x - y‖ ^ (1 - s) ≤ ((3 : ℝ) ^ ((Q.scale : ℤ) : ℝ)) ^ (1 - s) :=
    Real.rpow_le_rpow (norm_nonneg _) hdist h1s.le
  have hpow : ((3 : ℝ) ^ ((Q.scale : ℤ) : ℝ)) ^ (1 - s)
      = (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) * (1 - s)) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hbound : |w x| ≤ K * (3 : ℝ) ^ (((Q.scale : ℤ) : ℝ) * (1 - s)) := by
    refine hHxy.trans ?_
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left hmono hK
  have hmul := mul_le_mul_of_nonneg_left hbound
    (three_rpow_nonneg (-((Q.scale : ℤ) : ℝ)))
  refine hmul.trans (le_of_eq ?_)
  have hexp : -((Q.scale : ℤ) : ℝ) + ((Q.scale : ℤ) : ℝ) * (1 - s)
      = -((Q.scale : ℤ) : ℝ) * s := by ring
  rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (-((Q.scale : ℤ) : ℝ))) K, mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hexp]

/-! ## 5. The composition with the lifting -/

/-- **The `∀ᵐ x` form** used by the frozen root's conclusion (C3): the
pointwise bound on the open cube upgrades to an almost-everywhere bound
against the restricted volume measure. -/
theorem ae_linfty_of_holder_of_boundary_zero_cube [NeZero d] (Q : TriadicCube d)
    {w : Vec d → ℝ} {s K : ℝ} (hs1 : s < 1) (hK : 0 ≤ K)
    (hHol : HolderSeminormBoundOn (closedCubeSet Q) (1 - s) K w)
    (hzero : ∀ y ∈ cubeFaceSet Q, w y = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      (3 : ℝ) ^ (-((Q.scale : ℤ) : ℝ)) * |w x| ≤
        K * (3 : ℝ) ^ (-((Q.scale : ℤ) : ℝ) * s) := by
  have hptwise := linfty_of_holder_of_boundary_zero_cube Q hs1 hK hHol hzero
  refine (ae_restrict_iff' (measurableSet_openCubeSet Q)).2 ?_
  exact Filter.Eventually.of_forall fun x hx => hptwise x hx

end

end Algsuperdiff.Section4.Provider.Homogenization
