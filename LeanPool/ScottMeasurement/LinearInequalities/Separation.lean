/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.LinearInequalities.Definitions
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Finite convex separation

The separation lemma used in Scott's proof of Theorem 1.1.
-/

@[expose] public section

open Set

namespace Scott1964.MeasurementStructures.LinearInequalities

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L]

/-- A finite set `A` can be made strictly positive while `B` is made zero
exactly when its convex hull misses the span of `B`. -/
theorem finite_strict_separation {A B : Set L} (hA : A.Finite) :
    Disjoint (convexHull ℝ A) (Submodule.span ℝ B : Set L) ↔
      ∃ φ : Module.Dual ℝ L, (∀ x ∈ A, 0 < φ x) ∧ ∀ x ∈ B, φ x = 0 := by
  constructor
  · intro hdisj
    let M : Submodule ℝ L := Submodule.span ℝ B
    have hMclosed : IsClosed (M : Set L) := M.closed_of_finiteDimensional
    obtain ⟨f, u, v, hfA, huv, hfM⟩ :=
      geometric_hahn_banach_compact_closed (convex_convexHull ℝ A)
        (hA.isCompact_convexHull ℝ) M.convex hMclosed hdisj
    have hf_zero : ∀ m ∈ M, f m = 0 := by
      intro m hm
      by_contra hne
      have hscaled := hfM (((v - 1) / f m) • m) (M.smul_mem _ hm)
      have hmap : f (((v - 1) / f m) • m) = v - 1 := by
        rw [map_smul, smul_eq_mul]
        field_simp
      rw [hmap] at hscaled
      linarith
    let φ : Module.Dual ℝ L := -(f : L →L[ℝ] ℝ).toLinearMap
    refine ⟨φ, ?_, ?_⟩
    · intro x hx
      have hxHull : x ∈ convexHull ℝ A := subset_convexHull ℝ A hx
      have hv : v < 0 := by simpa using hfM 0 M.zero_mem
      have hfx : f x < 0 := (hfA x hxHull).trans (huv.trans hv)
      simpa [φ] using neg_pos.mpr hfx
    · intro x hx
      have hxM : x ∈ M := Submodule.subset_span hx
      simp [φ, hf_zero x hxM]
  · rintro ⟨φ, hφA, hφB⟩
    rw [Set.disjoint_left]
    intro z hzA hzB
    have hzpos : 0 < φ z := by
      exact convexHull_min (fun x hx ↦ hφA x hx)
        (convex_halfSpace_gt φ.isLinear 0) hzA
    have hzM : φ z = 0 := by
      have hle : Submodule.span ℝ B ≤ LinearMap.ker φ :=
        Submodule.span_le.mpr fun x hx => LinearMap.mem_ker.mpr (hφB x hx)
      exact LinearMap.mem_ker.mp (hle hzB)
    linarith

end Scott1964.MeasurementStructures.LinearInequalities
