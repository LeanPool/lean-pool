/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineTriangularComplexChart
public import LeanPool.ApollonianSuperharmonic.AffineTriangularFaceCoordinateSwap
public import LeanPool.ApollonianSuperharmonic.AffineTriangularFaceVertices
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: SwappedAffineTriangularChartAlignment]

/-!
# SwappedAffineTriangularChartAlignment

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SwappedAffineTriangularChartAlignment {ι : Type} [DecidableEq ι]
    (P : PeriodicTileComplex ι) (base : ProtoTile) (a b : GaussianInt)
    (chart : AffineTriangularComplexChart P (fun z : Int × Int =>
      TileTranslation base
        ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b))) :
    (∀ x y : Int × Int,
      TriangularLatticeAdjacent (Prod.swap x)
          (Prod.swap y) ↔
        TriangularLatticeAdjacent x y) ∧
    (∀ f : AffineTriangularFace,
      (AffineTriangularFaceVertices f).image Prod.swap =
        AffineTriangularFaceVertices
          (AffineTriangularFaceCoordinateSwap f)) ∧
    (∀ z : Int × Int,
      TileTranslation base
          ((z.1 : GaussianInt) * b + (z.2 : GaussianInt) * a) =
        P.tile (chart.vertexEquiv (Prod.swap z))) ∧
    ∀ f : AffineTriangularFace,
      let F : P.plane.Face :=
        match AffineTriangularFaceCoordinateSwap f with
        | .up z => chart.up z
        | .down z => chart.down z
      (AffineTriangularFaceVertices f).image
          (fun z => chart.vertexEquiv (Prod.swap z)) =
        {P.plane.faceVertex F 0, P.plane.faceVertex F 1,
          P.plane.faceVertex F 2} := by
-- BODY
  constructor
  · intro x y
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp only [Prod.swap, TriangularLatticeAdjacent,
      Prod.mk_sub_mk, Prod.ext_iff]
    omega
  constructor
  · intro f
    cases f <;> ext x <;>
      simp [AffineTriangularFaceVertices, AffineTriangularFaceCoordinateSwap,
        Prod.swap, Prod.ext_iff] <;>
      aesop
  constructor
  · intro z
    rw [chart.tile_eq]
    rcases z with ⟨m, n⟩
    simp [Prod.swap, add_comm]
  intro f
  cases f with
  | up z =>
      rw [show (match AffineTriangularFaceCoordinateSwap
          (AffineTriangularFace.up z) with
        | .up w => chart.up w
        | .down w => chart.down w) =
          chart.down (Prod.swap z) by rfl]
      rcases chart.down_vertices (Prod.swap z) with
        ⟨h₀', h₁', h₂'⟩
      have h₀ := h₀'
      have h₁ := h₁'
      have h₂ := h₂'
      simp [Prod.swap] at h₀ h₁ h₂
      ext x
      simp [h₀, h₁, h₂, AffineTriangularFaceVertices,
        Prod.swap]
      aesop
  | down z =>
      rw [show (match AffineTriangularFaceCoordinateSwap
          (AffineTriangularFace.down z) with
        | .up w => chart.up w
        | .down w => chart.down w) =
          chart.up (Prod.swap z) by rfl]
      rcases chart.up_vertices (Prod.swap z) with
        ⟨h₀', h₁', h₂'⟩
      have h₀ := h₀'
      have h₁ := h₁'
      have h₂ := h₂'
      simp [Prod.swap] at h₀ h₁ h₂
      ext x
      simp [h₀, h₁, h₂, AffineTriangularFaceVertices,
        Prod.swap]
      aesop

end ApollonianSuperharmonic

end
