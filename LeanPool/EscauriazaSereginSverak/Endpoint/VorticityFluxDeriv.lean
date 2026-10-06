/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakLinear

/-!
# Weak derivatives of the vorticity flux

The vorticity flux `-(uⱼ ωᵢ - ωⱼ uᵢ)` and its first derivative are sums of products of
square-integrable fields with square-integrable weak derivatives; the product rule gives their
weak derivatives (the product structure of `lem:vorticity-products`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak derivative of a difference of two products. -/
theorem vorticity_weakPartial_prodDiff {W : Set (Vec3 × ℝ)} (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W) {a b c d a' b' c' d' : Vec3 × ℝ → ℝ} {m : Fin 3}
    (ha : MemLp a 2 (volume.restrict W)) (hb : MemLp b 2 (volume.restrict W))
    (hc : MemLp c 2 (volume.restrict W)) (hd : MemLp d 2 (volume.restrict W))
    (ha' : MemLp a' 2 (volume.restrict W)) (hb' : MemLp b' 2 (volume.restrict W))
    (hc' : MemLp c' 2 (volume.restrict W)) (hd' : MemLp d' 2 (volume.restrict W))
    (hda : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, a y * spatialPartial ψ m y = -∫ y in W, a' y * ψ y)
    (hdb : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, b y * spatialPartial ψ m y = -∫ y in W, b' y * ψ y)
    (hdc : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, c y * spatialPartial ψ m y = -∫ y in W, c' y * ψ y)
    (hdd : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, d y * spatialPartial ψ m y = -∫ y in W, d' y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, (a y * b y - c y * d y) * spatialPartial ψ m y =
        -∫ y in W, ((a' y * b y + a y * b' y) - (c' y * d y + c y * d' y)) * ψ y := by
  have hi : ∀ f g : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      MemLp g 2 (volume.restrict W) → IntegrableOn (fun y => f y * g y) W :=
    fun f g hf hg => hf.integrable_mul hg
  exact vorticity_weakPartial_sub (hi a b ha hb) (hi c d hc hd)
    ((hi a' b ha' hb).add (hi a b' ha hb')) ((hi c' d hc' hd).add (hi c d' hc hd'))
    (vorticity_weakPartial_mul hWo hWb ha hb ha' hb' hda hdb)
    (vorticity_weakPartial_mul hWo hWb hc hd hc' hd' hdc hdd)

end ESS
