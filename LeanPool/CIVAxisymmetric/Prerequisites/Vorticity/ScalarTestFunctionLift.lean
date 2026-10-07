/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction

/-!
# Scalar Test Function Lift

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-- If `ψ` is smooth then `ψ • basisVec i` is also smooth, because scalar multiplication
by a constant vector is a smooth operation on `Vec3`. -/
theorem contDiff_smul_basisVec_of_contDiff
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ψ z • basisVec i) :=
  hψ.smul_const (basisVec i)

/-- If `ψ` has compact support then `ψ • basisVec i` also has compact support, since
`support (ψ • basisVec i) ⊆ support ψ` (the basis vector is non-zero, so `ψ z • basisVec i = 0`
only when `ψ z = 0`). -/
theorem hasCompactSupport_smul_basisVec_of_hasCompactSupport
    {ψ : Vec3 × ℝ → ℝ} (hψc : HasCompactSupport ψ) (i : Fin 3) :
    HasCompactSupport (fun z : Vec3 × ℝ => ψ z • basisVec i) :=
  hψc.smul_right (f' := fun _ : Vec3 × ℝ => basisVec i)

/-- A scalar test function `ψ` lifts to a vector test function `ψ • basisVec i` in
`spaceTimeTestFunction (V := Vec3) Ω I`. This is the technical lemma that licenses
isolating the `i`-th scalar component of the vector momentum equation by testing
against `φ := ψ • basisVec i`. -/
theorem smul_basisVec_mem_spaceTimeTestFunction
    {Ω : Set Vec3} {I : Set ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) (i : Fin 3) :
    (fun z : Vec3 × ℝ => ψ z • basisVec i) ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
  rcases hψ with ⟨hψ_contDiff, hψ_cs, hψ_tsupport⟩
  refine ⟨contDiff_smul_basisVec_of_contDiff hψ_contDiff i,
    hasCompactSupport_smul_basisVec_of_hasCompactSupport hψ_cs i, ?_⟩
  have h_support : tsupport (fun z : Vec3 × ℝ => ψ z • basisVec i) ⊆ tsupport ψ :=
    tsupport_smul_subset_left ψ (fun _ : Vec3 × ℝ => basisVec i)
  exact subset_trans h_support hψ_tsupport

end CIV
