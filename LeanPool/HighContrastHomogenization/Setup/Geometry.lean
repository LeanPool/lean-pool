/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SpectralBound
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCube

/-!
# High-contrast homogenization: Setup.Geometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Triadic and adapted geometry

The centered triadic cubes of `s.introduction`, the standard aligned cubes of
`e.coarse.ellipticity`, the rounding convention of `s.scale.selection`, the
adapted cells of a rounded geometry, and the ellipsoids of the homogenization
theorem.
-/

namespace HCPolySupport
namespace HighContrast

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-! ## Triadic geometry -/

/-- The centered open triadic cube `□_m = (-3^m/2, 3^m/2)^d`
(the triadic cube of generation m). -/
@[expose]
def centeredCube (d : ℕ) (m : ℤ) : Set (Vec d) :=
  openCubeSet (originCube d m)

/-- The standard aligned cube `z + □_k` with `z = 3^k w`, `w ∈ ℤ^d`. -/
@[expose]
def standardCell (d : ℕ) (k : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  openCubeSet (translateCube w (originCube d k))

/-- The center `3^k w` of a standard aligned cube. -/
@[expose]
def standardCellCenter (k : ℤ) (w : Fin d → ℤ) : Vec d :=
  fun i => (3 : ℝ) ^ k * (w i : ℝ)

/-- The standard aligned cube at the zero index is the centered cube. -/
theorem standardCell_zero (k : ℤ) : standardCell d k 0 = centeredCube d k := by
  simp only [standardCell, centeredCube, translateCube, originCube, Pi.zero_apply,
    add_zero]
  rfl

/-- The origin, the center of the standard cell at index zero, lies in every
centered cube. -/
theorem standardCellCenter_zero_mem_centeredCube (k m : ℤ) :
    standardCellCenter (d := d) k 0 ∈ centeredCube d m := by
  intro i
  have h : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  constructor <;> simp [standardCellCenter, originCube, cubeScaleFactor] <;>
    linarith only [h]

/-! ## The rounding convention: `k_0(d)`, rounded grids, adapted cells -/

/-- The fixed rounding scale `k_0(d)` of the rounded adapted grid.  Chosen
concretely with slack; consumers use only `kZero_spec`. -/
@[expose]
def kZero (d : ℕ) : ℕ :=
  d + 5

/-- The quantitative constraint the paper places on `k_0(d)`:
`d 3^{-k_0(d)} ≤ 1/101`. -/
theorem kZero_spec (d : ℕ) :
    (d : ℝ) * (3 : ℝ) ^ (-(kZero d : ℤ)) ≤ 1 / 101 := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(kZero d : ℤ)) := by positivity
  have hd : (d : ℝ) ≤ (3 : ℝ) ^ (d : ℤ) := by
    rw [zpow_natCast]
    exact_mod_cast (Nat.lt_pow_self (by norm_num) (n := d)).le
  have hmul := mul_le_mul_of_nonneg_right hd h3.le
  refine hmul.trans ?_
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hexp : (d : ℤ) + -(kZero d : ℤ) = -5 := by
    simp [kZero]
  rw [hexp]
  norm_num

/-- The rounded grid `Q_j(m)` (the rounded adapted grid of a metric):
`(Q_j(m))_{ik} = 3^{-j} ⌈3^j |m^{-1}|^{1/2} (m^{1/2})_{ik}⌉`. -/
@[expose]
def roundedGrid (j : ℤ) (m : Mat d) : Mat d :=
  Matrix.of fun i k =>
    (3 : ℝ) ^ (-j) *
      (⌈(3 : ℝ) ^ j * Real.sqrt (specBound m⁻¹) * matSqrt m i k⌉ : ℤ)

/-- The base rounded grid `Q(m) := Q_{k_0(d)}(m)`. -/
@[expose]
def baseRoundedGrid (m : Mat d) : Mat d :=
  roundedGrid (kZero d : ℤ) m

/-- A rounded adapted grid at alignment scale `ℓ ≥ k_0(d)`: the rounding of a
positive symmetric witness. -/
@[expose]
def IsRoundedGrid (ℓ : ℤ) (q : Mat d) : Prop :=
  (kZero d : ℤ) ≤ ℓ ∧ ∃ m : Mat d, m.PosDef ∧ q = roundedGrid ℓ m

/-- The adapted cell `⋄_j^q = q □_j` (the adapted cubes of a rounded geometry). -/
@[expose]
def adaptedCell (q : Mat d) (j : ℤ) : Set (Vec d) :=
  matVecMul q '' centeredCube d j

/-- The adapted lattice `𝕃_q = q ℤ^d` (the adapted cubes of a rounded geometry). -/
@[expose]
def adaptedLattice (q : Mat d) : Set (Vec d) :=
  Set.range fun w : Fin d → ℤ => matVecMul q fun i => (w i : ℝ)

/-- The aligned adapted cell `z + ⋄_r^q` with `z = 3^r q w ∈ 3^r 𝕃_q`. -/
@[expose]
def adaptedCellAt (q : Mat d) (r : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  (fun x => (3 : ℝ) ^ r • matVecMul q (fun i => (w i : ℝ)) + x) '' adaptedCell q r

/-- The translate `y + ⋄_j^q` of an adapted cell by an arbitrary vector. -/
@[expose]
def adaptedCellTranslate (q : Mat d) (j : ℤ) (y : Vec d) : Set (Vec d) :=
  (fun x => y + x) '' adaptedCell q j

/-! ## Ellipsoids for the homogenization theorem -/

/-- The ellipsoid `E_r = {x : x · s̄⁻¹ x ≤ λ̄⁻¹ r²}` of
`e.homogenized.ellipsoids`, where
`s̄ = ½(ā + āᵗ)` and `λ̄⁻¹ = |s̄⁻¹|`. -/
@[expose]
def ellipsoid (abar : Mat d) (r : ℝ) : Set (Vec d) :=
  {x | vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤
    specBound (symmPart abar)⁻¹ * r ^ 2}

end

end HighContrast
end HCPolySupport
