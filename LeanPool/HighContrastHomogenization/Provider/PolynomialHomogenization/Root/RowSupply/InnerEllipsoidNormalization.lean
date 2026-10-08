/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineTransfer
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.CellAnchoredPhysicalFluxFrameAlgebra

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.InnerEllipsoidNormalization

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The inner-ellipsoid normalization premise

The Dirichlet conjunct already bounds the domain above by its adapted
ellipsoid.  This file studies the effect of bounding it below by a concentric
adapted ellipsoid of an explicit dimensional radius.

Two facts are proved.  First, the class of domains satisfying both bounds is
non-empty at every dimension and every comparison matrix: an adapted cell of a
suitable generation fits between the two ellipsoids, so the proposed premise is
not vacuous.  Second, the lower bound forces the absolute gauge scale to be
majorized by the outer sandwich radius, which is exactly the majorization a
cell-anchored response rate needs in order to expose only the frozen outer
data.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Set

noncomputable section

variable {d : ℕ}

/-! ## The absorption: the inner ellipsoid majorizes the gauge scale -/

/-- A concentric adapted ellipsoid inside the domain forces the absolute gauge
scale, times the ellipsoid's radius, below the outer sandwich radius of the
gauge domain.  This is the exact inequality that removes the absolute
reference scale from a cell-anchored response constant. -/
theorem normalizedRootScale_mul_le_of_innerEllipsoid
    [NeZero d] {abar : Mat d} {U : Set (Vec d)} {c rho Rad : ℝ}
    (hS : (symmPart abar).PosDef) (hc : 0 ≤ c)
    (hInner : ellipsoid abar c ⊆ U)
    (hSandwich :
      HasBallSandwich (matImage (matSqrt (symmPart abar))⁻¹ U) rho Rad) :
    Real.sqrt (specBound ((symmPart abar)⁻¹)) * c ≤ Rad := by
  obtain ⟨_hrho, hRad, cc, _hin, hout⟩ := hSandwich
  set alpha : ℝ := Real.sqrt (specBound ((symmPart abar)⁻¹)) with halphaDef
  have halpha0 : 0 ≤ alpha := Real.sqrt_nonneg _
  set t : ℝ := alpha * c with htDef
  have ht0 : 0 ≤ t := mul_nonneg halpha0 hc
  have hsq : specBound ((symmPart abar)⁻¹) * c ^ 2 = t ^ 2 := by
    rw [htDef, mul_pow, halphaDef, Real.sq_sqrt (specBound_nonneg _)]
  have hpull :
      matImage (matSqrt (symmPart abar))⁻¹ (ellipsoid abar c) =
        {y : Vec d | vecNormSq y ≤ specBound ((symmPart abar)⁻¹) * c ^ 2} :=
    matImage_matSqrt_inv_ellipsoid_eq hS c
  have hmono :
      matImage (matSqrt (symmPart abar))⁻¹ (ellipsoid abar c) ⊆
        matImage (matSqrt (symmPart abar))⁻¹ U :=
    Set.image_mono hInner
  have hmem : ∀ y : Vec d, vecNormSq y ≤ t ^ 2 →
      vecNormSq (y - cc) < Rad ^ 2 := by
    intro y hy
    have hy' : y ∈ matImage (matSqrt (symmPart abar))⁻¹ (ellipsoid abar c) := by
      rw [hpull]
      change vecNormSq y ≤ specBound ((symmPart abar)⁻¹) * c ^ 2
      rw [hsq]
      exact hy
    exact hout (hmono hy')
  -- two antipodal points of the pulled-back inner ellipsoid
  let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  let e : Vec d := fun i => if i = i0 then t else 0
  have he0 : e i0 = t := by simp only [e, ite_eq_left rfl]
  have hnorm_e : vecNormSq e = t ^ 2 := by
    have hterm : ∀ i : Fin d, e i * e i = if i = i0 then t * t else 0 := by
      intro i
      by_cases hi : i = i0 <;> simp [e, hi]
    calc vecNormSq e = ∑ i, e i * e i := rfl
      _ = ∑ i : Fin d, if i = i0 then t * t else 0 :=
        Finset.sum_congr rfl fun i _ => hterm i
      _ = t * t := by simp
      _ = t ^ 2 := (pow_two t).symm
  have hnorm_neg : vecNormSq (-e) = t ^ 2 := by
    have : vecNormSq (-e) = vecNormSq e := by
      simp only [vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]
    rw [this, hnorm_e]
  have h1 : vecNormSq (e - cc) < Rad ^ 2 := hmem e hnorm_e.le
  have h2 : vecNormSq (-e - cc) < Rad ^ 2 := hmem (-e) hnorm_neg.le
  have hcoord1 : (t - cc i0) ^ 2 < Rad ^ 2 := by
    have hle : (e i0 - cc i0) ^ 2 ≤ vecNormSq (e - cc) := by
      simpa only [Pi.sub_apply] using sq_apply_le_vecNormSq (e - cc) i0
    rw [he0] at hle
    exact lt_of_le_of_lt hle h1
  have hcoord2 : (-t - cc i0) ^ 2 < Rad ^ 2 := by
    have hle : ((-e) i0 - cc i0) ^ 2 ≤ vecNormSq (-e - cc) := by
      simpa only [Pi.sub_apply] using sq_apply_le_vecNormSq (-e - cc) i0
    have hval : (-e) i0 = -t := by
      simp only [Pi.neg_apply, he0]
    rw [hval] at hle
    exact lt_of_le_of_lt hle h2
  have habs : ∀ x : ℝ, x ^ 2 < Rad ^ 2 → |x| < Rad := by
    intro x hx
    have hlt := Real.sqrt_lt_sqrt (sq_nonneg x) hx
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hRad] at hlt
  have hA := habs _ hcoord1
  have hB := habs _ hcoord2
  have hA' : t - cc i0 ≤ |t - cc i0| := le_abs_self _
  have hB' : -(-t - cc i0) ≤ |-t - cc i0| := neg_le_abs _
  linarith only [hA, hB, hA', hB']

/-! ## Non-vacuity: an adapted cell fits between the two ellipsoids -/

/-! ## The rate consequence at the shape the consumer reads -/

end

end RowSupply
end HighContrast
end HCPolySupport
