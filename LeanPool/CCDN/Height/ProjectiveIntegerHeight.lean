/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveAffineChart

/-! Integral representatives need not be primitive to provide an upper
bound on projective height. Removing their gcd can only decrease the
maximum absolute coordinate. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- If the chosen representative of `x` has nonzero first coordinate, then so does its primitive
integer representative, and the affine chart coordinates of `x` are the ratios of the
remaining primitive coordinates to the first one. -/
theorem primitiveProjectiveRep_chart {n : ℕ} (x : ProjectivePoint n) (hx : x.rep 0 ≠ 0) :
    primitiveProjectiveRep x 0 ≠ 0 ∧
      projectiveAffineCoordinates x =
        fun j => (primitiveProjectiveRep x j.succ : ℚ) / (primitiveProjectiveRep x 0 : ℚ) := by
  have he := (primitiveProjectiveRep_mk x).trans x.mk_rep.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp he
  have hcoord (j : Fin (n + 1)) :
      (c : ℚ) * x.rep j = (primitiveProjectiveRep x j : ℚ) := congrFun hc j
  have h0 : (primitiveProjectiveRep x 0 : ℚ) ≠ 0 := by
    rw [← hcoord 0]
    exact mul_ne_zero c.ne_zero hx
  refine ⟨by exact_mod_cast h0, ?_⟩
  funext j
  change x.rep j.succ / x.rep 0 = _
  rw [← hcoord j.succ, ← hcoord 0, mul_div_mul_left _ _ c.ne_zero]

/-- A nonzero integer vector with all coordinates of absolute value at most `B` spans a projective
point of height at most `B`, whether or not its coordinates are coprime. -/
theorem projective_integer_height_le {n : ℕ} (z : IntPoint (n + 1)) (hz : z ≠ 0)
    {B : ℝ} (hbox : InBox z B) :
    (Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz)).mulHeight ≤ B := by
  classical
  obtain ⟨v, hv, hprim⟩ := Finset.extract_gcd z
    (show (Finset.univ : Finset (Fin (n + 1))).Nonempty from Finset.univ_nonempty)
  have he (j : Fin (n + 1)) : z j = Finset.univ.gcd z * v j := hv j (Finset.mem_univ j)
  have hg0 : Finset.univ.gcd z ≠ 0 := by
    intro h
    apply hz
    funext j
    simpa only [h, Pi.zero_apply, zero_mul] using he j
  have hv0 : v ≠ 0 := by
    intro h
    apply hz
    funext j
    simpa only [h, Pi.zero_apply, mul_zero] using he j
  have hg1 : (1 : ℝ) ≤ |((Finset.univ.gcd z : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hg0
  have hvbox : InBox v B := by
    intro j
    have hh := hbox j
    rw [he j, Int.cast_mul, abs_mul] at hh
    nlinarith [abs_nonneg (v j : ℝ)]
  have hproj : Projectivization.mk ℚ (rationalPoint z) (rationalPoint_ne_zero hz) =
      Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0) := by
    apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
    refine ⟨((Finset.univ.gcd z : ℤ) : ℚ), ?_⟩
    funext j
    change ((Finset.univ.gcd z : ℤ) : ℚ) * (v j : ℚ) = (z j : ℚ)
    rw [he j, Int.cast_mul]
  rw [hproj, projective_height_primitive v hv0 hprim]
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j => |v j|)
  have hmax : (⨆ j, |v j| : ℤ) = |v j| := by
    apply le_antisymm
    · exact ciSup_le hj
    · exact le_ciSup (Finite.bddAbove_range (fun k => |v k|)) j
  rw [hmax, Int.cast_abs]
  exact hvbox j

end
end CCDN
