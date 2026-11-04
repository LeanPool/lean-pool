/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Height.ScaledHypersurfaceHeight
import LeanPool.CCDN.Plane.Bezout

/-! A logarithm-free plane-curve estimate in terms of the
geometric bad-prime factor. Uniformly bounded bad-prime factors therefore
give a coefficient-independent logarithm-free counting theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem affine_plane_expression_le_bad_prime {d : ℕ} (hd : 0 < d)
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineAuxiliaryDegreeExpression 0 d B L b ≤
      (d : ℝ) ^ 3 * (b + 2) * B ^ (1 / (d : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hdR
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have hlogL := Real.log_nonneg hL
  have hpow : 1 ≤ B ^ (1 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hden : 1 ≤ L ^ (1 / ((d : ℝ) * d)) := Real.one_le_rpow hL (by positivity)
  have hmin : 0 ≤ min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) :=
    le_min (by positivity) (by positivity)
  have hfrac :
      (d : ℝ) * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
        B ^ (1 / (d : ℝ)) / L ^ (1 / ((d : ℝ) * d)) ≤
      (d : ℝ) ^ 3 * b * B ^ (1 / (d : ℝ)) := by
    calc
      _ ≤ (d : ℝ) *
          min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
          B ^ (1 / (d : ℝ)) := div_le_self (by positivity) hden
      _ ≤ (d : ℝ) * ((d : ℝ) ^ 2 * b) * B ^ (1 / (d : ℝ)) := by
        gcongr
        exact min_le_right _ _
      _ = _ := by ring
  have hlog : Real.log B ≤ (d : ℝ) * B ^ (1 / (d : ℝ)) :=
    log_le_dimension_root hd hB0
  have hdcube : (d : ℝ) ≤ (d : ℝ) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hdR (by omega : 1 ≤ 3)
  have hlog' := hlog.trans (mul_le_mul_of_nonneg_right hdcube (by positivity))
  have hcube := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (d : ℝ) ^ 3 by positivity)
  unfold affineAuxiliaryDegreeExpression
  norm_num only [Nat.cast_zero, zero_add, div_one, Real.rpow_one, Real.rpow_zero,
    one_mul, sub_self, mul_one, show (2 - 1 : ℝ) = 1 by norm_num,
    show (4 - 1 : ℝ) = 3 by norm_num, Real.rpow_natCast, Real.rpow_ofNat]
  nlinarith

/-- The plane auxiliary and Bezout prove the bad-prime bound for
integer zeros. -/
theorem affine_plane_count_bad_prime
    (f : MvPolynomial (Fin 2) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      affineHypersurfaceAuxiliaryConstant 0 * (f.totalDegree : ℝ) ^ 4 *
        (hypersurfaceBadPrimeFactor f + 2) * B ^ (1 / (f.totalDegree : ℝ)) := by
  obtain ⟨g, ⟨_, hfg, hgz⟩, hgdeg⟩ :=
    affine_hypersurface_auxiliary f hprim (hprim.irreducible_of_rational_map hir) hd hB
  have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
  have hdegree := hgdeg.trans (mul_le_mul_of_nonneg_left
    (affine_plane_expression_le_bad_prime hd hB (leading_height_one_le f hf0)
      (hypersurfaceBadPrimeFactor_nonneg f)) (affineHypersurfaceAuxiliaryConstant_pos 0).le)
  have hfgQ : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g :=
    fun h => hfg (hprim.rational_map_dvd_iff.mp h)
  apply integer_zero_count_le_of_family_bound
  intro t z hinj hzf hbox
  have hzQ : Function.Injective (fun i => rationalPoint (z i)) := by
    intro i j h
    apply hinj
    funext k
    exact Int.cast_injective (congrFun h k)
  have hmapzero (p : MvPolynomial (Fin 2) ℤ) (i : Fin t) (hp : eval (z i) p = 0) :
      eval (rationalPoint (z i)) (map (Int.castRingHom ℚ) p) = 0 := by
    have hh := congrArg (Int.castRingHom ℚ) hp
    rw [map_eval, map_zero] at hh
    exact hh
  have hbezout := plane_common_zeros_card_le (map (Int.castRingHom ℚ) f)
    (map (Int.castRingHom ℚ) g) hir hfgQ (fun i => rationalPoint (z i)) hzQ
    (fun i => hmapzero f i (hzf i)) (fun i => hmapzero g i (hgz (z i) (hbox i) (hzf i)))
  rw [Fintype.card_fin, rational_map_totalDegree, rational_map_totalDegree] at hbezout
  have hcount : (t : ℝ) ≤ (f.totalDegree : ℝ) * g.totalDegree := by exact_mod_cast hbezout
  have hm := mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg (α := ℝ) f.totalDegree)
  apply hcount.trans
  convert hm using 1
  ring

end
end CCDN
