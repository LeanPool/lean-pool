/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.RationalPlaneAssembly
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Plane.NonabsolutePlaneCount
import LeanPool.CCDN.Plane.StepanovBound
import LeanPool.CCDN.Plane.StepanovDimension
import LeanPool.CCDN.Plane.StepanovParameters

/-!
Sharp finite-field counting and the complete rational-plane
integral-point bound. The finite-field proof uses the constructed Stepanov
auxiliary and retains an explicit absolute error constant.

The complete rational plane reduction to sharp finite-field counting.
The non-absolutely-irreducible case is bounded by d².

The explicit real-valued error term for the integer Stepanov parameters.

The affine residue points of an integer plane equation are the
zeros of its reduction.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma planeResidue_card_eq_zero_card (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Nat.card (PlaneResidue f p) =
      Nat.card {x : Fin 2 → ZMod p //
        eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  simp only [eval_map]

end
end CCDN

namespace CCDN

/-- The Stepanov count `t N ≤ d (D + p A) + d (d - 1) N` gives the plane-curve bound
`t ≤ p + 161 d² √p`; see `planeResidueConstant` for the derivation of `161`. -/
lemma stepanov_real_bound (d p A D N t : ℕ) (hd : 0 < d)
    (hp : stepanovThreshold d < p) (hD : d * D < p)
    (hN : N + 4 * d ^ 2 = d * A) (hNpos : 0 < N)
    (hpx : p < (d * A + d) ^ 2)
    (hcount : t * N ≤ d * (D + p * A) + d * (d - 1) * N) :
    (t : ℝ) ≤ p + planeResidueConstant * (d : ℝ) ^ 2 * Real.sqrt p := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  have hdle : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
  unfold stepanovThreshold at hp
  have hpR : 27 * (d : ℝ) ^ 4 < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by nlinarith only [hpR, pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) 4]
  let s := Real.sqrt (p : ℝ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = p := Real.sq_sqrt (le_of_lt hp0)
  have hs1 : 1 ≤ s := by nlinarith only [hs0, hs2, hpR, hd2]
  have hNR : (N : ℝ) + 4 * (d : ℝ) ^ 2 = (d : ℝ) * A := by exact_mod_cast hN
  have hpxR : (p : ℝ) < ((d : ℝ) * A + d) ^ 2 := by exact_mod_cast hpx
  have hxp0 : (0 : ℝ) ≤ (d : ℝ) * A + d := by positivity
  have hsnear : s < (N : ℝ) + 5 * (d : ℝ) ^ 2 := by
    have hh : s < (d : ℝ) * A + d := by nlinarith only [hpxR, hs2, hs0, hxp0]
    nlinarith only [hh, hNR, hdle]
  have hsN : s < 32 * (N : ℝ) := by
    by_contra! hn
    have hh : 31 * s < 160 * (d : ℝ) ^ 2 := by linarith only [hn, hsnear]
    have hsq := mul_self_lt_mul_self (by positivity : 0 ≤ 31 * s) hh
    nlinarith only [hsq, hpR, hs2]
  have hsp : (p : ℝ) ≤ 32 * N * s := by
    have hh := mul_le_mul_of_nonneg_right (le_of_lt hsN) hs0
    nlinarith only [hh, hs2]
  have hcoef : 4 * (d : ℝ) ^ 2 + 1 ≤ 5 * (d : ℝ) ^ 2 := by linarith only [hd2]
  have hprod1 := mul_le_mul_of_nonneg_right hcoef (le_of_lt hp0)
  have hprod2 := mul_le_mul_of_nonneg_left hsp (by positivity : 0 ≤ 5 * (d : ℝ) ^ 2)
  have hsmall := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ (d : ℝ) ^ 2 * N)
  have hsub : d * (d - 1) ≤ d ^ 2 := by nlinarith only [Nat.sub_le d 1]
  have hc : t * N ≤ d * D + p * (d * A) + d ^ 2 * N := by
    have hh := Nat.mul_le_mul_right N hsub
    nlinarith only [hcount, hh]
  have hcR : (t : ℝ) * N ≤ (d : ℝ) * D + p * ((d : ℝ) * A) + (d : ℝ) ^ 2 * N := by
    exact_mod_cast hc
  have hDR : (d : ℝ) * D ≤ p := by exact_mod_cast hD.le
  rw [← hNR] at hcR
  have hfin : (t : ℝ) * N ≤ (p + 161 * (d : ℝ) ^ 2 * s) * N := by
    nlinarith only [hcR, hDR, hprod1, hprod2, hsmall]
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hNpos : (0 : ℝ) < N)).mp hfin

end CCDN

namespace CCDN
noncomputable section
open MvPolynomial Real

/-- Every box on a rational irreducible plane curve which splits over a field
extension has at most d² integer points, independently of the radius. -/
private theorem count_nonabsolute_plane_le {F : Type*} [Field F] [CharZero F]
    (f : MvPolynomial (Fin 2) ℚ) (hf : Irreducible f) (hd : 0 < f.totalDegree)
    (hred : ¬ Irreducible (MvPolynomial.map (algebraMap ℚ F) f)) (B : ℝ) :
    count (zeroLocus f) B ≤ f.totalDegree ^ 2 := by
  classical
  let S := integralPoints (zeroLocus f) B
  let z : S → Fin 2 → ℚ := fun i => rationalPoint i.val
  have hi : Function.Injective z := by
    intro i j he
    apply Subtype.ext
    funext k
    exact Int.cast_injective (congrFun he k)
  have hz : ∀ i, eval (z i) f = 0 := fun i => (mem_integralPoints.mp i.property).2
  have h := nonabsolute_plane_points_card_le f hf hd hred z hi hz
  simpa only [Fintype.card_coe, S, count] using h

/-- The exact PlaneCurveBound target follows from the sharp finite-field
estimate. The rational nonabsolute case is covered by the d² bound. -/
private theorem planeCurveBound_of_residue_bound {C : ℝ}
    (hC : 0 ≤ C) (hres : PlaneResidueBound C) : PlaneCurveBound := by
  let K := 2 * Real.exp 1 * affineNonzeroConstantBound C
  have hK : 0 < K := mul_pos (by positivity) (affineNonzeroConstantBound_pos C)
  refine ⟨K + 1, by linarith, ?_⟩
  intro f hf hd B hB
  have hG : 0 ≤ curveBound f.totalDegree B := by
    have h := degree_four_le_curveBound hd hB
    exact (by positivity : (0 : ℝ) ≤ (f.totalDegree : ℝ) ^ 4).trans h
  by_cases habs : AbsolutelyIrreducibleRat f
  · exact (count_rational_plane_of_residue_bound f habs hd hB hC hres).trans
      (mul_le_mul_of_nonneg_right (by linarith) hG)
  · have hh := count_nonabsolute_plane_le f hf hd habs B
    have ht : (count (zeroLocus f) B : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by exact_mod_cast hh
    have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
    have hpow : (f.totalDegree : ℝ) ^ 2 ≤ (f.totalDegree : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((f.totalDegree : ℝ) ^ 2 - 1)]
    have hb := ht.trans (hpow.trans (degree_four_le_curveBound hd hB))
    exact hb.trans (by nlinarith)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- An irreducible plane equation over the prime field has at most
`p + planeResidueConstant * d² * √p` rational points when `p > stepanovThreshold d`. -/
theorem plane_finite_field_card_bound {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin 2) (ZMod p)) (hf : Irreducible f)
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p)
    (z : ι → Fin 2 → ZMod p) (hz : Function.Injective z)
    (hzero : ∀ i, eval (z i) f = 0) :
    (Fintype.card ι : ℝ) ≤ p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p := by
  classical
  have hd := totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit
  have hp : 27 * f.totalDegree ^ 4 < p := by exact_mod_cast hsize
  have hchar : f.totalDegree < p := by
    have h1 := Nat.le_mul_self f.totalDegree
    have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
    nlinarith only [hp, h1, h2]
  obtain ⟨A, D, N, hA, hD, hDp, hNp, hN, hNpos, hx, hy, hpx⟩ :=
    exists_stepanov_integer_parameters f.totalDegree p hd hp
  have hdim := stepanov_hilbert_dimension_inequality f hf.ne_zero p A D N hd hp hA hD hx hy hN hNpos
  have hc := plane_stepanov_bound p f hf hd hchar z hz hzero hDp hNp hdim
  exact stepanov_real_bound f.totalDegree p A D N (Fintype.card ι) hd hp hDp hN hNpos hpx hc

/-- The sharp finite-field hypothesis used by the affine determinant argument
holds with the absolute constant `planeResidueConstant = 161`. -/
theorem planeResidueBound : PlaneResidueBound planeResidueConstant := by
  intro f _hd p hp hsize hir
  let : Fact p.Prime := ⟨hp⟩
  classical
  let q := MvPolynomial.map (Int.castRingHom (ZMod p)) f
  have hqd : q.totalDegree ≤ f.totalDegree := totalDegree_map_le _ _
  have hs : stepanovThreshold (q.totalDegree : ℝ) < (p : ℝ) := by
    apply lt_of_le_of_lt _ hsize
    gcongr
  let S := {x : Fin 2 → ZMod p // eval x q = 0}
  have hh := plane_finite_field_card_bound p q hir hs (fun x : S => x.val)
    Subtype.val_injective (fun x => x.property)
  rw [planeResidue_card_eq_zero_card, Nat.card_eq_fintype_card]
  apply hh.trans
  gcongr
  exact planeResidueConstant_pos.le

/-- The full coefficient-uniform rational-plane integral-point bound. -/
theorem planeCurveBound : PlaneCurveBound :=
  planeCurveBound_of_residue_bound planeResidueConstant_pos.le planeResidueBound

end
end CCDN
