/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectiveLocalDeterminant
import LeanPool.CCDN.Height.ProjectiveZeroLocus

/-! Projective reduction of primitive integer points, and the affine
coordinate charts determined by their finite-field residue points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The projective space `ℙⁿ(𝔽_p)` over the prime field `𝔽_p`. -/
abbrev ProjectiveResidueSpace (n p : ℕ) [Fact p.Prime] :=
  Projectivization (ZMod p) (Fin (n + 1) → ZMod p)

/-- A primitive integer vector has nonzero reduction modulo every prime. -/
lemma primitive_mod_ne_zero {n p : ℕ} [Fact p.Prime]
    (z : IntPoint n) (hz : Finset.univ.gcd z = 1) :
    (fun i => (z i : ZMod p)) ≠ 0 := by
  intro h
  have hd : (p : ℤ) ∣ Finset.univ.gcd z := by
    apply Finset.dvd_gcd
    intro i _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun h i)
  rw [hz] at hd
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  exact hp.not_isUnit (isUnit_of_dvd_one hd)

/-- The reduction modulo `p` of a primitive integer point, as a point of `ℙⁿ(𝔽_p)`. -/
def primitiveProjectiveReduction {n p : ℕ} [Fact p.Prime]
    (z : IntPoint (n + 1)) (hz : Finset.univ.gcd z = 1) : ProjectiveResidueSpace n p :=
  Projectivization.mk (ZMod p) (fun i => (z i : ZMod p)) (primitive_mod_ne_zero z hz)

/-- A coordinate index at which the chosen representative of a point of `ℙ²(𝔽_p)` is nonzero. -/
def projectiveResiduePivot {p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace 2 p) :
    Fin 3 := Classical.choose (Function.ne_iff.mp r.rep_nonzero)

/-- The representative of `r` is nonzero at the coordinate `projectiveResiduePivot r`. -/
lemma projectiveResiduePivot_ne_zero {p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace 2 p) : r.rep (projectiveResiduePivot r) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp r.rep_nonzero)

/-- Integer lifts of the affine coordinates of a point `r` of `ℙ²(𝔽_p)` in the chart where its pivot
coordinate `projectiveResiduePivot r` is moved to the front and set to `1`. -/
def projectiveResidueChartLift {p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace 2 p) :
    Fin 2 → ℤ := fun j =>
  (r.rep (Equiv.swap 0 (projectiveResiduePivot r) j.succ) /
    r.rep (projectiveResiduePivot r)).val

/-- Modulo `p`, `projectiveResidueChartLift r` gives the coordinates of `r` divided by its pivot
coordinate, with the pivot coordinate swapped to the front. -/
lemma cast_projectiveResidueChartLift {p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace 2 p) (j : Fin 2) :
    (projectiveResidueChartLift r j : ZMod p) =
      r.rep (Equiv.swap 0 (projectiveResiduePivot r) j.succ) /
        r.rep (projectiveResiduePivot r) := by
  simp [projectiveResidueChartLift]

/-- Reduction determines both a unit coordinate and all affine congruences;
these are derived from equality of projective residue points. -/
theorem primitiveProjectiveReduction_chart {p : ℕ} [Fact p.Prime]
    (z : IntPoint 3) (hz : Finset.univ.gcd z = 1)
    (r : ProjectiveResidueSpace 2 p) (he : primitiveProjectiveReduction z hz = r) :
    IsCoprime (p : ℤ) (z (projectiveResiduePivot r)) ∧
      ∀ j : Fin 2, (p : ℤ) ∣ z (Equiv.swap 0 (projectiveResiduePivot r) j.succ) -
        projectiveResidueChartLift r j * z (projectiveResiduePivot r) := by
  have he' : Projectivization.mk (ZMod p) (fun i => (z i : ZMod p))
      (primitive_mod_ne_zero z hz) = Projectivization.mk (ZMod p) r.rep r.rep_nonzero :=
    he.trans r.mk_rep.symm
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp he'
  have hcoord (j : Fin 3) : (z j : ZMod p) = (u : ZMod p) * r.rep j :=
    (congrFun hu j).symm
  constructor
  · apply (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).irreducible.coprime_iff_not_dvd.mpr
    intro hd
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    rw [hcoord] at hh
    exact (mul_ne_zero u.ne_zero (projectiveResiduePivot_ne_zero r)) hh
  · intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub, Int.cast_mul, cast_projectiveResidueChartLift, hcoord, hcoord]
    field_simp [projectiveResiduePivot_ne_zero]
    ring

/-- Homogeneous equations remain zero at the projective reduction. -/
theorem primitiveProjectiveReduction_zero {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d)
    (z : IntPoint (n + 1)) (hz : Finset.univ.gcd z = 1) (hzf : eval z f = 0) :
    eval (primitiveProjectiveReduction (p := p) z hz).rep
      (map (Int.castRingHom (ZMod p)) f) = 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep
    (ZMod p) (fun i => (z i : ZMod p)) (primitive_mod_ne_zero z hz)
  change eval (Projectivization.mk (ZMod p) _ _).rep _ = 0
  rw [← hu]
  change eval ((u : ZMod p) • (fun i => (z i : ZMod p))) _ = 0
  rw [homogeneous_eval_smul (hf.map _)]
  have he : eval (fun i => (z i : ZMod p)) (map (Int.castRingHom (ZMod p)) f) = 0 := by
    have h := congrArg (Int.castRingHom (ZMod p)) hzf
    rw [map_eval, map_zero] at h
    exact h
  rw [he, mul_zero]

/-- The integer chart representative of a projective residue zero satisfies
the reduced affine equation. -/
theorem projectiveResidueChartLift_zero {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (r : ProjectiveResidueSpace 2 p)
    (hr : eval r.rep (map (Int.castRingHom (ZMod p)) f) = 0) :
    eval₂ (Int.castRingHom (ZMod p))
      (fun j => (projectiveResidueChartLift r j : ZMod p))
      (projectivePlaneChart (projectiveResiduePivot r) f) = 0 := by
  let k := projectiveResiduePivot r
  let a : Fin 2 → ZMod p := fun j => (projectiveResidueChartLift r j : ZMod p)
  have hv : Fin.cons 1 a = (r.rep k)⁻¹ • (r.rep ∘ Equiv.swap 0 k) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [projectiveResiduePivot_ne_zero, k]
    · simp [a, cast_projectiveResidueChartLift, div_eq_mul_inv, mul_comm, k]
  have hv' : (Fin.cons 1 a) ∘ Equiv.swap 0 k = (r.rep k)⁻¹ • r.rep := by
    rw [hv]
    funext j
    simp
  change eval₂ (Int.castRingHom (ZMod p)) a
    (affineChart 2 (rename (Equiv.swap 0 k) f)) = 0
  rw [eval₂_affineChart, eval₂_rename, hv', ← eval_map,
    homogeneous_eval_smul (hf.map _), hr, mul_zero]

end
end CCDN
