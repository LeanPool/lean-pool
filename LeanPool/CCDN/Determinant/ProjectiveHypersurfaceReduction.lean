/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceLocal
public import LeanPool.CCDN.Determinant.ProjectiveReduction
import LeanPool.CCDN.Height.ProjectiveZeroLocus

/-! Projective residue points determine unit charts and integral lifts
in arbitrary dimension. Their reduced affine equations vanish at those lifts. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A coordinate index at which the chosen representative of a point of `ℙⁿ⁺²(𝔽_p)` is nonzero. -/
def hypersurfaceResiduePivot {n p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace (n + 2) p) :
    Fin (n + 3) := Classical.choose (Function.ne_iff.mp r.rep_nonzero)

/-- The representative of `r` is nonzero at the coordinate `hypersurfaceResiduePivot r`. -/
lemma hypersurfaceResiduePivot_ne_zero {n p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace (n + 2) p) : r.rep (hypersurfaceResiduePivot r) ≠ 0 :=
  Classical.choose_spec (Function.ne_iff.mp r.rep_nonzero)

/-- Integer lifts of the affine coordinates of a point `r` of `ℙⁿ⁺²(𝔽_p)` in the chart where its
pivot coordinate `hypersurfaceResiduePivot r` is moved to the front and set to `1`. -/
def hypersurfaceResidueChartLift {n p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace (n + 2) p) :
    Fin (n + 2) → ℤ := fun j =>
  (r.rep (Equiv.swap 0 (hypersurfaceResiduePivot r) j.succ) /
    r.rep (hypersurfaceResiduePivot r)).val

/-- Modulo `p`, `hypersurfaceResidueChartLift r` gives the coordinates of `r` divided by its pivot
coordinate, with the pivot coordinate swapped to the front. -/
lemma cast_hypersurfaceResidueChartLift {n p : ℕ} [Fact p.Prime]
    (r : ProjectiveResidueSpace (n + 2) p) (j : Fin (n + 2)) :
    (hypersurfaceResidueChartLift r j : ZMod p) =
      r.rep (Equiv.swap 0 (hypersurfaceResiduePivot r) j.succ) /
        r.rep (hypersurfaceResiduePivot r) := by
  simp [hypersurfaceResidueChartLift]

/-- Reduction determines both a unit coordinate and all affine congruences;
these are derived from equality of projective residue points. -/
theorem primitiveProjectiveReduction_hypersurface_chart {n p : ℕ} [Fact p.Prime]
    (z : IntPoint (n + 3)) (hz : Finset.univ.gcd z = 1)
    (r : ProjectiveResidueSpace (n + 2) p) (he : primitiveProjectiveReduction z hz = r) :
    IsCoprime (p : ℤ) (z (hypersurfaceResiduePivot r)) ∧
      ∀ j : Fin (n + 2), (p : ℤ) ∣ z (Equiv.swap 0 (hypersurfaceResiduePivot r) j.succ) -
        hypersurfaceResidueChartLift r j * z (hypersurfaceResiduePivot r) := by
  have he' : Projectivization.mk (ZMod p) (fun i => (z i : ZMod p))
      (primitive_mod_ne_zero z hz) = Projectivization.mk (ZMod p) r.rep r.rep_nonzero :=
    he.trans r.mk_rep.symm
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp he'
  have hcoord (j : Fin (n + 3)) : (z j : ZMod p) = (u : ZMod p) * r.rep j :=
    (congrFun hu j).symm
  constructor
  · apply (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).irreducible.coprime_iff_not_dvd.mpr
    intro hd
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    rw [hcoord] at hh
    exact (mul_ne_zero u.ne_zero (hypersurfaceResiduePivot_ne_zero r)) hh
  · intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [Int.cast_sub, Int.cast_mul, cast_hypersurfaceResidueChartLift, hcoord, hcoord]
    field_simp [hypersurfaceResiduePivot_ne_zero]
    ring

/-- Evaluating the affine chart of a form `f` at `a` is evaluating `f` at `(1, a)`. -/
lemma eval₂_hypersurfaceAffineChart {R : Type*} [CommRing R] {n : ℕ} (φ : ℤ →+* R)
    (a : Fin (n + 2) → R) (f : MvPolynomial (Fin (n + 3)) ℤ) :
    eval₂ φ a (affineChart (n + 2) f) = eval₂ φ (Fin.cons 1 a) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp only [affineChart, eval₂Hom_C, eval₂_C]
  | add f g hf hg => simp only [map_add, eval₂_add, hf, hg]
  | mul_X f j hf =>
    rw [map_mul, eval₂_mul, eval₂_mul, hf]
    congr 1
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [affineChart]

/-- The integer chart representative of a projective residue zero satisfies
the reduced affine equation. -/
theorem hypersurfaceResidueChartLift_zero {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (r : ProjectiveResidueSpace (n + 2) p)
    (hr : eval r.rep (map (Int.castRingHom (ZMod p)) f) = 0) :
    eval₂ (Int.castRingHom (ZMod p))
      (fun j => (hypersurfaceResidueChartLift r j : ZMod p))
      (projectiveHypersurfaceChart (hypersurfaceResiduePivot r) f) = 0 := by
  let k := hypersurfaceResiduePivot r
  let a : Fin (n + 2) → ZMod p := fun j => (hypersurfaceResidueChartLift r j : ZMod p)
  have hv : Fin.cons 1 a = (r.rep k)⁻¹ • (r.rep ∘ Equiv.swap 0 k) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [hypersurfaceResiduePivot_ne_zero, k]
    · simp [a, cast_hypersurfaceResidueChartLift, div_eq_mul_inv, mul_comm, k]
  have hv' : (Fin.cons 1 a) ∘ Equiv.swap 0 k = (r.rep k)⁻¹ • r.rep := by
    rw [hv]
    funext j
    simp
  change eval₂ (Int.castRingHom (ZMod p)) a
    (affineChart (n + 2) (rename (Equiv.swap 0 k) f)) = 0
  rw [eval₂_hypersurfaceAffineChart, eval₂_rename, hv', ← eval_map,
    homogeneous_eval_smul (hf.map _), hr, mul_zero]

end
end CCDN
