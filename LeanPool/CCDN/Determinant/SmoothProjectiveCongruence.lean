/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.ProjectiveHypersurfaceLocal
import LeanPool.CCDN.Determinant.BlockDeterminant
import LeanPool.CCDN.Determinant.PlaneMultiplicitySmooth

/-!
Smooth projective congruence classes give simultaneous divisors
for homogeneous evaluation matrices.

At a nonsingular reduced point the translated hypersurface
equation has multiplicity one.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- At a nonsingular reduced point the translated equation has
multiplicity one. -/
private theorem smooth_hypersurface_origin_order {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    map (Int.castRingHom (ZMod p)) (originShift a f) ∈ idealOfVars σ (ZMod p) ^ 1 ∧
    homogeneousComponent 1 (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0 := by
  have hf : map (Int.castRingHom (ZMod p)) f ≠ 0 := by
    intro hz
    obtain ⟨j, hj⟩ := hs
    exact hj (by simp [hz])
  obtain ⟨μ, hμ, _, hpow, hcomp⟩ := exists_hypersurface_reduction_multiplicity f a hf ha
  have he : μ = 1 := by
    rw [originShift_map] at hpow
    exact origin_order_eq_one_of_smooth _ _ hμ hpow hs
  subst μ
  exact ⟨hpow, hcomp⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- If integer zeros `z i` of a homogeneous `f` all have their `k`-th coordinate prime to `p` and
reduce, in the affine chart `k`, to the same nonsingular point `a` of `f mod p`, then for forms `F
j` of a common degree `M` the power `p ^ hypersurfaceMultiplicityExponent (n + 1) 1 s` divides the
gcd of the maximal minors of the evaluation matrix `(F j (z i))`. -/
theorem smooth_projective_hypersurface_congruence_minorGcd {p n s N d M : ℕ}
    [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (k : Fin (n + 3)) (a : Fin (n + 2) → ℤ)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p))
      (projectiveHypersurfaceChart k f) = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p)) (pderiv j
      (map (Int.castRingHom (ZMod p)) (projectiveHypersurfaceChart k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  obtain ⟨hpow, hcomp⟩ := smooth_hypersurface_origin_order
    (projectiveHypersurfaceChart k f) a ha hs
  rw [minorGcd_eq_gcd_plucker]
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  exact projective_hypersurface_local_det_divisibility f hf _
    (fun j => hF _) z k a hpow hcomp hunit hres hz

end
end CCDN
