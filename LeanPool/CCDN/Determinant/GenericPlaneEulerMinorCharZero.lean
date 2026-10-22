/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfacePositioning
public import LeanPool.CCDN.Noether.EulerPairBasis
import LeanPool.CCDN.Determinant.GenericPlaneMinor
import LeanPool.CCDN.Noether.EulerPairBasisValues
import LeanPool.CCDN.Noether.EulerPairSpecialization
import LeanPool.CCDN.Noether.ShearNormalization

/-! Nonzero Euler minors in smooth generic-plane families. The order is
exactly d²−1, and the smooth-point argument constructs the geometric
irreducibility needed by the characteristic-zero closed-form theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix MvPolynomial

private theorem exists_euler_minor_of_smooth_plane_point_charZero
    {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = k + 2) :
    (eulerClosedFormCoefficientMatrix k (bivariatePolynomialEquiv K f)).HasNonzeroMinor
      ((k + 2) ^ 2 - 1) := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  let g := bivariateMap φ (bivariatePolynomialEquiv K f)
  have hgi : Irreducible g := by
    dsimp only [g]
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)]
    exact irreducible_map_of_smooth_plane_point f hf z j hz hj
  have hgm : g.Monic := bivariateMap_monic φ hm
  have hgd : g.natDegree = k + 2 := by
    rw [bivariateMap_natDegree_of_monic φ hm, hdeg]
  obtain ⟨a, c, hdet⟩ := exists_eulerClosedForm_nonzero_minor k g hgi
    1 one_ne_zero (by simpa using hgm.leadingCoeff) hgd
  refine ⟨a, c, ?_⟩
  intro he
  apply hdet
  rw [← eulerClosedForm_minor_map, he, map_zero]

private theorem exists_genericPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = k + 2)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    (eulerClosedFormCoefficientMatrix k (genericPlanePolynomial f)).HasNonzeroMinor
      ((k + 2) ^ 2 - 1) := by
  obtain ⟨hgi, hgz, hgs, hgm, hgd⟩ := genericPlaneMap_smooth_monic (k + 2) (by omega) f hf hm
    hdeg hz hs
  obtain ⟨a, c, hdet⟩ := exists_euler_minor_of_smooth_plane_point_charZero
    k _ hgi 0 0 hgz hgs hgm hgd
  refine ⟨a, c, ?_⟩
  intro he
  apply hdet
  rw [genericPlaneMap_bivariate, ← eulerClosedForm_minor_map, he, map_zero]

/-- Over an algebraically closed field of characteristic zero, every irreducible polynomial `f` of
degree `k + 2` admits an affine coordinate change, given by `a` and `b` with `b none ≠ 0` and the
top-degree form of `f` nonvanishing at `b`, after which the Euler closed-form coefficient matrix of
the generic plane section has a nonzero minor of order `(k + 2) ^ 2 - 1`. -/
theorem exists_positioned_genericPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Finite σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : f.totalDegree = k + 2) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (eulerClosedFormCoefficientMatrix k
        (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).HasNonzeroMinor
          ((k + 2) ^ 2 - 1) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨a, b, hb, hdir, hg⟩ :=
    exists_monic_smooth_hypersurface_coordinates f hf (by omega) (.of_charZero _)
  exact ⟨a, b, hb, hdir, exists_genericPlane_euler_minor_charZero k _ hg.irreducible hg.monic
    (hd ▸ hg.natDegree_eq) hg.eval_zero hg.pderiv_ne_zero⟩

end
end CCDN
