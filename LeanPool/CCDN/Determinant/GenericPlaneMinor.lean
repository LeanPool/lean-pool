/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.CharZeroOrGT
public import LeanPool.CCDN.Determinant.GenericPlaneSmoothness
public import LeanPool.CCDN.ForMathlib.Matrix
import LeanPool.CCDN.Determinant.ClosedFormIntegerMinor
import LeanPool.CCDN.Determinant.PlaneMultiplicity
import LeanPool.CCDN.Noether.ClosedFormScaling
import LeanPool.CCDN.Noether.FormalBranchBaseChange
import LeanPool.CCDN.Noether.ShearNormalization

/-!
A nonzero polynomial determinant in the generic slope parameters. For a
positioned irreducible equation with a smooth origin, the minor is constructed
over the parameter polynomial ring, by descent from its fraction field.

A smooth rational point supplies a nonzero closed-form coefficient minor
for an irreducible plane equation in characteristic zero or large characteristic.
The base field need not be algebraically closed.

A smooth rational point on an irreducible plane curve implies geometric
irreducibility. The proof uses the faithful formal branch, extends its
coordinate algebra to every field, and identifies the resulting prime ideal
in the polynomial ring over that field.
-/

@[expose] public section
namespace CCDN
noncomputable section
open scoped TensorProduct

/-- An irreducible plane equation with a smooth rational point remains
irreducible over every extension field. The base field need not be perfect. -/
theorem irreducible_map_of_smooth_plane_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    Irreducible (MvPolynomial.map (algebraMap K L) f) := by
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  let J : Ideal (L ⊗[K] MvPolynomial (Fin 2) K) :=
    I.map Algebra.TensorProduct.includeRight
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L
    (MvPolynomial (Fin 2) K) L I
  have : IsDomain (L ⊗[K] (MvPolynomial (Fin 2) K ⧸ I)) :=
    isDomain_tensor_plane_quotient_of_smooth_point f hf z j hz hj
  have : IsDomain ((L ⊗[K] MvPolynomial (Fin 2) K) ⧸ J) :=
    Function.Injective.isDomain e.symm e.symm.injective
  have : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  let E := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) K L
  have hmap : J.map E = Ideal.span {MvPolynomial.map (algebraMap K L) f} := by
    simp only [J, I, Ideal.map_span, Set.image_singleton]
    congr 1
    change {E (1 ⊗ₜ[K] f)} = _
    simp [E]
  have hp : (Ideal.span {MvPolynomial.map (algebraMap K L) f}).IsPrime := by
    rw [← hmap]
    infer_instance
  have hne : MvPolynomial.map (algebraMap K L) f ≠ 0 := by
    exact (map_ne_zero_iff _ (MvPolynomial.map_injective _ (algebraMap K L).injective)).mpr
      hf.ne_zero
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial Matrix

/-- A nonzero minor over the original coefficient field, obtained by proving
geometric irreducibility from the smooth point. -/
private theorem exists_closedForm_minor_of_smooth_plane_point
    {K : Type*} [Field K]
    (d : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = d)
    (htotal : f.totalDegree ≤ d) (hchar : CharZeroOrGT K (2 * d ^ 2)) :
    (closedFormCoefficientMatrix d (bivariatePolynomialEquiv K f)).HasNonzeroMinor
      (2 * d ^ 2 - 1) := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  let g := bivariateMap φ (bivariatePolynomialEquiv K f)
  have hgi : Irreducible g := by
    dsimp only [g]
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)]
    exact irreducible_map_of_smooth_plane_point f hf z j hz hj
  have hgm : g.Monic := bivariateMap_monic φ hm
  have hgd : g.degree = d := by
    rw [degree_eq_natDegree hgm.ne_zero, bivariateMap_natDegree_of_monic φ hm, hdeg]
  have hgt : bivariateTotalDegree g ≤ d := by
    apply (bivariateTotalDegree_map_le φ _).trans
    simpa only [bivariateTotalDegree, AlgEquiv.symm_apply_apply] using htotal
  have hr := closedForm_coefficient_rank_lower d g hgi hgm hgd d hgt
    ((hchar.map φ).mono (by rw [sq, mul_assoc]))
  obtain ⟨a, c, hdet⟩ := Matrix.hasNonzeroMinor_of_le_rank
    (closedFormCoefficientMatrix d g) (r := 2 * d ^ 2 - 1) (by omega)
  refine ⟨a, c, ?_⟩
  intro he
  apply hdet
  rw [← closedForm_minor_map, he, map_zero]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma genericPlaneMap_totalDegree_le {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    (genericPlaneMap K F σ f).totalDegree ≤ f.totalDegree := by
  apply linear_eval₂_totalDegree_le _ _ _ f
  intro i
  cases i with
  | none => simp
  | some i => exact (totalDegree_mul _ _).trans (by simp)

/-- Over the fraction field of the slope ring, the generic plane of a positioned irreducible
equation with a smooth origin is irreducible, smooth at the origin in the first coordinate,
and monic of the same outer degree. -/
lemma genericPlaneMap_smooth_monic {K σ : Type*} [Field K]
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = d)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    Irreducible (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f) ∧
      eval 0 (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f) = 0 ∧
      eval 0 (pderiv 0 (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)) ≠ 0 ∧
      (bivariatePolynomialEquiv _
        (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)).Monic ∧
      (bivariatePolynomialEquiv _
        (genericPlaneMap K (FractionRing (MvPolynomial σ K)) σ f)).natDegree = d := by
  let F := FractionRing (MvPolynomial σ K)
  let φ : MvPolynomial σ K →+* F := algebraMap (MvPolynomial σ K) F
  have hx : 0 < (optionEquivLeft K σ f).natDegree := hdeg ▸ hd
  have hpos : 0 < f.totalDegree := by
    rw [natDegree_optionEquivLeft] at hx
    exact hx.trans_le (degreeOf_le_totalDegree f none)
  refine ⟨genericPlaneMap_irreducible f hf hpos hm hx, ?_, ?_, ?_, ?_⟩
  · rw [genericPlaneMap_eval_zero, hz, map_zero]
  · rw [genericPlaneMap_pderiv, genericPlaneMap_eval_zero]
    exact (map_ne_zero (algebraMap K F)).mpr hs
  · rw [genericPlaneMap_bivariate]
    exact bivariateMap_monic φ (genericPlanePolynomial_monic f hm)
  · rw [genericPlaneMap_bivariate, bivariateMap_natDegree_of_monic φ
      (genericPlanePolynomial_monic f hm), genericPlanePolynomial_natDegree f hm, hdeg]

/-- In characteristic zero or greater than 2*d^2, a positioned irreducible hypersurface
with a smooth origin supplies a nonzero minor polynomial in its plane slopes. -/
theorem exists_genericPlane_minor
    {K σ : Type*} [Field K]
    (d : ℕ) (hd : 0 < d) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = d)
    (htotal : f.totalDegree ≤ d) (hchar : CharZeroOrGT K (2 * d ^ 2))
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    (closedFormCoefficientMatrix d (genericPlanePolynomial f)).HasNonzeroMinor
      (2 * d ^ 2 - 1) := by
  let F := FractionRing (MvPolynomial σ K)
  obtain ⟨hgi, hgz, hgs, hgm, hgd⟩ := genericPlaneMap_smooth_monic d hd f hf hm hdeg hz hs
  obtain ⟨a, c, hdet⟩ := exists_closedForm_minor_of_smooth_plane_point d _ hgi 0 0
    hgz hgs hgm hgd ((genericPlaneMap_totalDegree_le f).trans htotal)
    (hchar.map (algebraMap K F))
  refine ⟨a, c, fun he ↦ hdet ?_⟩
  rw [genericPlaneMap_bivariate, ← closedForm_minor_map, he, map_zero]

end
end CCDN
