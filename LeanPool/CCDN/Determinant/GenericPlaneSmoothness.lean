/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateTotalDegree
public import LeanPool.CCDN.Noether.GenericPlaneIrreducibility
import LeanPool.CCDN.Noether.ShearNormalization

/-! The generic plane f(x,y*z), with slopes in their rational function
field, has a smooth origin whenever the original equation does. Together with
ordinary irreducibility this proves geometric irreducibility of the generic
plane in the positioned coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The generic plane substitution as a map of multivariate polynomial rings. -/
def genericPlaneMap (K F σ : Type*) [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F] :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial (Fin 2) F :=
  aeval (fun i => Option.elim i (X 0)
    (fun j => C (algebraMap (MvPolynomial σ K) F (X j)) * X 1))

/-- The generic plane substitution `genericPlaneMap K F σ f` corresponds, as a bivariate polynomial
over `F`, to the generic plane equation `genericPlanePolynomial f` with its coefficients mapped into
`F`. -/
lemma genericPlaneMap_bivariate {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    [IsScalarTower K (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    bivariatePolynomialEquiv F (genericPlaneMap K F σ f) =
      bivariateMap (algebraMap (MvPolynomial σ K) F) (genericPlanePolynomial f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simpa [genericPlaneMap, genericPlanePolynomial, genericPlaneCoefficients,
      bivariateMap, bivariatePolynomialEquiv_C] using
      IsScalarTower.algebraMap_apply K (MvPolynomial σ K) F a
  | add f g hf hg =>
    simp only [map_add, hf, hg, genericPlanePolynomial, Polynomial.map_add]
  | mul_X f i hf =>
    cases i <;>
      simp [genericPlaneMap, genericPlanePolynomial, genericPlaneCoefficients,
        bivariateMap, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one,
        bivariatePolynomialEquiv_C] at hf ⊢
    all_goals simp only [hf, true_or]

/-- The generic plane section of `f` takes at the origin the value `f(0)`. -/
lemma genericPlaneMap_eval_zero {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    eval (0 : Fin 2 → F) (genericPlaneMap K F σ f) =
      algebraMap K F (eval (0 : Option σ → K) f) := by
  have he : (eval (0 : Fin 2 → F)).comp (genericPlaneMap K F σ).toRingHom =
      (algebraMap K F).comp (eval (0 : Option σ → K)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [genericPlaneMap]
    · intro i
      cases i <;> simp [genericPlaneMap]
  exact RingHom.congr_fun he f

/-- The derivative of the generic plane section of `f` in its first variable is the generic plane
section of the derivative of `f` in the distinguished variable `none`. -/
lemma genericPlaneMap_pderiv {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) :
    pderiv 0 (genericPlaneMap K F σ f) = genericPlaneMap K F σ (pderiv none f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp [genericPlaneMap]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    cases i <;> simp [genericPlaneMap, pderiv_X] at hf ⊢
    all_goals simp only [hf, true_or]

/-- Ordinary irreducibility over the rational function field in slopes. -/
theorem genericPlaneMap_irreducible
    {K F σ : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (MvPolynomial σ K) F]
    [IsScalarTower K (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : 0 < f.totalDegree) (hm : (optionEquivLeft K σ f).Monic)
    (hx : 0 < (optionEquivLeft K σ f).natDegree) :
    Irreducible (genericPlaneMap K F σ f) := by
  apply (MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv F)).mp
  rw [genericPlaneMap_bivariate]
  exact genericPlanePolynomial_irreducible_fraction_slopes f hf hd hm hx

end
end CCDN
