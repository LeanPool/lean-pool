/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.CharZeroOrGT
public import LeanPool.CCDN.Noether.BivariateClosedForms
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import LeanPool.CCDN.Determinant.ResidueEliminantEvaluation
import LeanPool.CCDN.ForMathlib.Polynomial
import LeanPool.CCDN.Noether.DifferentialConstantRelation
import LeanPool.CCDN.Noether.DifferentialResidue
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
The monic irreducible closed-form criterion, in characteristic zero or in
characteristic larger than the displayed degree bounds. Separability, the
differential root extension and constant-residue descent are all constructed
from the polynomial and the degree bounds.

Constant residues in characteristic zero or large characteristic. The nonzero
annihilating relation and its degree bound are constructed by a Sylvester
resultant.

Extend a differential structure to an explicitly separable monic root
extension in any characteristic. The construction is the implicit-derivative
quotient construction from Mathlib's characteristic-zero instance, with the
nonvanishing derivative supplied by separability.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

/-- The differential structure on `AdjoinRoot f` extending the derivation of `K`, for a monic
irreducible separable `f`: the root `α` is sent to `-(f^D)(α) / f'(α)`, where `f^D` is `f` with
its coefficients differentiated. -/
@[reducible]
def separableAdjoinRootDifferential {K : Type*} [Field K] [Differential K]
    (f : K[X]) [Fact (Irreducible f)] [Fact f.Monic] (hsep : f.Separable) :
    Differential (AdjoinRoot f) where
  deriv := Derivation.liftOfSurjective (f := (AdjoinRoot.mk f).toIntAlgHom) AdjoinRoot.mk_surjective
    (d := implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
      - (aeval (AdjoinRoot.root f) (Differential.mapCoeffs f)) /
        (aeval (AdjoinRoot.root f) f.derivative)) (by
      rintro x hx
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv
      simp only [AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel]
      have hc : aeval (AdjoinRoot.root f) f = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simpa only [AdjoinRoot.aeval_eq] using hsep.aeval_derivative_ne_zero hc)

private theorem separableAdjoinRootDifferential_algebra {K : Type*} [Field K] [Differential K]
    (f : K[X]) [Fact (Irreducible f)] [Fact f.Monic] (hsep : f.Separable) :
    let := separableAdjoinRootDifferential f hsep
    DifferentialAlgebra K (AdjoinRoot f) := by
  dsimp only
  let := separableAdjoinRootDifferential f hsep
  refine { deriv_algebraMap := ?_ }
  intro a
  change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk f).toIntAlgHom (C a)) = _
  erw [Derivation.liftOfSurjective_apply (f := (AdjoinRoot.mk f).toIntAlgHom),
    implicitDeriv_C]
  rfl

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential

/-- The bounded-residue constant lemma used in the differential
irreducibility criterion. This is the needed irreducible case of Gao's
Lemma 2.4, proved directly by differentiating the constructed eliminant. -/
private theorem simple_root_ratio_mem_base_of_differential_constant
    {F L : Type*} [Field F] [IsAlgClosed F] [Field L] [Algebra F L]
    [Differential L]
    (hbase : ∀ a : F, (algebraMap F L a)′ = 0)
    (t β : L) (ht : t′ = 1) (f g : F[X][X])
    (hf : Irreducible (f.map (algebraMap F[X] (RatFunc F))))
    (hdeg : g.natDegree < f.natDegree) (D : ℕ)
    (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hchar : CharZeroOrGT L ((f.natDegree + (f.natDegree - 1)) * D))
    (hroot : (f.map (aeval t).toRingHom).eval β = 0)
    (hsimple : (f.map (aeval t).toRingHom).derivative.eval β ≠ 0)
    (hder : ((g.map (aeval t).toRingHom).eval β /
      (f.map (aeval t).toRingHom).derivative.eval β)′ = 0) :
    (g.map (aeval t).toRingHom).eval β /
      (f.map (aeval t).toRingHom).derivative.eval β ∈ (algebraMap F L).range := by
  by_cases hg : g = 0
  · simp only [hg, Polynomial.map_zero, eval_zero, zero_div]
    exact ⟨0, map_zero _⟩
  · exact differential_constant_mem_base_of_relation hbase t _ ht hder
      (residueEliminant f g) (residueEliminant_ne_zero f g hf hg hdeg)
      (hchar.mono (residueEliminant_natDegree_le f g D hfD hgD))
      (residueEliminant_eval_ratio_eq_zero t β f g hdeg hroot hsimple)

end
end CCDN

namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Differential
attribute [local instance] rationalDifferential

/-- An irreducible polynomial of degree below the characteristic is separable. -/
private lemma irreducible_separable_of_natDegree_lt_char
    {K : Type*} [Field K] (f : K[X]) (hf : Irreducible f)
    (hchar : CharZeroOrGT K f.natDegree) :
    f.Separable :=
  (separable_iff_derivative_ne_zero hf).mpr (derivative_ne_zero_of_natCast_natDegree_ne_zero
    (hchar.natCast_ne_zero hf.natDegree_pos.ne' le_rfl))

private lemma aeval_ratFunc_variable {F L : Type*} [Field F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    (a : F[X]) :
    aeval (algebraMap (RatFunc F) L RatFunc.X) a =
      algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) a) := by
  induction a using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | monomial n c =>
    simp only [aeval_monomial, RatFunc.algebraMap_monomial, map_mul, map_pow,
      ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]

/-- In a differential algebra over `F(t)`, the constants of `F` have derivative zero. -/
private lemma deriv_algebraMap_ratFunc_base {F L : Type*} [Field F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    [Differential L] [DifferentialAlgebra (RatFunc F) L] (a : F) :
    (algebraMap F L a)′ = 0 := by
  rw [IsScalarTower.algebraMap_apply F (RatFunc F) L, deriv_algebraMap]
  have ha : (algebraMap F (RatFunc F) a)′ = 0 := by
    change rationalDerivative (algebraMap F (RatFunc F) a) = 0
    rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F), rationalDerivative_polynomial]
    simp
  rw [ha, map_zero]

/-- In a differential algebra over `F(t)`, the image of `t` has derivative one. -/
private lemma deriv_algebraMap_ratFunc_X {F L : Type*} [Field F] [Field L]
    [Algebra (RatFunc F) L] [Differential L] [DifferentialAlgebra (RatFunc F) L] :
    (algebraMap (RatFunc F) L RatFunc.X)′ = 1 := by
  rw [deriv_algebraMap]
  have hX : (RatFunc.X : RatFunc F)′ = 1 := by
    change rationalDerivative RatFunc.X = 1
    rw [← RatFunc.algebraMap_X, rationalDerivative_polynomial, derivative_X, map_one]
  rw [hX, map_one]

/-- The closed-form equation persists over the rational function field. -/
private lemma bivariate_closed_form_map_ratFunc {F : Type*} [Field F] (f g h : F[X][X])
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    Differential.mapCoeffs (g.map (algebraMap F[X] (RatFunc F))) *
        f.map (algebraMap F[X] (RatFunc F)) -
      g.map (algebraMap F[X] (RatFunc F)) *
        Differential.mapCoeffs (f.map (algebraMap F[X] (RatFunc F))) =
      (h.map (algebraMap F[X] (RatFunc F))).derivative * f.map (algebraMap F[X] (RatFunc F)) -
        h.map (algebraMap F[X] (RatFunc F)) * (f.map (algebraMap F[X] (RatFunc F))).derivative := by
  rw [← bivariateCoefficientDerivative_map, ← bivariateCoefficientDerivative_map]
  simpa only [Polynomial.map_sub, Polynomial.map_mul, derivative_map] using
    congrArg (Polynomial.map (algebraMap F[X] (RatFunc F))) hclosed

/-- At a simple root over `F(t)`, the residue of a closed form lies in `F`. This is
the constant-residue descent, with the characteristic bounded by the residue
eliminant's degree. -/
private lemma closed_form_residue_mem_base {F L : Type*} [Field F] [IsAlgClosed F] [Field L]
    [Algebra F L] [Algebra (RatFunc F) L] [IsScalarTower F (RatFunc F) L]
    [Differential L] [DifferentialAlgebra (RatFunc F) L]
    (f g h : F[X][X]) (hf : Irreducible (f.map (algebraMap F[X] (RatFunc F))))
    (hgdeg : g.natDegree < f.natDegree) (D : ℕ)
    (hfD : ∀ i, (f.coeff i).natDegree ≤ D) (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hchar : CharZeroOrGT L ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative)
    (β : L) (hβ : aeval β (f.map (algebraMap F[X] (RatFunc F))) = 0)
    (hs : aeval β (f.map (algebraMap F[X] (RatFunc F))).derivative ≠ 0) :
    aeval β (g.map (algebraMap F[X] (RatFunc F))) /
      aeval β (f.map (algebraMap F[X] (RatFunc F))).derivative ∈ (algebraMap F L).range := by
  let φ := algebraMap F[X] (RatFunc F)
  let ψ := algebraMap (RatFunc F) L
  let t : L := ψ RatFunc.X
  have hmaps (q : F[X][X]) : q.map (aeval t).toRingHom = (q.map φ).map ψ := by
    ext i
    simp only [coeff_map]
    exact aeval_ratFunc_variable _
  have hclosedL : Differential.mapCoeffs ((g.map φ).map ψ) * (f.map φ).map ψ -
      (g.map φ).map ψ * Differential.mapCoeffs ((f.map φ).map ψ) =
      ((h.map φ).map ψ).derivative * (f.map φ).map ψ -
        (h.map φ).map ψ * ((f.map φ).map ψ).derivative := by
    dsimp only [ψ]
    simp only [differential_mapCoeffs_map, derivative_map]
    simpa only [Polynomial.map_sub, Polynomial.map_mul, derivative_map] using
      congrArg (Polynomial.map (algebraMap (RatFunc F) L))
        (bivariate_closed_form_map_ratFunc f g h hclosed)
  have hrootL : ((f.map φ).map ψ).eval β = 0 := by simpa only [eval_map, aeval_def] using hβ
  have hsL : ((f.map φ).map ψ).derivative.eval β ≠ 0 := by
    simpa only [derivative_map, eval_map, aeval_def] using hs
  have hder := closed_form_residue_deriv_eq_zero ((f.map φ).map ψ) ((g.map φ).map ψ)
    ((h.map φ).map ψ) β
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hrootL)
    (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hsL) hclosedL
  have hh := simple_root_ratio_mem_base_of_differential_constant
    deriv_algebraMap_ratFunc_base t β deriv_algebraMap_ratFunc_X f g hf hgdeg D hfD hgD hchar
    (by simpa only [hmaps] using hrootL) (by simpa only [hmaps] using hsL)
    (by simpa only [hmaps, aeval_def, Algebra.algebraMap_self, eval₂_id] using hder)
  simpa only [hmaps, ψ, derivative_map, eval_map, aeval_def] using hh

/-- The closed-form criterion over `F(t)`: a closed form within the degree bounds
is a constant multiple of the gradient. -/
private lemma ratFunc_closed_form_eq_gradient {F : Type*} [Field F] [IsAlgClosed F]
    (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree)
    (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D) (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hmchar : CharZeroOrGT F f.natDegree)
    (hchar : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    ∃ a : F,
      g.map (algebraMap F[X] (RatFunc F)) = C (algebraMap F (RatFunc F) a) *
        (f.map (algebraMap F[X] (RatFunc F))).derivative ∧
      h.map (algebraMap F[X] (RatFunc F)) = C (algebraMap F (RatFunc F) a) *
        Differential.mapCoeffs (f.map (algebraMap F[X] (RatFunc F))) := by
  let φ := algebraMap F[X] (RatFunc F)
  let fr := f.map φ
  have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
  have hfr : Irreducible fr := (hm.irreducible_iff_irreducible_map_fraction_map).mp hf
  have hfd : fr.natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  have hsep : fr.Separable := irreducible_separable_of_natDegree_lt_char fr hfr
    (hfd ▸ (hmchar.map (algebraMap F (RatFunc F))))
  let : Fact (Irreducible fr) := ⟨hfr⟩
  let : Fact fr.Monic := ⟨hm.map φ⟩
  let : Differential (AdjoinRoot fr) := separableAdjoinRootDifferential fr hsep
  have : DifferentialAlgebra (RatFunc F) (AdjoinRoot fr) :=
    separableAdjoinRootDifferential_algebra fr hsep
  let β : AdjoinRoot fr := AdjoinRoot.root fr
  have hβ : aeval β fr = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hs : aeval β fr.derivative ≠ 0 := hsep.aeval_derivative_ne_zero hβ
  have hres := closed_form_residue_mem_base f g h hfr hgdeg D hfD hgD
    (hchar.map (algebraMap F (AdjoinRoot fr))) hclosed β hβ hs
  have hdeg_lt (q : F[X][X]) (hq : q.natDegree < f.natDegree) : (q.map φ).degree < fr.degree := by
    rw [degree_eq_natDegree hfr.ne_zero]
    exact degree_le_natDegree.trans_lt
      (by exact_mod_cast (natDegree_map_eq_of_injective hinj q).trans_lt (hfd ▸ hq))
  exact closed_form_eq_constant_gradient_of_residue_mem_base fr (g.map φ) (h.map φ) hfr
    (hm.map φ) β hβ hs (hdeg_lt g hgdeg) (hdeg_lt h hhdeg)
    (bivariate_closed_form_map_ratFunc f g h hclosed) hres

/-- Over an algebraically closed field `F` of characteristic zero or larger than the
degree bounds, a monic irreducible bivariate equation has only constant-gradient closed
forms within the strict outer-variable degree bounds. -/
theorem bivariate_closed_form_eq_gradient
    {F : Type*} [Field F] [IsAlgClosed F]
    (f g h : F[X][X]) (hf : Irreducible f) (hm : f.Monic)
    (hgdeg : g.natDegree < f.natDegree) (hhdeg : h.natDegree < f.natDegree)
    (D : ℕ) (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hmchar : CharZeroOrGT F f.natDegree)
    (hchar : CharZeroOrGT F ((f.natDegree + (f.natDegree - 1)) * D))
    (hclosed : (bivariateCoefficientDerivative F) g * f -
        g * (bivariateCoefficientDerivative F) f = h.derivative * f - h * f.derivative) :
    ∃ a : F, g = C (C a) * f.derivative ∧
      h = C (C a) * (bivariateCoefficientDerivative F) f := by
  let φ := algebraMap F[X] (RatFunc F)
  have hinj : Function.Injective φ := RatFunc.algebraMap_injective F
  obtain ⟨a, ha, hb⟩ := ratFunc_closed_form_eq_gradient f g h hf hm hgdeg hhdeg D hfD hgD
    hmchar hchar hclosed
  refine ⟨a, Polynomial.map_injective φ hinj ?_, Polynomial.map_injective φ hinj ?_⟩
  · simpa only [φ, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, derivative_map] using ha
  · simpa only [φ, Polynomial.map_mul, Polynomial.map_C, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C, bivariateCoefficientDerivative_map] using hb

end
end CCDN
