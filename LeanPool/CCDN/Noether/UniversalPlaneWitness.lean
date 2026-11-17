/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.AffineLineLeading
public import LeanPool.CCDN.Algebra.CharZeroOrGT
public import LeanPool.CCDN.Noether.UniversalPlane
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanPool.CCDN.Determinant.ClosedFormIntegerMinor
import LeanPool.CCDN.Determinant.UniversalPlaneMinor
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Noether.ClosedFormParameterDegree
import LeanPool.CCDN.Noether.ShearNormalization

/-!
A nonzero universal minor of cubic parameter degree, over the original coefficient field; the
nonvanishing proof descends from an algebraic closure. The leading coefficient of a universal
plane section, evaluated by the highest homogeneous form in the first direction, detects loss of
the full outer degree.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma universalPlaneMap_map {K L σ : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlaneMap L σ (MvPolynomial.map φ f) =
      MvPolynomial.map (MvPolynomial.map φ) (universalPlaneMap K σ f) := by
  have he : (universalPlaneMap L σ).toRingHom.comp (MvPolynomial.map φ) =
      (MvPolynomial.map (MvPolynomial.map φ)).comp (universalPlaneMap K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [universalPlaneMap]
    · intro i
      simp [universalPlaneMap]
  exact RingHom.congr_fun he f

/-- The universal plane restriction commutes with applying a coefficient ring homomorphism. -/
lemma universalPlanePolynomial_map {K L σ : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlanePolynomial (MvPolynomial.map φ f) =
      bivariateMap (MvPolynomial.map φ) (universalPlanePolynomial f) := by
  rw [universalPlanePolynomial, universalPlaneMap_map, universalPlanePolynomial,
    bivariatePolynomialEquiv_map]

/-- A geometrically irreducible equation yields a nonzero polynomial
in the full affine-plane parameter ring, of degree at most (2*d^2-1)*d.
There are no smoothness or positioning hypotheses on the input equation. -/
theorem exists_universalPlane_minor_degree
    {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      ((closedFormCoefficientMatrix f.totalDegree
        (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 ∧
      (((closedFormCoefficientMatrix f.totalDegree
        (universalPlanePolynomial f)).submatrix rows cols).det).totalDegree ≤
          (2 * f.totalDegree ^ 2 - 1) * f.totalDegree := by
  classical
  let := Fintype.ofFinite σ
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  have hex := exists_universalPlane_minor
    (MvPolynomial.map φ f) hf (ht ▸ hpos) (ht ▸ hchar.map φ)
  rw [ht] at hex
  obtain ⟨rows, cols, hdet⟩ := hex
  refine ⟨rows, cols, ?_, ?_⟩
  · intro he
    rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero] at hdet
    exact hdet rfl
  · exact closedForm_minor_parameterDegree _ _ _ _
      (universalPlanePolynomial_coefficient_degree f) rows cols

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma universalPlanePolynomial_specialize_axis {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    Polynomial.map (Polynomial.evalRingHom 0)
      (bivariateMap (planeParameterEval (RingHom.id K) a b c) (universalPlanePolynomial f)) =
      affineLinePolynomial a b f := by
  rw [universalPlanePolynomial_specialize]
  have he : (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))).comp
      ((bivariatePolynomialEquiv K).toRingHom.comp
        (eval₂Hom (C.comp (RingHom.id K))
          (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1))) = affineLinePolynomial a b := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [affineLinePolynomial, bivariatePolynomialEquiv_C]
    · intro i
      simp [affineLinePolynomial, bivariatePolynomialEquiv_C,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

/-- The coefficient of x^d y^0, as a polynomial in all plane parameters. -/
def universalPlaneLeading {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) :
    MvPolynomial (PlaneParameters σ) K :=
  ((universalPlanePolynomial f).coeff f.totalDegree).coeff 0

private lemma universalPlaneLeading_specialize {K σ : Type*} [CommRing K]
    (a b c : σ → K) (f : MvPolynomial σ K) :
    planeParameterEval (RingHom.id K) a b c (universalPlaneLeading f) =
      eval b (homogeneousComponent f.totalDegree f) := by
  have h := congrArg (fun q : Polynomial K => q.coeff f.totalDegree)
    (universalPlanePolynomial_specialize_axis a b c f)
  rw [Polynomial.coeff_map, affineLinePolynomial_top_coefficient a b f _ le_rfl] at h
  change Polynomial.eval 0 ((bivariateMap (planeParameterEval (RingHom.id K) a b c)
    (universalPlanePolynomial f)).coeff f.totalDegree) = _ at h
  rw [← Polynomial.coeff_zero_eq_eval_zero, bivariateMap_coeff] at h
  exact h

private lemma universalPlaneLeading_map {K L σ : Type*} [Field K] [Field L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlaneLeading (MvPolynomial.map φ f) =
      MvPolynomial.map φ (universalPlaneLeading f) := by
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  simp only [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]

/-- Over an algebraically closed field, irreducibility and the characteristic bound
suffice for the leading polynomial to be nonzero. -/
theorem universalPlaneLeading_ne_zero_of_irreducible
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f) (hpos : 0 < f.totalDegree)
    (hchar : CharZeroOrGT K f.totalDegree) :
    universalPlaneLeading f ≠ 0 := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨a, b, _, hdir, _⟩ := exists_monic_smooth_hypersurface_coordinates f hf hpos hchar
  intro hz
  apply hdir
  rw [← universalPlaneLeading_specialize a b 0, hz, map_zero]

/-- Geometric irreducibility and the characteristic bound suffice for the
leading polynomial to be nonzero. -/
theorem universalPlaneLeading_ne_zero
    {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K f.totalDegree) :
    universalPlaneLeading f ≠ 0 := by
  classical
  let := Fintype.ofFinite σ
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  have hn := universalPlaneLeading_ne_zero_of_irreducible (MvPolynomial.map φ f) hf (ht ▸ hpos)
    (ht ▸ hchar.map φ)
  rw [universalPlaneLeading_map] at hn
  exact fun hz ↦ hn (by rw [hz, map_zero])

end
end CCDN
