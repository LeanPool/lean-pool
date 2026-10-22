/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
public import LeanPool.CCDN.Height.PrimitiveIntegerPolynomial
import LeanPool.CCDN.Algebra.PrimitiveNormalization
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import LeanPool.CCDN.Surface.TopFormIrreducibility

/-! Bad reduction of an affine equation is contained in bad reduction of
 its top homogeneous form. This includes degree loss in the defined predicate. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If the top form has good geometric reduction, the original affine
 equation keeps its degree and has good geometric reduction as well. -/
private theorem hypersurfaceBadReduction_imp_top_homogeneousComponent {σ : Type*}
    (f : MvPolynomial σ ℤ) (p : ℕ) :
    HypersurfaceBadReduction f p →
      HypersurfaceBadReduction (homogeneousComponent f.totalDegree f) p := by
  intro hbad
  let : Fact p.Prime := ⟨hbad.1⟩
  by_contra hgood
  have hir : Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p)))
      (homogeneousComponent f.totalDegree f)) := by
    by_contra h
    exact hgood ⟨hbad.1, Or.inr h⟩
  obtain ⟨hdegree, hfull⟩ := map_degree_and_irreducible_of_top_irreducible _ f hir
  exact hbad.2.elim (fun h => h hdegree) (fun h => h hfull)

/-- Absolute irreducibility of the highest homogeneous component implies
 absolute irreducibility of the original integer equation. -/
theorem absolute_irreducible_of_top_homogeneousComponent_irreducible {σ : Type*}
    (f : MvPolynomial σ ℤ)
    (hir : HasAbsIrreducibleTopForm f) :
    AbsolutelyIrreducible f :=
  (map_degree_and_irreducible_of_top_irreducible _ f hir).2

/-- The affine bad-prime factor is no greater than that of the top
 form when the latter is absolutely irreducible. -/
theorem hypersurfaceBadPrimeFactor_le_top_homogeneousComponent {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hir : HasAbsIrreducibleTopForm f) :
    hypersurfaceBadPrimeFactor f ≤
      hypersurfaceBadPrimeFactor (homogeneousComponent f.totalDegree f) := by
  have htop : homogeneousComponent f.totalDegree f ≠ 0 := by
    intro hz
    exact hir.ne_zero (by rw [hz, map_zero])
  apply hypersurfaceBadPrimeFactor_mono_of_badReduction_imp
  · exact ((homogeneousComponent_isHomogeneous _ _).totalDegree htop).symm
  · exact fun _ => hir
  · exact hypersurfaceBadReduction_imp_top_homogeneousComponent f

/-- Primitivity reflects the irreducibility supplied by the absolute top form
 back to the integer polynomial ring. -/
theorem PrimitiveIntegerPolynomial.irreducible_of_absolute_top {σ : Type*}
    {f : MvPolynomial σ ℤ} (hprim : PrimitiveIntegerPolynomial f)
    (hir : HasAbsIrreducibleTopForm f) : Irreducible f := by
  apply hprim.irreducible_of_rational_map
  exact rational_irreducible_of_charZero_map f
    (absolute_irreducible_of_top_homogeneousComponent_irreducible f hir)

/-- Removing nonzero integer content preserves absolute irreducibility of
 the top homogeneous form, along with the affine degree. -/
theorem absolute_top_irreducible_of_integer_scalar_factor {σ : Type*}
    {f g : MvPolynomial σ ℤ} {c : ℤ} (hc : c ≠ 0) (he : f = C c * g)
    (hir : HasAbsIrreducibleTopForm f) :
    g.totalDegree = f.totalDegree ∧
      HasAbsIrreducibleTopForm g := by
  have hf : f ≠ 0 := by
    intro hz
    exact hir.ne_zero (by rw [hz, map_zero, map_zero])
  have hdegree := integer_scalar_factor_degree hf hc he
  refine ⟨hdegree, ?_⟩
  have htop : homogeneousComponent f.totalDegree f =
      C c * homogeneousComponent g.totalDegree g := by
    calc
      _ = homogeneousComponent f.totalDegree (C c * g) := congrArg (homogeneousComponent _) he
      _ = C c * homogeneousComponent f.totalDegree g := homogeneousComponent_C_mul _ _ _
      _ = _ := by rw [hdegree]
  dsimp only [HasAbsIrreducibleTopForm, AbsolutelyIrreducible] at hir
  rw [htop, map_mul, map_C] at hir
  have hcK : (Int.castRingHom (AlgebraicClosure ℚ)) c ≠ 0 := by
    simpa only [Int.coe_castRingHom, ne_eq, Int.cast_eq_zero] using hc
  exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hcK).map C)).mp hir

end
end CCDN
