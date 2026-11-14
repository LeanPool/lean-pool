/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.Algebra.PolynomialSection
import LeanPool.CCDN.Hilbert.PlaneHilbert
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Sharp bounds for distinct points in proper polynomial sections. In the plane,
the principal Hilbert function gives the usual product-of-degrees bound. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- An irreducible plane curve and a polynomial not divisible by its equation
have at most the product of their degrees many distinct common zeros. -/
theorem plane_common_zeros_card_le {K ι : Type*} [Field K] [Fintype ι]
    (f g : MvPolynomial (Fin 2) K) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzf : ∀ i, MvPolynomial.eval (z i) f = 0)
    (hzg : ∀ i, MvPolynomial.eval (z i) g = 0) :
    Fintype.card ι ≤ f.totalDegree * g.totalDegree := by
  classical
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  apply polynomial_section_card_le_degree I f.totalDegree
    ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
      fun N hN => principal_plane_hilbert_function f hf.ne_zero hN⟩
    g (by simpa only [I, Ideal.mem_span_singleton] using hfg)
    g.totalDegree le_rfl z hz _ hzg
  intro i h hh
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hh
  rw [MvPolynomial.eval_mul, hzf, zero_mul]

/-- The section bound directly in the real-radius integer counting interface. -/
theorem count_curve_section_le {n d : ℕ} (I : Ideal (CoordinatePolynomial n))
    [I.IsPrime] (hd : HasAffineCurveDegree I d)
    (g : CoordinatePolynomial n) (hg : g ∉ I) (B : ℝ) :
    count (idealZeroLocus I ∩ zeroLocus g) B ≤ d * g.totalDegree := by
  classical
  let S := integralPoints (idealZeroLocus I ∩ zeroLocus g) B
  let z : S → RatPoint n := fun x => rationalPoint x.val
  have hz : Function.Injective z := by
    intro x y h
    apply Subtype.ext
    funext j
    exact Int.cast_injective (congrFun h j)
  have hzp (i : S) : z i ∈ idealZeroLocus I :=
    (mem_integralPoints.mp i.property).2.1
  have hzg (i : S) : MvPolynomial.eval (z i) g = 0 :=
    (mem_integralPoints.mp i.property).2.2
  have h := polynomial_section_card_le_degree I d hd g hg g.totalDegree le_rfl z hz hzp hzg
  simpa only [Fintype.card_coe, S, count] using h

end
end CCDN
