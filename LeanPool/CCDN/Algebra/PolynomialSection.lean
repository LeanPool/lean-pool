/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.Hilbert.FilteredIntersection
import LeanPool.CCDN.Algebra.PointSeparation
import LeanPool.CCDN.Algebra.SectionImageRank

/-! A sharp affine curve intersection bound from the Hilbert function.
Bounds intersections with arbitrary section polynomials. No projective intersection theorem or
point-counting axiom is used. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A proper polynomial section of a prime curve contains at most the product
of the curve's affine Hilbert degree and the section degree many distinct points. -/
theorem polynomial_section_card_le_degree {K σ ι : Type*} [Field K] [Finite σ]
    [Fintype ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (d : ℕ)
    (hdegree : HasFilteredCurveDegree p d)
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ idealZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    Fintype.card ι ≤ d * m := by
  classical
  obtain ⟨h, hsep⟩ := exists_point_separators z hz
  let φ : ι → (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
    fun i => Ideal.Quotient.liftₐ p (MvPolynomial.aeval (z i)) (by
      intro f hf
      simpa only [MvPolynomial.aeval_eq_eval] using hzp i f hf)
  have hφ (i : ι) (f : MvPolynomial σ K) :
      φ i ((Ideal.Quotient.mk p) f) = MvPolynomial.eval (z i) f := by
    simp [φ, Ideal.Quotient.liftₐ_apply]
  have hlin := separator_images_independent φ (fun i => (Ideal.Quotient.mk p) (h i))
    (fun i j => by rw [hφ]; exact hsep i j)
  apply section_image_rank_le p d hdegree (AlgHom.pi φ) h hlin l hl m hld
  ext i
  exact (hφ i l).trans (hzl i)

end
end CCDN
