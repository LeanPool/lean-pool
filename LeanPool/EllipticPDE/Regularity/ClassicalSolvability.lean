/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.InteriorSmooth


/-!
# Solvability and interior smoothness composed

Existence supplies a weak solution and the interior theory supplies a smooth representative of
it. This file puts the two together, which is the regularity half of classical solvability: for
coefficients and a datum of every order, the Dirichlet problem has a weak solution with a
representative that is `C^∞` on the interior of every compact subset of the domain.

The pointwise equation is the step this file does not take. A `C^∞` representative on the
interior satisfies the equation there by the fundamental lemma of the calculus of variations,
which `EllipticPdes.Regularity.PointwiseEquation` proves and
`EllipticPdes.Regularity.exists_weakSolution_interior_classical` composes with this result.

## Main declarations

* `EllipticPdes.Regularity.exists_weakSolution_interior_smooth`: a weak solution together with
  its smooth interior representative.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.3.1 Theorem 3 (p. 334);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.3.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

/-- **Weak solution with a smooth interior representative.** On a bounded domain, for an
operator with no transport term and a nonnegative zeroth-order coefficient, whose diffusion is
`W^{1,∞}` and whose coefficients lie in `W^{k,∞}` at every order, and for a datum with weak
derivatives of every order bounded in `L²`, the Dirichlet problem has a weak solution whose
class has a `C^∞` representative on the interior of every compact subset of the domain. -/
theorem exists_weakSolution_interior_smooth {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x)
    (hA1 : IsLipCoeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u : H01 Ω,
      (∀ v : H01 Ω, Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) ∧
      ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
        u' =ᵐ[volume.restrict (interior V)]
            (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
          ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  obtain ⟨_CP, _hCP, hsol⟩ :=
    FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded Op hΩb hb hc
  obtain ⟨⟨u, hu, -⟩, -⟩ := hsol f
  exact ⟨u, hu, interior_smooth Op hΩm hΩo hA1 hA hbc u f hf hu hVc hVΩ⟩

end EllipticPdes.Regularity
