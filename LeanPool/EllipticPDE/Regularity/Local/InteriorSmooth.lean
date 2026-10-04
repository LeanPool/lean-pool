/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Local.HigherInterior
public import LeanPool.EllipticPDE.Regularity.InteriorSmoothGlobal


/-!
# Infinite differentiability in the interior for a weak solution in `H¹`

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 (p. 334), for a local
weak solution `U ∈ W12 Ω` with no boundary condition. The proof is the one of `interior_smooth`
with `higher_interior_regularity_W12` in place of `higher_interior_regularity`: every order of
weak differentiability on a compact `V`, the Sobolev ladder
`contDiffOn_interior_of_hasIteratedWeakDerivOn` on its interior, and
`exists_contDiffOn_of_compact_ae` to glue the representatives into one on `Ω`.

## Main declarations

* `interior_smooth_W12`: a smooth representative on the interior of each compact `V ⊆ Ω`.
* `interior_smooth_global_W12`: one smooth representative on all of `Ω`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Infinite differentiability in the interior of a compact set for a weak solution in
`H¹`.** A local weak solution `U ∈ W12 Ω` of `L U = f`, with no boundary condition, whose
coefficients lie in `W^{k,∞}` at every order and whose datum has weak derivatives of every
order in `L²(Ω)`, has a representative smooth on the interior of each compact `V ⊆ Ω`. -/
theorem interior_smooth_W12 (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (U : H1amb Ω) (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    (hsol : IsLocalWeakSolution Op Ω U f)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict (interior V)]
          (extendL2 hΩm (U 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  have hall : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k
      (restrictL2 (Ω := V) (extendL2 hΩm (U 0)))) := by
    intro k
    obtain ⟨hfk, M, hM⟩ := hf k
    obtain ⟨C, _hC0, hC⟩ :=
      higher_interior_regularity_W12 Op hΩm hΩo hA1 k (hA (k + 1)) (hbc k) hVc hVΩ
    obtain ⟨hu, _⟩ := hC U f M hfk hM hsol
    exact ⟨hu.mono (by omega)⟩
  obtain ⟨u', hu'ae, hu'smooth⟩ := contDiffOn_interior_of_hasIteratedWeakDerivOn _ hall
  refine ⟨u', ?_, hu'smooth⟩
  have hres : (restrictL2 (Ω := V) (extendL2 hΩm (U 0))
        : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict (interior V)]
        (extendL2 hΩm (U 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :=
    (coeFn_restrictL2 (Ω := V) (extendL2 hΩm (U 0))).filter_mono
      (ae_mono (Measure.restrict_mono interior_subset le_rfl))
  exact hu'ae.trans hres

/-- **Infinite differentiability in the interior for a weak solution in `H¹` (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1, Theorem 3, p. 334), with one representative on all
of `Ω`.** Under the hypotheses of `interior_smooth_W12`, which ask nothing of `U` at the
boundary, a single function smooth on the open set `Ω` agrees almost everywhere on `Ω` with the
function coordinate of `U`. -/
theorem interior_smooth_global_W12 (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (U : H1amb Ω) (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    (hsol : IsLocalWeakSolution Op Ω U f) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict Ω]
          (extendL2 hΩm (U 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' Ω :=
  exists_contDiffOn_of_compact_ae hΩo _ fun _V hVc hVΩ =>
    interior_smooth_W12 Op hΩm hΩo hA1 hA hbc U f hf hsol hVc hVΩ

end EllipticPdes.Regularity
