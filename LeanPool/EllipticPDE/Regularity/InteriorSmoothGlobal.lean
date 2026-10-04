/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.InteriorSmooth


/-!
# Infinite differentiability on the whole of the interior

`interior_smooth` produces a smooth representative on the interior of each compact `V ⋐ Ω`
separately, with nothing relating the representatives two different choices of `V` supply. This
file glues them into a single function smooth on the whole of `Ω`.

The gluing needs no construction of its own. Two representatives, one for a compact `V₁` and one
for a compact `V₂`, are continuous and agree almost everywhere with the same class wherever their
interiors meet, so they agree there; `exists_contDiffOn_of_compact_ae` is exactly this fact
packaged for a hypothesis stated over every compact subset of `Ω` at once, and applying it to the
family `interior_smooth` supplies is the whole proof.

## Main declarations

* `interior_smooth_global`: Evans's Theorem 3, with one representative smooth on all of `Ω`
  rather than on the interior of each compact exhaustion piece.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Infinite differentiability in the interior (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.1, Theorem 3, p. 334), with one representative on all of `Ω`.** Under the
hypotheses of `interior_smooth`, the local representatives on the interior of every compact
`V ⊆ Ω` agree on the interiors they share, so `exists_contDiffOn_of_compact_ae` assembles them
into a single function smooth on the whole open set `Ω`, rather than merely on the interior of
each compact subset in turn. -/
theorem interior_smooth_global (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (u : H01 Ω) (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    (hweak : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict Ω]
          (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' Ω :=
  exists_contDiffOn_of_compact_ae hΩo _ fun _V hVc hVΩ =>
    interior_smooth Op hΩm hΩo hA1 hA hbc u f hf hweak hVc hVΩ

end EllipticPdes.Regularity
