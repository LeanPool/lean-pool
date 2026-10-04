/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Spectrum.SpectrumSigma
public import LeanPool.EllipticPDE.Spectrum.RellichDischarge


/-!
# Bounded-domain instances of the Σ-spectrum results

`SpectrumSigma.lean` proves Existence III and the boundedness of the resolvent for the
FULL operator (nonzero `bⁱ`, arbitrary sign of `c`) on any `Ω`, under the single
hypothesis that the compact
part `opK` is a compact operator. On a bounded measurable domain that hypothesis is a
theorem (`embL2_isCompact` + `opK_isCompact`), so each result holds with no analytic
hypotheses at all. These are the paper-facing statements.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace EllipticPdes.Sobolev

namespace FullEllipticOp

variable {d : ℕ} (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- **Existence III on a bounded measurable domain.** -/
theorem existence_three_of_bounded (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∃ S : Set ℝ, S.Countable ∧ (∀ C : ℝ, (S ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ S ↔ ∀ f : L2D Ω, ∃! u : H01 Ω, ∀ v : H01 Ω,
        Op.fullBilin Ω u v
          = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
            + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ) :=
  Op.existence_three Ω (Op.opK_isCompact Ω (embL2_isCompact hΩm hΩb))

/-- The `Σ`-membership characterisation on a bounded measurable domain. -/
theorem notMem_sigmaSet_iff_solvable_of_bounded (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (lam : ℝ) :
    lam ∉ Op.sigmaSet Ω
      ↔ ∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω,
          Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v :=
  Op.notMem_sigmaSet_iff_solvable Ω (Op.opK_isCompact Ω (embL2_isCompact hΩm hΩb)) lam

/-- Bounded-above slices of `Σ` are finite, on a bounded measurable domain. -/
theorem sigmaSet_inter_Iic_finite_of_bounded (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (C : ℝ) :
    (Op.sigmaSet Ω ∩ Set.Iic C).Finite :=
  Op.sigmaSet_inter_Iic_finite Ω (Op.opK_isCompact Ω (embL2_isCompact hΩm hΩb)) C

/-- **Resolvent bound on a bounded measurable domain.** -/
theorem resolvent_bound_of_bounded (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) {lam : ℝ} (hlam : lam ∉ Op.sigmaSet Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2D Ω, ∀ u : H01 Ω,
      (∀ v : H01 Ω, Op.fullBilin Ω u v
        = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
          + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      ‖(u : H1amb Ω) 0‖ ≤ C * ‖f‖ :=
  Op.resolvent_bound Ω (Op.opK_isCompact Ω (embL2_isCompact hΩm hΩb)) hlam

end FullEllipticOp

end EllipticPdes.Sobolev
