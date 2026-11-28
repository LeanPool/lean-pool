/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionMixing
public import LeanPool.MathFin.Probability.Jumps.PoissonThinning

/-!
# Thinning the jumps of a Merton-type jump-diffusion

`JumpDiffusionHyp Q Λ Z N J` (`Models/Jumps/JumpDiffusionMixing.lean`) is a Merton-type
jump-diffusion at a fixed horizon (any i.i.d. jump law, Merton's Gaussian jumps among them): a
standard normal diffusion sample `Z`, a `Poisson(Λ)` jump count `N` and i.i.d. log-jump sizes
`J 0, J 1, …`, the count independent of the sizes. Sorting the jumps by a measurable set `A` of
sizes (for instance `A = (0, ∞)`, the up-jumps) is a thinning of the Poisson count by i.i.d. marks,
so `PoissonThinning.thinned_streams_of_iid_marks` applies: the number of jumps with size in `A` and
the number with size in `Aᶜ` are independent Poisson counts with means `Λ·P(J₀ ∈ A)` and
`Λ·P(J₀ ∉ A)`.

## Main results

* `JumpDiffusionHyp.jumpCounts_split`

## References

* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]
* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 3.3.10

## Tags

Poisson thinning, up-jumps and down-jumps, splitting a Poisson process, jump-diffusion,
independent Poisson counts, MSC 60G55, MSC 60G51, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Λ : ℝ≥0} {Z : Ω → ℝ}
  {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

namespace JumpDiffusionHyp

/-- **The jumps of a Merton-type jump-diffusion split into independent Poisson streams.** In the
model `JumpDiffusionHyp Q Λ Z N J` and for a measurable set `A` of jump sizes, with `p = Q(J₀ ∈ A)`,
the number of the `N` jumps whose size lies in `A` is `Poisson(p·Λ)`, the number whose size lies in
`Aᶜ` is `Poisson((1 − p)·Λ)`, and the two counts are independent. -/
theorem jumpCounts_split (h : JumpDiffusionHyp Q Λ Z N J) {A : Set ℝ} (hA : MeasurableSet A) :
    Q.map (fun ω ↦ PoissonThinning.marksIn J A (N ω) ω)
        = poissonMeasure ((Q (J 0 ⁻¹' A)).toNNReal * Λ) ∧
      Q.map (fun ω ↦ PoissonThinning.marksIn J Aᶜ (N ω) ω)
        = poissonMeasure ((1 - (Q (J 0 ⁻¹' A)).toNNReal) * Λ) ∧
      IndepFun (fun ω ↦ PoissonThinning.marksIn J A (N ω) ω)
        (fun ω ↦ PoissonThinning.marksIn J Aᶜ (N ω) ω) Q := by
  have := h.J_indep.isProbabilityMeasure
  -- the thinning theorem wants measurable marks: replace the jump sizes by measurable versions
  obtain ⟨J', hJ'm, hJJ'⟩ : ∃ J' : ℕ → Ω → ℝ, (∀ i, Measurable (J' i)) ∧ ∀ i, J i =ᵐ[Q] J' i :=
    ⟨fun i ↦ (h.aemeasurable_J i).mk (J i), fun i ↦ (h.aemeasurable_J i).measurable_mk,
      fun i ↦ (h.aemeasurable_J i).ae_eq_mk⟩
  have hall : ∀ᵐ ω ∂Q, ∀ i, J i ω = J' i ω := ae_all_iff.2 hJJ'
  have hmarks (B : Set ℝ) : (fun ω ↦ PoissonThinning.marksIn J B (N ω) ω)
      =ᵐ[Q] fun ω ↦ PoissonThinning.marksIn J' B (N ω) ω :=
    hall.mono fun ω hω ↦
      congrArg Finset.card (Finset.ext fun i ↦ by simp only [Finset.mem_filter, hω])
  have hpre : Q (J 0 ⁻¹' A) = Q (J' 0 ⁻¹' A) :=
    measure_congr (Filter.eventuallyEqSet_iff.2 ((hJJ' 0).mono fun ω hω ↦ by
      simp only [Set.mem_preimage, hω]))
  have hid (i : ℕ) : IdentDistrib (J' i) (J' 0) Q Q :=
    (IdentDistrib.of_ae_eq (h.aemeasurable_J i) (hJJ' i)).symm.trans
      ((h.J_ident i).trans (IdentDistrib.of_ae_eq (h.aemeasurable_J 0) (hJJ' 0)))
  obtain ⟨h1, h2, h3⟩ := PoissonThinning.thinned_streams_of_iid_marks hA h.N_law hJ'm
    ((iIndepFun_congr hJJ').1 h.J_indep) hid
    (h.N_indep_J.congr Filter.EventuallyEq.rfl (hall.mono fun ω hω ↦ funext hω))
  exact ⟨by rw [Measure.map_congr (hmarks A), hpre]; exact h1,
    by rw [Measure.map_congr (hmarks Aᶜ), hpre]; exact h2,
    h3.congr (hmarks A).symm (hmarks Aᶜ).symm⟩

end JumpDiffusionHyp

end MathFin
