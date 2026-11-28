/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Martingale.Basic

/-!
# A martingale from set-integral identities, over any index

Mathlib proves `martingale_of_setIntegral_eq_succ` for `ℕ`-indexed processes, where one-step
identities suffice. Over a general (e.g. continuous) index there is no successor, and the
identities are over every pair `i ≤ j`: `martingale_iff_setIntegral_eq` is that statement. It is
the characterisation of conditional expectation by set integrals
(`ae_eq_condExp_of_forall_setIntegral_eq`) read off as the martingale property, with Mathlib's
`Martingale.setIntegral_eq` as the converse, and the way the
library's continuous-time martingales (the exponential martingales, the stopped price of an
equivalent martingale measure, promoted local martingales) are built.

## Main results

* `martingale_iff_setIntegral_eq`: a process is a martingale iff it is adapted, integrable, and
  for `i ≤ j` its set integrals over `𝒢 i`-measurable sets agree at times `i` and `j`.

## Tags

martingale characterisation, set integral identity, continuous-time martingale,
conditional expectation, martingale property, MSC 60G44, MSC 60G48
-/

@[expose] public section

namespace MeasureTheory

variable {Ω ι E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {𝒢 : Filtration ι m0}
  {f : ι → Ω → E}

/-- **A process is a martingale iff it is adapted, integrable, and its set integrals over
`𝒢 i`-measurable sets are constant in time.** The forward direction is Mathlib's
`Martingale.setIntegral_eq`; the converse is the characterisation of conditional expectation by set
integrals. Over a `σ`-finite filtration (in particular any finite measure), with any index. -/
theorem martingale_iff_setIntegral_eq [SigmaFiniteFiltration μ 𝒢] :
    Martingale f 𝒢 μ ↔ StronglyAdapted 𝒢 f ∧ (∀ i, Integrable (f i) μ) ∧
      ∀ ⦃i j⦄, i ≤ j → ∀ s : Set Ω, MeasurableSet[𝒢 i] s →
        ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ :=
  ⟨fun hf ↦ ⟨hf.stronglyAdapted, hf.integrable, fun _ _ hij _ hs ↦ hf.setIntegral_eq hij hs⟩,
    fun ⟨hadp, hint, hf⟩ ↦ ⟨hadp, fun _ _ hij ↦
      (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le _) (hint _)
        (fun _ _ _ ↦ (hint _).integrableOn) (fun s hs _ ↦ hf hij s hs)
        (hadp _).aestronglyMeasurable).symm⟩⟩

end MeasureTheory
