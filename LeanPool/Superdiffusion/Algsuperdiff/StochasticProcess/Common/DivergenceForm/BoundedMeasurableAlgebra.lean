/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.BoundedMeasurableAgreement

/-!
# BoundedMeasurableAlgebra

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-
Algebraic properties of the analytic resolvent on bounded measurable data.
-/

/-!
# Linearity of the zero extension of bounded measurable data

The zero extension of a bounded measurable function on the domain is additive
and homogeneous, hence so is its `L²` class.  These are the closure properties
used by the monotone-class comparison with the process resolvent.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-! ## The zero extension is linear -/

theorem domainExtension_add_apply (f g : U → ℝ) (x : Vec d) :
    domainExtension (fun a => f a + g a) x =
      domainExtension f x + domainExtension g x := by
  by_cases hx : x ∈ U
  · simp [domainExtension_of_mem hx]
  · simp [domainExtension_of_notMem hx]

theorem domainExtension_smul_apply (c : ℝ) (f : U → ℝ) (x : Vec d) :
    domainExtension (c • f) x = c * domainExtension f x := by
  by_cases hx : x ∈ U
  · simp [domainExtension_of_mem hx]
  · simp [domainExtension_of_notMem hx]

/-! ## The `L²` class is linear -/

theorem boundedMeasurableToScalarL2_add (hU : IsOpenBoundedConvexDomain U)
    {f g : U → ℝ} (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E)
    (hfg : ∀ y, |(f + g) y| ≤ D + E) :
    boundedMeasurableToScalarL2 hU (hf.add hg) hfg =
      boundedMeasurableToScalarL2 hU hf hfD +
        boundedMeasurableToScalarL2 hU hg hgE := by
  refine (Lp.ext_iff).2 ?_
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU (hf.add hg) hfg,
    boundedMeasurableToScalarL2_coeFn hU hf hfD,
    boundedMeasurableToScalarL2_coeFn hU hg hgE,
    Lp.coeFn_add (boundedMeasurableToScalarL2 hU hf hfD)
      (boundedMeasurableToScalarL2 hU hg hgE)] with x h0 h1 h2 h3
  rw [h0, h3, Pi.add_apply, h1, h2]
  exact domainExtension_add_apply f g x

theorem boundedMeasurableToScalarL2_smul (hU : IsOpenBoundedConvexDomain U)
    (c : ℝ) {f : U → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hcf : ∀ y, |(c • f) y| ≤ |c| * D) :
    boundedMeasurableToScalarL2 hU (hf.const_smul c) hcf =
      c • boundedMeasurableToScalarL2 hU hf hfD := by
  refine (Lp.ext_iff).2 ?_
  filter_upwards [boundedMeasurableToScalarL2_coeFn hU (hf.const_smul c) hcf,
    boundedMeasurableToScalarL2_coeFn hU hf hfD,
    Lp.coeFn_smul c (boundedMeasurableToScalarL2 hU hf hfD)] with x h0 h1 h2
  rw [h0, h2, Pi.smul_apply, h1, domainExtension_smul_apply, smul_eq_mul]


section RepresentativeWitness

end RepresentativeWitness

section Representative

end Representative

end

end DivergenceFormProcess.Form
