/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.LocalHolderEstimateProvider

/-!
# LocalHolderEstimate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# The local Hölder estimate — [ABK] Theorem C (`e.local.Holder.estimate`)

Source: `references/algsuperdiff.tex:411-422`, under the hypotheses of the
regularity theorem at `references/algsuperdiff.tex:371-424`.

For a disorder model of strength `gamma` small enough, every Hölder exponent
`alpha ∈ (0, 1 - C √gamma]`, every scale `m` and every centre `y`, there is an
`ℕ`-valued random variable `X` with an exponential tail such that, almost
surely, every Dirichlet solution `u` of the rough-field problem on the cube
`y + □_m` with force `g` and zero boundary datum satisfies the normalized
`C^{0,alpha}` bound

`3^{alpha m} [u]_{C^{0,alpha}(y+□_m)} ≤ C 3^{(1-alpha) X}`
`  (‖u - (u)_{y+□_m}‖_{L²(y+□_m)} + σ_m⁻¹ 3^{3m/2} [g]_{C^{0,1/2}(y+□_m)})`.

## Reading of the statement

* **The minimal scale is existential, not a definition.** The regularity theorem
  introduces `X` inside its own statement — "there exists an `ℕ`-valued random
  variable satisfying …" — and the only body it ever receives is supplied inside
  the proof. The estimate is asserted under the hypotheses of that theorem and
  refers back to the same random variable, so it is re-introduced here as an
  existential carrying its tail bound as a conjunct, the shape the regularity
  theorem of this development already uses.
* **`X` is `ℕ`-valued.** The source says `ℕ`-valued, and the value occurs here
  inside the real prefactor `3^{(1-alpha) X}`, so the `ℕ∞`-valued form of the
  regularity theorem is recast; the recast costs nothing, since the tail clause
  forces the set where the value is infinite to be null and the conclusion is
  asserted almost surely.
* **Measurability.** `Measurable X` is asserted in addition to the printed
  conclusion; it is what the later use of `X` as a random scale needs.
* **Almost-sure quantifier.** `X` is finite only almost surely, so the estimate
  is asserted for almost every sample after the choice of `X`, a single random
  variable serving every truncation scale `L ≥ m`, every force and every
  solution.
* **Truncation scale.** The coefficient field is the one cut off at a scale
  `L ≥ m`; the estimate is uniform in `L`, which is how the proof of the
  regularity theorem runs and how Section 5.1 reads the result.
* **The centre.** The random variable is bound after `y`, so this is the
  translation-covariant family, one `X` for each triple `(alpha, m, y)`; it is
  not a strengthening to a single `X` uniform in the centre.
* **Seminorm of the continuous representative.** The left side is an infimum
  over continuous representatives of `u`, whose value is `⊤` when none exists;
  the bound therefore also asserts that a continuous representative exists
  whenever the right side is finite. The cube `cubeSetAt y m` is open, so this
  is continuity inside the cube.
* **Datum class.** No hypothesis `g ∈ C^{0,1/2}` appears: the conclusion holds
  trivially when the Hölder seminorm of `g` is `⊤`, both prefactors on the right
  being strictly positive.
* **Powers of three.** Every power of `3` is a real power (`Real.rpow`), the
  form carried by the quantities of Section 5.1 that consume the estimate.
* **Full exponent range.** The estimate is asserted for every
  `alpha ∈ (0, 1 - C √gamma]`, the printed range, not at one fixed exponent;
  Section 5.1 uses it at `alpha = 1/2`.

## Conventions

* **Zero boundary datum, seminorm on the full cube.** The paper's display is
  asserted under the hypotheses of the regularity theorem, hence for every
  boundary datum `h ∈ C^{1,1/2}(y + □_m)`, and measures the `C^{0,alpha}`
  seminorm on the inner cube `y + □_{m-1}`. The formal statement is the
  zero-datum case, which the paper's statement contains, read on the whole cube
  `y + □_m`: the Dirichlet problem here is the zero-datum one, the predicate the
  quantities of Section 5.1 are defined with and the only case those quantities
  use. At zero datum the interior cube is not needed. The paper's display
  carries no boundary-datum term, and the interior restriction is what makes it
  hold uniformly over the data; the oscillation family of the regularity theorem
  is already stated on the windows truncated to the cube, at every point of the
  cube, and the Campanato characterization of Hölder spaces on a cube converts
  that family into the seminorm up to the boundary. Reading the seminorm on the
  cube the solution lives on is what Section 5.1 consumes.
* **The datum seminorm.** The paper's datum term is a normalized `W^{1/2,∞}`
  seminorm; that gauge and the `C^{0,1/2}` seminorm agree up to dimensional
  constants, so the datum term is rendered as `holderSeminormOn … (1/2) g` with
  no further power of `3`.

The proof is supplied by the Section 4 provider named in the header import.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section4.local_holder_estimate
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
      ∀ (m : ℤ) (y : Vec d), ∃ X : Cutoff.CutoffSample d → ℕ,
        Measurable X ∧
        (∀ N : ℕ,
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ X omega} ≤
            ENNReal.ofReal
              (C * Real.exp
                (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          ∀ L : ℤ, m ≤ L →
            ∀ (g : Vec d → Vec d) (u : H1Function (cubeSetAt y m)),
              IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu L omega).toCoeffField)
                  y m u g →
              (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y m u uRep,
                  ENNReal.ofReal (Real.rpow 3 (alpha * (m : ℝ))) *
                    holderSeminormOn (cubeSetAt y m) alpha uRep) ≤
                ENNReal.ofReal (C * Real.rpow 3 ((1 - alpha) * (X omega : ℝ))) *
                  (eLpNorm
                      (fun x => u.toFun x -
                        HCPolySupport.volumeAverage (cubeSetAt y m) u.toFun) 2
                      (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                        (cubeSetAt y m)) +
                    ENNReal.ofReal ((Annealed.sigmaBar M m : ℝ)⁻¹ *
                        Real.rpow 3 (3 * (m : ℝ) / 2)) *
                      holderSeminormOn (cubeSetAt y m) (1 / 2) g)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.local_holder_estimate_provider d cstar hcstar
