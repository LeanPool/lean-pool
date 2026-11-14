/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.InjectionAssembly

/-!
# InjectionInLInftyV2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# The injection estimate on a good cube — [ABK] Proposition 5.1

Source: `references/algsuperdiff.tex:12929-12955` (`p.injection.in.L.infty`).

For a disorder model of strength `gamma` small enough there is a constant `C`
such that, for every accuracy `ep ∈ (0, 1/4]`, every scale `n : ℤ`, every centre
`y` and every datum `g`, on the intersection of the good cube event
`goodCubeEvent M Creg n y ep` and of the large-scale event
`largeScaleEvent M n y (C⁻¹ ep gamma^{-1/2})` the Dirichlet solution `u` of the
rough-field problem at any scale `m ≥ n` on the cube `y + □_n` lies within
`C ep 3^{n/2} [g]_{C^{0,1/2}}` of the solution `v` of the comparator problem
with coefficient `σ_n I`, measured in the normalized `L^∞` gauge of the cube,
and `u` obeys the normalized `1/2`-Hölder bound `C 3^{n/2} [g]_{C^{0,1/2}}`.

## Every integer scale

The estimate is asserted at every `n : ℤ`, as in the paper, and nothing in it
distinguishes a sign. The cube `y + □_n`, the annealed gauge `σ_n`, the good
cube event and the large-scale event are all defined at every integer scale;
every power of `3` that occurs is a real power, hence positive at every
exponent; and the shell law of the model at a scale `k` is exactly the triadic
rescaling of the shell at scale `0`, so a cube at a negative scale is a dilated
copy of a cube at a positive one. The negative scales are needed: the auxiliary
scale that the proof of the main theorem straddles is negative at every time
once the confinement scale is large.

## Reading of the statement

* **Essential supremum, and the seminorm of the continuous representative.**
  The first conclusion measures `u - v` by
  `eLpNorm … ⊤ (volume.restrict (cubeSetAt y n))`, the essential supremum of the
  two Sobolev functions themselves; no representative and no fallback value
  enters. The second conclusion measures the `1/2`-Hölder seminorm of a
  *continuous representative* of `u`, written as an infimum over
  representatives, whose value is `⊤` when no such representative exists. The
  bound therefore also asserts that a continuous representative exists whenever
  `[g]_{C^{0,1/2}}` is finite, which is what the printed estimate presupposes.
* **Powers of three.** Every power of `3` is a real power (`Real.rpow`), the
  form carried by the two quantities `localizedError` and `localizedRegularity`
  that define the good cube event.
* **Constants.** `C` may depend on the dimension `d`, on the value `cstar` of
  the model's ellipticity parameter `c⋆`, and on `Creg`, that is
  `C = C(d, c⋆, Creg)`. The single parameter `Creg` stands for the three
  constants that the source writes separately in the good cube event
  (`C_{e.error}`, `C_{e.reg}` and `2 C_{e.reg}`); enlarging `Creg` enlarges the
  good cube event, so identifying the three only weakens the statement.
* **Small-disorder premise.** The hypothesis `M.gamma ≤ gamma0` is *not* printed
  in Proposition 5.1. It is the standing regime in which the constants of the
  earlier sections are stated, and the annealed-gauge comparison
  `3^{gamma n} σ_{n-1}^{-1} ≤ C c⋆^{-1/2} gamma^{1/2}` that the estimate uses
  holds only there, so it is made explicit here.
* **Datum class.** No hypothesis `g ∈ C^{0,1/2}` appears: both conclusions hold
  trivially when `holderSeminormOn (cubeSetAt y n) (1 / 2) g = ⊤`.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section5.injection_in_L_infty_v2
    (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (g : Vec d → Vec d),
      ∀ omega ∈ goodCubeEvent M Creg n y ep ∩
          largeScaleEvent M n y (C⁻¹ * ep * (Real.sqrt M.gamma)⁻¹),
      ∀ m : ℤ, n ≤ m →
      ∀ u v : H1Function (cubeSetAt y n),
        IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u g →
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g →
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
              eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) ≤
            ENNReal.ofReal (C * ep * Real.rpow 3 ((n : ℝ) / 2)) *
              holderSeminormOn (cubeSetAt y n) (1 / 2) g ∧
          (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
              ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
                holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) ≤
            ENNReal.ofReal (C * Real.rpow 3 ((n : ℝ) / 2)) *
              holderSeminormOn (cubeSetAt y n) (1 / 2) g
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section5.Provider.injection_in_L_infty_v2_provider
    d cstar hcstar Creg hCreg
