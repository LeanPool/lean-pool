/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.TransposeError
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaCovariance
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaTransfer

/-!
# NegationSymmetry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `(J3)` negation symmetry of the clause-(i) slot families

ABK26, Section 4.1.

```
N : CutoffSample d → CutoffSample d ,     N ω = −ω  (every shell negated)
```

acts on the clause-(i) data in exactly two ways: it is the **identity** on
every shell-norm-built slot, and it is the **transpose** on every
coefficient-built slot.  `Cutoff.negateCutoffSample` is the proved carrier map.
The matching measure-preservation statement
`Cutoff.map_negateCutoffSample_cutoffSampleLaw` (the descent of the frozen
`ShellLawJ3.negation` through the lower-tail subtype) is also proved, but it is
**not consumed**: every invariance below is a *pointwise* identity, so the
transposed estimate is obtained sample by sample rather than in law.  Nothing
new is assumed anywhere in this file.

This module collects the pointwise `N`-invariances that the transposed ugly
estimate needs:

* the three shell gauges `shellW1InfGradNorm`, `shellW2InfNormAt` and the
  `localCubeControl` block (norms are even);
* the four even slot families `annularGradBlock`, `annularL2Block`,
  `gradTailSq`, `shellW2InfLatticeMax`;
* the good event `𝒢₁(m; s, T)` — every one of its two clauses is a shell-norm
  functional;
* the good event `𝒢₀(m)` and the `hlam` datum — the `λ_{γ,2}` atoms, which are
  *not* norm-built but are transpose invariant because the skew part drops out
  of the coarse quadratic form (proved as
  `CoarseEllipticity.lambdaSq_adjointFamily`, transported to the sample by
  `Localization.lambdaSq_negateCutoffSample`).

The `𝓔_{s,2,2}` atom is handled separately in `TransposeError.lean`.

## References

* ABK26; (`𝒢₀`); (`𝒢₁`).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Localization
open Algsuperdiff.Section3.Provider.Stream
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the shell gauges are even -/

/-- The `W^{1,∞}` shell gauge is even: it is a maximum of two norms. -/
theorem shellW1InfGradNorm_negate (m : ℤ) (j : ShellField d) :
    Support.shellW1InfGradNorm m (ShellField.negate j) =
      Support.shellW1InfGradNorm m j := by
  unfold Support.shellW1InfGradNorm
  rw [localCubeSecondDerivNorm_negate, localCubeDerivNorm_negate]

/-- The `W^{2,∞}` shell gauge at a translated cube is even. -/
theorem shellW2InfNormAt_negate (z : Vec d) (k : ℤ) (j : ShellField d) :
    Support.shellW2InfNormAt z k (ShellField.negate j) =
      Support.shellW2InfNormAt z k j := by
  unfold Support.shellW2InfNormAt
  rw [translate_negate, shellW1InfGradNorm_negate, Cutoff.localCubeControl_negate]

/-! ## Part B -- the four even slot families -/

/-- The `𝒢₁`-derived gradient block is `N`-invariant. -/
theorem annularGradBlock_negateCutoffSample (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    annularGradBlock M m (Cutoff.negateCutoffSample omega) j n =
      annularGradBlock M m omega j n := by
  unfold annularGradBlock
  refine congrArg (fun t : ℝ => ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) * t) ^ 2) ?_
  refine congrArg _ (funext fun v => ?_)
  rw [Cutoff.negateCutoffSample_val, shellIncrement_negateSequence, translate_negate,
    shellW1InfGradNorm_negate]

/-- The `𝒢₁`-derived `L²` block is `N`-invariant. -/
theorem annularL2Block_negateCutoffSample (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    annularL2Block M m (Cutoff.negateCutoffSample omega) j n =
      annularL2Block M m omega j n := by
  unfold annularL2Block
  refine congrArg (fun t : ℝ => ((3 : ℝ) ^ (-(M.gamma * (n : ℝ))) * t) ^ 2) ?_
  refine congrArg _ (funext fun v => ?_)
  rw [Cutoff.negateCutoffSample_val, shellIncrement_negateSequence, translate_negate,
    Cutoff.localCubeControl_negate]

/-- The squared `ℓ¹` shell tail is `N`-invariant. -/
theorem gradTailSq_negateCutoffSample (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    gradTailSq M m (Cutoff.negateCutoffSample omega) = gradTailSq M m omega := by
  unfold gradTailSq
  refine congrArg (fun t : ℝ => t ^ 2) ?_
  refine tsum_congr fun k => ?_
  rw [Cutoff.negateCutoffSample_val, ShellField.negateSequence_apply,
    shellW1InfGradNorm_negate]

/-! ## Part C -- the good event `𝒢₁` is `N`-invariant -/

/-- **`𝒢₁(m; s, T)` is invariant under whole-sequence negation**, pointwise:
both printed clauses are functionals of the shell gauges alone. -/
theorem mem_eventG1_negateCutoffSample_iff (M : ABKModel d) (m : ℤ) (s T : ℝ)
    (omega : Cutoff.CutoffSample d) :
    Cutoff.negateCutoffSample omega ∈ Support.eventG1 M m s T ↔
      omega ∈ Support.eventG1 M m s T := by
  have h1 : (∑' k : {k : ℤ // m ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
          Support.shellW1InfGradNorm m
            ((Cutoff.negateCutoffSample omega).1 k.1)))
      = ∑' k : {k : ℤ // m ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
          Support.shellW1InfGradNorm m (omega.1 k.1)) := by
    refine tsum_congr fun k => ?_
    rw [Cutoff.negateCutoffSample_val, ShellField.negateSequence_apply,
      shellW1InfGradNorm_negate]
  have h2 : (∑' n : {n : ℤ // n ≤ m},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
          ∑ k ∈ Finset.Icc (n.1 - 1) m,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                ⨆ v : ↥(Support.latticeCubeSet d k m),
                  ENNReal.ofReal
                    (Support.shellW2InfNormAt (Support.triadicLatticePoint k v.1) k
                      ((Cutoff.negateCutoffSample omega).1 k))) ^ 2)
      = ∑' n : {n : ℤ // n ≤ m},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
          ∑ k ∈ Finset.Icc (n.1 - 1) m,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                ⨆ v : ↥(Support.latticeCubeSet d k m),
                  ENNReal.ofReal
                    (Support.shellW2InfNormAt (Support.triadicLatticePoint k v.1) k
                      (omega.1 k))) ^ 2 := by
    refine tsum_congr fun n => ?_
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    refine congrArg (fun t : ℝ≥0∞ =>
      (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) * t) ^ 2) ?_
    refine iSup_congr fun v => ?_
    rw [Cutoff.negateCutoffSample_val, ShellField.negateSequence_apply,
      shellW2InfNormAt_negate]
  rw [Support.mem_eventG1_iff, Support.mem_eventG1_iff, h1, h2]

/-! ## Part D -- the `λ` atoms and the good event `𝒢₀` -/

/-- The literal centered inverse lower multiscale ellipticity is `N`-invariant.

The skew part of the coefficient drops out of the coarse quadratic form, so
`λ_{s,q}(Q; aᵀ) = λ_{s,q}(Q; a)`
(`CoarseEllipticity.lambdaSq_adjointFamily`); combined with the `(J3)` carrier
identity `a_m(−ω) = a_m(ω)ᵀ` this is exactly
`Localization.lambdaSq_negateCutoffSample`. -/
theorem cutoffLowerEllipticityInvLiteral_negateCutoffSample (M : ABKModel d)
    (domainScale cutoffScale : ℤ) (s : ℝ) (q : CoarseEllipticityExponent)
    (omega : Cutoff.CutoffSample d) :
    Observable.cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q
        (Cutoff.negateCutoffSample omega) =
      Observable.cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q omega := by
  have key : ∀ w : Cutoff.CutoffSample d,
      Observable.cutoffLowerEllipticityInvLiteral M domainScale cutoffScale s q w =
        (Ch02.lambdaSq (originCube d domainScale) s q.1
          (Cutoff.coefficientCutoffTriadicCoeffFamily M cutoffScale w))⁻¹ := by
    intro w
    have h := cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq M
      (originCube d domainScale) cutoffScale s q w
    rw [← h, inv_inv]
    exact congrFun
      (cubeLowerEllipticityInvLiteral_originCube M domainScale cutoffScale s q).symm w
  rw [key, key, lambdaSq_negateCutoffSample]

/-- **`𝒢₀(m)` is invariant under whole-sequence negation**, pointwise. -/
theorem mem_eventG0_negateCutoffSample_iff (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    Cutoff.negateCutoffSample omega ∈ Support.eventG0 M Ccg m ↔
      omega ∈ Support.eventG0 M Ccg m := by
  have hatom : ∀ (k : ℤ) (z : Vec d),
      Support.lambdaAnnulusAtom M k z (Cutoff.negateCutoffSample omega) =
        Support.lambdaAnnulusAtom M k z omega := by
    intro k z
    unfold Support.lambdaAnnulusAtom
    rw [translateCutoffSample_negateCutoffSample,
      cutoffLowerEllipticityInvLiteral_negateCutoffSample]
  have hsup : (⨆ k : {k : ℤ // k ≤ m - 1},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
          ⨆ v : ↥(Support.latticeAnnulusSet d (k.1 - 2) m k.1),
            ENNReal.ofReal
              ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
                  Support.lambdaAnnulusAtom M k.1
                    (Support.triadicLatticePoint (k.1 - 2) v.1)
                    (Cutoff.negateCutoffSample omega) - Ccg))
      = ⨆ k : {k : ℤ // k ≤ m - 1},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
          ⨆ v : ↥(Support.latticeAnnulusSet d (k.1 - 2) m k.1),
            ENNReal.ofReal
              ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
                  Support.lambdaAnnulusAtom M k.1
                    (Support.triadicLatticePoint (k.1 - 2) v.1) omega - Ccg) := by
    refine iSup_congr fun k => ?_
    refine congrArg _ (iSup_congr fun v => ?_)
    rw [hatom]
  constructor
  · intro h
    have h' : _ ≤ (1 : ℝ≥0∞) := h
    rwa [hsup] at h'
  · intro h
    have h' : _ ≤ (1 : ℝ≥0∞) := h
    show _ ≤ (1 : ℝ≥0∞)
    rwa [← hsup] at h'

end

end Algsuperdiff.Section4.Provider.Annular
