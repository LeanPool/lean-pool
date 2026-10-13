/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepOneParameters
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorPrefactor

/-!
# StepSevenCaccMatching

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7c: matching `l.coarse.grained.Caccioppoli.RHS` to the §4.4 data

## The target, and the gap this module closes

Step 7c says only

> Since `n'` is a good scale, we may apply the coarse-grained Caccioppoli
> inequality and the oscillation bound `e.oscillation.Holder.bound` at scale `n'`
> to obtain a gradient bound.

## The exponent pin (the one real choice, and it is forced)

The Caccioppoli's forcing slot is `𝐠 ∈ H^{2t}`.  So the §4.4 datum determines
`t` completely:

```text
      2 t  =  s_{§4.4}  =  1/4       ⟹      t = 1/8 = stepSevenCaccT
```

and the Caccioppoli's own first exponent is taken to be `s_{§4.4} = 1/4` as
well, giving

```text
      σ  =  1 - 1/4 - 1/8  =  5/8  >  0 .
```

Nothing else is available: any other `t` would measure the forcing at an
exponent §4.4 never produces.

## The binder-by-binder match

Each binder of `l.coarse.grained.Caccioppoli.RHS`, against the §4.4 datum that
discharges it.

* **`s ∈ (0,1)`** ⇝ `stepOneS = 1/4`.  Discharged, `stepSevenCaccS_lt_one`.
* **`t ∈ (0,1/2]`, `σ = 1-s-t > 0`** ⇝ `stepSevenCaccT = 1/8`, `σ = 5/8`.
  Discharged, `stepSevenCaccT_lt_half` and the positivity of `σ`.
* **`x ∈ □_0`** (the Dirichlet-patch centre) ⇝ the good-scale centre: the patch
  contains its own centre, so the patch inclusion implies it.
* **`𝐚 ∈ L^∞(□_0; ℝ_+^{d×d})`** ⇝ the truncated field `𝐚_{L,n'}`
  (`e.infrared.cutoff.def`).  Discharged as a `CoeffFamily` binder.
* **`u ∈ H^1(□_0)` with `-∇·𝐚∇u = ∇·𝐠`** ⇝ the §4.4 solution on `□_m`,
  restricted to the good-scale cube.  Discharged by `IsForcedEquation` together
  with S4.3's `EquationRestriction`.
* **`𝐠 ∈ H^{2t}(□_0;ℝ^d)`** ⇝ `[𝐠]_{H^{1/4}(U_{n'})}`, itself coming from
  `[𝐠]_{W^{1/2,∞}(□_m)}`.  Discharged at the exponent (`2t = 1/4`, the pin);
  the `W^{1/2,∞} → H^{1/4}` embedding is
  `normalizedGagliardoESeminormOn_stepThreeWindow_quarter_le`.  What remains:
  the Gagliardo `H^s` ↔ CoarseGraining `ForceBesovRegularity` /
  `scaleNormalizedPositiveBesovVectorSeminormTwo` carrier bridge is not
  performed here.
* **`h ∈ H^{1+2t}(□_0)` with `(h)_{□_0} = 0`** ⇝ `‖∇h‖_{W^{1/2,∞}(□_m)}`.  Not
  dischargeable from any proved source — see the residues below.  The mean-zero
  normalization is itself free: only `∇h` and the trace class of `u - h` are
  used, and both are invariant under `h ↦ h - c`.
* **the unit-cube normalization `□_0`** ⇝ the good-scale cube at scale `n'`.
  Discharged, and at zero cost: CoarseGraining does not state the lemma at the
  unit cube.  This is the largest single item the manuscript's silence hides.
* **the boundary condition `u = h` on `(∂□_0) ∩ (x + □_{-1})`** ⇝ §4.4's `u =
  h` on `∂□_m`.

## The two residues, stated exactly

**(R1) the `∇h` leg is not formalized anywhere.**  CoarseGraining proves
`l.coarse.grained.Caccioppoli.RHS` only at zero localized
boundary data: its datum `BoundaryForcedCaccioppoliDatum` carries
`LocalizedZeroTraceFunctionOn`, and its right-hand side
`boundaryCaccioppoliWithRHSRHS` has exactly two summands (the parent `L²` mass
and the `𝐠`-Besov mass).  The printed third summand
`t^{-3} Λ_t(□_0;𝐚) ‖∇h‖²_{H^{2t}(□_0)}` comes from move 3 of the printed proof,
which is not formalized here (it needs the mean-zero-boundary fractional Sobolev
embedding `e.fractional.Sobolev.embedding.zero.bndr` applied to `h` itself).  The
boundary cubes of Theorem C consume the estimate with the `h`-term switched on
but never need it in the `‖∇h‖`-only normal form, so the boundary-data defect is
carried as data — it vanishes identically on interior cubes.  The Step-7c display
therefore carries the `∇h` leg as an opaque scalar (`dataH`, guarded by the
indicator `1_{z ∉ □_{m-1}}`), and this module makes no claim about it.

**(R2) the truncated window is not a cube.**  Every proved form of the lemma
lives on a triadic cube (`caccioppoliCoreSet Q x ⊆ openCubeSet Q`), while §4.4's
window is the truncation `U_j = (z + □_j) ∩ □_m`.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`.
* ABK26, `t.regularity` Step 7c; Step 1.
* CoarseGraining, `Homogenization/Book/Ch03/Theorems/CoarseCaccioppoliRHS.lean`
  (`coarseCaccioppoliRHSTheory`).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The exponent pin -/

/-- **The Caccioppoli's first exponent at the §4.4 pin.**  It is §4.4's own `s =
1/4` (`e.parameter.choices.regularity`). -/
noncomputable def stepSevenCaccS : ℝ := stepOneS

/-- **The Caccioppoli's second exponent at the §4.4 pin.**  Determined by the
forcing slot: `l.coarse.grained.Caccioppoli.RHS` measures `𝐠` in `H^{2t}`, and
§4.4 measures it in `H^{1/4}`, so `2t = 1/4`. -/
noncomputable def stepSevenCaccT : ℝ := stepOneS / 2

@[simp] theorem stepSevenCaccS_eq : stepSevenCaccS = 1 / 4 := rfl

@[simp] theorem stepSevenCaccT_eq : stepSevenCaccT = 1 / 8 := by
  rw [stepSevenCaccT, stepOneS_eq]; norm_num

/-- **The pin, in the form that states WHY it is forced**: twice the Caccioppoli's
second exponent is §4.4's own exponent, so the forcing slot `H^{2t}` IS the
`H^{1/4}` slot of Steps 4--7. -/
theorem two_mul_stepSevenCaccT : 2 * stepSevenCaccT = stepOneS := by
  rw [stepSevenCaccT]; ring

theorem stepSevenCaccS_pos : 0 < stepSevenCaccS := by
  rw [stepSevenCaccS_eq]; norm_num

theorem stepSevenCaccS_lt_one : stepSevenCaccS < 1 := by
  rw [stepSevenCaccS_eq]; norm_num

theorem stepSevenCaccT_pos : 0 < stepSevenCaccT := by
  rw [stepSevenCaccT_eq]; norm_num

theorem stepSevenCaccT_lt_half : stepSevenCaccT < 1 / 2 := by
  rw [stepSevenCaccT_eq]; norm_num

theorem stepSevenCaccS_add_T_lt_one : stepSevenCaccS + stepSevenCaccT < 1 := by
  rw [stepSevenCaccS_eq, stepSevenCaccT_eq]; norm_num

/-! ## 2. The prefactor and the forcing factor at the pin -/

theorem stepSevenCaccPrefactor_le [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {C Theta0 : ℝ} (hC : 0 < C)
    (hTheta : Ch02.ThetaRatio Q stepSevenCaccS stepSevenCaccT a ≤ Theta0) :
    caccioppoliWithRHSPrefactor C Q a stepSevenCaccS stepSevenCaccT ≤
      (2 * max 1 C) ^ (4 : ℕ) * 4 * Theta0 ^ (2 : ℕ) := by
  have hs : stepSevenCaccS = 1 / 4 := stepSevenCaccS_eq
  have ht : stepSevenCaccT = (1 / 2 : ℝ) / 4 := by rw [stepSevenCaccT_eq]; norm_num
  rw [hs, ht] at hTheta ⊢
  exact caccioppoliWithRHSPrefactor_quarter_le hC (by norm_num) (by norm_num) hTheta

/-! ## 3. The coarse-grained Caccioppoli, at the §4.4 pin -/

/-- **`l.coarse.grained.Caccioppoli.RHS`, instantiated at the §4.4 exponent pin.**

For every triadic cube `Q`, every coefficient family `a`, every forced `H¹(Q)`
solution `u` whose Dirichlet patch `x + □_{Q.scale-1}` sits inside `Q`, and every
real `c`,

```text
  ⨍_{□_Q ∩ (x+□_{Q.scale-2})} ∇u · 𝐚 ∇u
      ≤  prefactor(C,Q,a,1/4,1/8) ·
         ( λ_{1/8,1} · 3^{-2·scale} · ‖u - c‖²_{L²(Q)}
           + 8^8·(4/3) · λ_{1/8,1}^{-1} · [𝐠]²_{B^{1/4}(Q)} ) ,
```

with the forcing seminorm displayed at §4.4's own exponent `stepOneS = 1/4`
(this is the pin `2t = s_{§4.4}`, `two_mul_stepSevenCaccT`).

Unconditional in `d`; the surviving hypotheses are exactly the pinned lemma's
own equation, patch and forcing-regularity binders.  The `∇h` leg of the
printed display is absent — see residue (R1) of the module docstring. -/
theorem exists_stepSevenCaccioppoliEnergy (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d} {g : Vec d → Vec d}
        (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ),
        IsForcedEquation Q a u g →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q stepOneS g →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            caccioppoliWithRHSPrefactor C Q a stepSevenCaccS stepSevenCaccT *
              (Ch02.lambdaS Q stepSevenCaccT a *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c) +
                (Real.rpow stepSevenCaccT (-8 : ℝ) / (1 - 2 * stepSevenCaccT)) *
                  Real.rpow (Ch02.lambdaS Q stepSevenCaccT a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q stepOneS g ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := exists_interiorCaccioppoliEnergy_subConst d
  refine ⟨C, hCpos, ?_⟩
  intro Q a x g u c hu hpatch hg
  have hgt : ForceBesovRegularity Q (2 * stepSevenCaccT) g := by
    rw [two_mul_stepSevenCaccT]; exact hg
  have h := hC (Q := Q) (a := a) (s := stepSevenCaccS) (t := stepSevenCaccT)
    (x := x) (g := g) u c hu stepSevenCaccS_pos stepSevenCaccS_lt_one
    stepSevenCaccT_pos stepSevenCaccT_lt_half stepSevenCaccS_add_T_lt_one hpatch hgt
  rw [← two_mul_stepSevenCaccT]
  exact h

end

end Algsuperdiff.Section4.Provider.Regularity
