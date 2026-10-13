/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchActualDisplay
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwo

/-!
# PrincipalResponseEllipBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
descriptions below are an informal inventory only.

# The grid ellipticity budget, and the display consumer that
# no longer binds it

Source displays in ABK26:

* the ellipticity budget itself: the sentence
  `By~\eqref{e.nablaw.in.L.eight} we have` and the display

  ```
    avsum_{z in 3^n Zd cap cu_K}
      E[ shom_{m-h} |p_z|^2 + shom_{m-h}^{-1} |q_z|^2 ]  <=  C ,
  ```

  which sits between the gauge-switch chain that ends and the independence
  sentence;
* `e.nablaw.in.L.eight` (label; display), the input the manuscript names;
* `e.Pz.def` (label; display), which defines `P_z = (p_z ; q_z)`;
* `e.lower.bound.principal.one` (label) and `e.lower.bound.principal.one.pre`
  (label; display), the display whose consumer binds the budget;
* `e.recurrence.params` (label; display);
* `e.def.w` (label), the two finite-volume correctors;
* the display of leg (iv), whose fourth moment is the input used below.

## What this module supplies

One thing.

**The budget.**
`exists_const_descendantsAverage_integral_switchEllipLoad_principalPz_le` is
the display at the actual carriers: the grid is the triadic descendants of
`cu_K` at a free depth `j`, the sample carrier is `Cutoff.CutoffSample d` under
`(Cutoff.cutoffSampleLaw M).toMeasure`, the load is the manuscript's own `P_z`
of `e.Pz.def` (`principalPz`) built from a sample family of solutions of
`e.def.w`, and the two weights are the manuscript's own `shom_{m-h}` and
`shom_{m-h}^{-1}`.

An earlier second public declaration of this module, a display consumer named
`exists_const_descendantsAverage_integral_principalGoodEventEnergy_le_annealedCube`,
has been **deleted**.  Only the budget above remains, and it is what that chain
consumes.

## Why `switchEllipLoad` and `annealedSqrtNormSq` are the same thing

`switchEllipLoad S X = S |X.1|^2 + S^{-1} |X.2|^2` and `annealedSqrtNormSq
sigma Y = sigma |Y.1|^2 + sigma^{-1} |Y.2|^2` are the same term;
`annealedSqrtNormSq_eq_switchEllipLoad` is `rfl`.  This is what makes the
fourth-moment display of leg (iv) an input to the first-moment budget rather
than a separate estimate.

## The route, and the loss it costs

The manuscript derives from `e.nablaw.in.L.eight` directly: Jensen on each
localization cube, then the volume-normalized `L^2 <= L^8` comparison on
`cu_K`.  What this repository already carries at the *actual* carriers is the
**fourth** moment of exactly the same quantity, namely
`exists_const_fourthMoment_annealedSqrtNormSq_principalPz_le` of
`ApproximateRecurrence.PrincipalResponseDisplayTwo`, which itself already
composes `e.nablaw.in.L.eight` for the two corrector gradients with
`e.km.kn.Lp` at `p = 8` for the extra forcing `shom^{-1} h e'` carried by the
Neumann slot of `e.Pz.def`, merges the two into a single `Gamma_1` lane, and
transports that lane to the cutoff-sample law.

The budget is therefore obtained here by descent from the fourth moment to the
first, which is Cauchy--Schwarz:

```
  avsum_R E[X_R]  <=  ( avsum_R E[X_R^2] )^{1/2} ,
```

implemented as the pointwise `X <= C/2 + X^2/(2C)` at `C` the square root of
the right-hand side.  The descent is lossy: the constant produced below is the
square root of the fourth-moment constant, not the sharp first-moment constant
the manuscript's own route would give.

The reading gauge is the load's own gauge `shom_{m-h}`, which is the gauge the
manuscript writes.  At that gauge `gaugeRatio` is `1` (`gaugeRatio_self`), so
no reading-gauge factor and no reading-scale gate `m - 1 <= m0` is incurred.

## The constant, factor by factor

```
  Cell = C0^2 = ( 32 + 16 ( 2 ( (2 Chead + 2 Clp (24 . 3^18))
                                 + 6 orliczSecondMomentScale 1 ) )^2 )^{1/2}
```

* `Chead` -- the head of `e.nablaw.in.L.eight`, produced by
  `Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow`;
* `24 . 3^18` -- `Corrector.inv_sigmaBarSq_mul_shellWidth_le`, the
  normalization `shom_{m-h}^{-2} h 3^{2 cgamma m} <= 24 . 3^18` under the
  gates/7183 and `e.recurrence.params`;
* `orliczSecondMomentScale 1` -- the second moment of a `Gamma_1` variable,
  from the proved Orlicz layer;
* the `2`s, `16` and `32` -- the elementary doublings `(a+b)^2 <= 2(a^2+b^2)`,
  the Minkowski step on the Neumann slot, the vector Jensen inequality at the
  fourth power and the two direction bounds `|e|, |e'| <= 1`, all inside
  `pathwise_descendantsAverage_sq_annealedSqrtNormSq_le`;
* the outer square root -- the Cauchy--Schwarz descent of this module;
* the reading gauge contributes the factor `1`, by `gaugeRatio_self`.

No factor is a fitted number: each is either produced by a named theorem or is
an elementary constant of a named inequality.

## What is NOT proved here

* **The manuscript's own derivation is not reproduced.**  The `L^2 <= L^8`
  route from `e.nablaw.in.L.eight` is not carried out; the fourth moment is
  used instead, at the cost recorded above.
* **Nothing about the other binders of the consumer.**  `hlam0`, `hshell`,
  `hgoodInt`, `hcubeInt`, `hindep` and `hbudget` remain binders and are listed
  by name in the docstring of the final theorem.
* **The corrector families are not selected.**  `wD` and `wN` are arbitrary
  sample families of solutions of `e.def.w`; no measurable selection is claimed
  or used, and the per-cube measurability of the load is a caller-supplied data
  condition (`hmeasR`), not a theorem of this module.
* **`e.lower.bound.principal.one` is not derived.**  Only the budget quoted is
  produced, and only the consumer's `hellip` and `hellipInt` binders are
  removed.

## Main results

* `exists_const_descendantsAverage_integral_switchEllipLoad_principalPz_le`

## References

* ABK26, (the budget), quoting `e.nablaw.in.L.eight` (label; display);
  `e.Pz.def` (label; display); `e.lower.bound.principal.one` (label);
  `e.lower.bound.principal.one.pre` (label; display); `e.recurrence.params`
  (label; display); `e.def.w` (label); the display of leg (iv); `e.km.kn.Lp`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## The two finite-average bookkeeping steps -/

/-- Expectation and grid average commute: `descendantsAverage Q j` is a
normalized finite `Finset` sum, so the swap is the linearity of the Bochner
integral over a finite index set, at the cost of the existence of each
individual expectation.

: this statement holds only under the proposition supplied by its binder
`hint`, the per-cube integrability of the family. -/
private theorem integral_descendantsAverage_eq_swap
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (Q : TriadicCube d) (j : ℕ) (F : Omega → TriadicCube d → ℝ)
    (hint : ∀ R ∈ descendantsAtDepth Q j, Integrable (fun z => F z R) mu) :
    ∫ z, descendantsAverage Q j (F z) ∂mu =
      descendantsAverage Q j (fun R => ∫ z, F z R ∂mu) := by
  classical
  have hexp : ∀ G : TriadicCube d → ℝ, descendantsAverage Q j G =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtDepth Q j, G R :=
    fun _ => rfl
  simp only [hexp]
  rw [integral_const_mul, integral_finsetSum _ hint]

/-- Per-cube measurability upgrades to measurability of the grid average.

: this statement holds only under the proposition supplied by its binder
`hmeas`. -/
private theorem measurable_descendantsAverage_family
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : TriadicCube d) (j : ℕ) (F : Omega → TriadicCube d → ℝ)
    (hmeas : ∀ R ∈ descendantsAtDepth Q j, Measurable (fun z => F z R)) :
    Measurable (fun z => descendantsAverage Q j (F z)) := by
  classical
  have hexp : (fun z => descendantsAverage Q j (F z)) =
      fun z => ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, F z R := rfl
  rw [hexp]
  exact measurable_const.mul (Finset.measurable_sum _ hmeas)

/-! ## The Cauchy--Schwarz descent from the second moment to the first -/

/-- **The descent.**  For a nonnegative family `X` on a probability space, the
grid average of the first moments is at most the square root of the grid average
of the second moments:

```
  avsum_R E[X_R]  <=  C     whenever     avsum_R E[X_R^2]  <=  C^2 .
```

The proof is the pointwise `X <= C/2 + X^2/(2C)`, integrated and then averaged;
no integrability of `X` itself is needed, only of `X^2`.

: this statement holds only under the propositions supplied by its binders
`hX0` (pointwise nonnegativity), `hint` (per-cube integrability of the
squares), `hC` (positivity of the constant) and `hsq` (the second-moment
bound). -/
private theorem descendantsAverage_integral_le_of_sq_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] (Q : TriadicCube d) (j : ℕ)
    (X : TriadicCube d → Omega → ℝ) (hX0 : ∀ R z, 0 ≤ X R z)
    (hint : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun z => X R z ^ (2 : ℕ)) mu)
    {C : ℝ} (hC : 0 < C)
    (hsq : descendantsAverage Q j (fun R => ∫ z, X R z ^ (2 : ℕ) ∂mu) ≤
      C ^ (2 : ℕ)) :
    descendantsAverage Q j (fun R => ∫ z, X R z ∂mu) ≤ C := by
  classical
  have hstep : ∀ R ∈ descendantsAtDepth Q j,
      (∫ z, X R z ∂mu) ≤ C / 2 + (2 * C)⁻¹ * ∫ z, X R z ^ (2 : ℕ) ∂mu := by
    intro R hR
    have hmaj : Integrable
        (fun z => C / 2 + (2 * C)⁻¹ * X R z ^ (2 : ℕ)) mu :=
      (integrable_const _).add ((hint R hR).const_mul _)
    have hpt : ∀ z, X R z ≤ C / 2 + (2 * C)⁻¹ * X R z ^ (2 : ℕ) := by
      intro z
      have hsqnn : (0 : ℝ) ≤ (X R z - C) ^ (2 : ℕ) := sq_nonneg _
      rw [← sub_nonneg]
      have hid : C / 2 + (2 * C)⁻¹ * X R z ^ (2 : ℕ) - X R z =
          (2 * C)⁻¹ * (X R z - C) ^ (2 : ℕ) := by
        field_simp
        ring
      rw [hid]
      positivity
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => hX0 R z) hmaj
      (Filter.Eventually.of_forall hpt)
    rw [MeasureTheory.integral_add (integrable_const _) ((hint R hR).const_mul _),
      MeasureTheory.integral_const, MeasureTheory.integral_const_mul] at hmono
    simpa using hmono
  have havg := descendantsAverage_le_descendantsAverage Q j hstep
  rw [descendantsAverage_add Q j (fun _ => C / 2)
      (fun R => (2 * C)⁻¹ * ∫ z, X R z ^ (2 : ℕ) ∂mu),
    descendantsAverage_const,
    descendantsAverage_mul_left Q j (2 * C)⁻¹
      (fun R => ∫ z, X R z ^ (2 : ℕ) ∂mu)] at havg
  have hcoef : (2 * C)⁻¹ *
      descendantsAverage Q j (fun R => ∫ z, X R z ^ (2 : ℕ) ∂mu) ≤
      (2 * C)⁻¹ * C ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  have hval : (2 * C)⁻¹ * C ^ (2 : ℕ) = C / 2 := by
    field_simp
  linarith

/-! ## The reading gauge, and the identification of the two integrands -/

/-- At the load's own gauge the reading cost is `1`.

Unconditional: no caller-supplied proposition enters. -/
private theorem gaugeRatio_self (sigma : PositiveScalar) :
    gaugeRatio sigma sigma = 1 := by
  rw [gaugeRatio, div_self (ne_of_gt sigma.2), max_self]

/-- The integrand read at a positive scalar and the ellipticity load read at the
same scalar are the same term.

Unconditional: no caller-supplied proposition enters. -/
private theorem annealedSqrtNormSq_eq_switchEllipLoad (sigma : PositiveScalar)
    (X : BlockVec d) :
    annealedSqrtNormSq sigma X = switchEllipLoad ((sigma : ℝ)) X := rfl

/-! ## The budget -/

/-- **The grid ellipticity budget, at the actual carriers.**

```
  avsum_R E[ shom_{m-h} |p_R|^2 + shom_{m-h}^{-1} |q_R|^2 ]  <=  Cell ,
```

with `R` running over the triadic descendants of `cu_K` at depth `j`,
`(p_R; q_R) = P_R` the localized load of `e.Pz.def`, and the expectation taken
on `Cutoff.CutoffSample d` under `(Cutoff.cutoffSampleLaw M).toMeasure`.

The constant is `Cell =^2` with the constant of
`exists_const_fourthMoment_annealedSqrtNormSq_principalPz_le`; the module
docstring lists every factor and its origin, and records that the descent from
the fourth moment to the first is lossy.

Reaches exactly the one frozen theorem
`Algsuperdiff.Frozen.External.calderon_zygmund`, a **proved** external.

: this statement holds only under the propositions supplied by its binders --
`hd`; under the leading quantifiers, `M.gamma <= gamma0`, the induction state
`Algsuperdiff.Frozen.Section3.inductionState M m0 Eind`, the parameter gates `0
< hgap`, `m - hgap <= m0`, `hgap <= 6 cstar cgamma^{-1}`, `10^10 cgamma^{-1} <=
K - m`, and the two direction bounds; then the two solution families of
`e.def.w`, and the two per-cube data conditions `hmeasR` (measurability in the
sample of the load) and `hintR` (integrability in the sample of its square).
It is a provider A, not a source-facing frozen declaration. -/
theorem exists_const_descendantsAverage_integral_switchEllipLoad_principalPz_le
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cell : ℝ, 0 < Cell ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
            ∀ (m K : ℤ) (hgap : ℕ), 0 < hgap → m - (hgap : ℤ) ≤ m0 →
              (hgap : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
              (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
              ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
                Book.Ch02.vecNorm e' ≤ 1 →
                ∀ (j : ℕ)
                  (wD : Cutoff.CutoffSample d →
                    H10Function (openCubeSet (originCube d K)))
                  (wN : Cutoff.CutoffSample d →
                    H1MeanZeroFunction (openCubeSet (originCube d K))),
                  (∀ z : Cutoff.CutoffSample d,
                    IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wD z)
                      (fun x => -Corrector.streamForcing
                        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ z.val
                        (m - (hgap : ℤ)) m e x)) →
                  (∀ z : Cutoff.CutoffSample d,
                    IsMeanZeroNeumannRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wN z)
                      (fun x => -Corrector.streamForcing
                        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ z.val
                        (m - (hgap : ℤ)) m e' x)) →
                  (∀ R ∈ descendantsAtDepth (originCube d K) j,
                    Measurable (fun z : Cutoff.CutoffSample d =>
                      switchEllipLoad
                        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
                        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                          z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)))) →
                  (∀ R ∈ descendantsAtDepth (originCube d K) j,
                    Integrable (fun z : Cutoff.CutoffSample d =>
                      switchEllipLoad
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
                          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                            z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) ^
                        (2 : ℕ))
                      (Cutoff.cutoffSampleLaw M).toMeasure) →
                  descendantsAverage (originCube d K) j
                      (fun R => ∫ z : Cutoff.CutoffSample d,
                        switchEllipLoad
                          ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
                          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
                            z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z))
                        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ Cell := by
  classical
  obtain ⟨C0, hC0pos, gamma0, hg0pos, hg0quarter, hbase⟩ :=
    exists_const_fourthMoment_annealedSqrtNormSq_principalPz_le d hd
  refine ⟨C0 ^ (2 : ℕ), by positivity, gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hS m K hgap hhpos hm hh hK e e' he he' j wD wN hwD hwN
    hmeasR hintR
  have hmeasA : ∀ R ∈ descendantsAtDepth (originCube d K) j,
      Measurable (fun z : Cutoff.CutoffSample d =>
        annealedSqrtNormSq (Annealed.sigmaBar M (m - (hgap : ℤ)))
          (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
            z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ)) :=
    fun R hR => (hmeasR R hR).pow_const 2
  have hmeasX := measurable_descendantsAverage_family (originCube d K) j
    (fun (z : Cutoff.CutoffSample d) R =>
      annealedSqrtNormSq (Annealed.sigmaBar M (m - (hgap : ℤ)))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
          z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ)) hmeasA
  have hdisp := hbase M hMgamma m0 Eind hS m K hgap hhpos hm hh hK e e' he he' j
    (Annealed.sigmaBar M (m - (hgap : ℤ))) wD wN hwD hwN hmeasX
  simp only [annealedSqrtNormSq_eq_switchEllipLoad] at hdisp
  have hswap := integral_descendantsAverage_eq_swap
    (Cutoff.cutoffSampleLaw M).toMeasure (originCube d K) j
    (fun (z : Cutoff.CutoffSample d) R =>
      switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
          z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ)) hintR
  rw [hswap, gaugeRatio_self, Real.one_rpow, one_mul] at hdisp
  set A : ℝ := descendantsAverage (originCube d K) j
    (fun R => ∫ z : Cutoff.CutoffSample d,
      switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
          z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact descendantsAverage_nonneg _ _ _ fun R _ =>
      MeasureTheory.integral_nonneg fun z => by positivity
  have hAsq : A ≤ (C0 ^ (2 : ℕ)) ^ (2 : ℕ) := by
    have hid : A = (A ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (A ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hA0]
      norm_num
    have hle : (A ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) ≤ C0 ^ (4 : ℕ) :=
      pow_le_pow_left₀ (Real.rpow_nonneg hA0 _) hdisp 4
    calc A = (A ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) := hid
      _ ≤ C0 ^ (4 : ℕ) := hle
      _ = (C0 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
  exact descendantsAverage_integral_le_of_sq_le (originCube d K) j
    (fun R (z : Cutoff.CutoffSample d) =>
      switchEllipLoad ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))
        (principalPz (Annealed.sigmaBar M (m - (hgap : ℤ)))
          z.val (m - (hgap : ℤ)) m e e' R (wD z) (wN z)))
    (fun R z => switchEllipLoad_nonneg
      (Annealed.sigmaBar M (m - (hgap : ℤ))).2 _) hintR
    (C := C0 ^ (2 : ℕ)) (by positivity) hAsq

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
