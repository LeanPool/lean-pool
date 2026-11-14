/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.JResponseApplication
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# PrincipalResponseComposeDisplayTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: display 2 of leg (iv) in the manuscript's own printed shape

Source display in ABK26, inside Step 3 of the proof of
`l.approximate.recurrence.formula` (label):

```
  ( avsum_{z in 3^n Zd cap cu_K} E[ | bfAhom_{m-1}^{1/2} P_z |^4 ] )^{1/4}  <=  C .
```

The proved `exists_const_fourthMoment_annealedSqrtNormSq_principalPz_le`
(`PrincipalResponseDisplayTwo`) delivers this display in two respects weaker
than printed:

* its right-hand side carries the **visible gauge factor**
  `(gaugeRatio shom_{m-h} sigmaTop)^{1/2}` instead of the bare `C`, because the
  three scale gates that theorem binds constrain no scale above `m0 >= m - h`,
  hence say nothing about the reading scale `m - 1`.

This module removes both gaps, and nothing else.

## The order swap

`descendantsAverage Q j` is by definition `(card)^{-1}` times a **finite**
`Finset` sum, so the swap is the linearity of the Bochner integral over a
finite index set (`integral_const_mul` and `integral_finsetSum`).  What
linearity costs is exactly one side condition: each individual expectation must
exist.  That is `hintR` below, a per-cube integrability binder.  It is a
well-definedness condition on the manuscript's own `E[ ... ]`, of the same
class as the measurability binder `hmeasX` already carried by the proved
display, and it is *not* a bound: no numerical estimate, and no conclusion of
any predecessor node, is assumed by it.  `hmeasR` is the matching per-cube
measurability, from which the proved display's own composite `hmeasX` is
produced here rather than demanded of the caller.

## The bare `C`

`gaugeRatio sigmaLow sigmaTop = max (sigmaTop / sigmaLow) (sigmaLow /
sigmaTop)`.  At the manuscript's own pair of scales, `sigmaLow = shom_{m-h}`
and `sigmaTop = shom_{m-1}`, the two-sided envelope `e.shom.h.bounds` (the
first clause of `d.mathcalS.def`) controls both quotients through the two
proved running-diffusivity comparisons

```
  shom_i <= 4 . 3^{cgamma (i - j)} . shom_j ,      shom_j <= 4 shom_i
                                                  (j <= i <= m_0) .
```

Since `h >= 1` we have `m - h <= m - 1`, and the shell budget `h <= 6 cstar
cgamma^{-1}`/7183 -- a gate the proved display already binds -- together with
`cstar <= 3/2` gives `cgamma ((m-1) - (m-h)) = cgamma (h - 1) <= 6 cstar <= 9`,
so the exponential factor is at most `3^9`.  Hence

```
  gaugeRatio shom_{m-h} shom_{m-1}  <=  4 . 3^9 ,
```

an absolute constant.  The *only* genuinely new input is the gate `m - 1 <= m_0`
(`hm1`), which places the reading scale inside the range on which the induction
state is available; it is carried as an explicit binder, never discharged and
never hidden.  The manuscript's "by `e.shom.h.bounds`" is exactly this step, and
this is where its scale requirement becomes visible.

## Binders

Every theorem below is a **** provider result: each is stated under
propositions the caller must supply, and none of them is a source-facing frozen
declaration.  What the caller owes, plainly:

* `integral_descendantsAverage_eq_descendantsAverage_integral_real` and
  `measurable_descendantsAverage_real` ask only for per-cube integrability
  respectively per-cube measurability of the family being averaged.  These are
  well-definedness conditions on the manuscript's own `E[ . ]`, not estimates.
* `gaugeRatio_sigmaBar_le_readingConst` asks for the induction state `hS`
  (`d.mathcalS.def`, supplying `e.shom.h.bounds`), the shell budget `hh` (`h <=
  6 cstar cgamma^{-1}`,/7183) and the reading-scale gate `hm1` (`m - 1 <= m0`).
  `hm1` is the one genuinely new input; it is the scale requirement the
  manuscript leaves implicit when it appeals to `e.shom.h.bounds` at the
  reading scale.
* `exists_const_gridAverage_fourthMoment_annealedSqrtNormSq_principalPz_le`
  asks for `hS`, the two corrector definitions `hwD`/`hwN` (`e.def.w`), the
  four scale gates `hm` (`m - h <= m0`), `hm1`, `hh` and `hK`
  (`e.recurrence.params`), and the two per-cube regularity binders
  `hmeasR`/`hintR`.

No proof step of the source argument, and no conclusion of a predecessor node,
is assumed by any of them.

## References

* ABK26, display, inside `l.approximate.recurrence.formula`; `e.Pz.def`;
  `e.def.w`; `e.recurrence.params`; `e.shom.h.bounds` (first clause of
  `d.mathcalS.def`); ABK26 (the running-diffusivity comparison at constant `4`).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The order of the two averages -/

/-- **Expectation and grid average commute.**  `descendantsAverage Q j` is a
normalized finite `Finset` sum, so the manuscript's `avsum_z E[ . ]` and the
pathwise-then-integrate `E[ avsum_z . ]` agree as soon as each individual
expectation exists.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem integral_descendantsAverage_eq_descendantsAverage_integral_real
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

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem measurable_descendantsAverage_real
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

/-! ## The reading gauge -/

/-- **The gauge factor is an absolute constant** at the manuscript's own pair of
scales.

On the range where the induction state is available -- `m - h <= m - 1 <= m0`
-- `e.shom.h.bounds` gives `shom_{m-1} <= 4 . 3^{cgamma (h-1)} shom_{m-h}` and
`shom_{m-h} <= 4 shom_{m-1}`.  The shell budget `h <= 6 cstar cgamma^{-1}`/7183
together with `cstar <= 3/2` caps the exponent at `9`, so both quotients are at
most `4 . 3^9`.

`hm1` is the reading-scale gate: it is a genuine input, not derivable from the
gates, and is carried as a binder.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem gaugeRatio_sigmaBar_le_readingConst (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {m : ℤ} {h : ℕ}
    (hhpos : 0 < h) (hm1 : m - 1 ≤ m0)
    (hh : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹) :
    gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ))) (Annealed.sigmaBar M (m - 1)) ≤
      4 * (3 : ℝ) ^ (9 : ℕ) := by
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hle : m - (h : ℤ) ≤ m - 1 := by
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
    omega
  have hposLow : (0 : ℝ) < (Annealed.sigmaBar M (m - (h : ℤ)) : ℝ) :=
    (Annealed.sigmaBar M (m - (h : ℤ))).2
  have hposTop : (0 : ℝ) < (Annealed.sigmaBar M (m - 1) : ℝ) :=
    (Annealed.sigmaBar M (m - 1)).2
  have hexp : M.gamma * (((m - 1 : ℤ) : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ)) ≤ (9 : ℝ) := by
    have hcast : ((m - 1 : ℤ) : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ) = (h : ℝ) - 1 := by
      push_cast
      ring
    rw [hcast]
    have hmul : M.gamma * ((h : ℝ) - 1) ≤ M.gamma * (h : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) hgamma.le
    have hprod : M.gamma * (h : ℝ) ≤ M.gamma * (6 * Disorder.cstar M * M.gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hh hgamma.le
    have hcancel : M.gamma * (6 * Disorder.cstar M * M.gamma⁻¹) =
        6 * Disorder.cstar M := by
      field_simp
    have hcstar : Disorder.cstar M ≤ 3 / 2 := Provider.Disorder.cstar_le_three_halves M
    rw [hcancel] at hprod
    linarith
  have hrpow : (3 : ℝ) ^ (M.gamma * (((m - 1 : ℤ) : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ))) ≤
      (3 : ℝ) ^ (9 : ℕ) := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hnine : (3 : ℝ) ^ (9 : ℝ) = (3 : ℝ) ^ (9 : ℕ) := by
      rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [hnine] at hmono
  have hforward :=
    Provider.Multiscale.sigmaBar_le_four_mul_rpow_mul_sigmaBar M hS hle hm1
  have hreverse := Provider.Multiscale.sigmaBar_le_four_mul_sigmaBar M hS hle hm1
  refine max_le ?_ ?_
  · rw [div_le_iff₀ hposLow]
    refine hforward.trans ?_
    have hcoef : 4 * (3 : ℝ) ^
        (M.gamma * (((m - 1 : ℤ) : ℝ) - ((m - (h : ℤ) : ℤ) : ℝ))) ≤
        4 * (3 : ℝ) ^ (9 : ℕ) := by linarith
    exact mul_le_mul_of_nonneg_right hcoef hposLow.le
  · rw [div_le_iff₀ hposTop]
    refine hreverse.trans ?_
    have h4 : (4 : ℝ) ≤ 4 * (3 : ℝ) ^ (9 : ℕ) := by
      have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (9 : ℕ) := one_le_pow₀ (by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right h4 hposTop.le

/-! ## Display 2 in the printed shape -/

/-- **Display 2 of leg (iv) of `l.approximate.recurrence.formula`, in the
manuscript's own order and with the printed bare constant.**

There is a dimension-free constant `C` and a positive threshold `gamma0` such
that, for every ABK model with `cgamma <= gamma0`, every valid induction state
`S(m0, E)`, every `m, K, h` obeying the four scale gates `m - h <= m0`,
`m - 1 <= m0`, `h <= 6 cstar cgamma^{-1}` and `K >= m + 10^10 cgamma^{-1}`, all
directions `e, e'` of Euclidean length at most one, every localization depth `j`
and every sample family of solutions of the two problems `e.def.w`,

```
  ( avsum_R E[ | bfAhom_{m-1}^{1/2} P_R |^4 ] )^{1/4}  <=  C ,
```

with `R` running over the triadic descendants of `cu_K` at depth `j` and `P_R`
the localized load of `e.Pz.def`, read at the manuscript's own gauge
`shom_{m-1}`.

`hmeasR` and `hintR` are the per-cube well-definedness binders of the printed
`E[ . ]`; `hm1` is the reading-scale gate discussed in the module header.

: this statement holds only under the propositions supplied by its binders; it
is a provider A, not a source-facing frozen declaration. -/
theorem exists_const_gridAverage_fourthMoment_annealedSqrtNormSq_principalPz_le
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
        ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
          ∀ (m0 : ℤ) (E : {E : ℝ // 1 ≤ E}),
            Algsuperdiff.Frozen.Section3.inductionState M m0 E →
            ∀ (m K : ℤ) (h : ℕ), 0 < h → m - (h : ℤ) ≤ m0 → m - 1 ≤ m0 →
              (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
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
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
                        (m - (h : ℤ)) m e x)) →
                  (∀ z : Cutoff.CutoffSample d,
                    IsMeanZeroNeumannRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wN z)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ z.val
                        (m - (h : ℤ)) m e' x)) →
                  (∀ R ∈ descendantsAtDepth (originCube d K) j,
                    Measurable (fun z : Cutoff.CutoffSample d =>
                      annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
                        (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val
                          (m - (h : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ))) →
                  (∀ R ∈ descendantsAtDepth (originCube d K) j,
                    Integrable (fun z : Cutoff.CutoffSample d =>
                      annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
                        (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val
                          (m - (h : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ))
                      (Cutoff.cutoffSampleLaw M).toMeasure) →
                  (descendantsAverage (originCube d K) j
                      (fun R => ∫ z : Cutoff.CutoffSample d,
                        annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
                          (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val
                            (m - (h : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ)
                        ∂(Cutoff.cutoffSampleLaw M).toMeasure)) ^ ((1 : ℝ) / 4) ≤
                    C := by
  obtain ⟨C0, hC0pos, gamma0, hg0pos, hg0quarter, hbase⟩ :=
    exists_const_fourthMoment_annealedSqrtNormSq_principalPz_le d hd
  refine ⟨(4 * (3 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 2) * C0,
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) hC0pos,
    gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 E hS m K h hhpos hm hm1 hh hK e e' he he' j wD wN hwD hwN
    hmeasR hintR
  have hswap := integral_descendantsAverage_eq_descendantsAverage_integral_real
    (Cutoff.cutoffSampleLaw M).toMeasure (originCube d K) j
    (fun z R => annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
      (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val
        (m - (h : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ)) hintR
  have hmeasX := measurable_descendantsAverage_real (originCube d K) j
    (fun (z : Cutoff.CutoffSample d) R =>
      annealedSqrtNormSq (Annealed.sigmaBar M (m - 1))
        (principalPz (Annealed.sigmaBar M (m - (h : ℤ))) z.val
          (m - (h : ℤ)) m e e' R (wD z) (wN z)) ^ (2 : ℕ)) hmeasR
  have hdisp := hbase M hMgamma m0 E hS m K h hhpos hm hh hK e e' he he' j
    (Annealed.sigmaBar M (m - 1)) wD wN hwD hwN hmeasX
  rw [hswap] at hdisp
  refine hdisp.trans ?_
  have hgauge := gaugeRatio_sigmaBar_le_readingConst M hS hhpos hm1 hh
  have hgpos : (0 : ℝ) < gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ)))
      (Annealed.sigmaBar M (m - 1)) := gaugeRatio_pos _ _
  have hrp : gaugeRatio (Annealed.sigmaBar M (m - (h : ℤ)))
        (Annealed.sigmaBar M (m - 1)) ^ ((1 : ℝ) / 2) ≤
      (4 * (3 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hgpos.le hgauge (by norm_num)
  exact mul_le_mul_of_nonneg_right hrp hC0pos.le

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
