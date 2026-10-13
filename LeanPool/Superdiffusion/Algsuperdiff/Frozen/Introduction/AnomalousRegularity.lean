/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ClassicalGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.FreezingRadius
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Introduction.AnomalousRegularityLimit

/-!
# AnomalousRegularity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Anomalous regularity for the coefficient field — [ABK] Theorem C

Source: `algsuperdiff.tex` of arXiv:2601.22142v2, Theorem C of the introduction (`t.regularity`).

For a disorder model of strength `gamma` small enough, and every Hölder
exponent `alpha` below `1 - C sqrt gamma`, there is an almost surely finite
minimal scale `X` with an exponential tail such that, above `X`, every
Dirichlet solution of the coefficient field `nu I + k` on a triadic cube with
`C^{0,1/2}` force `g` and `C^{1,1/2}` boundary datum `h` satisfies the
`C^{0,alpha}` large-scale excess decay `3^{(1-alpha)(m-n)}` between any two
scales `n ≤ m`.

## The carrier and the coefficient field

The disorder is read on `Algsuperdiff.Section5.Field.FullSample d M.gamma`
under `Algsuperdiff.Section5.Field.fullSampleLaw M`, the carrier the quenched
superdiffusivity estimates use: the subtype of samples on which the field's
two-sided scale rates and gradient bounds hold.  That event has full measure
for the unrestricted law, so the restriction loses nothing, and it is what
makes the coefficient field a total function of the sample rather than a
partially defined one.

The field is `Algsuperdiff.Section5.Field.streamCoefficient M.nu omega`, that
is `nu I + k_omega` with `k_omega x = Σ_{n ∈ ℤ} (j_n x - j_n 0)`.  The shell
sum is normalized at the origin, which fixes the additive constant the source
leaves free.  The choice is invisible to the Dirichlet problem of the
statement: the shift is by a constant antisymmetric matrix, and
`Algsuperdiff.Section4.Provider.ExcessDecay.isDirichletSolutionOn_sub_const_of_skew`
says that such a shift moves no solution of the weak problem.

## The form with an infrared cutoff

`Algsuperdiff.Frozen.Section4.anomalous_regularity` asserts the same estimate
for the truncated field `(coefficientCutoff nu L omega).toCoeffField`,
uniformly in the cutoff `L ≥ m`, on the unrestricted sample space.  That form
is the more general one and stays part of the public surface; the statement
here is the one the introduction prints, and follows from it in the limit
`L → ∞`.  Outside the carrier, the law and the coefficient field the two
statements share every token.

## Reading of the statement

* **Almost-sure form.** The excess decay holds for almost every sample under
  `fullSampleLaw M`, with a single exceptional set serving the whole family of
  data at the scale `m`.  The tail bound on the minimal scale is a separate,
  annealed clause, and the same random variable `X` carries both.
* **The minimal scale.** `X` takes values in `ℕ∞`, so its type carries no finiteness
  assumption; the tail bound is what forces it to be almost surely finite.  The scale clause `X omega ≤ (m - n).toNat` is the printed
  `X_m(alpha) ≤ m - n` under the hypothesis `n ≤ m`, where the truncated
  subtraction agrees with the integer one.
* **The diffusivity.** The comparison amplitude is the named annealed gauge
  `Annealed.sigmaBar M m`, not an existential: this theorem quotes the
  diffusivity that the renormalization theorem produces rather than producing
  one of its own.
* **The boundary datum.** The normalized norm
  `3^{m/2} ‖∇h‖_{W^{1/2,∞}(□_m)}` of the source is
  `‖∇h‖_{L^∞(□_m)} + 3^{m/2} [∇h]_{C^{0,1/2}(□_m)}`.  A single constant `Kh`
  bounds both pieces here — the sup norm of `h.grad` by `3^{m/2} Kh` and its
  `1/2`-Hölder seminorm by `Kh` — so the printed sum is at most `2 · 3^{m/2}
  Kh` and the factor `2` is absorbed into `C`.  The datum enters as an
  `H1Function` carrying a classical gradient, which `HasGradientOn` pins to
  `h.grad`.
* **The force.** `[g]_{W^{1/2,∞}(□_m)}` is the `1/2`-Hölder seminorm bound
  `Kg` on the open cube.
* **The indicator.** The boundary-datum term of the printed display carries the
  indicator of `x ∉ □_{m-1}`.  It appears here as a conjunction of two
  estimates: the one with that term, valid at every `x` in the cube, and the
  one without it, valid when `x ∈ □_{m-1}`.  The two readings are equivalent.
* **The norms.** `nu^{1/2} ‖∇u‖_{L²(S)}` is
  `ENNReal.ofReal (sqrt nu)` times the `L²` norm of `|∇u|` against
  `normalizedVolumeMeasureOn S`, the volume measure of `S` normalized to a
  probability measure, and the sets `S` are the intersections of the translated
  cube `x + □_n` with `□_m`.
* **Constants.** `gamma0` and `C` are chosen before the model, before the
  exponent and before the scale, so they depend only on the dimension `d` and
  on the value `cstar` of the model's ellipticity parameter, which is the
  printed dependence.  One `C` serves the range of `alpha`, the tail of the
  minimal scale and the amplitude of the excess decay, as printed.
* **Non-vacuity.** `FullSample d M.gamma` is inhabited for every model, since
  its law is a probability measure.  The model clause is another matter: this
  development constructs no `ABKModel d`, so the clause is satisfiable only
  vacuously until a construction is supplied, exactly as for the other main
  statements of the development.  The remedy is a separate construction
  theorem, not a change here.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Introduction.anomalous_regularity
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Algsuperdiff.Section5.Field.FullSample d M.gamma → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure
                    {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure,
              ∀ (u h : HCPolySupport.H1Function
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                (g : HCPolySupport.Vec d → HCPolySupport.Vec d)
                (Kg Kh : ℝ),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
                    (HCPolySupport.originCube d m) u h g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kg g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kh h.grad →
                (∀ y ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m),
                  ‖h.grad y‖ ≤ Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh) →
                Algsuperdiff.Section4.Support.HasGradientOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    h.toFun h.grad →
                ∀ x : HCPolySupport.Vec d,
                  x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m) →
                  ∀ n : ℤ, n ≤ m → X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) →
                    (ENNReal.ofReal (Real.sqrt M.nu) *
                        MeasureTheory.eLpNorm
                          (fun y => Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                          (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                            (((fun y => x + y) ''
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d n)) ∩
                              HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) ≤
                      ENNReal.ofReal
                          (C *
                            Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                        (ENNReal.ofReal (Real.sqrt M.nu) *
                            MeasureTheory.eLpNorm
                              (fun y =>
                                Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                              (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                (HCPolySupport.openCubeSet
                                  (HCPolySupport.originCube d m))) +
                          ENNReal.ofReal
                            (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg) +
                          ENNReal.ofReal
                            (Real.sqrt (Annealed.sigmaBar M m : ℝ) *
                              Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                    (x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d (m - 1)) →
                      ENNReal.ofReal (Real.sqrt M.nu) *
                          MeasureTheory.eLpNorm
                            (fun y => Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                            (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                              (((fun y => x + y) ''
                                  HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d n)) ∩
                                HCPolySupport.openCubeSet (HCPolySupport.originCube d m))) ≤
                        ENNReal.ofReal
                            (C *
                              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
                          (ENNReal.ofReal (Real.sqrt M.nu) *
                              MeasureTheory.eLpNorm
                                (fun y =>
                                  Real.sqrt (HCPolySupport.vecNormSq (u.grad y))) 2
                                (Algsuperdiff.Section4.Support.normalizedVolumeMeasureOn
                                  (HCPolySupport.openCubeSet
                                    (HCPolySupport.originCube d m))) +
                            ENNReal.ofReal
                              (Real.sqrt (Annealed.sigmaBar M m : ℝ)⁻¹ *
                                  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)))
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.Introduction.anomalous_regularity_provider d cstar _hcstar
