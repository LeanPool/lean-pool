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
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Introduction.GeneratorRenormalizationLimit

/-!
# GeneratorRenormalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# Generator renormalization for the coefficient field — [ABK] Theorem B

Source: `algsuperdiff.tex` of arXiv:2601.22142v2, Theorem B of the introduction (`t.homogenization`).

At every scale `m` the coarse-grained generator of the coefficient field
`a = nu I + k` is a constant multiple `sigmaBar` of the identity,
quantitatively close to `sqrt (nu^2 + cstar gamma^{-1} 3^{2 gamma m})`, and
the disorder solution `u` is compared with the homogenized solution `v` of the
same Dirichlet problem: a single random error amplitude with Gaussian-type
moments controls both the uniform difference `u - v` and the difference of the
two Dirichlet energies.

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
leaves free.  The choice is invisible to the two Dirichlet problems of the
statement: the shift is by a constant antisymmetric matrix, and
`Algsuperdiff.Section4.Provider.ExcessDecay.isDirichletSolutionOn_sub_const_of_skew`
says that such a shift moves no solution of the weak problem.

## The form with an infrared cutoff

`Algsuperdiff.Frozen.Section4.generator_renormalization` asserts the same
estimate for the truncated field `(coefficientCutoff nu L omega).toCoeffField`,
uniformly in the cutoff `L ≥ m`, on the unrestricted sample space.  That form
is the more general one and stays part of the public surface; the statement
here is the one the introduction prints, and follows from it in the limit
`L → ∞`.  Outside the carrier, the law and the coefficient field the two
statements share every token.

## Reading of the statement

* **Almost-sure form.** The comparison holds for almost every sample under
  `fullSampleLaw M`, with a single exceptional set serving the whole family of
  data at the scale `m`: the quantifiers over `u`, `v`, `h`, `g` and the three
  constants sit inside the almost-sure clause.  The moment bound on the error
  amplitude is a separate, annealed clause.
* **The diffusivity.** `sigmaBarM` is existential, as the printed statement has
  it: "there exist an effective diffusivity and a random variable".  It is not
  tied to a name here, and it may depend on `m`.
* **Moments.** The bound on `E_B` is stated as
  `∫⁻ E_B^p ≤ (ENNReal.ofReal B)^p` rather than through the `p`-th root of the
  integral.  The two are equivalent for a nonnegative bound, and the power form
  is the one an `ℝ≥0∞`-valued integral states without a division; it also needs
  no integrability or measurability premise, which the printed estimate does
  not have either.
* **The boundary datum.** The normalized norm
  `3^{m/2} ‖∇h‖_{W^{1/2,∞}(□_m)}` of the source is
  `‖∇h‖_{L^∞(□_m)} + 3^{m/2} [∇h]_{C^{0,1/2}(□_m)}`, and it appears here as
  `KhInf + 3^{m/2} Kh`: `KhInf` bounds `‖h.grad x‖` in the sup norm over the
  open cube and `Kh` bounds its `1/2`-Hölder seminorm.  The datum enters as an
  `H1Function` carrying a classical gradient, which `HasGradientOn` pins to
  `h.grad`.
* **The force.** `[g]_{W^{1/2,∞}(□_m)}` is the `1/2`-Hölder seminorm bound
  `Kg` on the open cube.
* **The two conclusions.** The uniform estimate is written as an
  almost-everywhere pointwise bound of `3^{-m} |u - v|` against the volume
  measure restricted to the open cube, which is the essential supremum of the
  source read without a supremum.  The energy estimate compares the volume
  averages of `nu |∇u|²` and of `sigmaBarM |∇v|²` over the same cube.
* **Constants.** `gamma0` and `C` are chosen before the model and before the
  scale, so they depend only on the dimension `d` and on the value `cstar` of
  the model's ellipticity parameter, which is the printed dependence.  One `C`
  serves the diffusivity comparison, the moment amplitude and the upper end of
  the range of `p`, as printed.
* **Non-vacuity.** `FullSample d M.gamma` is inhabited for every model, since
  its law is a probability measure.  The model clause is another matter: this
  development constructs no `ABKModel d`, so the clause is satisfiable only
  vacuously until a construction is supplied, exactly as for the other main
  statements of the development.  The remedy is a separate construction
  theorem, not a change here.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Introduction.generator_renormalization
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
          |sigmaBarM -
              Real.sqrt (M.nu ^ (2 : ℕ) +
                cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
          ∃ EB : Algsuperdiff.Section5.Field.FullSample d M.gamma → ℝ,
            (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                  ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure) ≤
                ENNReal.ofReal
                    (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
            ∀ᵐ omega ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure,
              ∀ (u v h : HCPolySupport.H1Function
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                (g : HCPolySupport.Vec d → HCPolySupport.Vec d)
                (Kg Kh KhInf : ℝ),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
                    (HCPolySupport.originCube d m) u h g →
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (fun _ : HCPolySupport.Vec d => sigmaBarM • (1 : HCPolySupport.Mat d))
                    (HCPolySupport.originCube d m) v h g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kg g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kh h.grad →
                (∀ x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m),
                  ‖h.grad x‖ ≤ KhInf) →
                Algsuperdiff.Section4.Support.HasGradientOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    h.toFun h.grad →
                (∀ᵐ x ∂(MeasureTheory.volume.restrict
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))),
                    Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                      EB omega *
                        (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                  |HCPolySupport.volumeAverage
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                        (fun y => M.nu * HCPolySupport.vecNormSq (u.grad y)) -
                      HCPolySupport.volumeAverage
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                        (fun y => sigmaBarM * HCPolySupport.vecNormSq (v.grad y))| ≤
                    EB omega *
                      (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          Real.sqrt sigmaBarM *
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                        (2 : ℕ)
-- FROZEN-STATEMENT-END
    := by
  exact Algsuperdiff.Section4.Provider.Introduction.generator_renormalization_provider d cstar
    _hcstar
