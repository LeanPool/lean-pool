/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationNestedAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.StreamForcingDeriv

/-!
# OscillationAssemblyShell

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `e.nablaw.oscillations` at the fresh-shell correctors

ABK26 claims, for every mesh point `z` with `z + cu_{m-h} ⊂ cu_K`,

```
  ‖ ∇w_{D,e}^{(K)} - (∇w_{D,e}^{(K)})_{z+cu_n} ‖_{L2bar(z+cu_n)}
    ≤ C 3^{-(m-h-n)} ‖ ∇w_{D,e}^{(K)} ‖_{L2bar(z+cu_{m-h})}
      + C shom_{m-h}^{-1} (m-h-n) 3^n ‖ ∇(k_m - k_{m-h}) ‖_{L∞(z+cu_{m-h})} ,
```

and adds "the same results are valid for `w_{N,e'}^{(K)}`".

This module instantiates the abstract nested-recentring display of
`OscillationNestedAssembly` at exactly those carriers: `w` is the actual
finite-volume corrector of `e.def.w` on `cu_K` (Dirichlet or Neumann), the
forcing is the actual fresh-shell forcing `streamForcing`, and the concentric
family is the interior mesh cube `z + cu_{n+N}` with `N = m - h - n`.

## The three ingredients

* The abstract display, `exists_gradient_oscillation_nested_telescope_norm`.
* Coordinatewise differentiability and the differential bound of the forcing,
  `StreamForcingDeriv`.
* The passage of the weak equation from `cu_K` to the interior mesh cube,
  `forall_h10Function_integral_vecDot_grad_eq_of_subset`
  (`OscillationNestedTransport`), which is CoarseGraining's restriction of
  solenoidality along the extension by zero.

## The Neumann leg

The Neumann corrector's natural boundary condition enlarges its test class from
`H^1_0(cu_K)` to the mean-zero gauge of `H^1(cu_K)`, and the mean-zero
representative of an `H^1_0` competitor has the same gradient
(`H1Function.toMeanZero_grad`).  So the Neumann weak equation *implies* the
`H^1_0`-tested equation on `cu_K`, and from there the interior transport and the
telescope are word for word the Dirichlet ones.  Both legs are therefore
produced below, from one shared core.

## Contents

* `exists_freshShellDirichlet_gradient_oscillation_interior_mesh` and
  `exists_freshShellNeumann_gradient_oscillation_interior_mesh` -- the display
  at the two correctors, with the forcing amplitude quantified over majorants of
  the exact induced shell-derivative gauge.
* `exists_freshShellDirichlet_gradient_oscillation_interior_mesh_localGauge` and
  its Neumann counterpart -- the same, with the amplitude written as the summed
  first-derivative gauges `∑_{k ∈ (m-h,m]} ‖∇j_k‖_{L∞(z+cu_{m-h})}`, which is the
  carrier of `e.nabla.km.kn.infty` at base point `z`
  (`Provider.Stream.isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate`).

All four statements quantify over the corrector families rather than producing
them: `wD` and `wN` enter as arbitrary families of weak solutions of `e.def.w`,
and their existence is the business of `FreshShellExistence`.

## Divergences from the printed statement

* **.**  The statement is the *interior* one: it is quantified over base points
  `z` subject to `z + cu_{n+N} ⊆ cu_K`, exactly the restriction printed.
* **The lattice hypothesis is dropped.**  The manuscript restricts to
  `z ∈ 3^n Z^d ∩ cu_K`; the proof uses no lattice property, so the realization
  below quantifies over all base points with the containment, which is strictly
  stronger.
* **The gap restriction `d + 3`.**  The telescope's coarse term uses the
  arbitrary-gap harmonic decay, available only for gaps `≥ d + 3`, so the
  number of scales `N = m - h - n` must satisfy `d + 3 ≤ N`.  This is inherited
  from `OscillationNestedAssembly`  and is carried as an explicit hypothesis.
* **The forcing amplitude is quantified over majorants.**  The printed
  right-hand side contains `‖∇(k_m - k_{m-h})‖_{L∞(z+cu_{m-h})}`.  Here the
  statement is universally quantified over real numbers `Kgrad` dominating that
  exact induced gauge pointwise on `z + cu_{m-h}`; since the supremum is itself
  such a number, this form implies the printed one and is stronger.
* **The gauge reading of the forcing term is the lossless one.**  The summed
  first-derivative gauges `∑_{k ∈ (n',m]} ‖∇j_k‖_{L∞(z+cu_ell)}` dominate
  `‖∇(k_m - k_{n'})‖_{L∞(z+cu_ell)}` by the triangle inequality with no loss;
  that is the `_localGauge` form, and it is the carrier of
  `e.nabla.km.kn.infty`.  Reading the amplitude off the *summand* of
  `e.W.1.inf.bound` instead would cost the factor `3^{-(n'+1)}` applied to the
  whole sum, because that summand carries the increasing weight `3^k`, hence a
  loss of at most `3^{m-n'-1}` in general and of `3^{gamma(m-n')}` once the
  shell gauges are inserted at their own amplitudes.  In the parameter regime
  of `e.recurrence.params` that residue is `3^{gamma h}` with
  `gamma h ≤ 6 cstar`, i.e. bounded, but it is **not** dimension-only, so only
  the lossless reading is delivered here.
* **The visible `sqrt d`.**  The ambient carrier `Vec d` is sup-normed while the
  shell-derivative gauge is Euclidean, so the amplitude reads
  `sigmaInv * sqrt d * |e|_2 * Kgrad`.  The factor is written out, not absorbed;
  the manuscript's `C` is dimension-only and absorbs it.

## References

* ABK26, `e.nablaw.oscillations`.
* ABK26, `e.def.w`.
* ABK26, `e.W.1.inf.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3

noncomputable section

variable {d : ℕ}

/-! ## One elementary fact -/

/-- The Laplacian's coefficient field acts trivially on the gradient. -/
private theorem matVecMul_identity (v : Vec d) :
    matVecMul (1 : Matrix (Fin d) (Fin d) ℝ) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

/-! ## The shared core -/

/-- **The nested-recentring display at the fresh-shell forcing.**

An `H^1` function on the large cube `cu_K` which solves
`int <grad u, grad psi> = int <-streamForcing, grad psi>` against every
`H^1_0(cu_K)` competitor obeys, on every interior mesh cube `z + cu_{n+N}`
with `N ≥ d + 3`, the oscillation display of `e.nablaw.oscillations`. -/
private theorem exists_streamForcing_gradient_oscillation_core (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : TriadicCube d) (z : Vec d) (n : ℤ) (N : ℕ), d + 3 ≤ N →
        openCubeAtScale z (n + (N : ℤ)) ⊆ openCubeSet Q →
        ∀ (sigmaInv : ℝ), 0 ≤ sigmaInv →
          ∀ (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e : Vec d)
            (Kgrad : ℝ),
            (∀ y ∈ openCubeAtScale z (n + (N : ℤ)),
              ShellField.matrixDerivativeNorm
                (∑ k ∈ Finset.Ioc lowScale highScale,
                  ShellField.deriv (omega k) y) ≤ Kgrad) →
            ∀ u : H1Function (openCubeSet Q),
              (∀ ψ : H10Function (openCubeSet Q),
                ∫ x in openCubeSet Q, vecDot (u.grad x) (ψ.toH1Function.grad x) ∂volume =
                  ∫ x in openCubeSet Q,
                    vecDot (-streamForcing sigmaInv omega lowScale highScale e x)
                      (ψ.toH1Function.grad x) ∂volume) →
              Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
                  (openCubeAtScale z n) u.grad)
                ≤ C * (3 : ℝ) ^ (-(N : ℤ)) *
                    Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                      (openCubeAtScale z (n + (N : ℤ))) u.grad 0)
                  + C * (N : ℝ) * ((3 : ℝ) ^ n *
                      (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e * Kgrad)) := by
  obtain ⟨C, hCnn, hC⟩ := exists_gradient_oscillation_nested_telescope_norm hd
  refine ⟨C, hCnn, ?_⟩
  intro Q z n N hN hsub sigmaInv hsigma omega lowScale highScale e Kgrad hKgrad u hu
  have : IsFiniteMeasure (volumeMeasureOn (openCubeAtScale z (n + (N : ℤ)))) :=
    isFiniteMeasure_restrict.mpr (volume_openCubeAtScale_ne_top z (n + (N : ℤ)))
  -- the forcing, in the sign convention of the CoarseGraining weak-solution predicates
  set G : Vec d → Vec d :=
    fun x => -streamForcing sigmaInv omega lowScale highScale e x with hGdef
  have hGcont : Continuous G := (continuous_streamForcing _ _ _ _ _).neg
  -- the amplitude
  have hKgradnn : 0 ≤ Kgrad :=
    le_trans (ShellField.matrixDerivativeNorm_nonneg _)
      (hKgrad z (mem_openCubeAtScale_self z (n + (N : ℤ))))
  have hhead : (0 : ℝ) ≤ sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e :=
    mul_nonneg (mul_nonneg hsigma (Real.sqrt_nonneg _)) (Book.Ch02.vecNorm_nonneg e)
  have hMnn : (0 : ℝ) ≤ sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e * Kgrad :=
    mul_nonneg hhead hKgradnn
  -- the two properties of the forcing the telescope consumes
  have hGdiff : ∀ i : Fin d, Differentiable ℝ fun y => G y i := by
    intro i
    exact differentiable_neg_streamForcing_coord sigmaInv omega lowScale highScale e i
  have hGbound : ∀ x ∈ openCubeAtScale z (n + (N : ℤ)), ∀ i : Fin d,
      ‖fderiv ℝ (fun y => G y i) x‖ ≤
        sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e * Kgrad := by
    intro x hx i
    refine (norm_fderiv_neg_streamForcing_coord_le sigmaInv omega lowScale highScale
      e i x).trans ?_
    rw [abs_of_nonneg hsigma]
    exact mul_le_mul_of_nonneg_left (hKgrad x hx) hhead
  -- the weak equation, moved to the interior mesh cube
  have hAL2 : MemVectorL2 (openCubeSet Q) u.grad := u.grad_memVectorL2
  have hGL2 : MemVectorL2 (openCubeSet Q) G :=
    memVectorL2_openCubeSet_of_continuous Q hGcont
  have hwV := forall_h10Function_integral_vecDot_grad_eq_of_subset
    (isOpen_openCubeSet Q) (isOpen_openCubeAtScale z (n + (N : ℤ))) hsub hAL2 hGL2 hu
  exact hC z n N hN (u.restrict (isOpen_openCubeAtScale z (n + (N : ℤ))) hsub) G
    (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e * Kgrad) hMnn hGdiff hGbound hwV

/-! ## The Dirichlet leg -/

/-- **`e.nablaw.oscillations` for the Dirichlet corrector of `e.def.w`.**

For the actual zero-trace solution `w_{D,e}^{(K)}` of `e.def.w` on `cu_K`, on
every interior mesh cube `z + cu_{n+N}` with `z + cu_{n+N} ⊆ cu_K` and
`N ≥ d + 3`,

```
  ‖ ∇w_D - (∇w_D)_{z+cu_n} ‖_{L2bar(z+cu_n)}
    ≤ C 3^{-N} ‖ ∇w_D ‖_{L2bar(z+cu_{n+N})}
      + C N 3^n (sigmaInv sqrt d |e|_2 Kgrad) ,
```

with `N = m - h - n`, `sigmaInv = shom_{m-h}^{-1}` and `Kgrad` any pointwise
majorant of `‖∇(k_m - k_{m-h})‖` on `z + cu_{n+N}` in the exact induced
shell-derivative gauge. -/
theorem exists_freshShellDirichlet_gradient_oscillation_interior_mesh (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K n : ℤ) (N : ℕ), d + 3 ≤ N →
        ∀ z : Vec d,
          openCubeAtScale z (n + (N : ℤ)) ⊆ openCubeSet (originCube d K) →
          ∀ (sigmaInv : ℝ), 0 ≤ sigmaInv →
            ∀ (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e : Vec d)
              (Kgrad : ℝ),
              (∀ y ∈ openCubeAtScale z (n + (N : ℤ)),
                ShellField.matrixDerivativeNorm
                  (∑ k ∈ Finset.Ioc lowScale highScale,
                    ShellField.deriv (omega k) y) ≤ Kgrad) →
              ∀ wD : H10Function (openCubeSet (originCube d K)),
                IsZeroTraceDirichletRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) wD
                    (fun x => -streamForcing sigmaInv omega lowScale highScale e x) →
                Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
                    (openCubeAtScale z n) wD.toH1Function.grad)
                  ≤ C * (3 : ℝ) ^ (-(N : ℤ)) *
                      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                        (openCubeAtScale z (n + (N : ℤ))) wD.toH1Function.grad 0)
                    + C * (N : ℝ) * ((3 : ℝ) ^ n *
                        (sigmaInv * Real.sqrt (d : ℝ) *
                          Book.Ch02.vecNorm e * Kgrad)) := by
  obtain ⟨C, hCnn, hC⟩ := exists_streamForcing_gradient_oscillation_core hd
  refine ⟨C, hCnn, ?_⟩
  intro K n N hN z hsub sigmaInv hsigma omega lowScale highScale e Kgrad hKgrad wD hwD
  refine hC (originCube d K) z n N hN hsub sigmaInv hsigma omega lowScale highScale e
    Kgrad hKgrad wD.toH1Function ?_
  intro ψ
  have h := hwD ψ
  simpa only [matVecMul_identity] using h

/-! ## The Neumann leg -/

/-- **`e.nablaw.oscillations` for the Neumann corrector of `e.def.w`.**

The manuscript's "the same results are valid for `w_{N,e'}^{(K)}`".  The natural
boundary condition of the Neumann problem *enlarges* the test class from
`H^1_0(cu_K)` to the mean-zero gauge of `H^1(cu_K)`, and mean subtraction does
not change a gradient, so the Neumann weak equation implies the `H^1_0`-tested
equation, and the interior transport and telescope are unchanged. -/
theorem exists_freshShellNeumann_gradient_oscillation_interior_mesh (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K n : ℤ) (N : ℕ), d + 3 ≤ N →
        ∀ z : Vec d,
          openCubeAtScale z (n + (N : ℤ)) ⊆ openCubeSet (originCube d K) →
          ∀ (sigmaInv : ℝ), 0 ≤ sigmaInv →
            ∀ (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d)
              (Kgrad : ℝ),
              (∀ y ∈ openCubeAtScale z (n + (N : ℤ)),
                ShellField.matrixDerivativeNorm
                  (∑ k ∈ Finset.Ioc lowScale highScale,
                    ShellField.deriv (omega k) y) ≤ Kgrad) →
              ∀ wN : H1MeanZeroFunction (openCubeSet (originCube d K)),
                IsMeanZeroNeumannRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) wN
                    (fun x => -streamForcing sigmaInv omega lowScale highScale e' x) →
                Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
                    (openCubeAtScale z n) wN.toH1Function.grad)
                  ≤ C * (3 : ℝ) ^ (-(N : ℤ)) *
                      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                        (openCubeAtScale z (n + (N : ℤ))) wN.toH1Function.grad 0)
                    + C * (N : ℝ) * ((3 : ℝ) ^ n *
                        (sigmaInv * Real.sqrt (d : ℝ) *
                          Book.Ch02.vecNorm e' * Kgrad)) := by
  obtain ⟨C, hCnn, hC⟩ := exists_streamForcing_gradient_oscillation_core hd
  refine ⟨C, hCnn, ?_⟩
  intro K n N hN z hsub sigmaInv hsigma omega lowScale highScale e' Kgrad hKgrad wN hwN
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d K))) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet (originCube d K)
  refine hC (originCube d K) z n N hN hsub sigmaInv hsigma omega lowScale highScale e'
    Kgrad hKgrad wN.toH1Function ?_
  intro ψ
  have h := hwN ψ.toH1Function.toMeanZero
  simpa only [matVecMul_identity, H1Function.toMeanZero_grad] using h

/-! ## The forcing term in the gauges of `e.W.1.inf.bound` -/

/-- **The Dirichlet display with the forcing term in the summed first-derivative
shell gauges.**

Same statement as
`exists_freshShellDirichlet_gradient_oscillation_interior_mesh`, with the
majorant `Kgrad` taken to be `∑_{k ∈ (lowScale, highScale]} ‖∇j_k‖_{L∞(z+cu_ell)}`
at `ell = n + N`.  This is the sharp reading: the triangle inequality over the
shells loses nothing, and the random variable on the right is literally the one
bounded by `Provider.Stream.isBigOWith_gammaSigma_shellDerivNormSum_Ioc_translate`
(ABK26's `e.nabla.km.kn.infty`) when `lowScale = n + N`. -/
theorem exists_freshShellDirichlet_gradient_oscillation_interior_mesh_localGauge
    (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K n : ℤ) (N : ℕ), d + 3 ≤ N →
        ∀ z : Vec d,
          openCubeAtScale z (n + (N : ℤ)) ⊆ openCubeSet (originCube d K) →
          ∀ (sigmaInv : ℝ), 0 ≤ sigmaInv →
            ∀ (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e : Vec d),
              ∀ wD : H10Function (openCubeSet (originCube d K)),
                IsZeroTraceDirichletRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) wD
                    (fun x => -streamForcing sigmaInv omega lowScale highScale e x) →
                Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
                    (openCubeAtScale z n) wD.toH1Function.grad)
                  ≤ C * (3 : ℝ) ^ (-(N : ℤ)) *
                      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                        (openCubeAtScale z (n + (N : ℤ))) wD.toH1Function.grad 0)
                    + C * (N : ℝ) * ((3 : ℝ) ^ n *
                        (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e *
                          ∑ k ∈ Finset.Ioc lowScale highScale,
                            Provider.Stream.localCubeDerivNorm (n + (N : ℤ))
                              (ShellField.translate z (omega k)))) := by
  obtain ⟨C, hCnn, hC⟩ :=
    exists_freshShellDirichlet_gradient_oscillation_interior_mesh hd
  refine ⟨C, hCnn, ?_⟩
  intro K n N hN z hsub sigmaInv hsigma omega lowScale highScale e wD hwD
  exact hC K n N hN z hsub sigmaInv hsigma omega lowScale highScale e _
    (fun y hy => matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm_translate
      (n + (N : ℤ)) (Finset.Ioc lowScale highScale) z omega hy) wD hwD

/-- **The Neumann display with the forcing term in the summed first-derivative
shell gauges.**  The Neumann counterpart of the previous statement. -/
theorem exists_freshShellNeumann_gradient_oscillation_interior_mesh_localGauge
    (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (K n : ℤ) (N : ℕ), d + 3 ≤ N →
        ∀ z : Vec d,
          openCubeAtScale z (n + (N : ℤ)) ⊆ openCubeSet (originCube d K) →
          ∀ (sigmaInv : ℝ), 0 ≤ sigmaInv →
            ∀ (omega : Cutoff.ShellSeq d) (lowScale highScale : ℤ) (e' : Vec d),
              ∀ wN : H1MeanZeroFunction (openCubeSet (originCube d K)),
                IsMeanZeroNeumannRhsWeakSolution
                    (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                    (openCubeSet (originCube d K)) wN
                    (fun x => -streamForcing sigmaInv omega lowScale highScale e' x) →
                Real.sqrt (Book.Ch01.meanSquareOscillationVecOn
                    (openCubeAtScale z n) wN.toH1Function.grad)
                  ≤ C * (3 : ℝ) ^ (-(N : ℤ)) *
                      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
                        (openCubeAtScale z (n + (N : ℤ))) wN.toH1Function.grad 0)
                    + C * (N : ℝ) * ((3 : ℝ) ^ n *
                        (sigmaInv * Real.sqrt (d : ℝ) * Book.Ch02.vecNorm e' *
                          ∑ k ∈ Finset.Ioc lowScale highScale,
                            Provider.Stream.localCubeDerivNorm (n + (N : ℤ))
                              (ShellField.translate z (omega k)))) := by
  obtain ⟨C, hCnn, hC⟩ :=
    exists_freshShellNeumann_gradient_oscillation_interior_mesh hd
  refine ⟨C, hCnn, ?_⟩
  intro K n N hN z hsub sigmaInv hsigma omega lowScale highScale e' wN hwN
  exact hC K n N hN z hsub sigmaInv hsigma omega lowScale highScale e' _
    (fun y hy => matrixDerivativeNorm_sum_deriv_le_sum_localCubeDerivNorm_translate
      (n + (N : ℤ)) (Finset.Ioc lowScale highScale) z omega hy) wN hwN

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
