/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.External.CubeSchauder
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderCalculus
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SkewTransfer
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionScaling

/-!
# IterationStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# One step of the perturbation iteration on `y + □_n`

Section 5.1 compares the solution of the rough-field Dirichlet problem at scale
`m` with the one at scale `n ≤ m` by treating `k_m - k_n` as a perturbation and
iterating.  One step of that iteration takes an `H¹` function `w` on `y + □_n`
with a continuous representative and produces

* the solution `h` of the Laplace problem `-Δ h = -∇·(w ∇·(k_m - k_n))` on
  `y + □_n` with zero boundary values, together with the sup and Hölder bounds
  its gradient inherits from the boundary Schauder estimate for the Poisson
  equation in a cube; and
* the next iterate `w'`, the solution of the rough-field problem at scale `n`
  with forcing field `∇h`.

Both halves are assembled here.  The Laplace half is the cube Schauder estimate
`Algsuperdiff.Frozen.External.cube_schauder` at `s = 1/2`, unit coefficient and
zero boundary datum, transported from the origin cube to `y + □_n`; the size of
its right-hand side is the Hölder Leibniz rule of `HolderCalculus`; the
antisymmetry of the perturbation rewrites the forcing field through
`SkewTransfer`; and the next iterate exists by `DirichletSolvability`.

## Main results

* `exists_isDirichletSolutionAt_laplacian` — the Laplace problem on `y + □_n`
  with a `1/2`-Hölder forcing field, with `‖∇h‖_{L^∞} ≤ C 3^{n/2} [G]` and
  `[∇h]_{C^{0,1/2}} ≤ C [G]`.
* `holderSeminormBoundOn_neg_smul` — the Leibniz rule in the form the forcing
  field of the iteration needs.
* `exists_iterationStep` — one step of the iteration.
* `contDiff_one_shellIncrement_entry`, `matTranspose_shellIncrement` — the shell
  increment `k_m - k_n` satisfies the two hypotheses of the step.
* `holderSeminormOn_le_of_mem_goodCubeEvent` — on the good cube event the next
  iterate obeys `σ_n 3^{-n/2} [w'] ≤ 2 C_reg 3^{n/2} [∇h]`.
* `exists_iterationStep_of_mem_goodCubeEvent` — the two combined.

## References

* ABK26, the iteration scheme of the proof of Proposition 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Stream
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Schauder (rpow_three_pos)
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Reading a solution of the origin-cube problem on `y + □_n` -/

@[simp] theorem translateSolution_grad (y : Vec d) (n : ℤ)
    (v : H1Function (openCubeSet (originCube d n))) (x : Vec d) :
    (translateSolution y n v).grad x = v.grad (x - y) := by
  simp [translateSolution]

/-- The `C^{0,α}` bound transports from the origin cube to `y + □_n`. -/
theorem holderSeminormBoundOn_cubeSetAt_of_originCube {E : Type*} [NormedAddCommGroup E]
    {y : Vec d} {n : ℤ} {alpha K : ℝ} {f : Vec d → E}
    (hf : HolderSeminormBoundOn (openCubeSet (originCube d n)) alpha K f) :
    HolderSeminormBoundOn (cubeSetAt y n) alpha K fun x => f (x - y) := by
  intro x hx z hz
  have hsub : (x - y) - (z - y) = x - z := by ring
  have h := hf (x - y) (mem_cubeSetAt_iff.1 hx) (z - y) (mem_cubeSetAt_iff.1 hz)
  rwa [hsub] at h

/-- A `C^{0,α}` bound depends on the field only through its values on the set. -/
theorem holderSeminormBoundOn_congr {E : Type*} [NormedAddCommGroup E] {U : Set (Vec d)}
    {alpha K : ℝ} {f f' : Vec d → E} (hf : HolderSeminormBoundOn U alpha K f)
    (h : Set.EqOn f f' U) : HolderSeminormBoundOn U alpha K f' := by
  intro x hx z hz
  rw [← h hx, ← h hz]
  exact hf x hx z hz

/-! ## 2. The Laplace problem on `y + □_n` -/

/-- **The Laplace problem in the cube `y + □_n` with a `1/2`-Hölder forcing
field.**

For every `G` with `[G]_{C^{0,1/2}(y+□_n)} ≤ K` there is a zero-boundary weak
solution `h` of `-Δ h = ∇·G` on `y + □_n` whose gradient obeys

```text
  ‖∇h‖_{L^∞(y+□_n)} ≤ C 3^{n/2} K ,   [∇h]_{C^{0,1/2}(y+□_n)} ≤ C K ,
```

with `C = C(d)` independent of the scale, the centre and the forcing field.

This is the boundary Schauder estimate for the Poisson equation in a cube at
`s = 1/2`, unit coefficient and zero boundary datum, read on `y + □_n` through
the translation bridge of `Translation.lean`.  The two displayed powers of the
scale are exactly what the frozen estimate produces: its left-hand gauge is
`3^{-n/2} ‖∇h‖_{L^∞} + [∇h]_{C^{0,1/2}}` and its right-hand side at zero datum
is `C 3^{-n/2} · 3^{n/2} K = C K`. -/
theorem exists_isDirichletSolutionAt_laplacian (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y : Vec d) (n : ℤ) (G : Vec d → Vec d) (K : ℝ),
        HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K G →
        ∃ h : H1Function (cubeSetAt y n),
          IsDirichletSolutionAt (fun _ => (1 : ℝ) • (1 : Mat d)) y n h G ∧
            (∀ x ∈ cubeSetAt y n, ‖h.grad x‖ ≤ C * Real.rpow 3 ((n : ℝ) / 2) * K) ∧
            HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (C * K) h.grad := by
  obtain ⟨C, hCpos, hsch⟩ :=
    Algsuperdiff.Frozen.External.cube_schauder hdim (1 / 2) (by norm_num) le_rfl
  refine ⟨C, hCpos, fun y n G K hG => ?_⟩
  have hd : 0 < d := by omega
  have hK : 0 ≤ K := holderSeminormBoundOn_nonneg_cubeSetAt hd hG
  have hzeroSup : ∀ x ∈ openCubeSet (originCube d n),
      ‖(0 : H1Function (openCubeSet (originCube d n))).grad x‖ ≤ 0 := by
    intro x _; simp
  have hzeroHol : HolderSeminormBoundOn (openCubeSet (originCube d n)) (1 / 2) 0
      (0 : H1Function (openCubeSet (originCube d n))).grad := by
    intro x _ z _; simp
  obtain ⟨v, hv, Ksup, KHol, hKsup0, hKHol0, hvsup, hvhol, hbound⟩ :=
    hsch n 1 one_pos (fun x => G (y + x)) 0 K 0 0
      (holderSeminormBoundOn_originCube_of_cubeSetAt hG) hzeroSup hzeroHol
  have hhalf : (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 := by ring
  have hneg : Real.rpow 3 (-((n : ℝ) / 2)) = (Real.rpow 3 ((n : ℝ) / 2))⁻¹ :=
    Real.rpow_neg (by norm_num) _
  rw [hhalf, hneg] at hbound
  have hP : (0 : ℝ) < Real.rpow 3 ((n : ℝ) / 2) := rpow_three_pos _
  have hrhs : C * (Real.rpow 3 ((n : ℝ) / 2))⁻¹ *
      ((1 : ℝ)⁻¹ * Real.rpow 3 ((n : ℝ) / 2) * K + (0 + Real.rpow 3 ((n : ℝ) / 2) * 0)) =
      C * K := by
    field_simp
    ring
  rw [hrhs] at hbound
  have hKHol : KHol ≤ C * K := by
    have hnn : 0 ≤ (Real.rpow 3 ((n : ℝ) / 2))⁻¹ * Ksup :=
      mul_nonneg (inv_nonneg.2 hP.le) hKsup0
    linarith only [hbound, hnn]
  have hKsup : Ksup ≤ C * Real.rpow 3 ((n : ℝ) / 2) * K := by
    have h1 : (Real.rpow 3 ((n : ℝ) / 2))⁻¹ * Ksup ≤ C * K := by
      linarith only [hbound, hKHol0]
    have h2 := mul_le_mul_of_nonneg_left h1 hP.le
    rw [← mul_assoc, mul_inv_cancel₀ hP.ne', one_mul] at h2
    calc Ksup ≤ Real.rpow 3 ((n : ℝ) / 2) * (C * K) := h2
      _ = C * Real.rpow 3 ((n : ℝ) / 2) * K := by ring
  refine ⟨translateSolution y n v, ?_, ?_, ?_⟩
  · rw [isDirichletSolutionAt_iff_origin, originPullback_translateSolution]
    exact hv
  · intro x hx
    rw [translateSolution_grad]
    exact le_trans (hvsup (x - y) (mem_cubeSetAt_iff.1 hx)) hKsup
  · refine holderSeminormBoundOn_congr
      ((holderSeminormBoundOn_cubeSetAt_of_originCube hvhol).mono_const hKHol) ?_
    intro x _
    exact (translateSolution_grad y n v x).symm

/-! ## 3. The size of the forcing field of the iteration -/

/-- **The Hölder Leibniz rule in the form the iteration needs.**  The forcing
field of the Laplace step is `-w ∇·(k_m - k_n)`, a scalar field times a vector
field. -/
theorem holderSeminormBoundOn_neg_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set (Vec d)} {alpha Kf Sf KG SG : ℝ} {f : Vec d → ℝ}
    {G : Vec d → E} (hKf : 0 ≤ Kf) (hSf : 0 ≤ Sf)
    (hf : HolderSeminormBoundOn U alpha Kf f) (hfsup : ∀ x ∈ U, ‖f x‖ ≤ Sf)
    (hG : HolderSeminormBoundOn U alpha KG G) (hGsup : ∀ x ∈ U, ‖G x‖ ≤ SG) :
    HolderSeminormBoundOn U alpha (Kf * SG + Sf * KG) fun x => -f x • G x := by
  refine holderSeminormBoundOn_smul hKf hSf ?_ ?_ hG hGsup
  · intro x hx z hz
    calc ‖-f x - -f z‖ = ‖f x - f z‖ := by rw [neg_sub_neg, norm_sub_rev]
      _ ≤ Kf * ‖x - z‖ ^ alpha := hf x hx z hz
  · intro x hx
    simpa using hfsup x hx

/-! ## 4. One step of the iteration -/

/-- **One step of the perturbation iteration.**

Given a skew, entrywise `C¹` matrix field `k` and an `H¹` function `w` on
`y + □_n` with a continuous representative `wRep` obeying
`[wRep] ≤ Kw` and `‖wRep‖_{L^∞} ≤ Sw`, and given the two sizes
`[∇·k] ≤ Kk`, `‖∇·k‖_{L^∞} ≤ Sk` of the divergence of the perturbation, the
step produces

* `h`, the zero-boundary solution of `-Δ h = -∇·(w ∇·k)` on `y + □_n`, stated
  in the equivalent antisymmetric form `-∇·(k ∇w)` that the antisymmetry
  transfer supplies, with

  ```text
    ‖∇h‖_{L^∞(y+□_n)} ≤ C 3^{n/2} ([wRep] ‖∇·k‖_∞ + ‖wRep‖_∞ [∇·k]) ,
    [∇h]_{C^{0,1/2}(y+□_n)} ≤ C ([wRep] ‖∇·k‖_∞ + ‖wRep‖_∞ [∇·k]);
  ```

* `w'`, the next iterate: the solution of the rough-field problem at scale `n`
  with forcing field `∇h`.

`C = C(d)` is the constant of the cube Schauder estimate; it does not depend on
the scale, the centre, the sample, the perturbation or `w`. -/
theorem exists_iterationStep (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (n : ℤ) (y : Vec d) (omega : Cutoff.CutoffSample d)
        (k : Vec d → Mat d),
        (∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q) →
        (∀ x : Vec d, matTranspose (k x) = -k x) →
        ∀ (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ) (Kw Sw Kk Sk : ℝ),
          IsCubeRepresentative y n w wRep →
          HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kw wRep →
          (∀ x ∈ cubeSetAt y n, ‖wRep x‖ ≤ Sw) →
          HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kk (matFieldDiv k) →
          (∀ x ∈ cubeSetAt y n, ‖matFieldDiv k x‖ ≤ Sk) →
          ∃ h w' : H1Function (cubeSetAt y n),
            IsDirichletSolutionAt (fun _ => (1 : ℝ) • (1 : Mat d)) y n h
                (fun x => -matVecMul (k x) (w.grad x)) ∧
              (∀ x ∈ cubeSetAt y n,
                ‖h.grad x‖ ≤ C * Real.rpow 3 ((n : ℝ) / 2) * (Kw * Sk + Sw * Kk)) ∧
              HolderSeminormBoundOn (cubeSetAt y n) (1 / 2)
                (C * (Kw * Sk + Sw * Kk)) h.grad ∧
              IsDirichletSolutionAt
                ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n w' h.grad := by
  obtain ⟨C, hCpos, hlap⟩ := exists_isDirichletSolutionAt_laplacian hdim
  refine ⟨C, hCpos, fun M n y omega k hkC1 hkskew w wRep Kw Sw Kk Sk
    hwRep hwHol hwSup hkHol hkSup => ?_⟩
  have hd : 0 < d := by omega
  have hKw : 0 ≤ Kw := holderSeminormBoundOn_nonneg_cubeSetAt hd hwHol
  have hSw : 0 ≤ Sw := le_trans (norm_nonneg _) (hwSup y (mem_cubeSetAt_self y n))
  have hforce : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) (Kw * Sk + Sw * Kk)
      fun x => -wRep x • matFieldDiv k x :=
    holderSeminormBoundOn_neg_smul hKw hSw hwHol hwSup hkHol hkSup
  obtain ⟨h, hsol, hsup, hhol⟩ := hlap y n _ _ hforce
  have hae : (fun x => -wRep x • matFieldDiv k x)
      =ᵐ[volume.restrict (cubeSetAt y n)] fun x => -w.toFun x • matFieldDiv k x := by
    filter_upwards [hwRep.1] with x hx
    show -wRep x • matFieldDiv k x = -w.toFun x • matFieldDiv k x
    rw [hx]
  have hsol' := (isDirichletSolutionAt_smul_matFieldDiv_iff
      (a := fun _ => (1 : ℝ) • (1 : Mat d)) hkC1 hkskew w).1
    ((isDirichletSolutionAt_congr_ae hae).1 hsol)
  obtain ⟨w', hw'⟩ := exists_isDirichletSolutionAt_cutoff M n n y omega hhol
  exact ⟨h, w', hsol', hsup, hhol, hw'⟩

/-! ## 5. The perturbation of the iteration is the shell increment -/

/-- Every entry of the shell increment `k_q - k_p` is `C¹`, the first hypothesis
of the iteration step. -/
theorem contDiff_one_shellIncrement_entry (omega : Cutoff.ShellSeq d) (p q : ℤ)
    (a b : Fin d) : ContDiff ℝ 1 fun x => shellIncrement omega p q x a b :=
  contDiff_one_shellField_entry (shellIncrement omega p q) a b

/-- The shell increment `k_q - k_p` is pointwise antisymmetric, the second
hypothesis of the iteration step. -/
theorem matTranspose_shellIncrement (omega : Cutoff.ShellSeq d) (p q : ℤ) (x : Vec d) :
    matTranspose (shellIncrement omega p q x) = -shellIncrement omega p q x :=
  (shellIncrement omega p q).skew x

/-! ## 6. The good cube event bounds the next iterate -/

/-- **On the good cube event the localized regularity is at most `2 C_reg`, and
this bounds the next iterate.**

```text
  σ_n 3^{-n/2} [w']_{C^{0,1/2}(y+□_n)}
      ≤ 2 C_reg 3^{n/2} [∇h]_{C^{0,1/2}(y+□_n)} .
```
-/
theorem holderSeminormOn_le_of_mem_goodCubeEvent (M : ABKModel d) (Creg : ℝ) (n : ℤ)
    (y : Vec d) (ep : ℝ) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ goodCubeEvent M Creg n y ep) {g : Vec d → Vec d}
    (hg : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≠ ⊤)
    {u : H1Function (cubeSetAt y n)} {uRep : Vec d → ℝ}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g)
    (huRep : IsCubeRepresentative y n u uRep) :
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) uRep ≤
      ENNReal.ofReal (2 * Creg) * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) g := by
  refine le_trans (holderSeminormOn_le_localizedRegularity M n y omega hg hu huRep) ?_
  gcongr
  exact homega.2

/-- **On the good cube event the next iterate has a continuous representative.**
The infimum defining the localized regularity is `⊤` when none exists. -/
theorem exists_isCubeRepresentative_of_mem_goodCubeEvent (M : ABKModel d) (Creg : ℝ)
    (n : ℤ) (y : Vec d) (ep : ℝ) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ goodCubeEvent M Creg n y ep) {g : Vec d → Vec d}
    (hg : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≠ ⊤)
    {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g) :
    ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep :=
  exists_isCubeRepresentative_of_localizedRegularity_ne_top M n y omega
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top homega.2) hg hu

/-- **One step of the iteration on the good cube event.**  The step produces the
Laplace solution `h`, the next iterate `w'`, a continuous representative of `w'`,
and the estimate of the proof of Proposition 5.1 relating the two. -/
theorem exists_iterationStep_of_mem_goodCubeEvent (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (Creg : ℝ) (n : ℤ) (y : Vec d) (ep : ℝ)
        (omega : Cutoff.CutoffSample d),
        omega ∈ goodCubeEvent M Creg n y ep →
        ∀ (k : Vec d → Mat d),
          (∀ p q : Fin d, ContDiff ℝ 1 fun x => k x p q) →
          (∀ x : Vec d, matTranspose (k x) = -k x) →
          ∀ (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ) (Kw Sw Kk Sk : ℝ),
            IsCubeRepresentative y n w wRep →
            HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kw wRep →
            (∀ x ∈ cubeSetAt y n, ‖wRep x‖ ≤ Sw) →
            HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kk (matFieldDiv k) →
            (∀ x ∈ cubeSetAt y n, ‖matFieldDiv k x‖ ≤ Sk) →
            ∃ (h w' : H1Function (cubeSetAt y n)) (w'Rep : Vec d → ℝ),
              IsDirichletSolutionAt (fun _ => (1 : ℝ) • (1 : Mat d)) y n h
                  (fun x => -matVecMul (k x) (w.grad x)) ∧
                (∀ x ∈ cubeSetAt y n,
                  ‖h.grad x‖ ≤ C * Real.rpow 3 ((n : ℝ) / 2) * (Kw * Sk + Sw * Kk)) ∧
                HolderSeminormBoundOn (cubeSetAt y n) (1 / 2)
                  (C * (Kw * Sk + Sw * Kk)) h.grad ∧
                IsDirichletSolutionAt
                    ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n w' h.grad ∧
                  IsCubeRepresentative y n w' w'Rep ∧
                  ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) *
                        Real.rpow 3 (-(n : ℝ) / 2)) *
                      holderSeminormOn (cubeSetAt y n) (1 / 2) w'Rep ≤
                    ENNReal.ofReal (2 * Creg) *
                      ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
                        holderSeminormOn (cubeSetAt y n) (1 / 2) h.grad := by
  obtain ⟨C, hCpos, hstep⟩ := exists_iterationStep hdim
  refine ⟨C, hCpos, fun M Creg n y ep omega homega k hkC1 hkskew w wRep Kw Sw Kk Sk
    hwRep hwHol hwSup hkHol hkSup => ?_⟩
  obtain ⟨h, w', hsol, hsup, hhol, hw'⟩ :=
    hstep M n y omega k hkC1 hkskew w wRep Kw Sw Kk Sk hwRep hwHol hwSup hkHol hkSup
  have hd : 0 < d := by omega
  have hgradFin : holderSeminormOn (cubeSetAt y n) (1 / 2) h.grad ≠ ⊤ := by
    have hle := (holderSeminormOn_le_ofReal_iff
      (holderSeminormBoundOn_nonneg_cubeSetAt hd hhol)).2 hhol
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  obtain ⟨w'Rep, hw'Rep⟩ :=
    exists_isCubeRepresentative_of_mem_goodCubeEvent M Creg n y ep homega hgradFin hw'
  exact ⟨h, w', w'Rep, hsol, hsup, hhol, hw',  hw'Rep,
    holderSeminormOn_le_of_mem_goodCubeEvent M Creg n y ep homega hgradFin hw' hw'Rep⟩

end

end Algsuperdiff.Section5.Support
