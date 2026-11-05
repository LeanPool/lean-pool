/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.External.CalderonZygmund
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeEuclideanL8

/-!
# FreshShellCZ

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Step (i) of `e.nablaw.in.L.eight`: the Calderon-Zygmund line

The first inequality of ABK26's display `e.nablaw.in.L.eight` is

```
  ‖∇w_D‖²_{L^8(cu_K)} + ‖∇w_N‖²_{L^8(cu_K)}
      <=  C ‖forcing‖²_{L^8(cu_K)} ,
```

for the Dirichlet and Neumann problems `e.def.w` with constant-coefficient
Laplacian.  The manuscript's only justification is "By Calder\'on-Zygmund
estimates"; in this repository that is the author-designated external input

**Everything in this module therefore reaches that one anchor and no other, and
carries the standard three axioms `[propext, Classical.choice, Quot.sound]`.**

## What this module adds over the frozen theorem

1. The frozen theorem is stated in the *ambient sup gauge* of `Vec d = Fin d ->
   ℝ`.  The manuscript's `L^8` norm of a gradient is the *Euclidean* one.  This
   module carries the conversion explicitly, through `CubeEuclideanL8`, at the
   cost of one factor `sqrt d` on each side, which the dimension-only constant
   absorbs.
2. The frozen theorem bounds one solution at a time.  ABK26 needs the *sum* of
   a Dirichlet and a Neumann square, and its two lanes may carry **different**
   forcings (directions `e` and `e'`).  The theorem below is therefore stated
   with two independent forcings.
3. The frozen theorem demands `MemLp` of the forcing.  Here it is discharged
   from continuity, which is what the actual fresh-shell forcing supplies.

## References

* ABK26, `e.nablaw.in.L.eight` (first inequality).
* ABK26, `e.def.w` (the two corrector problems).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **Step (i) of `e.nablaw.in.L.eight`.**

There is one dimension-only constant such that, on every triadic cube, the
zero-trace Dirichlet and mean-zero Neumann weak solutions of `-Delta w = div f`
with continuous forcings satisfy

```
  ‖∇w_D‖²_{L^8} + ‖∇w_N‖²_{L^8}  <=  C ( ‖f_D‖²_{L^8} + ‖f_N‖²_{L^8} ) ,
```

all four norms being the manuscript's volume-normalized **Euclidean** `L^8`
norms.  The constant is produced once, before the cube, the forcings and the
solutions, so its dimension-only scope is part of the statement. -/
theorem exists_cubeEuclideanL8_gradient_sq_sum_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (fD fN : Vec d → Vec d),
        Continuous fD → Continuous fN →
        ∀ wD : H10Function (openCubeSet Q),
          IsZeroTraceDirichletRhsWeakSolution
              (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
              (openCubeSet Q) wD (fun x => -fD x) →
          ∀ wN : H1MeanZeroFunction (openCubeSet Q),
            IsMeanZeroNeumannRhsWeakSolution
                (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                (openCubeSet Q) wN (fun x => -fN x) →
            cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ 2 +
                cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ 2 ≤
              C * (cubeEuclideanLpNorm Q 8 fD ^ 2 +
                cubeEuclideanLpNorm Q 8 fN ^ 2) := by
  obtain ⟨C₀, hC₀pos, hCZ⟩ :=
    Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd (8 : ℝ≥0∞)
      (by norm_num) (by norm_num)
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : (0 : ℕ) < d := lt_of_lt_of_le (by norm_num) hd
    exact_mod_cast this
  refine ⟨(d : ℝ) * C₀ ^ 2, by positivity, ?_⟩
  intro Q fD fN hfD hfN wD hwD wN hwN
  -- the `MemLp` inputs, from continuity
  have hmemD : MemLp fD (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_continuous Q _ hfD
  have hmemN : MemLp fN (8 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_continuous Q _ hfN
  have hmemDE : MemLp (fun x => Book.Ch02.vecNorm (fD x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_continuous Q _ (continuous_vecNorm.comp hfD)
  have hmemNE : MemLp (fun x => Book.Ch02.vecNorm (fN x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_continuous Q _ (continuous_vecNorm.comp hfN)
  -- the frozen theorem, one lane at a time
  obtain ⟨hgradD, hDbound⟩ := (hCZ Q fD hmemD).1 wD hwD
  obtain ⟨hgradN, hNbound⟩ := (hCZ Q fN hmemN).2 wN hwN
  -- one lane of the gauge conversion
  have hlane : ∀ (f : Vec d → Vec d) (g : Vec d → Vec d),
      MemLp g (8 : ℝ≥0∞) (normalizedCubeMeasure Q) →
      MemLp (fun x => Book.Ch02.vecNorm (f x)) (8 : ℝ≥0∞)
        (normalizedCubeMeasure Q) →
      cubeLpNorm Q (8 : ℝ≥0∞) g ≤ C₀ * cubeLpNorm Q (8 : ℝ≥0∞) f →
      cubeEuclideanLpNorm Q 8 g ^ 2 ≤
        (d : ℝ) * C₀ ^ 2 * cubeEuclideanLpNorm Q 8 f ^ 2 := by
    intro f g hg hfE hbound
    have hstep1 : cubeEuclideanLpNorm Q 8 g ≤
        Real.sqrt (d : ℝ) * cubeLpNorm Q (8 : ℝ≥0∞) g :=
      cubeEuclideanLpNorm_le_sqrt_dim_mul_cubeLpNorm Q (8 : ℝ≥0∞) g hg
    have hstep2 : cubeLpNorm Q (8 : ℝ≥0∞) f ≤ cubeEuclideanLpNorm Q 8 f :=
      cubeLpNorm_le_cubeEuclideanLpNorm Q (8 : ℝ≥0∞) f hfE
    have hchain : cubeEuclideanLpNorm Q 8 g ≤
        Real.sqrt (d : ℝ) * C₀ * cubeEuclideanLpNorm Q 8 f := by
      calc cubeEuclideanLpNorm Q 8 g
          ≤ Real.sqrt (d : ℝ) * cubeLpNorm Q (8 : ℝ≥0∞) g := hstep1
        _ ≤ Real.sqrt (d : ℝ) * (C₀ * cubeLpNorm Q (8 : ℝ≥0∞) f) :=
            mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (d : ℝ) * (C₀ * cubeEuclideanLpNorm Q 8 f) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left hstep2 hC₀pos.le
        _ = Real.sqrt (d : ℝ) * C₀ * cubeEuclideanLpNorm Q 8 f := by ring
    have hnn : (0 : ℝ) ≤ cubeEuclideanLpNorm Q 8 g :=
      cubeEuclideanLpNorm_nonneg _ _ _
    have hsq : cubeEuclideanLpNorm Q 8 g ^ 2 ≤
        (Real.sqrt (d : ℝ) * C₀ * cubeEuclideanLpNorm Q 8 f) ^ 2 := by
      have hrhs : (0 : ℝ) ≤ Real.sqrt (d : ℝ) * C₀ * cubeEuclideanLpNorm Q 8 f :=
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC₀pos.le)
          (cubeEuclideanLpNorm_nonneg _ _ _)
      nlinarith [hchain, hnn, hrhs]
    have hd2 : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR.le
    calc cubeEuclideanLpNorm Q 8 g ^ 2
        ≤ (Real.sqrt (d : ℝ) * C₀ * cubeEuclideanLpNorm Q 8 f) ^ 2 := hsq
      _ = (d : ℝ) * C₀ ^ 2 * cubeEuclideanLpNorm Q 8 f ^ 2 := by
          rw [mul_pow, mul_pow, hd2]
  have hD := hlane fD wD.toH1Function.grad hgradD hmemDE hDbound
  have hN := hlane fN wN.toH1Function.grad hgradN hmemNE hNbound
  calc cubeEuclideanLpNorm Q 8 wD.toH1Function.grad ^ 2 +
        cubeEuclideanLpNorm Q 8 wN.toH1Function.grad ^ 2
      ≤ (d : ℝ) * C₀ ^ 2 * cubeEuclideanLpNorm Q 8 fD ^ 2 +
          (d : ℝ) * C₀ ^ 2 * cubeEuclideanLpNorm Q 8 fN ^ 2 := by linarith
    _ = (d : ℝ) * C₀ ^ 2 *
          (cubeEuclideanLpNorm Q 8 fD ^ 2 + cubeEuclideanLpNorm Q 8 fN ^ 2) := by
        ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
