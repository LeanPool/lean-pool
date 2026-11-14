/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier

/-!
# StoppedPositionStream

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The stopped position of the stream process

Fix one realization of the stream field, an open subset `U` of the one-point compactification of
the live space, a deterministic horizon `t`, and a starting point `x` of `U`.  Write `theta` for
the exit time from `U` truncated at `t`.  Almost every continuous path of the stream process
started at `x` satisfies

```text
  eta theta ∈ closure U ,
```

that is, at the moment it either leaves `U` or reaches the horizon the path is in the closure of
`U`: inside `U` if the horizon comes first, on the frontier if the exit comes first.

The statement is the one already available for the continuous-path process of an abstract
conservative Feller semigroup (`ae_eval_exitTimeTrunc_mem_closure`), read at the process the
model produces.  The reading is definitional: the stream process is the continuous-path process
of the compactified kernel semigroup of the split-skew analytic resolvent, and the Kolmogorov
regularity that statement asks for is the corresponding field of the shift-dependent
exhaustion-tail input's regularity datum.

## Main results

* `ae_eval_exitTimeTrunc_mem_closure_streamProcess` — the stopped position lies in the closure of
  the domain, almost surely.
* `ae_eval_exitTimeTrunc_mem_closure_streamProcess_cubeSetAt` — the same at the image of a
  triadic cube, from any starting point of the cube.

## References

* ABK26, the stopped displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open MeasureTheory
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 2. The stopped position lies in the closure -/

/-- **The stopped position of the stream process lies in the closure of the domain.**  Almost
every path of the stream process started at a point of the open set `U` is, at the time at which
it either leaves `U` or reaches the horizon `t`, in the closure of `U`.

The two ingredients are the path-level statement, that a continuous path started inside `U` is in
the closure of `U` at the truncated exit time, and the fact that the process started at `x`
starts at `x` almost surely; the latter is where the Kolmogorov regularity of the compactified
kernel semigroup enters. -/
theorem ae_eval_exitTimeTrunc_mem_closure_streamProcess
    (M : ABKModel d) (omega : FullSample d M.gamma)
    {U : Set (OnePoint (Vec d))} (hU : IsOpen U) (t : NNReal)
    {x : OnePoint (Vec d)} (hx : x ∈ U) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∀ᵐ eta ∂streamProcess M omega x,
      eta (ContinuousPath.exitTimeTrunc U t eta) ∈ closure U := by
  let := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  exact ae_eval_exitTimeTrunc_mem_closure
    (streamWholeSpaceResolvent M omega).onePointKernelSemigroup
    (streamWholeSpaceResolvent M omega).isConservative_onePointKernelSemigroup
    (streamExhaustionTailInput M omega).toOnePointRegular.kolmogorovRegular hU t hx

/-! ## 3. The stopped position on a triadic cube -/

/-- **The stopped position of the stream process on a triadic cube.**  From any live starting
point of the cube, the position at the exit time from the image of the cube truncated at the
horizon lies almost surely in the closure of that image. -/
theorem ae_eval_exitTimeTrunc_mem_closure_streamProcess_cubeSetAt
    (M : ABKModel d) (omega : FullSample d M.gamma) (y : Vec d) (n : ℤ) (t : NNReal)
    {z : Vec d} (hz : z ∈ cubeSetAt y n) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∀ᵐ eta ∂streamProcess M omega (z : OnePoint (Vec d)),
      eta (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t eta) ∈
        closure (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) :=
  ae_eval_exitTimeTrunc_mem_closure_streamProcess M omega
    (isOpen_image_coe_of_isOpen (isOpen_cubeSetAt y n)) t (Set.mem_image_of_mem _ hz)

/-- **The stopped position of the stream process on a triadic cube, from its centre.** -/
theorem ae_eval_exitTimeTrunc_mem_closure_streamProcess_cubeSetAt_self
    (M : ABKModel d) (omega : FullSample d M.gamma) (y : Vec d) (n : ℤ) (t : NNReal) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∀ᵐ eta ∂streamProcess M omega (y : OnePoint (Vec d)),
      eta (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) t eta) ∈
        closure (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt y n) :=
  ae_eval_exitTimeTrunc_mem_closure_streamProcess_cubeSetAt M omega y n t
    (mem_cubeSetAt_self y n)

end

end Algsuperdiff.Section5.Provider
