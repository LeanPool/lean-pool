/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationEnvelopeMesh
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeJensenVec
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeEuclideanL8
public import LeanPool.HighContrastHomogenization.Support.Geometry.OriginCubeMeasureBridge

/-!
# LocalizationEnvelopeSpatial

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
descriptions below are an informal inventory only.

# Provider: the spatial `L^4 <= L^8` bridge at the fourth-energy carrier

Source displays in ABK26:

* `e.nablaw.in.L.eight` (label; display), whose left side is `‖grad
  w‖^2_{L8bar(cu_K)}`;
* `e.lower.bound.oscillations` (label; display), whose covering step (module
  `LocalizationEnvelopeMesh`) consumes the annealed *fourth* energy
  `fint_{cu_K} |grad w|^4`.

## The gap this module closes

The two displays are stated on different carriers, and the difference is not
only the exponent:

* the fourth-energy carrier `originCubeFourthEnergy K u` of
  `LocalizationEnvelopeMesh` is `volumeAverage` over the **open** cube
  `openCubeSet (originCube d K)`;
* the `L^8` carrier `Corrector.cubeEuclideanLpNorm (originCube d K) 8 u` is
  `cubeLpNorm` against `normalizedCubeMeasure`, which is built from the
  **half-open** `cubeSet (originCube d K)`.

The two cube realizations differ by their boundary, a Lebesgue null set, so the
two averages agree exactly; the exponent step is then the volume-normalized
`L^4 <= L^8` comparison, which on a probability measure costs constant `1`.

## What is proved

* `originCubeFourthEnergy_eq_cubeAverage` -- **unconditional**: the open-cube
  fourth energy is the half-open cube average of `|u|^4`.  This is the
  measure-zero boundary step, from CoarseGraining's
  `cubeSet_originCube_ae_eq_openCubeSet`.
* `originCubeFourthEnergy_le_cubeEuclideanLpNorm_eight_pow_four` -- the bridge
  `fint_{cu_K} |u|^4 <= ‖u‖^4_{L8bar(cu_K)}`, with constant `1`.
* `originCubeFourthEnergy_le_sq_of_cubeEuclideanLpNorm_sq_le` -- the shape the
  envelope derivation consumes: a pathwise bound `‖u‖^2_{L8bar(cu_K)} <= B`
  gives `fint_{cu_K} |u|^4 <= B^2`.

## What is not proved here

* **`MemLp` is a binder, not a consequence.**  A finite value of
  `cubeEuclideanLpNorm` does not imply `L^8` membership: `cubeLpNorm` is a
  `toReal`, and `(⊤ : ℝ≥0∞).toReal = 0`.  So the `L^8` membership of the
  Euclidean pointwise length is a genuine analytic side condition and is
  carried explicitly on every statement that needs it.
* **Nothing about correctors is used.**  The statements below hold for an
  arbitrary field `u : Vec d -> Vec d`.

## References

* ABK26, `e.nablaw.in.L.eight`.
* `Corrector.CubeJensenVec`,
  `cubeAverage_vecNormSq_sq_le_cubeLpNorm_eight_vecNorm_pow_four_of_memLp` (the
  exponent step, itself the iterated `p = 2` cube Jensen inequality of
  CoarseGraining).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## The measure-zero boundary step -/

/-- **Unconditional.**  The open-cube fourth energy of `u` on `cu_K` is the
half-open cube average of `|u|^4`.  The two cube realizations differ by their
boundary, which is Lebesgue null. -/
theorem originCubeFourthEnergy_eq_cubeAverage (K : ℤ) (u : Vec d → Vec d) :
    originCubeFourthEnergy K u =
      cubeAverage (originCube d K) (fun x => vecNormSq (u x) ^ 2) := by
  unfold originCubeFourthEnergy volumeAverage cubeAverage
  rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal,
    setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube]

/-! ## The exponent step -/

/-- **The spatial `L^4 <= L^8` bridge on `cu_K`.**

```
  fint_{cu_K} |u|^4  <=  ‖u‖^4_{L8bar(cu_K)} ,
```

with `‖.‖_{L8bar(cu_K)}` the manuscript's volume-normalized `L^8` norm read
with the Euclidean pointwise length.  The constant is `1`.

: the caller supplies `hu`, the `L^8` membership of the Euclidean pointwise
length `x |-> vecNorm (u x)` for the normalized cube measure of `originCube d
K`.  This is the only hypothesis. -/
theorem originCubeFourthEnergy_le_cubeEuclideanLpNorm_eight_pow_four (K : ℤ)
    (u : Vec d → Vec d)
    (hu : MemLp (fun x => Book.Ch02.vecNorm (u x)) 8
      (normalizedCubeMeasure (originCube d K))) :
    originCubeFourthEnergy K u ≤
      Corrector.cubeEuclideanLpNorm (originCube d K) 8 u ^ (4 : ℕ) := by
  rw [originCubeFourthEnergy_eq_cubeAverage, Corrector.cubeEuclideanLpNorm]
  exact Corrector.cubeAverage_vecNormSq_sq_le_cubeLpNorm_eight_vecNorm_pow_four_of_memLp
    (originCube d K) u hu

/-- **The shape the envelope derivation consumes.**  A pathwise bound on the
*squared* normalized `L^8` norm gives a pathwise bound on the fourth energy:

```
  ‖u‖^2_{L8bar(cu_K)} <= B    implies    fint_{cu_K} |u|^4 <= B^2 .
```

: the caller supplies `hu` (the `L^8` membership above) and `hle :
cubeEuclideanLpNorm (originCube d K) 8 u ^ 2 <= B`.  Nonnegativity of `B` is
*not* assumed: it follows from `hle`. -/
theorem originCubeFourthEnergy_le_sq_of_cubeEuclideanLpNorm_sq_le (K : ℤ)
    (u : Vec d → Vec d) {B : ℝ}
    (hu : MemLp (fun x => Book.Ch02.vecNorm (u x)) 8
      (normalizedCubeMeasure (originCube d K)))
    (hle : Corrector.cubeEuclideanLpNorm (originCube d K) 8 u ^ (2 : ℕ) ≤ B) :
    originCubeFourthEnergy K u ≤ B ^ (2 : ℕ) := by
  refine (originCubeFourthEnergy_le_cubeEuclideanLpNorm_eight_pow_four K u hu).trans ?_
  have hsq : (0 : ℝ) ≤ Corrector.cubeEuclideanLpNorm (originCube d K) 8 u ^ (2 : ℕ) :=
    sq_nonneg _
  calc Corrector.cubeEuclideanLpNorm (originCube d K) 8 u ^ (4 : ℕ)
      = (Corrector.cubeEuclideanLpNorm (originCube d K) 8 u ^ (2 : ℕ)) ^ (2 : ℕ) := by
        ring
    _ ≤ B ^ (2 : ℕ) := by gcongr

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
