/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenAssemblyCell
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenAssemblyMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenStripTransfer

/-!
# GammaTenStripAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 2 from an **interior**-mesh cell fold plus the boundary strip

ABK26, Step 2 of `l.approximate.recurrence.formula`, target
`e.lower.bound.localization.terms`.

## What this module is

`Closure.GammaTenAssemblyBridge.fluctuationEnergyAverage_le_of_cell_fold` and
its grid-load mirror `Closure.GammaTenCloserAssembly` both consume the per-cell
fold bound at **every** cell of the mesh `descendantsAtDepth (cu_{Kc}) j`.  The
interior route of `Closure.GammaTenInterior*` and
`Closure.GammaTenStripEnvelope` supplies the Besov envelope, hence the per-cell
fold bound, only on the **interior** mesh `interiorMesoCubeGrid d Kc (Kc - j)
outer` --- the carrier forces, and the depth refinement of
`Closure.GammaTenInteriorGeometry.mem_interiorMesoCubeGrid_of_mem_descendantsAtDepth`
preserves.

This module is the passage from the one to the other.  The full mesh splits into
the interior mesh and the boundary strip; the strip is handled by the signed
Cauchy--Schwarz transfer
`Closure.GammaTenStripTransfer.cubeFamilyAverage_mesoCubeGrid_le_max_interior_add`,
whose remainder is `sqrt(d 3^{g-p})` times the square root of the full-mesh
average of the **squared** cell expectations.  That last quantity is the module's
one exposed binder, `hstrip`.

## What is proved

* `cubeFamilyAverage_integral_fold_le_of_memLp_four_grid_load` --- the grid
  Hoelder fold of Step 2 at an **arbitrary** family `I` of cells, with the load
  leg on the grid and the right-hand side a free `target`.  The analytic
  content is
  `Closure.GammaTenLoadFold.cubeFamilyAverage_integral_fold_le_gridLoad`, which
  is already stated at an arbitrary `Finset (TriadicCube d)`; its eight side
  conditions are discharged from the three `L^4` legs by
  `Closure.GammaTenAssemblyMoments`, and the closing step uses `hthr` only.
* `fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load` --- **the strip
  bridge**: `fluctuationEnergyAverage <= cgamma^{10}` from
  - the per-cell fold bound `hcell` on the **interior** mesh only,
  - the three `L^4` legs and the three moment bounds on the interior mesh only,
  - the numerical gate `hthr` at a free `target`,
  - the strip second moment `hstrip`, and
  - the absorption gate `hgate`, `target + sqrt(d 3^{g-p}) sqrt(Cstrip) <=
    cgamma^{10}`.

  As in the proved bridge, **no** integrability or measurability of the cell
  integrand itself is assumed: `integral_mono_ae` where it is integrable and
  `integral_undef` where it is not.

## The residual this module isolates

`hstrip` is the **only** thing the interior route still owes beyond the interior
Besov envelope.  Stated in full, at the closure's own data, it is

```
  cubeFamilyAverage (mesoCubeGrid d Kc (Kc - j))
    (fun R => (integral_omega meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
                 d(cutoffSampleLaw M))^2)
    <= Cstrip
```

with `Cstrip` independent of `Kc` --- or, since the consumer quantifies `Kc`
through `Filter.atTop` **after** `M`, `n`, `h`, merely independent of the strip
fraction, which tends to `0` as `Kc -> infinity`.  This module does not prove it
and does not hide it.

## Binders

The scale bookkeeping `Kc = (Kc - j) + p`, `outer + 1 = (Kc - j) + g`, `g <= p`;
pointwise nonnegativity and interior-mesh `L^4` membership of the three legs;
the three interior-mesh moment bounds; `hthr`, `hcell`, `hstrip`, `hgate` and
`0 <= target`.  No smallness gate on `cgamma` is imposed beyond what `hthr` and
`hgate` state.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]

/-! ## The grid Hoelder fold at an arbitrary family -/

/-- **The Step-2 grid Hoelder fold at an arbitrary family of cells, with the load
leg on the grid and a free right-hand side.**

The Step-2 grid fold at an arbitrary `I : Finset (TriadicCube d)` rather than a
full descendant mesh, and with `cgamma^{10}` replaced by whatever `target` the
numerical gate `hthr` delivers.  Neither generalization touches the proof: the
analytic content is
`Closure.GammaTenLoadFold.cubeFamilyAverage_integral_fold_le_gridLoad`, which is
already stated at an arbitrary family, and `target` occurs only in the closing
step.

on the pointwise nonnegativity of the three legs, their `L^4` membership at
each cell of `I`, the three moment bounds on `I` and the numerical gate. -/
theorem cubeFamilyAverage_integral_fold_le_of_memLp_four_grid_load
    (mu : Measure Omega) [IsProbabilityMeasure mu] (I : Finset (TriadicCube d))
    (F G H : TriadicCube d → Omega → ℝ)
    (hF : ∀ R w, 0 ≤ F R w) (hG : ∀ R w, 0 ≤ G R w) (hH : ∀ R w, 0 ≤ H R w)
    (hF4 : ∀ R ∈ I, MemLp (F R) 4 mu) (hG4 : ∀ R ∈ I, MemLp (G R) 4 mu)
    (hH4 : ∀ R ∈ I, MemLp (H R) 4 mu)
    {gamma Cload c1 c2 target : ℝ} (hgamma : 0 < gamma) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hell : ∀ R ∈ I, ∫ w, F R w ^ (4 : ℝ) ∂mu ≤ (gamma ^ (8 : ℕ))⁻¹)
    (hload : gridFourthMomentRoot mu I G ≤ Cload)
    (hosc : gridFourthMomentRoot mu I H ≤ gamma ^ (15 : ℕ))
    (hthr : ∀ Bosc : ℝ, 0 ≤ Bosc → Bosc ≤ gamma ^ (15 : ℕ) →
      c1 * Cload * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) +
          c2 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc ^ (2 : ℕ)) ≤ target) :
    cubeFamilyAverage I (fun R => ∫ w,
        c1 * (F R w * G R w * H R w) + c2 * (F R w * H R w * H R w) ∂mu) ≤ target := by
  set Bload : ℝ := gridFourthMomentRoot mu I G with hBload
  set Bosc : ℝ := gridFourthMomentRoot mu I H with hBosc
  have hBosc0 : (0 : ℝ) ≤ Bosc := by
    rw [hBosc, gridFourthMomentRoot]
    exact Real.rpow_nonneg (gridFourthMoment_nonneg mu _ H) _
  have hafold := cubeFamilyAverage_integral_fold_le_gridLoad mu I F G H hF hG hH
    (fun R hR => memLp_ofRealTwo_rpow_two_of_memLp_four (hF R) (hF4 R hR))
    (fun R hR => memLp_ofRealTwo_rpow_two_of_memLp_four (hG R) (hG4 R hR))
    (fun R hR => memLp_ofRealTwo_rpow_two_of_memLp_four (hH R) (hH4 R hR))
    (fun R hR => hH4 R hR)
    (fun R hR => memLp_ofRealTwo_mul_of_memLp_four (hF4 R hR) (hG4 R hR))
    (fun R hR => memLp_ofRealTwo_mul_of_memLp_four (hF4 R hR) (hH4 R hR))
    (fun R hR => integrable_mul_mul_of_memLp_four (hF4 R hR) (hG4 R hR) (hH4 R hR))
    (fun R hR => integrable_mul_mul_of_memLp_four (hF4 R hR) (hH4 R hR) (hH4 R hR))
    (show (0 : ℝ) ≤ (gamma ^ (2 : ℕ))⁻¹ by positivity) hc1 hc2
    (fun R hR => rpowFourRoot_le_inv_sq_of_integral_rpow_four_le mu (hF R) hgamma
      (hell R hR))
  refine hafold.trans ?_
  have hcross : c1 * ((gamma ^ (2 : ℕ))⁻¹ * (Bload * Bosc)) ≤
      c1 * Cload * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) := by
    have hbase : c1 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) * Bload ≤
        c1 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) * Cload :=
      mul_le_mul_of_nonneg_left hload (by positivity)
    calc c1 * ((gamma ^ (2 : ℕ))⁻¹ * (Bload * Bosc))
        = c1 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) * Bload := by ring
      _ ≤ c1 * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) * Cload := hbase
      _ = c1 * Cload * ((gamma ^ (2 : ℕ))⁻¹ * Bosc) := by ring
  have hthrapp := hthr Bosc hBosc0 hosc
  linarith [hcross, hthrapp]

/-! ## The strip bridge -/

/-- **Step 2 at one localization scale, from a fold bound on the interior mesh
only.**

```
  fluctuationEnergyAverage  =  avsum_{R in mesh} E[ fluct_R ]
      <=  target  +  sqrt(d 3^{g-p}) . sqrt(Cstrip)  <=  cgamma^{10} ,
```

the first inequality being the signed Cauchy--Schwarz split of
`Closure.GammaTenStripTransfer.cubeFamilyAverage_mesoCubeGrid_le_max_interior_add`
and the interior average being folded by
`cubeFamilyAverage_integral_fold_le_of_memLp_four_grid_load`.  The cell integrand
has no sign, which is why the signed split is needed; only its **interior**
values are ever compared with the majorant.

As in `Closure.GammaTenAssemblyBridge.fluctuationEnergyAverage_le_of_cell_fold`,
no integrability and no measurability of the cell integrand is assumed:
`integral_mono_ae` where it is integrable, `integral_undef` where it is not. -/
theorem fluctuationEnergyAverage_le_of_interior_cell_fold_grid_load [NeZero d]
    (M : ABKModel d) (n : ℤ) (h : ℕ) (Kc : ℤ) (j : ℕ) (e e' : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d Kc)))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d Kc)))
    {outer : ℤ} {p g : ℕ}
    (hKp : Kc = (Kc - (j : ℤ)) + (p : ℤ))
    (houter : outer + 1 = (Kc - (j : ℤ)) + (g : ℤ)) (hgp : g ≤ p)
    (F G H : TriadicCube d → CutoffSample d → ℝ)
    (hF : ∀ R w, 0 ≤ F R w) (hG : ∀ R w, 0 ≤ G R w) (hH : ∀ R w, 0 ≤ H R w)
    (hF4 : ∀ R ∈ interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer,
      MemLp (F R) 4 (cutoffSampleLaw M).toMeasure)
    (hG4 : ∀ R ∈ interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer,
      MemLp (G R) 4 (cutoffSampleLaw M).toMeasure)
    (hH4 : ∀ R ∈ interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer,
      MemLp (H R) 4 (cutoffSampleLaw M).toMeasure)
    {Cload c1 c2 target Cstrip : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (htarget0 : 0 ≤ target)
    (hell : ∀ R ∈ interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer,
      ∫ w, F R w ^ (4 : ℝ) ∂(cutoffSampleLaw M).toMeasure ≤ (M.gamma ^ (8 : ℕ))⁻¹)
    (hload : gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
      (interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer) G ≤ Cload)
    (hosc : gridFourthMomentRoot (cutoffSampleLaw M).toMeasure
      (interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer) H ≤ M.gamma ^ (15 : ℕ))
    (hthr : ∀ Bosc : ℝ, 0 ≤ Bosc → Bosc ≤ M.gamma ^ (15 : ℕ) →
      c1 * Cload * ((M.gamma ^ (2 : ℕ))⁻¹ * Bosc) +
          c2 * ((M.gamma ^ (2 : ℕ))⁻¹ * Bosc ^ (2 : ℕ)) ≤ target)
    (hcell : ∀ R ∈ interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer,
      ∀ᵐ omega ∂(cutoffSampleLaw M).toMeasure,
        meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega ≤
          c1 * (F R omega * G R omega * H R omega) +
            c2 * (F R omega * H R omega * H R omega))
    (hstrip : cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => (∫ omega, meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) ^ 2) ≤ Cstrip)
    (hgate : target +
      Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) * Real.sqrt Cstrip ≤
        M.gamma ^ (10 : ℕ)) :
    fluctuationEnergyAverage M n h Kc j e e' wD wN ≤ M.gamma ^ (10 : ℕ) := by
  classical
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hjle : Kc - (j : ℤ) ≤ Kc := by omega
  have hmesh : mesoCubeGrid d Kc (Kc - (j : ℤ)) = descendantsAtDepth (originCube d Kc) j := by
    rw [mesoCubeGrid_eq_descendantsAtDepth hjle]
    congr 1
    omega
  have heq : fluctuationEnergyAverage M n h Kc j e e' wD wN =
      cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
        (fun R => ∫ omega, meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
          ∂(cutoffSampleLaw M).toMeasure) := by
    rw [hmesh]
    rfl
  -- the interior average
  have hinterior : cubeFamilyAverage (interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer)
      (fun R => ∫ omega, meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
        ∂(cutoffSampleLaw M).toMeasure) ≤ target := by
    refine le_trans (cubeFamilyAverage_mono (G := fun R => ∫ omega,
        c1 * (F R omega * G R omega * H R omega) +
          c2 * (F R omega * H R omega * H R omega)
        ∂(cutoffSampleLaw M).toMeasure) ?_) ?_
    · intro R hR
      have hmaj : Integrable (fun w =>
          c1 * (F R w * G R w * H R w) + c2 * (F R w * H R w * H R w))
          (cutoffSampleLaw M).toMeasure :=
        ((integrable_mul_mul_of_memLp_four (hF4 R hR) (hG4 R hR)
          (hH4 R hR)).const_mul c1).add
          ((integrable_mul_mul_of_memLp_four (hF4 R hR) (hH4 R hR)
            (hH4 R hR)).const_mul c2)
      by_cases hint : Integrable
          (fun omega => meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega)
          (cutoffSampleLaw M).toMeasure
      · exact integral_mono_ae hint hmaj (hcell R hR)
      · have hnn : ∀ w : CutoffSample d, (0 : ℝ) ≤
            c1 * (F R w * G R w * H R w) + c2 * (F R w * H R w * H R w) := by
          intro w
          have h1 : (0 : ℝ) ≤ c1 * (F R w * G R w * H R w) :=
            mul_nonneg hc1 (mul_nonneg (mul_nonneg (hF R w) (hG R w)) (hH R w))
          have h2 : (0 : ℝ) ≤ c2 * (F R w * H R w * H R w) :=
            mul_nonneg hc2 (mul_nonneg (mul_nonneg (hF R w) (hH R w)) (hH R w))
          linarith
        rw [integral_undef hint]
        exact integral_nonneg hnn
    · exact cubeFamilyAverage_integral_fold_le_of_memLp_four_grid_load
        (cutoffSampleLaw M).toMeasure _ F G H hF hG hH hF4 hG4 hH4 hgamma hc1 hc2
        hell hload hosc hthr
  rw [heq]
  refine le_trans (cubeFamilyAverage_mesoCubeGrid_le_max_interior_add d hKp houter hgp _) ?_
  have hmax : max (cubeFamilyAverage (interiorMesoCubeGrid d Kc (Kc - (j : ℤ)) outer)
      (fun R => ∫ omega, meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
        ∂(cutoffSampleLaw M).toMeasure)) 0 ≤ target := max_le hinterior htarget0
  have hCstrip0 : (0 : ℝ) ≤ Cstrip :=
    le_trans (cubeFamilyAverage_nonneg fun R _ => sq_nonneg _) hstrip
  have hsq : Real.sqrt (cubeFamilyAverage (mesoCubeGrid d Kc (Kc - (j : ℤ)))
      (fun R => (∫ omega, meshFluctuationCellIntegrand M n h Kc e e' wD wN R omega
        ∂(cutoffSampleLaw M).toMeasure) ^ 2)) ≤ Real.sqrt Cstrip :=
    Real.sqrt_le_sqrt hstrip
  have hfrac0 : (0 : ℝ) ≤ Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) :=
    Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsq hfrac0
  linarith [hmax, hmul, hgate]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
