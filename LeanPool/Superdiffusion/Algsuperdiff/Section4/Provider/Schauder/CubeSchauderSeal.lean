/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderBoundaryCampanato
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderClose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderTopScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderFreezing

/-!
# CubeSchauderSeal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the zero-datum core, unconditional

`CubeSchauderClose.zeroDatumCubeSchauder_of_campanato` reduced the zero-datum
core to a single residue: the Campanato datum

```text
  E(w, (z + □_j) ∩ □_m) ≤ C · KG · √(3^j)   for every z ∈ □_m and every j ≤ m+1,
```

together with the existence of the zero-datum solution `w`.  This module
discharges it and therefore makes `ZeroDatumCubeSchauder` unconditional beyond
the dimension hypothesis.

Three proved legs meet:

* *existence* — `CubeSchauderFreezing.exists_h10_isDivFormWeakSolutionOn_one`
  (CoarseGraining's zero-trace Dirichlet solvability at the identity
  coefficient field);
* *the scales `j ≤ m`* —
  `CubeSchauderBoundaryCampanato.affineExcess_le_boundaryCampanato`, the Campanato
  bound at **every** base point of `□_m`;
* *the scale `j = m+1`* —
  `CubeSchauderTopScale.affineExcess_truncatedWindow_top_le`, where the window is
  the cube itself and the base point plays no role.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The Campanato constant of the full base-point range -/

/-- The Campanato constant covering **every** base point of `□_m` and every scale
`j ≤ m+1`: the boundary-route constant of the scales `j ≤ m` plus the top-scale
constant of `j = m+1`. -/
def zeroDatumCampanatoConst (d : ℕ) [NeZero d] : ℝ :=
  boundaryCampanatoFullConst d + schauderTopScaleConst d

theorem zeroDatumCampanatoConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ zeroDatumCampanatoConst d := by
  have h1 : (0 : ℝ) ≤ boundaryCampanatoFullConst d := boundaryCampanatoFullConst_nonneg d
  have h2 : (0 : ℝ) ≤ schauderTopScaleConst d := schauderTopScaleConst_nonneg d
  rw [zeroDatumCampanatoConst]
  linarith only [h1, h2]

/-! ## 2. The residue, discharged -/

/-- **The Campanato residue of the route, proved.**

For every scale `m` and every `C^{0,1/2}` forcing `G` on `□_m` there is a
zero-datum solution `w ∈ H¹₀(□_m)` of `-Δw = ∇·G` whose excess obeys the
Campanato bound at **every** base point of `□_m` and **every** scale `j ≤ m+1`.

This is exactly the hypothesis of
`CubeSchauderClose.zeroDatumCubeSchauder_of_campanato`. -/
theorem exists_zeroDatumSolution_campanato [NeZero d] (hd : d ≠ 0) (m : ℤ)
    (G : Vec d → Vec d) (KG : ℝ) (hKG : 0 ≤ KG)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G) :
    ∃ w : H10Function (openCubeSet (originCube d m)),
      IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) (openCubeSet (originCube d m))
          w.toH1Function G ∧
        (∀ z ∈ openCubeSet (originCube d m), ∀ j : ℤ, j ≤ m + 1 →
          affineExcess (truncatedWindow z m j) w.toH1Function.toFun
            ≤ zeroDatumCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ j)) := by
  have hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G :=
    memVectorL2_of_holderSeminormBoundOn hKG (by norm_num) hG
  obtain ⟨w, hw⟩ := exists_h10_isDivFormWeakSolutionOn_one
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m))
    ⟨0, zero_mem_openCubeSet_originCube m⟩ hGL2
  refine ⟨w, hw, ?_⟩
  intro z hz j hj
  have hB : (0 : ℝ) ≤ boundaryCampanatoFullConst d := boundaryCampanatoFullConst_nonneg d
  have hT : (0 : ℝ) ≤ schauderTopScaleConst d := schauderTopScaleConst_nonneg d
  have hsq : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ j) := Real.sqrt_nonneg _
  rcases le_or_gt j m with hjm | hjm
  · have h := affineExcess_le_boundaryCampanato hd hjm hz w hKG hGL2 hG hw
    refine h.trans ?_
    have hcmp : boundaryCampanatoFullConst d ≤ zeroDatumCampanatoConst d := by
      rw [zeroDatumCampanatoConst]
      linarith only [hT]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcmp hKG) hsq
  · have hjeq : j = m + 1 := by omega
    subst hjeq
    have h := affineExcess_truncatedWindow_top_le hd hz w hKG hGL2 hG hw
    refine h.trans ?_
    have hcmp : schauderTopScaleConst d ≤ zeroDatumCampanatoConst d := by
      rw [zeroDatumCampanatoConst]
      linarith only [hB]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcmp hKG) hsq

/-! ## 3. The zero-datum core -/

/-- **The zero-datum cube Schauder core, unconditional.**

`ZeroDatumCubeSchauder d C₀` at the explicit constant

```text
  C₀(d) = zeroDatumRouteConst d (zeroDatumCampanatoConst d) ,
```

with no hypothesis beyond `0 < d`. -/
theorem zeroDatumCubeSchauder_unconditional [NeZero d] :
    ZeroDatumCubeSchauder d (zeroDatumRouteConst d (zeroDatumCampanatoConst d)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine zeroDatumCubeSchauder_of_campanato hd (zeroDatumCampanatoConst_nonneg d) ?_
  intro m G KG hKG hG
  exact exists_zeroDatumSolution_campanato (NeZero.ne d) m G KG hKG hG

end

end Algsuperdiff.Section4.Provider.Schauder
