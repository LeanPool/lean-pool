/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.ZeroExtension
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.DoubledResponse
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.MultiscaleEllipticity
public import LeanPool.HighContrastHomogenization.Support.Geometry.BoundaryLayer
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure

/-!
# LocalizationGluingAdmissible

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: gluing admissibility of the localization cells

Source sentence in ABK26.

```
Since  grad w_{D,e}^{(K)} in L^2_{pot,0}(cu_K)  and
grad w_{N,e'}^{(K)} + shom_{m-h}^{-1} h e' in Lsolo(cu_K),
we have that  sum_{z in 3^n Z^d cap cu_K} X_z 1_{z+cu_n}
  in  P + L^2_{pot,0}(cu_K) x Lsolo(cu_K),
and we may insert it into the minimization problem in
(e.variational.mu.U.P) for bfA_m(cu_K).
```

This module proves exactly the membership assertion of that sentence, in the
two halves the manuscript's phrase names:

* the **potential half** — a family of fields that are `L^2_{pot,0}` on their
  own cell glues, cell by cell, to an `L^2_{pot,0}` field on the union;
* the **solenoidal half** — the same statement for `Lsolo`, i.e. for zero
  normal trace.

Both halves reduce to the extension-by-zero maps already available in this
repository
(`Algsuperdiff.Section3.Provider.Whitney.potentialZeroTraceFieldOn_indicator_of_subset`
and `..._solenoidalZeroNormalTraceFieldOn_indicator_of_subset`, both proved for
`l.subadd.betterer`), plus the exact triadic tiling of `cu_K` by its
depth-`(K-n)` descendants, which is CoarseGraining geometry:
`Homogenization.exists_mem_descendantsAtDepth_of_mem_cubeSet`,
`Homogenization.pairwiseDisjoint_openCubeSet_descendantsAtDepth`,
`Homogenization.volume_cubeBoundary_eq_zero`.

## What is proved

* `gluedDoubledField` — the manuscript's `sum_z X_z 1_{z+cu_n}`, rendered with
  the open cells `openCubeSet R` of the depth-`j` descendant family.
* `gluedDoubledField_eval_of_mem_openCubeSet` — the glued field agrees with the
  cell field `X_R` at every point of the open cell `R`.
* `isDoubledMuAdmissible_gluedDoubledField` — **the sentence itself**: if the
  affine background `G` is admissible at load `P` on `cu_K`, and each cell
  field `X_R` differs from `G` by a test field on its own cell, then the glued
  field is admissible at load `P` on `cu_K`.

## Divergences from the printed statement

* **Pin correction.**  `LocalizationBasicSplit.lean` cites this sentence as "".
  Verified against `\label{e.Pz.def}`, `\label{e.Fz.def}` and
  `\label{e.lower.bound.basic.split}`.  The mathematical content cited is
  unchanged.
* This is the principal (`A_4`) leg of the reconciliation entry, not the
  interior-filtered display leg.
* **.**  The glued field is totalized off the null set: it is defined by the
  *open* cells `openCubeSet R`, hence is `0` on the Lebesgue-null union of the
  internal faces.  Every conclusion below is an a.e. statement on `openCubeSet
  Q`, so no value on that null set is load-bearing.
* **.**  Nothing in this module asserts that the glued field minimizes
  anything: the only conclusion drawn is membership in the admissible class.
  The competitor insertion this membership licenses is an inequality, and it is
  not performed here.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The exact triadic tiling of a cube by its descendants -/

/-- The open cells of the depth-`j` descendant family cover `openCubeSet Q` up
to a Lebesgue-null set: what they miss is contained in the finite union of the
descendants' boundaries. -/
private theorem volume_openCubeSet_diff_iUnion_eq_zero (Q : TriadicCube d) (j : ℕ) :
    volume ((openCubeSet Q)
        \ ⋃ R ∈ (descendantsAtDepth Q j : Set (TriadicCube d)), openCubeSet R) = 0 := by
  have hsub : (openCubeSet Q)
        \ (⋃ R ∈ (descendantsAtDepth Q j : Set (TriadicCube d)), openCubeSet R)
      ⊆ ⋃ R ∈ (descendantsAtDepth Q j : Set (TriadicCube d)), cubeBoundary R := by
    rintro x ⟨hxQ, hxn⟩
    obtain ⟨R, hR, hxR⟩ :=
      exists_mem_descendantsAtDepth_of_mem_cubeSet j (openCubeSet_subset_cubeSet Q hxQ)
    refine Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hxR, fun hxopen => hxn ?_⟩⟩
    exact Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hR, hxopen⟩⟩
  refine measure_mono_null hsub ?_
  refine (measure_biUnion_null_iff ?_).2 fun R _ => volume_cubeBoundary_eq_zero R
  exact (descendantsAtDepth Q j).finite_toSet.countable

/-- The indicators of the open descendant cells form a partition of unity a.e.
on `openCubeSet Q`: summing any field against them returns the field. -/
private theorem sum_indicator_openCubeSet_ae (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → Vec d) :
    (fun x => ∑ R ∈ descendantsAtDepth Q j, (openCubeSet R).indicator f x)
      =ᵐ[volumeMeasureOn (openCubeSet Q)] f := by
  classical
  refine (ae_restrict_iff' (isOpen_openCubeSet Q).measurableSet).2 ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (volume_openCubeSet_diff_iUnion_eq_zero Q j)] with x hx hxQ
  have hmem : x ∈ ⋃ R ∈ (descendantsAtDepth Q j : Set (TriadicCube d)), openCubeSet R := by
    by_contra hcon
    exact hx ⟨hxQ, hcon⟩
  obtain ⟨R, hR, hxR⟩ : ∃ R ∈ (descendantsAtDepth Q j : Set (TriadicCube d)),
      x ∈ openCubeSet R := by
    simpa using hmem
  have hR' : R ∈ descendantsAtDepth Q j := hR
  rw [Finset.sum_eq_single R]
  · exact Set.indicator_of_mem hxR f
  · intro S hS hSR
    refine Set.indicator_of_notMem (fun hxS => ?_) f
    exact Set.disjoint_left.mp
      (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j hS hR' hSR) hxS hxR
  · intro hcon
    exact absurd hR' hcon

/-- A point of one open descendant cell is missed by every other cell, so the
glued sum collapses to that cell's summand. -/
private theorem sum_indicator_eq_of_mem {Q : TriadicCube d} {j : ℕ}
    (F : TriadicCube d → Vec d → Vec d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d} (hx : x ∈ openCubeSet R) :
    ∑ S ∈ descendantsAtDepth Q j, (openCubeSet S).indicator (F S) x = F R x := by
  classical
  rw [Finset.sum_eq_single R]
  · exact Set.indicator_of_mem hx (F R)
  · intro S hS hSR
    refine Set.indicator_of_notMem (fun hxS => ?_) (F S)
    exact Set.disjoint_left.mp
      (pairwiseDisjoint_openCubeSet_descendantsAtDepth Q j hS hR hSR) hxS hx
  · intro hcon
    exact absurd hR hcon

/-- Splitting each cell summand against a common background field. -/
private theorem sum_indicator_split (Q : TriadicCube d) (j : ℕ)
    (F G : TriadicCube d → Vec d → Vec d) (x : Vec d) :
    ∑ R ∈ descendantsAtDepth Q j, (openCubeSet R).indicator (F R) x
      = (∑ R ∈ descendantsAtDepth Q j,
            (openCubeSet R).indicator (fun y => F R y - G R y) x)
        + ∑ R ∈ descendantsAtDepth Q j, (openCubeSet R).indicator (G R) x := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun R _ => ?_
  by_cases hx : x ∈ openCubeSet R
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    abel
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx, add_zero]

/-! ## A.e. robustness of the two zero-trace classes -/

/-- The zero-trace potential class is insensitive to a.e. modification.  (The
solenoidal counterpart is `solenoidalZeroNormalTraceFieldOn_congr_ae'` below;
an equivalent statement is available in `Provider/Affine/H10SkewDivergence.lean`,
which this module deliberately does not import.) -/
private theorem potentialZeroTraceFieldOn_congr_ae {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) :
    Book.Ch01.PotentialZeroTraceFieldOn U g :=
  ⟨hf.1.ae_eq hfg, hf.2.imp fun _ hu => hfg.symm.trans hu⟩

/-- The zero-normal-trace solenoidal class is insensitive to a.e.
modification. -/
private theorem solenoidalZeroNormalTraceFieldOn_congr_ae' {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hfg : f =ᵐ[volumeMeasureOn U] g)
    (hf : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U f) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g := by
  refine ⟨hf.1.ae_eq hfg, ?_⟩
  intro phi
  have hint : (∫ x in U, vecDot (g x) (phi.grad x) ∂volume)
      = ∫ x in U, vecDot (f x) (phi.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [hint]
  exact hf.2 phi

/-! ## The glued field -/

/-- **The manuscript's `sum_{z in 3^n Z^d cap cu_K} X_z 1_{z+cu_n}`**, with the
lattice sites `z` rendered as the depth-`j` triadic descendants of `Q` and the
cell `z+cu_n` rendered as the open cell `openCubeSet R`.

Per the field is totalized off the null set: on the union of the internal faces
every indicator vanishes and the glued field is `0`. -/
def gluedDoubledField (Q : TriadicCube d) (j : ℕ)
    (X : TriadicCube d → DoubledField d) : DoubledField d where
  potential := fun x =>
    ∑ R ∈ descendantsAtDepth Q j, (openCubeSet R).indicator (X R).potential x
  flux := fun x =>
    ∑ R ∈ descendantsAtDepth Q j, (openCubeSet R).indicator (X R).flux x

/-- On its own open cell the glued field *is* the cell field: this is the sense
in which `sum_z X_z 1_{z+cu_n}` restricts to `X_z` on `z+cu_n`. -/
theorem gluedDoubledField_eval_of_mem_openCubeSet {Q : TriadicCube d} {j : ℕ}
    (X : TriadicCube d → DoubledField d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d} (hx : x ∈ openCubeSet R) :
    (gluedDoubledField Q j X).eval x = (X R).eval x := by
  refine Prod.ext ?_ ?_
  · exact sum_indicator_eq_of_mem (fun S => (X S).potential) hR hx
  · exact sum_indicator_eq_of_mem (fun S => (X S).flux) hR hx

/-! ## The gluing admissibility -/

/-- **Generic gluing admissibility (a conditional A toward; it is not itself the
manuscript's sentence, which operates at the specific corrector background and
minimizers).**

Let `G` be a doubled field admissible at load `P` on the cube `Q` — the
manuscript's `bfAhom^{-1/2}(e' + grad w_D^{(K)}, e + grad w_N^{(K)} + shom^{-1}
h e')`.  Its membership in `P + L^2_{pot,0}(cu_K) x Lsolo(cu_K)` is NOT a
stated hypothesis of the manuscript: D it from the gradient/solenoidal
structure of the corrector fields; here it enters as the caller proposition
`hG`.  Let `X_R` be, for each depth-`j` descendant `R` of `Q`, a field
differing from `G` by a test field on `R` — this is exactly the admissible
class of the manuscript's `X_z` (printed: `X_z` is the argmin over
`bfAhom^{-1/2}(...) + (L^2_{pot,0} x Lsolo)(z+cu_n)`).  Then the glued field
`sum_ 1_R` is admissible at load `P` on `Q`.

The potential half is piecewise `H^1_0` gluing (an `H^1_0(R)` primitive extends
by zero to an `H^1_0(Q)` primitive, and the gradient of the extension is the
extension of the gradient); the solenoidal half is that testing the glued flux
against `phi in H^1(Q)` splits over the cells, and each cell integral vanishes
because `phi` restricts to `H^1(R)`.

Per this is a membership statement only: it licenses inserting the glued field
into `e.variational.mu.U.P` as one competitor, and no declaration here asserts
that it is a minimizer. -/
theorem isDoubledMuAdmissible_gluedDoubledField {Q : TriadicCube d} {j : ℕ}
    {P : BlockVec d} {G : DoubledField d} {X : TriadicCube d → DoubledField d}
    (hG : IsDoubledMuAdmissible (cubeDomain Q) P G)
    (hX : ∀ R ∈ descendantsAtDepth Q j, IsDoubledTestField (cubeDomain R) (X R - G)) :
    IsDoubledMuAdmissible (cubeDomain Q) P (gluedDoubledField Q j X) := by
  classical
  constructor
  · have hterm : ∀ R ∈ descendantsAtDepth Q j,
        Book.Ch01.PotentialZeroTraceFieldOn (openCubeSet Q)
          ((openCubeSet R).indicator fun y => (X R).potential y - G.potential y) := by
      intro R hR
      exact potentialZeroTraceFieldOn_indicator_of_subset (isOpen_openCubeSet Q)
        (isOpen_openCubeSet R).measurableSet
        (openCubeSet_subset_of_mem_descendantsAtDepth hR) (hX R hR).1
    have hsum := potentialZeroTraceFieldOn_sum (descendantsAtDepth Q j)
      (U := openCubeSet Q)
      (fun R => (openCubeSet R).indicator fun y => (X R).potential y - G.potential y) hterm
    have hadd := potentialZeroTraceFieldOn_add hsum hG.1
    refine potentialZeroTraceFieldOn_congr_ae ?_ hadd
    filter_upwards [sum_indicator_openCubeSet_ae Q j G.potential] with x hx
    show (∑ R ∈ descendantsAtDepth Q j,
          (openCubeSet R).indicator (fun y => (X R).potential y - G.potential y) x)
        + (G.potential x - P.1)
      = (gluedDoubledField Q j X).potential x - P.1
    show _ = (∑ R ∈ descendantsAtDepth Q j,
          (openCubeSet R).indicator (X R).potential x) - P.1
    rw [sum_indicator_split Q j (fun R => (X R).potential) (fun _ => G.potential) x, hx]
    abel
  · have hterm : ∀ R ∈ descendantsAtDepth Q j,
        Book.Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet Q)
          ((openCubeSet R).indicator fun y => (X R).flux y - G.flux y) := by
      intro R hR
      exact solenoidalZeroNormalTraceFieldOn_indicator_of_subset (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR) (hX R hR).2
    have hsum := solenoidalZeroNormalTraceFieldOn_sum (descendantsAtDepth Q j)
      (U := openCubeSet Q)
      (fun R => (openCubeSet R).indicator fun y => (X R).flux y - G.flux y) hterm
    have hadd := solenoidalZeroNormalTraceFieldOn_add hsum hG.2
    refine solenoidalZeroNormalTraceFieldOn_congr_ae' ?_ hadd
    filter_upwards [sum_indicator_openCubeSet_ae Q j G.flux] with x hx
    show (∑ R ∈ descendantsAtDepth Q j,
          (openCubeSet R).indicator (fun y => (X R).flux y - G.flux y) x)
        + (G.flux x - P.2)
      = (gluedDoubledField Q j X).flux x - P.2
    show _ = (∑ R ∈ descendantsAtDepth Q j,
          (openCubeSet R).indicator (X R).flux x) - P.2
    rw [sum_indicator_split Q j (fun R => (X R).flux) (fun _ => G.flux) x, hx]
    abel

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
