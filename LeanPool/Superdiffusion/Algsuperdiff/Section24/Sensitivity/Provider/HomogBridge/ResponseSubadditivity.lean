/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SubadditivityScaling
public import LeanPool.HighContrastHomogenization.Support.Besov.Poincare.Projection

/-!
# ResponseSubadditivity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Response subadditivity patching for the homogenization-error bridge

The proof of the unconditional sensitivity estimate
(`l.J.sensitivity.no.conditions` of ABK26) opens with the display

  `J(cu_0, P, Q; a) <= avsum_{z in 3^{-h} Zd cap cu_0} J(z + cu_{-h}, P, Q; a)`,

that is, the root response at a fixed loading is dominated by the *unweighted*
average of the descendant responses at the same loading.  This module records
that step as a named node, together with the monotonicity in the depth `h`
which it implies.  Both are stated in the CoarseGraining triadic-family
vocabulary: `descendantsAverage Q j` is exactly `avsum_{z in 3^{scale(Q) - j}
Zd cap Q}`.

The two structural inputs are CoarseGraining's `responseJ_subadditive` (the
`CoeffOn`-level subadditivity over an arbitrary `DomainPartition`) applied to
`descendantsDomainPartition Q j`, and the identification of the corresponding
`weightedAverage` with `descendantsAverage`.  No representative, ellipticity or
admissibility premise is required: `TriadicCoeffFamily` already carries the
restriction compatibility on nested open cubes.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- **Response subadditivity patching.**  For a triadic coefficient family and
a depth `j`, the response on a cube is bounded by the unweighted average of the
responses of the depth-`j` descendants at the *same* loading `(p, q)`.

This is the opening display of the proof of `l.J.sensitivity.no.conditions` in
family vocabulary. -/
theorem responseJOnCube_le_descendantsAverage_responseJ
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) (j : ℕ) (p q : Vec d) :
    responseJ (cubeDomain Q) (F.coeffOn Q) p q ≤
      descendantsAverage Q j
        (fun R => responseJ (cubeDomain R) (F.coeffOn R) p q) := by
  classical
  let Pcell : DomainPartition (cubeDomain Q) := descendantsDomainPartition Q j
  have hcell :
      ∀ i : Pcell.Cell, CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    intro i
    exact F.restrictsTo_of_subset
      (openCubeSet_subset_of_mem_descendantsAtDepth i.2)
  have hsub :
      responseJ (cubeDomain Q) (F.coeffOn Q) p q ≤
        Pcell.weightedAverage fun i =>
          responseJ (Pcell.cell i) (F.coeffOn i.1) p q :=
    (responseSubadditivityAndScalingTheory
      (cubeDomain Q) (F.coeffOn Q)).responseJ_subadditive
        Pcell (fun i : Pcell.Cell => F.coeffOn i.1) hcell p q
  calc
    responseJ (cubeDomain Q) (F.coeffOn Q) p q
        ≤ Pcell.weightedAverage fun i =>
            responseJ (Pcell.cell i) (F.coeffOn i.1) p q := hsub
    _ = descendantsAverage Q j
          (fun R => responseJ (cubeDomain R) (F.coeffOn R) p q) := by
        simpa [Pcell] using!
          descendantsDomainPartition_weightedAverage Q j
            (fun R => responseJ (cubeDomain R) (F.coeffOn R) p q)

/-- The descendant averages of the response at a fixed loading are nondecreasing
in the depth.  This is the iterated form of
`responseJOnCube_le_descendantsAverage_responseJ`, obtained from the tower
property of `descendantsAverage`. -/
theorem descendantsAverage_responseJ_mono
    (F : TriadicCoeffFamily d) (Q : TriadicCube d) {j k : ℕ} (hjk : j ≤ k)
    (p q : Vec d) :
    descendantsAverage Q j
        (fun R => responseJ (cubeDomain R) (F.coeffOn R) p q) ≤
      descendantsAverage Q k
        (fun R => responseJ (cubeDomain R) (F.coeffOn R) p q) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q j n
    (fun R => responseJ (cubeDomain R) (F.coeffOn R) p q)]
  refine descendantsAverage_le_descendantsAverage Q j ?_
  intro R _hR
  exact responseJOnCube_le_descendantsAverage_responseJ F R n p q

end

end Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge
