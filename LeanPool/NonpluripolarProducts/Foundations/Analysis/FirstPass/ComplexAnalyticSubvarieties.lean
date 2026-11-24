/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold

/-!
# Complex analytic subsets and their regular loci

An analytic subset is described in the preferred holomorphic chart at every
ambient point.  The coordinate neighbourhood is required to be open, to contain
the coordinate of the centre, and to lie in the actual chart target.  The
zero-locus comparison is made only for points in the actual chart source, so it
does not depend on the arbitrary extension of a partial chart outside its
domain.

Analytic irreducibility below is the decomposition property for analytic
subsets.  It deliberately does not use the unrelated Hausdorff-topological
predicate `IsIrreducible`.
-/

@[expose] public section

open Set
open scoped Manifold ContDiff Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- A finite holomorphic zero-locus presentation near `x`, in the actual
preferred chart at `x`.

The functions are total functions on the model space, but holomorphicity and
the zero-locus equation are required only on `coordinateNeighborhood`.  The
latter lies in the genuine chart target. -/
structure ComplexAnalyticPresentationAt [IsComplexManifold n M]
    (A : Set M) (x : M) where
  /-- The number of holomorphic functions defining the germ. -/
  generatorCount : ℕ
  /-- The holomorphic equations for the local common zero set. -/
  generator : Fin generatorCount → ComplexModel n → ℂ
  /-- The neighborhood on which the common zero set presents the subset. -/
  coordinateNeighborhood : Set (ComplexModel n)
  isOpen_coordinateNeighborhood : IsOpen coordinateNeighborhood
  center_mem_coordinateNeighborhood :
    (complexChartAt (n := n) x).val x ∈ coordinateNeighborhood
  coordinateNeighborhood_subset_target :
    coordinateNeighborhood ⊆ (complexChartAt (n := n) x).val.target
  generator_holomorphic :
    ∀ i, DifferentiableOn ℂ (generator i) coordinateNeighborhood
  zeroLocus : ∀ {y : M},
    y ∈ (complexChartAt (n := n) x).val.source →
    (complexChartAt (n := n) x).val y ∈ coordinateNeighborhood →
      (y ∈ A ↔ ∀ i, generator i ((complexChartAt (n := n) x).val y) = 0)

/-- A subset which is locally the common zero locus of finitely many
holomorphic functions in every preferred manifold chart. -/
def IsComplexAnalyticSubset [IsComplexManifold n M] (A : Set M) : Prop :=
  ∀ x : M, Nonempty (ComplexAnalyticPresentationAt (n := n) A x)

variable [hM : IsComplexManifold n M]

namespace ComplexAnalyticPresentationAt

variable {A B : Set M} {x : M}

/-- Transport a local presentation across equality of the represented sets. -/
def congr (hAB : A = B)
    (p : ComplexAnalyticPresentationAt (n := n) A x) :
    ComplexAnalyticPresentationAt (n := n) B x := by
  subst B
  exact p

/-- The whole ambient manifold has the empty family of local equations. -/
def univ (x : M) :
    ComplexAnalyticPresentationAt (n := n) (Set.univ : Set M) x where
  generatorCount := 0
  generator := fun i => Fin.elim0 i
  coordinateNeighborhood := (complexChartAt (n := n) x).val.target
  isOpen_coordinateNeighborhood := (complexChartAt (n := n) x).val.open_target
  center_mem_coordinateNeighborhood :=
    (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  coordinateNeighborhood_subset_target := Subset.rfl
  generator_holomorphic := fun i => Fin.elim0 i
  zeroLocus := by
    intro y _ _
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      exact Set.mem_univ y

/-- The empty set is locally cut out by the constant equation `1 = 0`. -/
def empty (x : M) :
    ComplexAnalyticPresentationAt (n := n) (∅ : Set M) x where
  generatorCount := 1
  generator := fun _ _ => 1
  coordinateNeighborhood := (complexChartAt (n := n) x).val.target
  isOpen_coordinateNeighborhood := (complexChartAt (n := n) x).val.open_target
  center_mem_coordinateNeighborhood :=
    (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
  coordinateNeighborhood_subset_target := Subset.rfl
  generator_holomorphic := fun _ => differentiableOn_const 1
  zeroLocus := by
    intro y _ _
    constructor
    · intro hy
      simp at hy
    · intro h
      exfalso
      simpa using h (0 : Fin 1)

/-- Concatenate two finite equation families to present an intersection. -/
def inter (pA : ComplexAnalyticPresentationAt (n := n) A x)
    (pB : ComplexAnalyticPresentationAt (n := n) B x) :
    ComplexAnalyticPresentationAt (n := n) (A ∩ B) x where
  generatorCount := pA.generatorCount + pB.generatorCount
  generator := Fin.addCases pA.generator pB.generator
  coordinateNeighborhood :=
    pA.coordinateNeighborhood ∩ pB.coordinateNeighborhood
  isOpen_coordinateNeighborhood :=
    pA.isOpen_coordinateNeighborhood.inter pB.isOpen_coordinateNeighborhood
  center_mem_coordinateNeighborhood :=
    ⟨pA.center_mem_coordinateNeighborhood,
      pB.center_mem_coordinateNeighborhood⟩
  coordinateNeighborhood_subset_target := fun _ hz =>
    pA.coordinateNeighborhood_subset_target hz.1
  generator_holomorphic := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using
        (pA.generator_holomorphic j).mono
          (inter_subset_left :
            pA.coordinateNeighborhood ∩ pB.coordinateNeighborhood ⊆
              pA.coordinateNeighborhood)
    · intro j
      simpa using
        (pB.generator_holomorphic j).mono
          (inter_subset_right :
            pA.coordinateNeighborhood ∩ pB.coordinateNeighborhood ⊆
              pB.coordinateNeighborhood)
  zeroLocus := by
    intro y hy hyU
    change (y ∈ A ∧ y ∈ B) ↔ _
    rw [pA.zeroLocus hy hyU.1, pB.zeroLocus hy hyU.2]
    constructor
    · rintro ⟨hA, hB⟩ i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa using hA j
      · intro j
        simpa using hB j
    · intro h
      constructor
      · intro i
        simpa using h (Fin.castAdd pB.generatorCount i)
      · intro i
        simpa using h (Fin.natAdd pA.generatorCount i)

end ComplexAnalyticPresentationAt

@[simp] theorem isComplexAnalyticSubset_univ :
    IsComplexAnalyticSubset (n := n) (Set.univ : Set M) :=
  fun x => ⟨ComplexAnalyticPresentationAt.univ (n := n) x⟩

@[simp] theorem isComplexAnalyticSubset_empty :
    IsComplexAnalyticSubset (n := n) (∅ : Set M) :=
  fun x => ⟨ComplexAnalyticPresentationAt.empty (n := n) x⟩

theorem IsComplexAnalyticSubset.inter {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) :
    IsComplexAnalyticSubset (n := n) (A ∩ B) := by
  intro x
  obtain ⟨pA⟩ := hA x
  obtain ⟨pB⟩ := hB x
  exact ⟨pA.inter pB⟩

/-- Analyticity depends only on the underlying subset. -/
theorem isComplexAnalyticSubset_congr {A B : Set M} (hAB : A = B) :
    IsComplexAnalyticSubset (n := n) A ↔
      IsComplexAnalyticSubset (n := n) B := by
  subst B
  rfl

/-- Analytic irreducibility: a nonempty analytic set cannot be expressed as the
union of two proper analytic subsets of itself. -/
def IsComplexAnalyticallyIrreducible (A : Set M) : Prop :=
  IsComplexAnalyticSubset (n := n) A ∧ A.Nonempty ∧
    ∀ B C : Set M,
      IsComplexAnalyticSubset (n := n) B →
      IsComplexAnalyticSubset (n := n) C →
      B ⊆ A → C ⊆ A → A = B ∪ C → A = B ∨ A = C

namespace IsComplexAnalyticallyIrreducible

variable {A B C : Set M}

theorem analytic (hA : IsComplexAnalyticallyIrreducible (n := n) A) :
    IsComplexAnalyticSubset (n := n) A := hA.1

theorem nonempty (hA : IsComplexAnalyticallyIrreducible (n := n) A) : A.Nonempty :=
  hA.2.1

theorem eq_left_or_eq_right
    (hA : IsComplexAnalyticallyIrreducible (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B)
    (hC : IsComplexAnalyticSubset (n := n) C)
    (hBA : B ⊆ A) (hCA : C ⊆ A) (hABC : A = B ∪ C) :
    A = B ∨ A = C :=
  hA.2.2 B C hB hC hBA hCA hABC

/-- Analytic irreducibility also depends only on the underlying subset. -/
theorem congr (hAB : A = B) :
    IsComplexAnalyticallyIrreducible (n := n) A ↔
      IsComplexAnalyticallyIrreducible (n := n) B := by
  subst B
  rfl

end IsComplexAnalyticallyIrreducible

@[simp] theorem not_isComplexAnalyticallyIrreducible_empty :
    ¬ IsComplexAnalyticallyIrreducible (n := n) (∅ : Set M) := by
  intro h
  exact h.nonempty.ne_empty rfl

/-- The standard complex `k`-plane inside the ambient coordinate space:
the first `k` coordinates are free and every remaining coordinate vanishes. -/
def complexCoordinatePlane (n k : ℕ) : Set (ComplexModel n) :=
  {z | ∀ i : Fin n, k ≤ i.1 → z i = 0}

/-- A biholomorphic change of coordinates between open neighbourhoods, centered
at a specified point.  This is local data only; no global extension is
required. -/
structure LocalHolomorphicEquivAt (p : ComplexModel n) where
  /-- The open domain of the local holomorphic equivalence. -/
  source : Set (ComplexModel n)
  /-- The open image of the local holomorphic equivalence. -/
  target : Set (ComplexModel n)
  isOpen_source : IsOpen source
  isOpen_target : IsOpen target
  center_mem_source : p ∈ source
  /-- The forward holomorphic coordinate map. -/
  toFun : ComplexModel n → ComplexModel n
  /-- The inverse holomorphic coordinate map. -/
  invFun : ComplexModel n → ComplexModel n
  toFun_holomorphic : DifferentiableOn ℂ toFun source
  invFun_holomorphic : DifferentiableOn ℂ invFun target
  mapsTo_toFun : MapsTo toFun source target
  mapsTo_invFun : MapsTo invFun target source
  left_inv : ∀ z, z ∈ source → invFun (toFun z) = z
  right_inv : ∀ w, w ∈ target → toFun (invFun w) = w

namespace LocalHolomorphicEquivAt

/-- The underlying local biholomorphism is an actual open partial
homeomorphism.  Keeping this conversion explicit lets local analytic
flattenings use the topological covariance theorems for upper-semicontinuous
regularization. -/
def toOpenPartialHomeomorph {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    OpenPartialHomeomorph (ComplexModel n) (ComplexModel n) where
  toFun := Φ.toFun
  invFun := Φ.invFun
  source := Φ.source
  target := Φ.target
  map_source' := Φ.mapsTo_toFun
  map_target' := Φ.mapsTo_invFun
  left_inv' := Φ.left_inv
  right_inv' := Φ.right_inv
  continuousOn_toFun := Φ.toFun_holomorphic.continuousOn
  continuousOn_invFun := Φ.invFun_holomorphic.continuousOn
  open_source := Φ.isOpen_source
  open_target := Φ.isOpen_target

@[simp] theorem coe_toOpenPartialHomeomorph {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    (toOpenPartialHomeomorph Φ : ComplexModel n → ComplexModel n) = Φ.toFun := rfl

@[simp] theorem coe_toOpenPartialHomeomorph_symm {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    ((toOpenPartialHomeomorph Φ).symm : ComplexModel n → ComplexModel n) = Φ.invFun := rfl

end LocalHolomorphicEquivAt

include hM
/-- A point at which `A` is locally biholomorphically flattened to
`ℂ^k × {0}` in the preferred ambient chart. -/
def RegularAtDim (A : Set M) (x : M) (k : ℕ) : Prop :=
  k ≤ n ∧ x ∈ A ∧
    ∃ Φ : LocalHolomorphicEquivAt (n := n)
        ((complexChartAt (n := n) x).val x),
      Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
      Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
      ∀ {y : M},
        y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ A ↔
            Φ.toFun ((complexChartAt (n := n) x).val y) ∈
              complexCoordinatePlane n k)
/-- The points where `A` is regular of the specified complex dimension. -/
def regularLocus (A : Set M) (k : ℕ) : Set M :=
  {x | RegularAtDim (n := n) A x k}

omit hM in
@[simp] theorem mem_regularLocus {A : Set M} {x : M} {k : ℕ} :
    x ∈ regularLocus (n := n) A k ↔
      RegularAtDim (n := n) A x k := Iff.rfl

omit hM in
theorem regularLocus_subset (A : Set M) (k : ℕ) :
    regularLocus (n := n) A k ⊆ A := by
  intro x hx
  exact hx.2.1

omit hM in
/-- Regularity of a fixed dimension is invariant under equality of subsets. -/
theorem regularAtDim_congr {A B : Set M} (hAB : A = B) (x : M) (k : ℕ) :
    RegularAtDim (n := n) A x k ↔ RegularAtDim (n := n) B x k := by
  subst B
  rfl

omit hM in
theorem regularLocus_congr {A B : Set M} (hAB : A = B) (k : ℕ) :
    regularLocus (n := n) A k = regularLocus (n := n) B k := by
  subst B
  rfl

/-- A closed irreducible analytic subvariety together with a certified complex
dimension.  The regular-point field records evidence that the chosen dimension
is realized.  It does not postulate a global embedded manifold model or assert
that arbitrary analytic sets admit such data. -/
structure ClosedIrreducibleAnalyticSubvariety
    (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  /-- The underlying analytic subset of the ambient manifold. -/
  carrier : Set M
  isClosed_carrier : IsClosed carrier
  irreducible_carrier :
    IsComplexAnalyticallyIrreducible (n := n) carrier
  /-- The complex dimension of the pure-dimensional subset. -/
  dim : ℕ
  dim_le : dim ≤ n
  regularLocus_nonempty :
    (regularLocus (n := n) carrier dim).Nonempty

namespace ClosedIrreducibleAnalyticSubvariety

variable {V W : ClosedIrreducibleAnalyticSubvariety n M}

theorem analytic (V : ClosedIrreducibleAnalyticSubvariety n M) :
    IsComplexAnalyticSubset (n := n) V.carrier :=
  V.irreducible_carrier.analytic

theorem nonempty (V : ClosedIrreducibleAnalyticSubvariety n M) :
    V.carrier.Nonempty :=
  V.irreducible_carrier.nonempty

/-- The certified dimension is witnessed by an actual regular point. -/
theorem exists_regular_point (V : ClosedIrreducibleAnalyticSubvariety n M) :
    ∃ x ∈ V.carrier, RegularAtDim (n := n) V.carrier x V.dim := by
  obtain ⟨x, hx⟩ := V.regularLocus_nonempty
  exact ⟨x, regularLocus_subset V.carrier V.dim hx, hx⟩

/-- Extensionality includes the certified dimension; no unproved uniqueness of
analytic dimension is smuggled into the bundle. -/
@[ext] theorem ext (hcarrier : V.carrier = W.carrier) (hdim : V.dim = W.dim) :
    V = W := by
  cases V
  cases W
  cases hcarrier
  cases hdim
  rfl

end ClosedIrreducibleAnalyticSubvariety

end

end SGPT.Foundations.Analysis.FirstPass
