/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneFourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Weak `H¹` and `H²` graph spaces on the whole plane

This module gives the whole-plane Sobolev domains needed by the local seed of `prop:local-seed`
(Proposition 2.2).  The definitions are direct
weak-derivative definitions: an element consists of its physical `L²` field together with all
first (and, for `H²`, all ordered second) `L²` derivatives, constrained by exact equalities in
tempered distributions.

The jets use finite `ℓ²` products.  Consequently the ambient spaces, and the
closed graph subspaces cut out below, are complex Hilbert spaces.  No
equivalence with a separate Sobolev predicate is assumed.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped FourierTransform Laplacian LineDeriv SchwartzMap

section Graphs

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Index of a first-order jet: `none` is the physical field and `some j` is
the `j`-th weak derivative. -/
abbrev WholePlaneJet1Index := Option (Fin 2)

/-- Index of a second-order jet.  The left summand contains the whole
first-order jet and `(j,k)` in the right summand stores `∂_k ∂_j f`. -/
abbrev WholePlaneJet2Index :=
  Sum WholePlaneJet1Index (Fin 2 × Fin 2)

/-- Hilbert ambient space for whole-plane first-order weak jets. -/
abbrev WholePlaneH1Ambient :=
  PiLp 2 (fun _ : WholePlaneJet1Index => WholePlaneL2 F)

/-- Hilbert ambient space for whole-plane second-order weak jets. -/
abbrev WholePlaneH2Ambient :=
  PiLp 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)

/-- Defect in the `j`-th first weak-derivative equation. -/
def wholePlaneH1Defect (j : Fin 2) :
    WholePlaneH1Ambient F →L[ℂ] 𝓢'(WholePlane, F) :=
  (LineDeriv.lineDerivOpCLM ℂ (𝓢'(WholePlane, F)) (wholePlaneBasis j)).comp
      ((wholePlaneL2ToTempered F).comp
        (PiLp.proj 2 (fun _ : WholePlaneJet1Index => WholePlaneL2 F) none)) -
    (wholePlaneL2ToTempered F).comp
      (PiLp.proj 2 (fun _ : WholePlaneJet1Index => WholePlaneL2 F) (some j))

/-- Closed linear graph of all first weak derivatives. -/
def wholePlaneH1Graph : Submodule ℂ (WholePlaneH1Ambient F) :=
  ⨅ j : Fin 2, (wholePlaneH1Defect F j).ker

/-- Membership in the first-order weak graph: a jet lies in `wholePlaneH1Graph F` exactly when,
for each coordinate `j`, the `j`-th line derivative of the tempered distribution attached to the
stored value equals the one attached to the stored `j`-th derivative. -/
theorem mem_wholePlaneH1Graph_iff (u : WholePlaneH1Ambient F) :
    u ∈ wholePlaneH1Graph F ↔
      ∀ j : Fin 2,
        ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered F (u none)) =
          wholePlaneL2ToTempered F (u (some j)) := by
  simp [wholePlaneH1Graph, wholePlaneH1Defect, sub_eq_zero]

/-- The first-order weak graph is closed, being the intersection of the kernels of the two
continuous defect maps. -/
theorem isClosed_wholePlaneH1Graph :
    IsClosed (wholePlaneH1Graph F : Set (WholePlaneH1Ambient F)) := by
  rw [show (wholePlaneH1Graph F : Set (WholePlaneH1Ambient F)) =
      ⋂ j : Fin 2, ((wholePlaneH1Defect F j).ker : Set (WholePlaneH1Ambient F)) by
        ext u
        simp [wholePlaneH1Graph]]
  exact isClosed_iInter fun j => (wholePlaneH1Defect F j).isClosed_ker

/-- Defect in the first weak-derivative part of a second-order jet. -/
def wholePlaneH2FirstDefect (j : Fin 2) :
    WholePlaneH2Ambient F →L[ℂ] 𝓢'(WholePlane, F) :=
  (LineDeriv.lineDerivOpCLM ℂ (𝓢'(WholePlane, F)) (wholePlaneBasis j)).comp
      ((wholePlaneL2ToTempered F).comp
        (PiLp.proj 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)
          (Sum.inl none))) -
    (wholePlaneL2ToTempered F).comp
      (PiLp.proj 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)
        (Sum.inl (some j)))

/-- Defect in the `(j,k)` second weak-derivative equation. -/
def wholePlaneH2SecondDefect (j k : Fin 2) :
    WholePlaneH2Ambient F →L[ℂ] 𝓢'(WholePlane, F) :=
  (LineDeriv.lineDerivOpCLM ℂ (𝓢'(WholePlane, F)) (wholePlaneBasis k)).comp
      ((wholePlaneL2ToTempered F).comp
        (PiLp.proj 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)
          (Sum.inl (some j)))) -
    (wholePlaneL2ToTempered F).comp
      (PiLp.proj 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)
        (Sum.inr (j, k)))

/-- Closed linear graph of all first and ordered second weak derivatives. -/
def wholePlaneH2Graph : Submodule ℂ (WholePlaneH2Ambient F) :=
  (⨅ j : Fin 2, (wholePlaneH2FirstDefect F j).ker) ⊓
    (⨅ j : Fin 2, ⨅ k : Fin 2, (wholePlaneH2SecondDefect F j k).ker)

/-- Membership in the second-order weak graph: the stored first-order entries are the weak
coordinate derivatives of the stored value, and the `(j, k)` entry is the weak `∂_k` derivative of
the stored `j`-th first derivative. -/
theorem mem_wholePlaneH2Graph_iff (u : WholePlaneH2Ambient F) :
    u ∈ wholePlaneH2Graph F ↔
      (∀ j : Fin 2,
        ∂_{wholePlaneBasis j}
            (wholePlaneL2ToTempered F (u (Sum.inl none))) =
          wholePlaneL2ToTempered F (u (Sum.inl (some j)))) ∧
      (∀ j k : Fin 2,
        ∂_{wholePlaneBasis k}
            (wholePlaneL2ToTempered F (u (Sum.inl (some j)))) =
          wholePlaneL2ToTempered F (u (Sum.inr (j, k)))) := by
  simp [wholePlaneH2Graph, wholePlaneH2FirstDefect,
    wholePlaneH2SecondDefect, sub_eq_zero]

/-- The second-order weak graph is closed, being an intersection of kernels of continuous defect
maps. -/
theorem isClosed_wholePlaneH2Graph :
    IsClosed (wholePlaneH2Graph F : Set (WholePlaneH2Ambient F)) := by
  have hfirst : IsClosed
      ((↑(⨅ j : Fin 2, (wholePlaneH2FirstDefect F j).ker) :
        Set (WholePlaneH2Ambient F))) := by
    rw [Submodule.coe_iInf]
    exact isClosed_iInter fun j =>
      (wholePlaneH2FirstDefect F j).isClosed_ker
  have hsecond : IsClosed
      ((↑(⨅ j : Fin 2, ⨅ k : Fin 2,
          (wholePlaneH2SecondDefect F j k).ker) :
        Set (WholePlaneH2Ambient F))) := by
    rw [Submodule.coe_iInf]
    apply isClosed_iInter
    intro j
    rw [Submodule.coe_iInf]
    exact isClosed_iInter fun k =>
      (wholePlaneH2SecondDefect F j k).isClosed_ker
  rw [wholePlaneH2Graph, Submodule.coe_inf]
  exact hfirst.inter hsecond

/-- Whole-plane `H¹`, with its graph Hilbert norm. -/
abbrev WholePlaneH1 := wholePlaneH1Graph F

/-- Whole-plane `H²`, with its graph Hilbert norm. -/
abbrev WholePlaneH2 := wholePlaneH2Graph F

/-- `WholePlaneH1 F` is complete: it is a closed subspace of the Hilbert product of `L²` jets, so
the weak `H¹(ℝ²; F)` graph is itself a Hilbert space. -/
instance wholePlaneH1CompleteSpace : CompleteSpace (WholePlaneH1 F) :=
  (isClosed_wholePlaneH1Graph F).completeSpace_coe

/-- `WholePlaneH2 F` is complete: it is a closed subspace of the Hilbert product of `L²` jets, so
the weak `H²(ℝ²; F)` graph is itself a Hilbert space. -/
instance wholePlaneH2CompleteSpace : CompleteSpace (WholePlaneH2 F) :=
  (isClosed_wholePlaneH2Graph F).completeSpace_coe

/-- Scalar complex whole-plane `H¹`. -/
abbrev WholePlaneScalarH1 := WholePlaneH1 ℂ

/-- Three-component complex whole-plane `H¹`. -/
abbrev WholePlaneC3H1 := WholePlaneH1 C3

/-- Three-component complex whole-plane `H²`. -/
abbrev WholePlaneC3H2 := WholePlaneH2 C3

end Graphs

section Coordinates

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Physical `L²` field underlying a whole-plane `H¹` jet. -/
def wholePlaneH1Embedding : WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  (PiLp.proj 2 (fun _ : WholePlaneJet1Index => WholePlaneL2 F) none).comp
    (wholePlaneH1Graph F).subtypeL

/-- The `j`-th `L²` weak derivative stored by a whole-plane `H¹` jet. -/
def wholePlaneH1FirstDerivative (j : Fin 2) :
    WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  (PiLp.proj 2 (fun _ : WholePlaneJet1Index => WholePlaneL2 F) (some j)).comp
    (wholePlaneH1Graph F).subtypeL

/-- Physical `L²` field underlying a whole-plane `H²` jet. -/
def wholePlaneH2Embedding : WholePlaneH2 F →L[ℂ] WholePlaneL2 F :=
  (PiLp.proj 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)
    (Sum.inl none)).comp (wholePlaneH2Graph F).subtypeL

/-- The `j`-th `L²` weak derivative stored by a whole-plane `H²` jet. -/
def wholePlaneH2FirstDerivative (j : Fin 2) :
    WholePlaneH2 F →L[ℂ] WholePlaneL2 F :=
  (PiLp.proj 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)
    (Sum.inl (some j))).comp (wholePlaneH2Graph F).subtypeL

/-- The ordered second weak derivative `∂_k ∂_j` stored by a whole-plane
`H²` jet. -/
def wholePlaneH2SecondDerivative (j k : Fin 2) :
    WholePlaneH2 F →L[ℂ] WholePlaneL2 F :=
  (PiLp.proj 2 (fun _ : WholePlaneJet2Index => WholePlaneL2 F)
    (Sum.inr (j, k))).comp (wholePlaneH2Graph F).subtypeL

/-- The physical `L²` field of a first-order jet is its `none` coordinate. -/
@[simp] theorem wholePlaneH1Embedding_apply (u : WholePlaneH1 F) :
    wholePlaneH1Embedding F u = u.1 none :=
  rfl

/-- The `j`-th stored weak derivative of a first-order jet is its `some j` coordinate. -/
@[simp] theorem wholePlaneH1FirstDerivative_apply (j : Fin 2)
    (u : WholePlaneH1 F) :
    wholePlaneH1FirstDerivative F j u = u.1 (some j) :=
  rfl

/-- The physical `L²` field of a second-order jet is its `Sum.inl none` coordinate. -/
@[simp] theorem wholePlaneH2Embedding_apply (u : WholePlaneH2 F) :
    wholePlaneH2Embedding F u = u.1 (Sum.inl none) :=
  rfl

/-- The `j`-th stored first weak derivative of a second-order jet is its `Sum.inl (some j)`
coordinate. -/
@[simp] theorem wholePlaneH2FirstDerivative_apply (j : Fin 2)
    (u : WholePlaneH2 F) :
    wholePlaneH2FirstDerivative F j u = u.1 (Sum.inl (some j)) :=
  rfl

/-- The stored ordered second weak derivative `∂_k ∂_j` of a second-order jet is its
`Sum.inr (j, k)` coordinate. -/
@[simp] theorem wholePlaneH2SecondDerivative_apply (j k : Fin 2)
    (u : WholePlaneH2 F) :
    wholePlaneH2SecondDerivative F j k u = u.1 (Sum.inr (j, k)) :=
  rfl

/-- Exact first weak-derivative equation for a whole-plane `H¹` field. -/
theorem wholePlaneH1_firstDerivative_distribution (u : WholePlaneH1 F)
    (j : Fin 2) :
    ∂_{wholePlaneBasis j}
        (wholePlaneL2ToTempered F (wholePlaneH1Embedding F u)) =
      wholePlaneL2ToTempered F (wholePlaneH1FirstDerivative F j u) := by
  exact (mem_wholePlaneH1Graph_iff F u.1).mp u.2 j

/-- Exact first weak-derivative equation for a whole-plane `H²` field. -/
theorem wholePlaneH2_firstDerivative_distribution (u : WholePlaneH2 F)
    (j : Fin 2) :
    ∂_{wholePlaneBasis j}
        (wholePlaneL2ToTempered F (wholePlaneH2Embedding F u)) =
      wholePlaneL2ToTempered F (wholePlaneH2FirstDerivative F j u) := by
  exact (mem_wholePlaneH2Graph_iff F u.1).mp u.2 |>.1 j

/-- Exact ordered second weak-derivative equation for a whole-plane `H²`
field. -/
theorem wholePlaneH2_secondDerivative_distribution (u : WholePlaneH2 F)
    (j k : Fin 2) :
    ∂_{wholePlaneBasis k}
        (wholePlaneL2ToTempered F (wholePlaneH2FirstDerivative F j u)) =
      wholePlaneL2ToTempered F (wholePlaneH2SecondDerivative F j k u) := by
  exact (mem_wholePlaneH2Graph_iff F u.1).mp u.2 |>.2 j k

/-- Every coordinate projection of an `H¹` graph jet is bounded by its graph
norm. -/
theorem norm_wholePlaneH1_coordinate_le (u : WholePlaneH1 F)
    (i : WholePlaneJet1Index) :
    ‖u.1 i‖ ≤ ‖u‖ := by
  exact PiLp.norm_apply_le u.1 i

/-- Every coordinate projection of an `H²` graph jet is bounded by its graph
norm. -/
theorem norm_wholePlaneH2_coordinate_le (u : WholePlaneH2 F)
    (i : WholePlaneJet2Index) :
    ‖u.1 i‖ ≤ ‖u‖ := by
  exact PiLp.norm_apply_le u.1 i

/-- The physical `L²` field of an `H¹` element is bounded by its graph norm. -/
theorem norm_wholePlaneH1Embedding_le (u : WholePlaneH1 F) :
    ‖wholePlaneH1Embedding F u‖ ≤ ‖u‖ :=
  norm_wholePlaneH1_coordinate_le F u none

/-- Each stored first weak derivative of an `H¹` element is bounded by its graph norm. -/
theorem norm_wholePlaneH1FirstDerivative_le (u : WholePlaneH1 F)
    (j : Fin 2) :
    ‖wholePlaneH1FirstDerivative F j u‖ ≤ ‖u‖ :=
  norm_wholePlaneH1_coordinate_le F u (some j)

/-- The physical `L²` field of an `H²` element is bounded by its graph norm. -/
theorem norm_wholePlaneH2Embedding_le (u : WholePlaneH2 F) :
    ‖wholePlaneH2Embedding F u‖ ≤ ‖u‖ :=
  norm_wholePlaneH2_coordinate_le F u (Sum.inl none)

/-- Each stored first weak derivative of an `H²` element is bounded by its graph norm. -/
theorem norm_wholePlaneH2FirstDerivative_le (u : WholePlaneH2 F)
    (j : Fin 2) :
    ‖wholePlaneH2FirstDerivative F j u‖ ≤ ‖u‖ :=
  norm_wholePlaneH2_coordinate_le F u (Sum.inl (some j))

end Coordinates

section Characterization

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Build a whole-plane `H¹` element from explicit `L²` weak derivatives. -/
def wholePlaneH1OfWeakDerivatives (f : WholePlaneL2 F)
    (df : Fin 2 → WholePlaneL2 F)
    (hdf : ∀ j : Fin 2,
      ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered F f) =
        wholePlaneL2ToTempered F (df j)) :
    WholePlaneH1 F := by
  refine ⟨WithLp.toLp 2 (fun i => i.elim f df), ?_⟩
  rw [mem_wholePlaneH1Graph_iff]
  intro j
  simpa using hdf j

/-- Build a whole-plane `H²` element from explicit first and ordered second
`L²` weak derivatives. -/
def wholePlaneH2OfWeakDerivatives (f : WholePlaneL2 F)
    (df : Fin 2 → WholePlaneL2 F)
    (ddf : Fin 2 → Fin 2 → WholePlaneL2 F)
    (hdf : ∀ j : Fin 2,
      ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered F f) =
        wholePlaneL2ToTempered F (df j))
    (hddf : ∀ j k : Fin 2,
      ∂_{wholePlaneBasis k} (wholePlaneL2ToTempered F (df j)) =
        wholePlaneL2ToTempered F (ddf j k)) :
    WholePlaneH2 F := by
  refine ⟨WithLp.toLp 2 (fun i => i.elim
    (fun q => q.elim f df) (fun q => ddf q.1 q.2)), ?_⟩
  rw [mem_wholePlaneH2Graph_iff]
  constructor
  · intro j
    simpa using hdf j
  · intro j k
    simpa using hddf j k

/-- The `H²` element assembled from an `L²` field together with certified first and ordered
second `L²` weak derivatives has that field as its physical `L²` coordinate. -/
theorem wholePlaneH2Embedding_ofWeakDerivatives
    (f : WholePlaneL2 F) (df : Fin 2 → WholePlaneL2 F)
    (ddf : Fin 2 → Fin 2 → WholePlaneL2 F)
    (hdf : ∀ j : Fin 2,
      ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered F f) =
        wholePlaneL2ToTempered F (df j))
    (hddf : ∀ j k : Fin 2,
      ∂_{wholePlaneBasis k} (wholePlaneL2ToTempered F (df j)) =
        wholePlaneL2ToTempered F (ddf j k)) :
    wholePlaneH2Embedding F
      (wholePlaneH2OfWeakDerivatives F f df ddf hdf hddf) = f := by
  rfl

/-- The `H²` element assembled from certified weak derivatives stores `df j` as its `j`-th first
weak derivative. -/
theorem wholePlaneH2FirstDerivative_ofWeakDerivatives
    (f : WholePlaneL2 F) (df : Fin 2 → WholePlaneL2 F)
    (ddf : Fin 2 → Fin 2 → WholePlaneL2 F)
    (hdf : ∀ j : Fin 2,
      ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered F f) =
        wholePlaneL2ToTempered F (df j))
    (hddf : ∀ j k : Fin 2,
      ∂_{wholePlaneBasis k} (wholePlaneL2ToTempered F (df j)) =
        wholePlaneL2ToTempered F (ddf j k)) (j : Fin 2) :
    wholePlaneH2FirstDerivative F j
      (wholePlaneH2OfWeakDerivatives F f df ddf hdf hddf) = df j := by
  rfl

/-- The `H²` element assembled from certified weak derivatives stores `ddf j k` as its ordered
second weak derivative `∂_k ∂_j`. -/
theorem wholePlaneH2SecondDerivative_ofWeakDerivatives
    (f : WholePlaneL2 F) (df : Fin 2 → WholePlaneL2 F)
    (ddf : Fin 2 → Fin 2 → WholePlaneL2 F)
    (hdf : ∀ j : Fin 2,
      ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered F f) =
        wholePlaneL2ToTempered F (df j))
    (hddf : ∀ j k : Fin 2,
      ∂_{wholePlaneBasis k} (wholePlaneL2ToTempered F (df j)) =
        wholePlaneL2ToTempered F (ddf j k)) (j k : Fin 2) :
    wholePlaneH2SecondDerivative F j k
      (wholePlaneH2OfWeakDerivatives F f df ddf hdf hddf) = ddf j k := by
  rfl

/-- The physical projection from the weak `H¹` graph is injective. -/
theorem wholePlaneH1Embedding_injective :
    Function.Injective (wholePlaneH1Embedding F) := by
  intro u v huv
  change u.1 none = v.1 none at huv
  apply Subtype.ext
  apply PiLp.ext
  intro q
  cases q with
  | none => exact huv
  | some j =>
      apply wholePlaneL2ToTempered_injective F
      rw [← (mem_wholePlaneH1Graph_iff F u.1).mp u.2 j,
        ← (mem_wholePlaneH1Graph_iff F v.1).mp v.2 j, huv]

/-- The physical projection from the weak `H²` graph is injective. -/
theorem wholePlaneH2Embedding_injective :
    Function.Injective (wholePlaneH2Embedding F) := by
  intro u v huv
  change u.1 (Sum.inl none) = v.1 (Sum.inl none) at huv
  have hfirst (j : Fin 2) :
      u.1 (Sum.inl (some j)) = v.1 (Sum.inl (some j)) := by
    apply wholePlaneL2ToTempered_injective F
    rw [← (mem_wholePlaneH2Graph_iff F u.1).mp u.2 |>.1 j,
      ← (mem_wholePlaneH2Graph_iff F v.1).mp v.2 |>.1 j, huv]
  apply Subtype.ext
  apply PiLp.ext
  intro q
  cases q with
  | inl q =>
      cases q with
      | none => exact huv
      | some j => exact hfirst j
  | inr q =>
      apply wholePlaneL2ToTempered_injective F
      rw [← (mem_wholePlaneH2Graph_iff F u.1).mp u.2 |>.2 q.1 q.2,
        ← (mem_wholePlaneH2Graph_iff F v.1).mp v.2 |>.2 q.1 q.2,
        hfirst q.1]

end Characterization

section SobolevOperators

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Forgetting the ordered second derivatives at the ambient jet level.  This
is the orthogonal coordinate projection from the `H²` jet onto its first-order
part. -/
def wholePlaneH2ToH1Ambient :
    WholePlaneH2Ambient F →L[ℂ] WholePlaneH1Ambient F :=
  (WithLp.fstL 2 ℂ (WholePlaneH1Ambient F)
      (PiLp 2 (fun _ : Fin 2 × Fin 2 => WholePlaneL2 F))).comp
    (PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : WholePlaneJet2Index => WholePlaneL2 F)).toLinearIsometry.toContinuousLinearMap

omit [CompleteSpace F] in
/-- The ambient forgetful map leaves the first-order block untouched: its `q` coordinate is the
`Sum.inl q` coordinate of the second-order jet. -/
theorem wholePlaneH2ToH1Ambient_apply (u : WholePlaneH2Ambient F)
    (q : WholePlaneJet1Index) :
    wholePlaneH2ToH1Ambient F u q = u (Sum.inl q) := by
  change ((PiLp.sumPiLpEquivProdLpPiLp 2
    (fun _ : WholePlaneJet2Index => WholePlaneL2 F)) u).fst q = _
  rw [← WithLp.ofLp_fst]
  simp only [PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, PiLp.toLp_apply]

omit [CompleteSpace F] in
/-- The first-order coordinate projection is a contraction. -/
theorem norm_wholePlaneH2ToH1Ambient_le (u : WholePlaneH2Ambient F) :
    ‖wholePlaneH2ToH1Ambient F u‖ ≤ ‖u‖ := by
  calc
    ‖wholePlaneH2ToH1Ambient F u‖ =
        ‖((PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2
          (fun _ : WholePlaneJet2Index => WholePlaneL2 F)) u).fst‖ := rfl
    _ ≤ ‖(PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2
          (fun _ : WholePlaneJet2Index => WholePlaneL2 F)) u‖ :=
      WithLp.norm_fst_le _ _
    _ = ‖u‖ := (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2
      (fun _ : WholePlaneJet2Index => WholePlaneL2 F)).norm_map u

/-- The linear map underlying the canonical embedding `H² → H¹`. -/
def wholePlaneH2ToH1Linear : WholePlaneH2 F →ₗ[ℂ] WholePlaneH1 F where
  toFun u := ⟨wholePlaneH2ToH1Ambient F u.1, by
    rw [mem_wholePlaneH1Graph_iff]
    intro j
    simpa only [wholePlaneH2ToH1Ambient_apply] using
      (mem_wholePlaneH2Graph_iff F u.1).mp u.2 |>.1 j⟩
  map_add' u v := by
    apply Subtype.ext
    exact (wholePlaneH2ToH1Ambient F).map_add u.1 v.1
  map_smul' c u := by
    apply Subtype.ext
    exact (wholePlaneH2ToH1Ambient F).map_smul c u.1

/-- Canonical continuous inclusion from the weak graph `H²` into `H¹`. -/
def wholePlaneH2ToH1 : WholePlaneH2 F →L[ℂ] WholePlaneH1 F :=
  (wholePlaneH2ToH1Linear F).mkContinuous 1 fun u => by
    rw [one_mul]
    exact norm_wholePlaneH2ToH1Ambient_le F u.1

/-- The canonical inclusion `H² → H¹` preserves the physical `L²` field. -/
theorem wholePlaneH1Embedding_H2ToH1 (u : WholePlaneH2 F) :
    wholePlaneH1Embedding F (wholePlaneH2ToH1 F u) =
      wholePlaneH2Embedding F u := by
  exact wholePlaneH2ToH1Ambient_apply F u.1 none

/-- The canonical inclusion `H² → H¹` preserves the stored first weak derivatives. -/
theorem wholePlaneH1FirstDerivative_H2ToH1 (u : WholePlaneH2 F)
    (j : Fin 2) :
    wholePlaneH1FirstDerivative F j (wholePlaneH2ToH1 F u) =
      wholePlaneH2FirstDerivative F j u := by
  exact wholePlaneH2ToH1Ambient_apply F u.1 (some j)

/-- Ambient first-derivative row: its physical coordinate is ∂_j u and
its first-derivative coordinates are the ordered derivatives ∂_k ∂_j u. -/
def wholePlaneFirstDerivativeToH1AmbientLinear (j : Fin 2) :
    WholePlaneH2Ambient F →ₗ[ℂ] WholePlaneH1Ambient F where
  toFun u := WithLp.toLp 2 (fun q => q.elim
    (u (Sum.inl (some j))) (fun k => u (Sum.inr (j, k))))
  map_add' u v := by
    apply PiLp.ext
    intro q
    cases q <;> rfl
  map_smul' c u := by
    apply PiLp.ext
    intro q
    cases q <;> rfl

omit [CompleteSpace F] in
/-- The physical coordinate of the `j`-th derivative row of a second-order jet is the stored
first derivative `∂_j u`. -/
theorem wholePlaneFirstDerivativeToH1AmbientLinear_apply
    (j : Fin 2) (u : WholePlaneH2Ambient F) :
    wholePlaneFirstDerivativeToH1AmbientLinear F j u none =
      u (Sum.inl (some j)) := by
  rfl

omit [CompleteSpace F] in
/-- The `k`-th first-derivative coordinate of the `j`-th derivative row of a second-order jet is
the stored ordered second derivative `∂_k ∂_j u`. -/
theorem wholePlaneFirstDerivativeToH1AmbientLinear_apply_some
    (j k : Fin 2) (u : WholePlaneH2Ambient F) :
    wholePlaneFirstDerivativeToH1AmbientLinear F j u (some k) =
      u (Sum.inr (j, k)) := by
  rfl

omit [CompleteSpace F] in
/-- Selecting one derivative row of an H² jet is a contraction. -/
theorem norm_wholePlaneFirstDerivativeToH1AmbientLinear_le
    (j : Fin 2) (u : WholePlaneH2Ambient F) :
    ‖wholePlaneFirstDerivativeToH1AmbientLinear F j u‖ ≤ ‖u‖ := by
  have hnonneg (q : WholePlaneJet2Index) : 0 ≤ ‖u q‖ ^ 2 := sq_nonneg _
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  fin_cases j <;>
    simp [wholePlaneFirstDerivativeToH1AmbientLinear,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    nlinarith [hnonneg (Sum.inl none),
      hnonneg (Sum.inl (some 0)), hnonneg (Sum.inl (some 1)),
      hnonneg (Sum.inr (0, 0)), hnonneg (Sum.inr (0, 1)),
      hnonneg (Sum.inr (1, 0)), hnonneg (Sum.inr (1, 1))]

/-- The linear map underlying D_j : H² → H¹. -/
def wholePlaneFirstDerivativeToH1Linear (j : Fin 2) :
    WholePlaneH2 F →ₗ[ℂ] WholePlaneH1 F where
  toFun u := ⟨wholePlaneFirstDerivativeToH1AmbientLinear F j u.1, by
    rw [mem_wholePlaneH1Graph_iff]
    intro k
    simpa only [wholePlaneFirstDerivativeToH1AmbientLinear_apply,
      wholePlaneFirstDerivativeToH1AmbientLinear_apply_some] using
      (mem_wholePlaneH2Graph_iff F u.1).mp u.2 |>.2 j k⟩
  map_add' u v := by
    apply Subtype.ext
    exact (wholePlaneFirstDerivativeToH1AmbientLinear F j).map_add u.1 v.1
  map_smul' c u := by
    apply Subtype.ext
    exact (wholePlaneFirstDerivativeToH1AmbientLinear F j).map_smul c u.1

/-- The j-th weak derivative as a bounded map H² → H¹. -/
def wholePlaneFirstDerivativeToH1 (j : Fin 2) :
    WholePlaneH2 F →L[ℂ] WholePlaneH1 F :=
  (wholePlaneFirstDerivativeToH1Linear F j).mkContinuous 1 fun u => by
    rw [one_mul]
    exact norm_wholePlaneFirstDerivativeToH1AmbientLinear_le F j u.1

/-- The `H¹` element `∂_j u` extracted from `u : H²` has as physical `L²` field the first weak
derivative `∂_j u` stored by `u`. -/
theorem wholePlaneH1Embedding_firstDerivativeToH1
    (u : WholePlaneH2 F) (j : Fin 2) :
    wholePlaneH1Embedding F (wholePlaneFirstDerivativeToH1 F j u) =
      wholePlaneH2FirstDerivative F j u :=
  wholePlaneFirstDerivativeToH1AmbientLinear_apply F j u.1

/-- The `H¹` element `∂_j u` extracted from `u : H²` stores as its `k`-th weak derivative the
ordered second derivative `∂_k ∂_j u` of `u`. -/
theorem wholePlaneH1FirstDerivative_firstDerivativeToH1
    (u : WholePlaneH2 F) (j k : Fin 2) :
    wholePlaneH1FirstDerivative F k
        (wholePlaneFirstDerivativeToH1 F j u) =
      wholePlaneH2SecondDerivative F j k u :=
  wholePlaneFirstDerivativeToH1AmbientLinear_apply_some F j k u.1

/-- Coordinate orthonormal basis of the transverse Euclidean plane. -/
def wholePlaneOrthonormalBasis : OrthonormalBasis (Fin 2) ℝ WholePlane where
  repr := (EuclideanSpace.basisFun (Fin 2) ℝ).repr

/-- The orthonormal basis of the transverse plane is the coordinate basis: its `j`-th vector is
`wholePlaneBasis j`. -/
theorem wholePlaneOrthonormalBasis_apply (j : Fin 2) :
    wholePlaneOrthonormalBasis j = wholePlaneBasis j := by
  simp [wholePlaneOrthonormalBasis, wholePlaneBasis]

/-- The transverse Laplacian, as the sum of the two diagonal weak second
derivatives. -/
def wholePlaneLaplacian : WholePlaneH2 F →L[ℂ] WholePlaneL2 F :=
  ∑ j : Fin 2, wholePlaneH2SecondDerivative F j j

/-- The transverse Laplacian `Δ_⊥` of an `H²` element is the sum of its two diagonal stored
second derivatives `∂₀∂₀ u + ∂₁∂₁ u`. -/
theorem wholePlaneLaplacian_apply (u : WholePlaneH2 F) :
    wholePlaneLaplacian F u =
      wholePlaneH2SecondDerivative F 0 0 u +
        wholePlaneH2SecondDerivative F 1 1 u := by
  simp [wholePlaneLaplacian, Fin.sum_univ_two]

/-- The L²-valued Laplacian agrees exactly with the distributional
Laplacian of the physical field. -/
theorem wholePlaneLaplacian_toTempered (u : WholePlaneH2 F) :
    wholePlaneL2ToTempered F (wholePlaneLaplacian F u) =
      Δ (wholePlaneL2ToTempered F (wholePlaneH2Embedding F u)) := by
  rw [TemperedDistribution.laplacian_eq_sum wholePlaneOrthonormalBasis]
  simp only [wholePlaneLaplacian, map_sum, sum_apply,
    wholePlaneOrthonormalBasis_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← wholePlaneH2_secondDerivative_distribution F u j j,
    ← wholePlaneH2_firstDerivative_distribution F u j]

end SobolevOperators

end

end FastDynamo
