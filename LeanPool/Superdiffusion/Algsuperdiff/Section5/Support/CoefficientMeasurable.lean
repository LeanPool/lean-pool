/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Limit
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# CoefficientMeasurable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coefficient field is a measurable map into the continuous fields on a compact set

On a compact set `K` the cutoff coefficient field `a_m(ω) = ν I + k_m(ω)` is a
continuous matrix field, and the assignment `ω ↦ a_m(ω)|_K` is measurable into
the Banach space `C(K, Mat d)` of continuous matrix fields with the supremum
norm.

The proof uses no separability argument and no dense evaluation criterion.  Each
shell of the sample is, by construction, a bundled continuous map, and
restriction to `K` is continuous for the compact-open topologies, so every finite
partial sum of shells is a *continuous* image of finitely many coordinates of
the sample and is therefore measurable.  The lower-tail control makes the partial
sums converge uniformly on every centred cube, hence in `C(K, Mat d)`, and a
pointwise limit of measurable maps into a metrizable Borel space is measurable.

## Main definitions

* `cutoffCoeffMap nu m omega` — the coefficient field as a continuous matrix
  field on `ℝ^d`.
* `coefficientCutoffRestrict nu m K omega` — its restriction to `K`.

## Main results

* `measurable_coefficientCutoffRestrict` — the assignment is measurable.

## References

* ABK26, the cutoff coefficient field of Section 3.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open HCPolySupport MeasureTheory Filter
open scoped Matrix.Norms.Elementwise BigOperators Topology

noncomputable section

variable {d : ℕ}

/-! ## Measurability from closed balls -/

/-- In a separable pseudometric space, measurable closed-ball preimages imply
measurable open-set preimages. -/
theorem measurableSet_preimage_isOpen_of_closedBall {Omega X : Type*}
    (mOmega : MeasurableSpace Omega) [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] {F : Omega → X}
    (hF : ∀ (c : X) (r : ℝ), MeasurableSet[mOmega] (F ⁻¹' Metric.closedBall c r))
    {V : Set X} (hV : IsOpen V) : MeasurableSet[mOmega] (F ⁻¹' V) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have := hDc.to_subtype
  have hEq : F ⁻¹' V =
      ⋃ (c : ↥D) (q : ℚ) (_ : Metric.closedBall (c : X) (q : ℝ) ⊆ V),
        F ⁻¹' Metric.closedBall (c : X) (q : ℝ) := by
    refine Set.Subset.antisymm (fun w hw => ?_) ?_
    · obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.1 hV (F w) hw
      obtain ⟨c, hcD, hc⟩ :=
        Metric.mem_closure_iff.1 (hDd (F w)) (eps / 4) (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show eps / 4 < eps / 3 by linarith)
      refine Set.mem_iUnion.2 ⟨⟨c, hcD⟩, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩⟩
      · intro z hz
        refine hball (Metric.mem_ball.2 ?_)
        have h1 : dist z c ≤ (q : ℝ) := Metric.mem_closedBall.1 hz
        have h2 : dist c (F w) < eps / 4 := by rwa [dist_comm] at hc
        calc dist z (F w) ≤ dist z c + dist c (F w) := dist_triangle _ _ _
          _ < (q : ℝ) + eps / 4 := by linarith
          _ < eps := by linarith
      · exact Metric.mem_closedBall.2 (le_of_lt (hc.trans hq1))
    · refine Set.iUnion_subset fun c => Set.iUnion_subset fun q =>
        Set.iUnion_subset fun hsub => Set.preimage_mono hsub
  rw [hEq]
  exact MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun q =>
    MeasurableSet.iUnion fun _ => hF _ _

/-- A map into a separable pseudometric Borel space is measurable when its
closed-ball preimages are measurable. -/
theorem measurable_of_preimage_closedBall {Omega X : Type*}
    (mOmega : MeasurableSpace Omega) [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X] {F : Omega → X}
    (hF : ∀ (c : X) (r : ℝ), MeasurableSet[mOmega] (F ⁻¹' Metric.closedBall c r)) :
    Measurable[mOmega] F := by
  have key : @Measurable Omega X mOmega
      (MeasurableSpace.generateFrom {s : Set X | IsOpen s}) F :=
    measurable_generateFrom fun _t ht =>
      measurableSet_preimage_isOpen_of_closedBall mOmega hF ht
  intro s hs
  rw [BorelSpace.measurable_eq (α := X)] at hs
  exact key hs

/-! ## Instance caches for `Mat d`

Mathlib v4.33 assembles the scoped elementwise matrix norm with
`fast_instance%`, so the topology reachable from `Matrix.normedAddCommGroup`
is a flattened copy of the product topology and no longer *syntactically*
the one bare `Mat d` carries by default (the plain, unconditional
`TopologicalSpace (Matrix m n R) := inferInstanceAs (TopologicalSpace (m → n
→ R))` bridging instance). `SecondCountableTopology`/`PseudoMetrizableSpace`
have no dedicated `Matrix`-level bridging instance at all, so blind search
for them on `Mat d` fails outright. Both are supplied here, pinned to the
same `Fin d → Fin d → ℝ` spelling the bridging `TopologicalSpace` instance
already uses, so `inferInstanceAs` closes by unfolding the `Matrix` type
synonym rather than by a fresh (and now-failing) search. -/

instance instSecondCountableTopologyMat : SecondCountableTopology (Mat d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))

instance instPseudoMetrizableSpaceMat :
    TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))

instance instPseudoMetricSpaceMat : PseudoMetricSpace (Mat d) :=
  inferInstanceAs (PseudoMetricSpace (Fin d → Fin d → ℝ))

/-- The Borel structure on the continuous matrix fields over a compact carrier. -/
noncomputable instance continuousMatrixFieldMeasurableSpace (K : Set (Vec d))
    : MeasurableSpace C(K, Mat d) := borel _

instance continuousMatrixFieldBorelSpace (K : Set (Vec d)) : BorelSpace C(K, Mat d) := ⟨rfl⟩

/-- A continuous matrix field on a compact carrier is measurable when its
values on a countable dense subset are measurable. -/
theorem measurable_continuousMap_of_dense_evaluations {Omega : Type*}
    (mOmega : MeasurableSpace Omega) {K : Set (Vec d)} [CompactSpace K]
    {D : Set K} (hDc : D.Countable) (hDd : Dense D) {F : Omega → C(K, Mat d)}
    (hF : ∀ z : K, z ∈ D → Measurable[mOmega] fun w => F w z) :
    Measurable[mOmega] F := by
  have : SecondCountableTopology C(K, Mat d) := inferInstance
  refine measurable_of_preimage_closedBall mOmega fun g r => ?_
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.2 hr, Set.preimage_empty]
    exact MeasurableSet.empty
  · have hEqset : F ⁻¹' Metric.closedBall g r =
        ⋂ z ∈ D, {w | dist (F w z) (g z) ≤ r} := by
      ext w
      simp only [Set.mem_preimage, Metric.mem_closedBall, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h z _
        exact (ContinuousMap.dist_le hr).1 h z
      · intro h
        refine (ContinuousMap.dist_le hr).2 fun z => ?_
        have hclosed : IsClosed {z : ↥K | dist (F w z) (g z) ≤ r} :=
          isClosed_le ((F w).continuous.dist g.continuous) continuous_const
        have hsub : (Set.univ : Set ↥K) ⊆ {z : ↥K | dist (F w z) (g z) ≤ r} := by
          rw [← hDd.closure_eq]
          exact hclosed.closure_subset_iff.2 fun z hz => h z hz
        exact hsub (Set.mem_univ z)
    rw [hEqset]
    refine MeasurableSet.biInter hDc fun z hz => ?_
    have hdist : Measurable[mOmega] fun w => dist (F w z) (g z) :=
      (continuous_id.dist continuous_const).measurable.comp (hF z hz)
    exact measurableSet_le hdist measurable_const

/-! ## 1. Restricting a shell to a compact carrier -/

/-- The restriction of the value part of a shell to a compact carrier. -/
def shellRestrict (K : Set (Vec d)) (j : ShellField d) : C(K, Mat d) :=
  (j.1.1).restrict K

theorem continuous_shellRestrict (K : Set (Vec d)) :
    Continuous (shellRestrict (d := d) K) := by
  have hproj : Continuous fun j : ShellField d => j.1.1 :=
    (continuous_fst.comp continuous_subtype_val)
  have hincl : Continuous fun _ : ShellField d =>
      (⟨(Subtype.val : K → Vec d), continuous_subtype_val⟩ : C(K, Vec d)) :=
    continuous_const
  exact hproj.compCM hincl

theorem measurable_shellRestrict (K : Set (Vec d)) : Measurable (shellRestrict (d := d) K) :=
  (continuous_shellRestrict K).measurable

/-! ## 2. The coefficient field as a continuous matrix field -/

/-- The cutoff coefficient field at scale `m`, as a continuous matrix field. -/
def cutoffCoeffMap (nu : ℝ) (m : ℤ) (omega : Cutoff.CutoffSample d) : C(Vec d, Mat d) :=
  ⟨fun x => (Cutoff.coefficientCutoff nu m omega).toCoeffField x,
    continuous_matrix fun i j => by
      simp only [RegCoeffField.toCoeffField, Cutoff.coefficientCutoff_apply,
        Matrix.add_apply]
      exact continuous_const.add (Cutoff.continuous_cutoff_entry m omega i j)⟩

@[simp] theorem cutoffCoeffMap_apply (nu : ℝ) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (x : Vec d) :
    cutoffCoeffMap nu m omega x = (Cutoff.coefficientCutoff nu m omega).toCoeffField x :=
  rfl

/-- The coefficient field restricted to a compact carrier. -/
def coefficientCutoffRestrict (nu : ℝ) (m : ℤ) (K : Set (Vec d))
    (omega : Cutoff.CutoffSample d) : C(K, Mat d) :=
  (cutoffCoeffMap nu m omega).restrict K

/-! ## 3. Partial sums of shells are measurable -/

/-- The descending partial sum of shells, restricted to a compact carrier. -/
def shellPartialRestrict (K : Set (Vec d)) (m : ℤ) (q : ℕ)
    (omega : Cutoff.CutoffSample d) : C(K, Mat d) :=
  ∑ r ∈ Finset.range q, shellRestrict K (omega.1 (m - (r : ℤ)))

theorem measurable_shellPartialRestrict (K : Set (Vec d)) [CompactSpace K] (m : ℤ) (q : ℕ) :
    Measurable (shellPartialRestrict (d := d) K m q) := by
  have : SecondCountableTopology C(K, Mat d) := inferInstance
  refine Finset.measurable_sum _ fun r _ => ?_
  exact (measurable_shellRestrict K).comp
    ((measurable_pi_apply (m - (r : ℤ))).comp measurable_subtype_coe)

theorem shellPartialRestrict_apply (K : Set (Vec d)) (m : ℤ) (q : ℕ)
    (omega : Cutoff.CutoffSample d) (x : K) (i j : Fin d) :
    shellPartialRestrict K m q omega x i j =
      Cutoff.finiteLowerCutoff m q omega.1 (x : Vec d) i j := by
  rw [Cutoff.finiteLowerCutoff_apply_entry_eq_sum_range_desc]
  simp [shellPartialRestrict, shellRestrict, Matrix.sum_apply]

/-! ## 4. Uniform convergence of the partial sums on a compact carrier -/

/-- The cutoff field as a continuous matrix field. -/
def cutoffMap (m : ℤ) (omega : Cutoff.CutoffSample d) : C(Vec d, Mat d) :=
  ⟨fun x => Cutoff.cutoff m omega x,
    continuous_matrix fun i j => Cutoff.continuous_cutoff_entry m omega i j⟩

/-- The cutoff field restricted to a compact carrier. -/
def cutoffRestrict (K : Set (Vec d)) (m : ℤ) (omega : Cutoff.CutoffSample d) : C(K, Mat d) :=
  (cutoffMap m omega).restrict K

theorem tendsto_shellPartialRestrict (K : Set (Vec d)) [CompactSpace K] (m ell : ℤ)
    (hK : K ⊆ openCubeSet (originCube d ell)) (omega : Cutoff.CutoffSample d) :
    Tendsto (fun q => shellPartialRestrict K m q omega) atTop
      (𝓝 (cutoffRestrict K m omega)) := by
  refine (Metric.tendsto_atTop (α := C(K, Mat d)) (β := ℕ)).2 ?_
  intro eps heps
  have hhalf : (0 : ℝ) < eps / 2 := by linarith
  have hent : ∀ p : Fin d × Fin d, ∃ N : ℕ, ∀ q, N ≤ q → ∀ x ∈ K,
      dist (Cutoff.cutoff m omega x p.1 p.2)
        (Cutoff.finiteLowerCutoff m q omega.1 x p.1 p.2) < eps / 2 := by
    rintro ⟨i, j⟩
    have hbase :=
      (Cutoff.lowerTailGood_tendstoUniformlyOn_finiteLowerCutoff_entry omega.2 ell m i j).mono hK
    rw [Metric.tendstoUniformlyOn_iff] at hbase
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hbase (eps / 2) hhalf)
    exact ⟨N, fun q hq x hx => hN q hq x hx⟩
  choose N hN using hent
  refine ⟨Finset.univ.sup N, fun q hq => ?_⟩
  have hdist : dist (shellPartialRestrict K m q omega) (cutoffRestrict K m omega) ≤ eps / 2 := by
    rw [ContinuousMap.dist_le hhalf.le]
    intro x
    rw [dist_eq_norm, Matrix.norm_le_iff hhalf.le]
    intro i j
    have hle : N (i, j) ≤ q :=
      le_trans (Finset.le_sup (Finset.mem_univ (i, j))) hq
    have hx : (x : Vec d) ∈ K := x.2
    have h := hN (i, j) q hle (x : Vec d) hx
    rw [Real.dist_eq] at h
    have hentry : ((shellPartialRestrict K m q omega) x - (cutoffRestrict K m omega) x) i j =
        Cutoff.finiteLowerCutoff m q omega.1 (x : Vec d) i j -
          Cutoff.cutoff m omega (x : Vec d) i j := by
      rw [Matrix.sub_apply, shellPartialRestrict_apply]
      rfl
    rw [hentry, Real.norm_eq_abs, abs_sub_comm]
    exact h.le
  linarith

/-! ## 5. Measurability -/

theorem measurable_cutoffRestrict (K : Set (Vec d)) [CompactSpace K] (m ell : ℤ)
    (hK : K ⊆ openCubeSet (originCube d ell)) :
    Measurable (cutoffRestrict (d := d) K m) :=
  measurable_of_tendsto_metrizable (fun q => measurable_shellPartialRestrict K m q)
    (tendsto_pi_nhds.2 (tendsto_shellPartialRestrict K m ell hK))

/-- **The coefficient field is a measurable map into the continuous fields on a
compact carrier.** -/
theorem measurable_coefficientCutoffRestrict (nu : ℝ) (K : Set (Vec d)) [CompactSpace K]
    (m ell : ℤ) (hK : K ⊆ openCubeSet (originCube d ell)) :
    Measurable (coefficientCutoffRestrict (d := d) nu m K) := by
  have : SecondCountableTopology C(K, Mat d) := inferInstance
  have hconst : coefficientCutoffRestrict (d := d) nu m K = fun omega =>
      ((ContinuousMap.const (Vec d) (nu • (1 : Mat d))).restrict K) +
        cutoffRestrict K m omega := by
    funext omega
    ext x i j
    simp [coefficientCutoffRestrict, cutoffCoeffMap, cutoffRestrict, cutoffMap,
      RegCoeffField.toCoeffField, Cutoff.coefficientCutoff_apply]
  rw [hconst]
  exact (measurable_cutoffRestrict K m ell hK).const_add _

end

end Algsuperdiff.Section5.Support
