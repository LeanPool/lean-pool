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

theorem measurable_shellRestrict (K : Set (Vec d)) : Measurable (shellRestrict (d  := d) K) :=
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
