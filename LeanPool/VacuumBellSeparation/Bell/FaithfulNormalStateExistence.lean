/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalStateDominatedNormalization
public import LeanPool.VacuumBellSeparation.Bell.NormalStateMixtures
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Bases
public import Mathlib.Topology.DenseEmbedding

/-!
# A faithful normal state on a separably acting concrete VNA

The construction sums strictly positive weighted vector functionals in the
original full continuous dual. Normality is preserved by its norm-closed
positive cone. Faithfulness is tested on every positive square and follows
from an actual dense sequence in the original Hilbert space. No faithful
reference state or single-vector representation of the sum is assumed.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Filter SW88
open scoped Topology ComplexOrder InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance faithfulSeries_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- Finite positive sums preserve all directed positive suprema. -/
theorem positiveFunctional_finset_sum_isNormal (M : VonNeumannAlgebra H)
    {ι : Type*} (F : Finset ι) (φ : ι → M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : ∀ i ∈ F, IsNormalFunctional M (φ i)) :
    IsNormalFunctional M (∑ i ∈ F, φ i) := by
  rw [← FunLike.coe_sum F φ]
  intro s hs hd hp X hX
  let : Nonempty s := hs.to_subtype
  let : IsDirectedOrder s := hd.isDirectedOrder
  have hre (Y : M.toStarSubalgebra) :
      ((∑ i ∈ F, φ i) Y).re = ∑ i ∈ F, (φ i Y).re := by
    change Complex.reCLM ((∑ i ∈ F, φ i) Y) = _
    rw [sum_apply]
    exact map_sum Complex.reCLM _ _
  have ht : Tendsto (fun j : s => ((∑ i ∈ F, φ i) j.1).re) atTop
      (𝓝 (((∑ i ∈ F, φ i) X).re)) := by
    simpa only [hre] using tendsto_finsetSum F
      (fun i hi => positiveFunctional_real_tendsto_of_normal M (φ i) (hn i hi) hs hd hp hX)
  constructor
  · rintro _ ⟨Y, hY, rfl⟩
    exact (Complex.le_def.mp ((∑ i ∈ F, φ i).monotone' (hX.1 hY))).1
  · intro r hr
    exact le_of_tendsto ht (Eventually.of_forall fun j : s => hr ⟨j.1, j.2, rfl⟩)

/-- Convergence here is in the full dual norm, not pointwise or weak-star. -/
theorem positiveFunctional_tsum_positive_normal (M : VonNeumannAlgebra H)
    {ι : Type*} (φ : ι → M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hn : ∀ i, IsNormalFunctional M (φ i))
    (hs : Summable (fun i => (PositiveContinuousLinearMap.ofClass (φ i)).toContinuousLinearMap)) :
    let f := ∑' i, (PositiveContinuousLinearMap.ofClass (φ i)).toContinuousLinearMap
    (∀ X : M.toStarSubalgebra, 0 ≤ X → 0 ≤ f X) ∧ IsNormalFunctional M f := by
  apply (isClosed_positive_normal_cone M).mem_of_tendsto hs.hasSum
  apply Eventually.of_forall
  intro F
  have he : (∑ i ∈ F, (PositiveContinuousLinearMap.ofClass (φ i)).toContinuousLinearMap) =
      (PositiveContinuousLinearMap.ofClass (∑ i ∈ F, φ i)).toContinuousLinearMap := by
    ext X
    rw [sum_apply]
    change (∑ i ∈ F, φ i X) = (∑ i ∈ F, φ i) X
    exact (sum_apply F φ X).symm
  rw [he]
  refine ⟨fun X hX => (∑ i ∈ F, φ i).map_nonneg hX, ?_⟩
  simpa only [PositiveContinuousLinearMap.coe_toContinuousLinearMap,
    PositiveContinuousLinearMap.coe_ofClass, FunLike.coe_sum] using
    positiveFunctional_finset_sum_isNormal M F φ (fun i _ => hn i)

private theorem faithfulSeries_hasSum_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ℕ → StrongDual ℂ E} (hs : Summable g) (a : E) :
    HasSum (fun n => g n a) ((∑' n, g n) a) := by
  exact (ContinuousLinearMap.apply ℂ ℂ a).hasSum hs.hasSum

/-- A dense sequence yields a faithful normal positive functional on M itself. -/
theorem exists_faithful_normal_positive_of_denseRange (M : VonNeumannAlgebra H)
    (x : ℕ → H) (hx : DenseRange x) :
    ∃ φ : M.toStarSubalgebra →ₚ[ℂ] ℂ,
      IsNormalFunctional M φ ∧ ∀ a : M.toStarSubalgebra,
        φ (star a * a) = 0 → a = 0 := by
  let w : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n / (1 + ‖vectorDual M (x n)‖)
  have hw (n : ℕ) : 0 < w n :=
    div_pos (pow_pos (by norm_num) n) (by positivity)
  let ψ (n : ℕ) : M.toStarSubalgebra →ₚ[ℂ] ℂ :=
    distillationScaleFunctional (w n) (hw n).le (vectorPositiveLinearMap M (x n))
  let g (n : ℕ) : StrongDual ℂ M.toStarSubalgebra :=
    (PositiveContinuousLinearMap.ofClass (ψ n)).toContinuousLinearMap
  have hg (n : ℕ) : g n = w n • vectorDual M (x n) := by rfl
  have hbound (n : ℕ) : ‖g n‖ ≤ (1 / 2 : ℝ) ^ n := by
    rw [hg n, norm_smul, Real.norm_eq_abs, abs_of_pos (hw n)]
    have he : w n * (1 + ‖vectorDual M (x n)‖) = (1 / 2 : ℝ) ^ n :=
      div_mul_cancel₀ _ (ne_of_gt (by positivity))
    nlinarith [hw n]
  have hs : Summable g :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).of_norm_bounded hbound
  have hn (n : ℕ) : IsNormalFunctional M (ψ n) :=
    (vectorFunctional_isNormal M (x n)).positive_smul (w n) (hw n)
  let f : StrongDual ℂ M.toStarSubalgebra := ∑' n, g n
  obtain ⟨hfpos, hfn⟩ := positiveFunctional_tsum_positive_normal M ψ hn hs
  let φ : M.toStarSubalgebra →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ f.toLinearMap hfpos
  refine ⟨φ, hfn, ?_⟩
  intro a ha
  have ha0 : f (star a * a) = 0 := ha
  have hx0 (n : ℕ) : (a : H →L[ℂ] H) (x n) = 0 := by
    have heval : HasSum (fun i => g i (star a * a)) (f (star a * a)) :=
      faithfulSeries_hasSum_apply hs (star a * a)
    have hle : g n (star a * a) ≤ 0 := by
      rw [← ha0]
      exact le_hasSum heval n (fun i _ => (ψ i).map_nonneg (star_mul_self_nonneg a))
    have hz : g n (star a * a) = 0 :=
      le_antisymm hle ((ψ n).map_nonneg (star_mul_self_nonneg a))
    change w n • vectorFunctional M (x n) (star a * a) = 0 at hz
    have hv : vectorFunctional M (x n) (star a * a) = 0 := by
      have h := congrArg (fun z : ℂ => (w n)⁻¹ • z) hz
      simpa only [smul_smul, inv_mul_cancel₀ (hw n).ne', one_smul, smul_zero] using h
    change inner ℂ (x n) ((star (a : H →L[ℂ] H)) ((a : H →L[ℂ] H) (x n))) = 0 at hv
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at hv
    exact inner_self_eq_zero.mp hv
  have he : (fun z : H => (a : H →L[ℂ] H) z) = fun _ => (0 : H) :=
    hx.equalizer (a : H →L[ℂ] H).continuous continuous_const (funext hx0)
  apply Subtype.ext
  exact ContinuousLinearMap.ext (congrFun he)

/-- Separable nontrivial original H suffices. No faithful state is an input. -/
theorem exists_faithful_normal_state_of_separable [TopologicalSpace.SeparableSpace H] [Nontrivial H]
    (M : VonNeumannAlgebra H) :
    ∃ φ : M.toStarSubalgebra →ₚ[ℂ] ℂ,
      φ 1 = 1 ∧ IsNormalFunctional M φ ∧
        ∀ a : M.toStarSubalgebra, φ (star a * a) = 0 → a = 0 := by
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq H
  obtain ⟨ψ, hn, hf⟩ := exists_faithful_normal_positive_of_denseRange M x hx
  let f := (PositiveContinuousLinearMap.ofClass ψ).toContinuousLinearMap
  have hp : 0 < ‖f‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hψ : ψ (star (1 : M.toStarSubalgebra) * 1) = 0 := by
      have h := congrArg (fun F : StrongDual ℂ M.toStarSubalgebra => F 1) hz
      change ψ 1 = 0 at h
      simpa only [star_one, one_mul] using h
    have h10 : (1 : H →L[ℂ] H) = 0 := congrArg Subtype.val (hf 1 hψ)
    exact one_ne_zero h10
  refine ⟨unitMassPositiveFunctional ψ, unitMassPositiveFunctional_one ψ hp,
    hn.positive_smul ‖f‖⁻¹ (inv_pos.mpr hp), ?_⟩
  intro a ha
  apply hf a
  change ‖f‖⁻¹ • ψ (star a * a) = 0 at ha
  have h := congrArg (fun z : ℂ => ‖f‖ • z) ha
  simpa only [smul_smul, mul_inv_cancel₀ hp.ne', one_smul, smul_zero] using h

end VacuumBellSeparation.Bipartite
