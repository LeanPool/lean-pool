/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Adapted from CutoffRigidity/Riemann/DiffKer1.lean and DiffKer2.lean for Lean Pool.

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Compact

/-! # Continuous representatives of the range of an L² operator -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace CutoffRigidity.L2Kernel

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X}

/-- An operator has continuous representatives if every vector in its range has one. -/
def HasContinuousRepresentatives (T : (X →₂[μ] ℝ) →L[ℝ] (X →₂[μ] ℝ)) : Prop :=
  ∀ u, ∃ f : C(X, ℝ), (T u : X → ℝ) =ᵐ[μ] f

namespace HasContinuousRepresentatives

variable {T : (X →₂[μ] ℝ) →L[ℝ] (X →₂[μ] ℝ)}

/-- A continuous version of an output vector. Under full support it is unique. -/
noncomputable def representative (h : HasContinuousRepresentatives T) (u : X →₂[μ] ℝ) :
    C(X, ℝ) := Classical.choose (h u)

/-- The chosen continuous version is a representative of the original vector. -/
theorem ae_representative (h : HasContinuousRepresentatives T) (u : X →₂[μ] ℝ) :
    (T u : X → ℝ) =ᵐ[μ] h.representative u :=
  Classical.choose_spec (h u)

variable [μ.IsOpenPosMeasure]

/-- With full support a continuous representative is determined by the output vector. -/
theorem representative_eq (h : HasContinuousRepresentatives T)
    {u : X →₂[μ] ℝ} {f : C(X, ℝ)} (hf : (T u : X → ℝ) =ᵐ[μ] f) :
    h.representative u = f :=
  DFunLike.coe_injective <| Measure.eq_of_ae_eq ((h.ae_representative u).symm.trans hf)
    (h.representative u).continuous f.continuous

/-- Taking continuous representatives is linear when the measure has full support. -/
noncomputable def lift (h : HasContinuousRepresentatives T) : (X →₂[μ] ℝ) →ₗ[ℝ] C(X, ℝ) where
  toFun := h.representative
  map_add' u v := by
    apply h.representative_eq
    rw [map_add]
    filter_upwards [Lp.coeFn_add (T u) (T v), h.ae_representative u, h.ae_representative v]
      with x hAdd hu hv
    simpa only [Pi.add_apply, ContinuousMap.add_apply, hu, hv] using hAdd
  map_smul' c u := by
    apply h.representative_eq
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (T u), h.ae_representative u] with x hMul hu
    simpa only [Pi.smul_apply, ContinuousMap.smul_apply, RingHom.id_apply, hu] using hMul

@[simp] theorem lift_apply (h : HasContinuousRepresentatives T) (u : X →₂[μ] ℝ) :
    h.lift u = h.representative u := rfl

variable [BorelSpace X]

private noncomputable def restrictLift (h : HasContinuousRepresentatives T) (K : Set X) :
    (X →₂[μ] ℝ) →ₗ[ℝ] C(K, ℝ) where
  toFun u := (h.lift u).comp ⟨Subtype.val, continuous_subtype_val⟩
  map_add' u v := by
    rw [map_add]
    rfl
  map_smul' c u := by
    rw [map_smul]
    rfl

private theorem continuous_restrictLift (h : HasContinuousRepresentatives T)
    {K : Set X} (hClosed : IsClosed K) [CompactSpace K] (hK : K ⊆ closure (interior K)) :
    Continuous (h.restrictLift K) := by
  classical
  refine LinearMap.continuous_of_seq_closed_graph _ fun u f g hu hg => ?_
  obtain ⟨subsequence, hSubsequence, hLimit⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((T.continuous.tendsto f).comp hu)).exists_seq_tendsto_ae
  have hAll := ae_all_iff.2 fun n => h.ae_representative (u n)
  have hPoint : ∀ᵐ x ∂μ, ∀ hx : x ∈ K, g ⟨x, hx⟩ = h.representative f x := by
    filter_upwards [hLimit, hAll, h.ae_representative f] with x hx hRep hf hxK
    have hEval := ((ContinuousMap.evalCLM ℝ (⟨x, hxK⟩ : K)).continuous.tendsto g).comp
      (hg.comp hSubsequence.tendsto_atTop)
    have hx' : Tendsto (fun n => h.representative (u (subsequence n)) x) atTop
        (𝓝 (h.representative f x)) := by
      simpa only [Function.comp_apply, hRep, hf] using hx
    exact tendsto_nhds_unique hEval hx'
  let gExtension (x : X) := if hx : x ∈ K then g ⟨x, hx⟩ else 0
  have hCont : ContinuousOn gExtension K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : K.domRestrict gExtension = g := by
      funext x
      simp [gExtension, x.property]
    rw [hEq]
    exact g.continuous
  have hAE : gExtension =ᵐ[μ.restrict K] h.representative f := by
    filter_upwards [ae_restrict_of_ae hPoint, ae_restrict_mem hClosed.measurableSet] with x hx hxK
    simpa [gExtension, hxK] using hx hxK
  have hEq := Measure.eqOn_of_ae_eq hAE hCont (h.representative f).continuous.continuousOn hK
  ext x
  simpa [restrictLift, gExtension, x.property] using hEq x.property

/-- On each compact set in a locally compact Hausdorff space, continuous representatives satisfy a
uniform bound by the input vector norm. -/
theorem locally_bounded [T2Space X] [LocallyCompactSpace X]
    (h : HasContinuousRepresentatives T) {K : Set X} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ (u : X →₂[μ] ℝ) (x : X), x ∈ K →
      ‖h.representative u x‖ ≤ C * ‖u‖ := by
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  let K' := closure (interior L)
  have hK' : IsCompact K' := hL.of_isClosed_subset isClosed_closure
    (closure_minimal interior_subset hL.isClosed)
  let : CompactSpace K' := isCompact_iff_compactSpace.1 hK'
  have hRegular : K' ⊆ closure (interior K') :=
    closure_mono (interior_maximal subset_closure isOpen_interior)
  let bound : (X →₂[μ] ℝ) →L[ℝ] C(K', ℝ) :=
    ⟨h.restrictLift K', h.continuous_restrictLift isClosed_closure hRegular⟩
  refine ⟨‖bound‖, fun u x hx => ?_⟩
  have hx' : x ∈ K' := subset_closure (hKL hx)
  calc
    ‖h.representative u x‖ ≤ ‖bound u‖ := ContinuousMap.norm_coe_le_norm (bound u) (⟨x, hx'⟩ : K')
    _ ≤ ‖bound‖ * ‖u‖ := bound.le_opNorm u

end HasContinuousRepresentatives
end CutoffRigidity.L2Kernel
