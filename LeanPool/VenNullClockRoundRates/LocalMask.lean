/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AbPh project (AI-generated Lean proofs)
-/

-- Modified for Lean Pool: adapted the module name and imports.

module

public import LeanPool.VenNullClockRoundRates.LocalMaskAngular
public import LeanPool.VenNullClockRoundRates.LocalMaskSphereModel
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The nonparallel-axis energy pair genuinely images an open set. An explicit
angular preimage uses positive square roots on a patch below (1,1). -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace VenMask

private def reverseEnergy (a : ℝ) : ℝ := Real.sqrt (1 - Real.sqrt a)

private theorem energy_reverse {a : ℝ} (h : a ∈ Set.Ioo (0 : ℝ) 1) :
    energy (reverseEnergy a) = a := by
  have r := Real.sq_sqrt (sub_nonneg.mpr (Real.sqrt_le_one.mpr h.2.le))
  unfold energy reverseEnergy
  rw [r]
  simpa using Real.sq_sqrt h.1.le

private theorem open_image (θ : ℝ) (hs : Real.sin θ ≠ 0) :
    ∃ p : ℝ × ℝ, Set.range (fun y ↦ (firstEnergy y, secondEnergy θ y)) ∈ 𝓝 p := by
  let X := fun p : ℝ × ℝ ↦ reverseEnergy p.1
  let Y := fun p : ℝ × ℝ ↦ (reverseEnergy p.2 - Real.cos θ * X p) / Real.sin θ
  let D := fun p : ℝ × ℝ ↦ (X p)^2 + (Y p)^2
  have hc : Continuous D := by unfold D Y X reverseEnergy; fun_prop
  have h1 : D (1,1) = 0 := by simp [D, X, Y, reverseEnergy]
  have dio : ∀ᶠ p in 𝓝 ((1,1) : ℝ × ℝ), D p < 1 :=
    hc.continuousAt.eventually_lt continuousAt_const (by simp [h1])
  have diag : Tendsto (fun t : ℝ ↦ (t,t)) (𝓝 1) (𝓝 (1,1)) :=
    (continuous_id.prodMk continuous_id).continuousAt
  have far : ∀ᶠ t in 𝓝[Set.Iio (1 : ℝ)] 1, D (t,t) < 1 :=
    (diag.eventually dio).filter_mono nhdsWithin_le_nhds
  have pos : ∀ᶠ t in 𝓝[Set.Iio (1 : ℝ)] 1, 0 < t :=
    (lt_mem_nhds (zero_lt_one : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have lo : ∀ᶠ t in 𝓝[Set.Iio (1 : ℝ)] 1, t < 1 := self_mem_nhdsWithin
  obtain ⟨t, ht0, ht1, htD⟩ := (pos.and (lo.and far)).exists
  refine ⟨(t,t), ?_⟩
  have h0 : Set.Ioo (0:ℝ) 1 ∈ 𝓝 t := Ioo_mem_nhds ht0 ht1
  have hfst := (continuous_fst.continuousAt (x := (t,t))).tendsto.eventually h0
  have hsnd := (continuous_snd.continuousAt (x := (t,t))).tendsto.eventually h0
  have hd := (hc.continuousAt (x := (t,t))).eventually_lt continuousAt_const htD
  filter_upwards [hfst,hsnd,hd] with p hf hg hdis
  let y : UnitSphere := ⟨(X p, Y p, Real.sqrt (1 - D p)), by
    change (X p)^2 + (Y p)^2 + (Real.sqrt (1-D p))^2 = 1
    rw [Real.sq_sqrt (by linarith)]; dsimp [D]; ring⟩
  refine ⟨y, Prod.ext ?_ ?_⟩
  · exact energy_reverse hf
  · change energy (Real.cos θ * X p + Real.sin θ * Y p) = p.2
    have heq : Real.cos θ * X p + Real.sin θ * Y p = reverseEnergy p.2 := by
      unfold Y; field_simp; ring
    rw [heq]; exact energy_reverse hg

private theorem energy_bounds {u : ℝ} (hu : u ^ 2 ≤ 1) : |energy u| ≤ 1 := by
  unfold energy
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith only [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu), sq_nonneg u]

/-- Actual nonaligned quadrupole axes on the unit sphere satisfy the
finite-scan obstruction; there is no open-image or Gram hypothesis. -/
theorem sphere_local_masking : SphereMaskingCertificate := by
  intro n μ _ _ x s θ₀ w₀ hw hs hm
  let _ : OpensMeasurableSpace UnitSphere := inferInstanceAs
    (OpensMeasurableSpace {q : ℝ × ℝ × ℝ // q.1^2 + q.2.1^2 + q.2.2^2 = 1})
  have h₁ : Continuous firstEnergy := by
    change Continuous (fun y : {q : ℝ × ℝ × ℝ // _} ↦ (1 - y.val.1 ^ 2)^2); fun_prop
  have h₂ (θ : ℝ) : Continuous (secondEnergy θ) := by
    change Continuous (fun y : {q : ℝ × ℝ × ℝ // _} ↦
      (1 - (Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1)^2)^2); fun_prop
  have hθ (y : UnitSphere) : ContinuousAt (fun θ ↦ secondEnergy θ y) θ₀ := by
    unfold secondEnergy energy; fun_prop
  have hbound (θ : ℝ) (y : UnitSphere) : |firstEnergy y| ≤ 1 ∧ |secondEnergy θ y| ≤ 1 := by
    have hlen := y.property
    have hproj := Real.sin_sq_add_cos_sq θ
    have alg : (Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1)^2 +
        (Real.sin θ * y.val.1 - Real.cos θ * y.val.2.1)^2 =
        (Real.sin θ ^2 + Real.cos θ ^2)*(y.val.1^2+y.val.2.1^2) := by ring
    rw [hproj, one_mul] at alg
    constructor
    · apply energy_bounds
      nlinarith only [hlen, sq_nonneg y.val.2.1, sq_nonneg y.val.2.2]
    · apply energy_bounds
      nlinarith only [hlen, alg, sq_nonneg (Real.sin θ * y.val.1-Real.cos θ * y.val.2.1),
        sq_nonneg y.val.2.2]
  have H := exponential_local_masking μ x s (fun _ ↦ firstEnergy) secondEnergy θ₀ w₀
    hw hm (open_image _ hs) (fun θ ↦ ⟨h₁,h₂ θ⟩) (fun y ↦ ⟨continuousAt_const,hθ y⟩) hbound
  filter_upwards [H] with θ hh
  obtain ⟨c, hc, hr⟩ := hh
  exact ⟨c, hc, fun i ↦ congrFun hr i⟩
end VenMask
