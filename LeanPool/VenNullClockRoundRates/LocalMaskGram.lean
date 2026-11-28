/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AbPh project (AI-generated Lean proofs)
-/

-- Modified for Lean Pool: adapted the module name and imports.

module

public import LeanPool.VenNullClockRoundRates.LocalMaskModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact interpolation with a strict positivity margin. The invertibility
step is proved from the integral of the square, not stipulated. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology
namespace VenMask
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
variable (μ : Measure Ω) (k : Fin n → Ω → ℝ)

private theorem linInt (f : Fin n → Ω → ℝ) (g : Ω → ℝ) (c : Fin n → ℝ)
    (h : ∀ i, Integrable (fun y ↦ f i y * g y) μ) :
    Integrable (fun y ↦ synthesis f c y * g y) μ ∧
    (∫ y, synthesis f c y * g y ∂μ) =
      ∑ j, c j * ∫ y, f j y * g y ∂μ := by
  have eqn (y : Ω) : synthesis f c y * g y = ∑ i, c i * (f i y * g y) := by
    simp [synthesis, Finset.sum_mul, mul_assoc]
  have hint (i : Fin n) : Integrable (fun y ↦ c i * (f i y * g y)) μ := (h i).const_mul _
  simp_rw [eqn]
  exact ⟨integrable_finsetSum _ fun i _ ↦ hint i, by
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    simp only [integral_const_mul]⟩

/-- Independence modulo null sets implies that the finite response matrix
is a unit, with no matrix nondegeneracy assumption. -/
theorem gram_isUnit
    (h : ∀ i j, Integrable (fun y ↦ k j y * k i y) μ)
    (hind : AEIndependent μ k) : IsUnit (gram μ k) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  apply (injective_iff_map_eq_zero (gram μ k).mulVecLin).2
  intro c hc
  change (gram μ k).mulVec c = 0 at hc
  have inner (i : Fin n) : Integrable (fun y ↦ synthesis k c y * k i y) μ ∧
      (∫ y, synthesis k c y * k i y ∂μ) = 0 := by
    obtain ⟨int, eqn⟩ := linInt μ k (k i) c (h i)
    refine ⟨int, eqn.trans ?_⟩
    simpa [gram, Matrix.mulVec, dotProduct, mul_comm] using congrFun hc i
  have outer (i : Fin n) : Integrable (fun y ↦ k i y * synthesis k c y) μ := by
    simpa only [mul_comm] using (inner i).1
  obtain ⟨int, eqn⟩ := linInt μ k (synthesis k c) c outer
  have inside (i : Fin n) : (∫ y, k i y * synthesis k c y ∂μ) = 0 := by
    simpa only [mul_comm] using (inner i).2
  simp only [inside, mul_zero, Finset.sum_const_zero] at eqn
  have hzero := (integral_eq_zero_iff_of_nonneg
    (f := fun y ↦ synthesis k c y * synthesis k c y)
    (fun y ↦ mul_self_nonneg _) int).mp eqn
  apply hind
  filter_upwards [hzero] with y hy
  change synthesis k c y * synthesis k c y = 0 at hy
  exact (mul_self_eq_zero.mp hy)

private theorem perturb_read (c : Fin n → ℝ) (w : ℝ)
    (hk : ∀ i, Integrable (k i) μ)
    (h : ∀ i j, Integrable (fun y ↦ k j y * k i y) μ) :
    read μ k (fun y ↦ w + synthesis k c y) =
      read μ k (fun _ ↦ w) + (gram μ k).mulVec c := by
  funext i
  obtain ⟨hi, eqn⟩ := linInt μ k (k i) c (h i)
  change (∫ y, (w + synthesis k c y) * k i y ∂μ) = _
  simp_rw [add_mul]
  rw [integral_add ((hk i).const_mul _) hi, eqn]
  simp [read, gram, Matrix.mulVec, dotProduct, mul_comm]

omit [MeasurableSpace Ω] in
private theorem synthesis_bound (c : Fin n → ℝ) (B : ℝ) (hk : ∀ i y, |k i y| ≤ B) (y : Ω) :
    |synthesis k c y| ≤ ∑ j, |c j| * B :=
  (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun i _ ↦ by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hk i y) (abs_nonneg _)

/-- A local change of geometry can be exactly erased across an arbitrary
finite list of measured kernels. The geometry enters through independence and
continuity of the *unperturbed* integrals; no masking field is assumed. -/
theorem local_masking : LocalMaskingCertificate := by
  intro Ω Z _ _ n μ k z₀ w₀ B hw hB hint hprod hind hG hread
  let G := fun z ↦ gram μ (k z)
  let d := fun z ↦ read μ (k z) (fun _ ↦ w₀)
  let c := fun z ↦ ((G z)⁻¹).mulVec (d z₀ - d z)
  have base : IsUnit (G z₀).det :=
    (G z₀).isUnit_iff_isUnit_det.mp (gram_isUnit μ _ hprod.self_of_nhds hind)
  have hdet : ContinuousAt (fun z ↦ (G z).det) z₀ :=
    continuous_id.matrix_det.continuousAt.comp hG
  have nearbyDet := hdet.eventually_ne base.ne_zero
  have hInv : ContinuousAt (fun z ↦ (G z)⁻¹) z₀ := by
    apply (continuousAt_matrix_inv (G z₀) ?_).comp hG
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ base.ne_zero
  have hrem : ContinuousAt (fun z ↦ d z₀ - d z) z₀ := continuousAt_const.sub hread
  have hcoeff (i : Fin n) : ContinuousAt (fun z ↦ c z i) z₀ := by
    change ContinuousAt (fun z ↦ ∑ j, (G z)⁻¹ i j * (d z₀ - d z) j) z₀
    have step (j : Fin n) : ContinuousAt (fun z ↦ (G z)⁻¹ i j * (d z₀ - d z) j) z₀ :=
      ((continuousAt_pi.mp (continuousAt_pi.mp hInv i)) j).mul (continuousAt_pi.mp hrem j)
    fun_prop (disch := assumption)
  have hc0 : c z₀ = 0 := by simp [c]
  have habs : ContinuousAt (fun z ↦ ∑ j, |c z j| * B) z₀ := by
    fun_prop (disch := assumption)
  have small : ∀ᶠ z in 𝓝 z₀, (∑ j, |c z j| * B) < w₀ - 1 := by
    apply habs.eventually_lt continuousAt_const
    simpa [hc0] using sub_pos.mpr hw
  filter_upwards [small, nearbyDet, hB, hint, hprod] with z hs hz hb hk hp
  refine ⟨c z, fun y ↦ ?_, ?_⟩
  · have he := (abs_le.mp (synthesis_bound (k z) (c z) B hb y)).1
    linarith
  · rw [perturb_read μ (k z) (c z) w₀ hk hp]
    change d z + (G z).mulVec (((G z)⁻¹).mulVec (d z₀ - d z)) = d z₀
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hz),
      Matrix.one_mulVec, add_sub_cancel]
end VenMask
