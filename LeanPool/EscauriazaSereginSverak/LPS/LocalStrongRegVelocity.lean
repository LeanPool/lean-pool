/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegSlab

/-!
# The regularized velocity on the whole slab

The uniform bound of the regularized family makes the regularized velocity square integrable on the
whole slab `ℝ³ × (0, T)`, including times arbitrarily close to zero (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

section

variable (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
  (b : Vec3 → Vec3) (hb : CKN.IsInJ b)

/-- The uniform bound of the regularized family controls the `L²` norm of every slice
(`lem:lps-regularized-Hk-start`). -/
theorem lps_regR12_l2Energy_le {t : ℝ} (ht : 0 ≤ t) {M : ℝ}
    (h : (∫ x : Vec3, vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ) +
      spatialGradientSq (lpsRegU ρ ε hε b hb)
        (fun z i j => spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z) (x, t)) ≤ M) :
    (∫ x : Vec3, ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2) ≤ M := by
  have hUw := lps_regR12_slice_memLp ρ ε hε b hb t ht
  have ha : ∀ x : Vec3, vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ) =
      ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2 := fun x =>
    lps_vec3EuclideanNorm_sq_eq_sum_sq _
  have hai : Integrable (fun x : Vec3 => vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ))
      volume := by
    simp only [ha]
    exact integrable_finsetSum _ fun i _ => (hUw i []).integrable_sq
  have hbi : Integrable (fun x : Vec3 => spatialGradientSq (lpsRegU ρ ε hε b hb)
      (fun z i j => spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z) (x, t)) volume := by
    unfold spatialGradientSq
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact (hUw i [j]).integrable_sq
  rw [integral_add hai hbi] at h
  have h0 : 0 ≤ ∫ x : Vec3, spatialGradientSq (lpsRegU ρ ε hε b hb)
      (fun z i j => spatialPartial (fun y => lpsRegU ρ ε hε b hb y i) j z) (x, t) :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have : (∫ x : Vec3, vec3EuclideanNorm (lpsRegU ρ ε hε b hb (x, t)) ^ (2 : ℕ)) =
      ∫ x : Vec3, ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2 := by
    congr 1; funext x; exact ha x
  linarith only [h, h0, this]

/-- The regularized velocity is square integrable on the whole slab when its slices are uniformly
bounded in `L²`. -/
theorem lps_regR12_velocity_memLp_open_slab {T M : ℝ}
    (h : ∀ t ∈ Ioc 0 T, (∫ x : Vec3, ∑ i : Fin 3, lpsRegU ρ ε hε b hb (x, t) i ^ 2) ≤ M)
    (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => lpsRegU ρ ε hε b hb z i) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have h1 := CKN.Leray.regR12_regularised_unconditional ρ b hb ε hε
  simp only [CKN.Leray.regR12Uε, CKN.Leray.regR12Pε, hε, ↓reduceDIte] at h1
  obtain ⟨-, hUc, -⟩ := h1
  have hslabSub : vlSlab 0 T ⊆ Set.univ ×ˢ Ioi 0 := fun z hz => ⟨hz.1, hz.2.1⟩
  have hslabMeas : MeasurableSet (vlSlab 0 T) := MeasurableSet.univ.prod measurableSet_Ioo
  have hUcc : ∀ j : Fin 3, ContinuousOn (fun z : Vec3 × ℝ =>
      lpsRegU ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) j) (vlSlab 0 T) := fun j =>
    (((hUc j).comp parabolicHomeomorph.symm.continuous.continuousOn
      (fun _ hz => hz)).mono hslabSub)
  have hUm : ∀ j : Fin 3, AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      lpsRegU ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) j) (volume.restrict (vlSlab 0 T)) :=
    fun j => (hUcc j).aestronglyMeasurable hslabMeas
  let F : Vec3 × ℝ → ℝ := fun z => ∑ j : Fin 3,
    (lpsRegU ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) j) ^ 2
  have hFm : AEStronglyMeasurable F (volume.restrict (vlSlab 0 T)) :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hUm j).pow 2
  have hFnn : ∀ z, 0 ≤ F z := fun z => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsl : ∀ t ∈ Ioo 0 T, Integrable (fun x : Vec3 => F (x, t)) volume ∧
      (∫ x : Vec3, F (x, t)) ≤ (fun _ : ℝ => M) t := by
    intro t ht
    have hUw := lps_regR12_slice_memLp ρ ε hε b hb t ht.1.le
    exact ⟨integrable_finsetSum _ fun j _ => (hUw j []).integrable_sq,
      h t ⟨ht.1, ht.2.le⟩⟩
  obtain ⟨hFint, -⟩ := lps_slab_integrable_of_slice_bound hFm hFnn
    (integrableOn_const (by simp)) hsl
  refine (memLp_two_iff_integrable_sq (hUm i)).2 ?_
  refine Integrable.mono' hFint ((hUm i).pow 2) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (f := fun j : Fin 3 =>
    (lpsRegU ρ ε hε b hb ((z.1, z.2) : ParabolicPoint) j) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

end

end ESS.LPS

end
