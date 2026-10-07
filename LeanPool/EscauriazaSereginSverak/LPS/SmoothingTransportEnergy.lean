/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTensorAlgebra
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportPairing

/-!
# Ordered transport-energy pairing

After one derivative is moved from the tensor divergence onto the
energy test field, the transport term is controlled by the gradient
energy and the tensor `H^m` energy.
-/

public section

open CKN

open MeasureTheory Set
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The differentiated transport tensor pairs against the velocity
gradient with a scale-independent `H^m` bound
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_ordered_transport_pairing_bound (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v u : Vec3 → Vec3),
      (∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j)) →
      (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) →
      (∀ (j : Fin 3) (α : List (Fin 3)), α.length ≤ m →
        MemLp (wordDeriv α (fun x => v x j)) 2 volume) →
      (∀ (i : Fin 3) (α : List (Fin 3)), α.length ≤ m + 1 →
        MemLp (wordDeriv α (fun x => u x i)) 2 volume) →
      let W := sobolevWords m
      let Nv := ∑ j : Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => v x j))
      let Nu := ∑ i : Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => u x i))
      let D := ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
        ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2
      (∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
        ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x *
          wordDeriv α (fun y => v y j * u y i) x) ≤
        Real.sqrt D * Real.sqrt (C * Nv * Nu) := by
  obtain ⟨C, hC, hTensor⟩ := lps_smooth_transport_tensor_normSq m hm
  refine ⟨C, hC, ?_⟩
  intro v u hv hu hvL2 huL2
  let W := sobolevWords m
  let Nv := ∑ j : Fin 3, sobolevNormSqOn m univ
    (fun α => wordDeriv α (fun x => v x j))
  let Nu := ∑ i : Fin 3, sobolevNormSqOn m univ
    (fun α => wordDeriv α (fun x => u x i))
  let D := ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
    ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2
  let s : Finset ((Fin 3 × List (Fin 3)) × Fin 3) :=
    ((Finset.univ : Finset (Fin 3)) ×ˢ W) ×ˢ Finset.univ
  let F : ((Fin 3 × List (Fin 3)) × Fin 3) → Vec3 → ℝ :=
    fun q x => wordDeriv (q.1.2 ++ [q.2])
      (fun y => u y q.1.1) x
  let G : ((Fin 3 × List (Fin 3)) × Fin 3) → Vec3 → ℝ :=
    fun q x => wordDeriv q.1.2
      (fun y => v y q.2 * u y q.1.1) x
  obtain ⟨hGL2, hGbound⟩ := hTensor v u hv hu hvL2
    (fun i α hα => huL2 i α (by omega))
  have hFL2 (q : (Fin 3 × List (Fin 3)) × Fin 3) (hq : q ∈ s) :
      MemLp (F q) 2 volume := by
    rcases Finset.mem_product.mp hq with ⟨hq1, _⟩
    have hα : q.1.2 ∈ W := (Finset.mem_product.mp hq1).2
    have hlen := mem_sobolevWords.mp hα
    exact huL2 q.1.1 (q.1.2 ++ [q.2]) (by simp; omega)
  have hGL2 (q : (Fin 3 × List (Fin 3)) × Fin 3) (hq : q ∈ s) :
      MemLp (G q) 2 volume := by
    rcases Finset.mem_product.mp hq with ⟨hq1, _⟩
    have hα : q.1.2 ∈ W := (Finset.mem_product.mp hq1).2
    exact hGL2 q.1.1 q.2 q.1.2 (mem_sobolevWords.mp hα)
  have hpair := lps_finset_integral_pairing_le s F G hFL2 hGL2
  have hpairEq : (∑ q ∈ s, ∫ x, F q x * G q x) =
      ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
        ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x *
          wordDeriv α (fun y => v y j * u y i) x := by
    simp only [s, F, G]
    rw [Finset.sum_product, Finset.sum_product]
  have hFEq : (∑ q ∈ s, ∫ x, F q x ^ 2) = D := by
    simp only [s, F, D]
    rw [Finset.sum_product, Finset.sum_product]
  have hGEq : (∑ q ∈ s, ∫ x, G q x ^ 2) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        sobolevNormSqOn m univ
          (fun α => wordDeriv α (fun x => v x j * u x i)) := by
    simp only [s, G, sobolevNormSqOn, Measure.restrict_univ]
    rw [Finset.sum_product, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  have hGle : (∑ q ∈ s, ∫ x, G q x ^ 2) ≤ C * Nv * Nu := by
    rw [hGEq]
    exact hGbound
  change (∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
    ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x *
      wordDeriv α (fun y => v y j * u y i) x) ≤
        Real.sqrt D * Real.sqrt (C * Nv * Nu)
  calc
    _ = ∑ q ∈ s, ∫ x, F q x * G q x := hpairEq.symm
    _ ≤ Real.sqrt (∑ q ∈ s, ∫ x, F q x ^ 2) *
          Real.sqrt (∑ q ∈ s, ∫ x, G q x ^ 2) := hpair
    _ ≤ Real.sqrt D * Real.sqrt (C * Nv * Nu) := by
      rw [hFEq]
      gcongr

/-- Contracting the transport velocity in `H^m` turns the tensor estimate
into the quadratic coefficient of the corrected energy inequality
(`eq:lps-Hm-energy`). -/
theorem lps_ordered_transport_pairing_contractive (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v u : Vec3 → Vec3),
      (∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j)) →
      (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) →
      (∀ (j : Fin 3) (α : List (Fin 3)), α.length ≤ m →
        MemLp (wordDeriv α (fun x => v x j)) 2 volume) →
      (∀ (i : Fin 3) (α : List (Fin 3)), α.length ≤ m + 1 →
        MemLp (wordDeriv α (fun x => u x i)) 2 volume) →
      let W := sobolevWords m
      let Nv := ∑ j : Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => v x j))
      let Nu := ∑ i : Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => u x i))
      let D := ∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
        ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x ^ 2
      Nv ≤ Nu →
      (∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
        ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x *
          wordDeriv α (fun y => v y j * u y i) x) ≤
        Real.sqrt C * Nu * Real.sqrt D := by
  obtain ⟨C, hC, hbound⟩ := lps_ordered_transport_pairing_bound m hm
  refine ⟨C, hC, ?_⟩
  intro v u hv hu hvL2 huL2 W Nv Nu D hNvNu
  have hNu : 0 ≤ Nu := by
    dsimp [Nu, sobolevNormSqOn]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro α _
    exact integral_nonneg (fun x => sq_nonneg _)
  have hprod : C * Nv * Nu ≤ C * Nu * Nu := by
    gcongr
  have hsqrt : Real.sqrt (C * Nv * Nu) ≤ Real.sqrt C * Nu := by
    calc
      Real.sqrt (C * Nv * Nu) ≤ Real.sqrt (C * Nu * Nu) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt C * Nu := by
        rw [show C * Nu * Nu = C * Nu ^ 2 by ring, Real.sqrt_mul hC,
          Real.sqrt_sq_eq_abs, abs_of_nonneg hNu]
  have hraw := hbound v u hv hu hvL2 huL2
  change (∑ i : Fin 3, ∑ α ∈ W, ∑ j : Fin 3,
    ∫ x, wordDeriv (α ++ [j]) (fun y => u y i) x *
      wordDeriv α (fun y => v y j * u y i) x) ≤
        Real.sqrt C * Nu * Real.sqrt D
  calc
    _ ≤ Real.sqrt D * Real.sqrt (C * Nv * Nu) := hraw
    _ ≤ Real.sqrt D * (Real.sqrt C * Nu) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
    _ = Real.sqrt C * Nu * Real.sqrt D := by ring

end ESS
