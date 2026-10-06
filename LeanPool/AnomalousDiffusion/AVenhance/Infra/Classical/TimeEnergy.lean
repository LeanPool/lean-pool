/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.PeriodicTimeEnergy

/-! Spatial difference identities for classical periodic solutions. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open AVenhance.Infra.Torus
open scoped Topology

namespace AVenhance.Infra.Classical

theorem smooth_spaceGrad_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceGrad (fun x => f x - g x) =
      fun x => AVenhance.spaceGrad f x - AVenhance.spaceGrad g x := by
  funext x i
  change fderiv ℝ (fun y => f y - g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem smooth_spaceLap_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceLap (fun x => f x - g x) =
      fun x => AVenhance.spaceLap f x - AVenhance.spaceLap g x := by
  funext x
  simp only [AVenhance.spaceLap]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y (Homogenization.basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hgi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad g y i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ g y (Homogenization.basisVec i))
    exact (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have hinner : (fun y => AVenhance.spaceGrad (fun z => f z - g z) y i) =
      (fun y => AVenhance.spaceGrad f y i - AVenhance.spaceGrad g y i) := by
    funext y
    exact congrFun (congrFun (smooth_spaceGrad_sub hf hg) y) i
  rw [hinner]
  change fderiv ℝ (fun y => AVenhance.spaceGrad f y i - AVenhance.spaceGrad g y i)
      x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hfi.differentiable (by simp) x) (hgi.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem continuous_integrableOn_unitCellAt {f : Vec 2 → ℝ} (a : Vec 2)
    (hf : Continuous f) : IntegrableOn f (AVenhance.Infra.Torus.unitCellAt 2 a) := by
  let closedCell : Set (Vec 2) := Set.pi Set.univ (fun i : Fin 2 => Set.Icc (a i) (a i + 1))
  have hclosed : IsCompact closedCell := by
    simpa [closedCell] using isCompact_univ_pi (fun i : Fin 2 => isCompact_Icc)
  have hsub : AVenhance.Infra.Torus.unitCellAt 2 a ⊆ closedCell := by
    intro x hx
    simp only [AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq] at hx
    simp only [closedCell, Set.mem_pi, mem_univ, forall_true_left]
    intro i
    exact ⟨le_of_lt (hx i).1, hx i |>.2⟩
  exact (hf.continuousOn.integrableOn_compact hclosed).mono_set hsub

end AVenhance.Infra.Classical

end
