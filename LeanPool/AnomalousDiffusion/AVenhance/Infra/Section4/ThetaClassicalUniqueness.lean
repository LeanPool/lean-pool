/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaTimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Uniqueness

/-! L² energy uniqueness for smooth periodic advection-diffusion solutions. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Torus
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaClassicalUniqueness.continuous_spaceGrad_component {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) := by
  exact AVenhance.Infra.Classical.Uniqueness.continuous_spaceGrad_component hf i

theorem ThetaClassicalUniqueness.continuous_spaceLap {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (AVenhance.spaceLap f) := by
  exact AVenhance.Infra.Classical.Uniqueness.continuous_spaceLap hf

theorem ThetaClassicalUniqueness.continuous_vecDot {f g : Vec 2 → Vec 2}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => Homogenization.vecDot (f x) (g x)) := by
  exact AVenhance.Infra.Classical.Uniqueness.continuous_vecDot hf hg

theorem ThetaClassicalUniqueness.theta_smooth_spaceGrad_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceGrad (fun x => f x - g x) =
      fun x => AVenhance.spaceGrad f x - AVenhance.spaceGrad g x := by
  exact AVenhance.Infra.Classical.smooth_spaceGrad_sub hf hg

theorem ThetaClassicalUniqueness.thetaSpaceGrad_contDiff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad f) := by
  apply contDiff_pi.2
  intro i
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem ThetaClassicalUniqueness.theta_smooth_spaceLap_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceLap (fun x => f x - g x) =
      fun x => AVenhance.spaceLap f x - AVenhance.spaceLap g x := by
  exact AVenhance.Infra.Classical.smooth_spaceLap_sub hf hg

theorem ThetaClassicalUniqueness.thetaTime_continuous_integrableOn_unitCellAt
    {f : Vec 2 → ℝ} (a : Vec 2) (hf : Continuous f) :
    IntegrableOn f (AVenhance.Infra.Torus.unitCellAt 2 a) := by
  exact AVenhance.Infra.Classical.continuous_integrableOn_unitCellAt a hf

theorem streamVel_classical_unique
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    {θ ψ : ℝ → Vec 2 → ℝ}
    (hθ : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ)
    (hψ : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ ψ) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Vec 2, ψ t x = θ t x := by
  exact AVenhance.Infra.Classical.streamVel_classical_unique φ hφ κ hκ F θ₀ hθ hψ

/-- A continuous periodic datum whose torus L² norm vanishes is pointwise
zero.  The shifted open cell lets periodicity move the integral away from
cell-boundary representatives. -/
theorem theta_continuous_periodic_eq_zero_of_l2NormSq_eq_zero
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : AVenhance.IsZ2Periodic f)
    (hzero : AVenhance.l2NormSq f = 0) : f = 0 := by
  funext x
  let a : Vec 2 := fun i => x i - (1 / 2 : ℝ)
  let U : Set (Vec 2) := Set.pi Set.univ (fun i => Set.Ioo (a i) (a i + 1))
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_set_pi Set.finite_univ (fun i hi => isOpen_Ioo)
  have hxU : x ∈ U := by
    intro i hi
    dsimp [a]
    constructor <;> linarith
  have hUsub : U ⊆ AVenhance.Infra.Torus.unitCellAt 2 a := by
    intro y hy i
    have hi := hy i (mem_univ i)
    exact ⟨hi.1, le_of_lt hi.2⟩
  let sqf : Vec 2 → ℝ := fun y => f y ^ 2
  have hsqper : AVenhance.IsZ2Periodic sqf := by
    intro k y
    simp [sqf, hper k y]
  have hsqper' : AVenhance.Infra.Torus.IsZdPeriodic sqf :=
    (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen sqf).2 hsqper
  have hsqInt : IntegrableOn sqf (AVenhance.Infra.Torus.unitCellAt 2 a) := by
    apply ThetaClassicalUniqueness.thetaTime_continuous_integrableOn_unitCellAt a
    exact hf.continuous.pow 2
  have hcell :
      (∫ y in AVenhance.Infra.Torus.unitCellAt 2 a, sqf y) = 0 := by
    calc
      _ = ∫ y in AVenhance.Infra.Torus.unitCell 2, sqf y :=
        AVenhance.Infra.Torus.integral_periodic_unitCellAt_eq hsqper' a
      _ = ∫ y in AVenhance.unitCube, sqf y :=
        AVenhance.Infra.Torus.integral_unitCell_eq_unitCube sqf
      _ = AVenhance.l2NormSq f := rfl
      _ = 0 := hzero
  have hnonneg : ∀ y, 0 ≤ sqf y := fun y => sq_nonneg _
  have haeSq : sqf =ᵐ[volume.restrict
      (AVenhance.Infra.Torus.unitCellAt 2 a)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hsqInt).mp hcell
  have hae : f =ᵐ[volume.restrict
      (AVenhance.Infra.Torus.unitCellAt 2 a)] 0 := by
    filter_upwards [haeSq] with y hy
    exact (sq_eq_zero_iff.mp (by simpa [sqf] using hy))
  have haeU : f =ᵐ[volume.restrict U] 0 :=
    ae_restrict_of_ae_restrict_of_subset hUsub hae
  have heqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq haeU hUopen
    hf.continuous.continuousOn continuousOn_const
  exact heqOn hxU

end AVenhance.Infra.Section4

end
