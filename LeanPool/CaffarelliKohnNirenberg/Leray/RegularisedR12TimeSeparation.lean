/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Pointwise separation for regularized time identities

Smooth compactly supported spatial tests determine a continuous vector field
on every interior time slice. The same fact recovers pointwise time increments
from their spatial pairings.
-/

public section

open MeasureTheory Set
open scoped Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

private theorem regularisedR12TimeSeparation_slice_continuous
    {T : ℝ} {F : Vec3 × ℝ → Vec3}
    (hF : ContinuousOn F (Set.univ ×ˢ Set.Ioo 0 T))
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
    Continuous (fun x : Vec3 => F (x, t)) := by
  rw [← continuousOn_univ]
  apply hF.comp (continuous_id.prodMk continuous_const).continuousOn
  intro x hx
  exact ⟨Set.mem_univ _, ht⟩

private theorem regularisedR12TimeSeparation_clampedIntegral_continuous
    {T t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Ioo 0 T)
    (ht₂ : t₂ ∈ Set.Ioo 0 T) (ht₁₂ : t₁ < t₂)
    {G : Vec3 × ℝ → Vec3}
    (hG : ContinuousOn G (Set.univ ×ˢ Set.Ioo 0 T)) :
    Continuous (fun x : Vec3 => ∫ s in Set.Icc t₁ t₂,
      G (x, min t₂ (max t₁ s)) ∂(volume : Measure ℝ)) := by
  let c : ℝ → ℝ := fun s => min t₂ (max t₁ s)
  have hccont : Continuous c := continuous_const.min (continuous_const.max continuous_id)
  have hcIcc (s : ℝ) : c s ∈ Set.Icc t₁ t₂ := by
    dsimp [c]
    exact ⟨le_min ht₁₂.le (le_max_left _ _), min_le_left _ _⟩
  have hcIoo (s : ℝ) : c s ∈ Set.Ioo 0 T := by
    have h := hcIcc s
    exact ⟨lt_of_lt_of_le ht₁.1 h.1, lt_of_le_of_lt h.2 ht₂.2⟩
  have hmap : Continuous (fun z : Vec3 × ℝ => (z.1, c z.2)) := by
    exact continuous_fst.prodMk (hccont.comp continuous_snd)
  have hGc : Continuous (fun z : Vec3 × ℝ => G (z.1, c z.2)) := by
    rw [← continuousOn_univ]
    apply hG.comp hmap.continuousOn
    intro z hz
    exact ⟨Set.mem_univ _, hcIoo z.2⟩
  let Q : Vec3 → ℝ → Vec3 := fun x s => G (x, c s)
  have hQ : Continuous Q.uncurry := by
    change Continuous (fun z : Vec3 × ℝ => G (z.1, c z.2))
    exact hGc
  exact continuous_parametric_integral_of_continuous hQ isCompact_Icc

/-- A continuous vector field on a positive-time slab vanishes if all its
spatial pairings with smooth compactly supported vector tests vanish. -/
theorem regularisedR12TimeSeparation_eq_zero_of_tests
    (T : ℝ) {F : Vec3 × ℝ → Vec3}
    (hFcont : ContinuousOn F (Set.univ ×ˢ Set.Ioo 0 T))
    (hzero : ∀ η : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η → ∀ t : ℝ, t ∈ Set.Ioo 0 T →
      ∫ x : Vec3, ∑ i : Fin 3, F (x, t) i * η x i = 0) :
    ∀ z : Vec3 × ℝ,
      z ∈ Set.univ ×ˢ Set.Ioo 0 T → F z = 0 := by
  intro z hz
  have hslice : Continuous (fun x : Vec3 => F (x, z.2)) :=
    regularisedR12TimeSeparation_slice_continuous hFcont z.2 hz.2
  have hcoord (i : Fin 3) : F z i = 0 := by
    let f : Vec3 → ℝ := fun x => F (x, z.2) i
    have hf : Continuous f := by
      exact (continuous_apply i).comp hslice
    have hloc : LocallyIntegrableOn f Set.univ (volume : Measure Vec3) :=
      hf.continuousOn.locallyIntegrableOn MeasurableSet.univ
    have hae : ∀ᵐ x : Vec3 ∂(volume : Measure Vec3), x ∈ Set.univ → f x = 0 := by
      apply isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
      intro ψ hψ hψc hψs
      let η : Vec3 → Vec3 := fun x => ψ x • (Pi.single i (1 : ℝ) : Vec3)
      have hη : ContDiff ℝ (⊤ : ℕ∞) η := by
        exact hψ.smul contDiff_const
      have hηc : HasCompactSupport η := by
        exact hψc.smul_right
      have hpair := hzero η hη hηc z.2 hz.2
      have hscalar : ∫ x : Vec3, ψ x * f x = 0 := by
        calc
          ∫ x : Vec3, ψ x * f x =
              ∫ x : Vec3, ∑ j : Fin 3, F (x, z.2) j * η x j := by
            apply integral_congr_ae
            filter_upwards with x
            simp [f, η, Pi.single_apply, smul_eq_mul, mul_comm]
          _ = 0 := hpair
      simpa [smul_eq_mul] using hscalar
    have hae' : ∀ᵐ x : Vec3 ∂(volume : Measure Vec3), f x = 0 := by
      filter_upwards [hae] with x hx
      exact hx (Set.mem_univ x)
    have haeAll : ∀ᵐ x : Vec3 ∂(volume : Measure Vec3),
        x ∈ Set.univ → f x = 0 := by
      filter_upwards [hae'] with x hx
      exact fun _ => hx
    have haeRestr : f =ᵐ[(volume : Measure Vec3).restrict Set.univ] 0 := by
      have h := (ae_restrict_iff'
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set Vec3))).2 haeAll
      filter_upwards [h] with x hx
      exact hx
    have hEqOn := Measure.eqOn_open_of_ae_eq haeRestr isOpen_univ
      hf.continuousOn continuousOn_const
    exact hEqOn (Set.mem_univ z.1)
  ext i
  exact hcoord i

/-- A pointwise interval increment follows from its spatial test pairings. -/
theorem regularisedR12TimeSeparation_eq_zero_of_interval_tests
    (T : ℝ) {u G : Vec3 × ℝ → Vec3}
    (hu : ContinuousOn u (Set.univ ×ˢ Set.Ioo 0 T))
    (hG : ContinuousOn G (Set.univ ×ˢ Set.Ioo 0 T))
    (hzero : ∀ η : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η → ∀ t₁ t₂ : ℝ, t₁ < t₂ →
      t₁ ∈ Set.Ioo 0 T → t₂ ∈ Set.Ioo 0 T →
      ∫ x : Vec3, ∑ i : Fin 3,
        (u (x, t₂) i - u (x, t₁) i -
          (∫ s in t₁..t₂, G (x, s)) i) * η x i = 0) :
    ∀ x : Vec3, ∀ t₁ t₂ : ℝ, t₁ < t₂ →
      t₁ ∈ Set.Ioo 0 T → t₂ ∈ Set.Ioo 0 T →
      u (x, t₂) - u (x, t₁) = ∫ s in t₁..t₂, G (x, s) := by
  intro x t₁ t₂ ht₁₂ ht₁ ht₂
  let Q : Vec3 → ℝ → Vec3 := fun y s => G (y, min t₂ (max t₁ s))
  have hQint : Continuous (fun y : Vec3 => ∫ s in Set.Icc t₁ t₂,
      Q y s ∂(volume : Measure ℝ)) :=
    regularisedR12TimeSeparation_clampedIntegral_continuous ht₁ ht₂ ht₁₂ hG
  have hclamp (s : ℝ) (hs : s ∈ Set.Icc t₁ t₂) :
      min t₂ (max t₁ s) = s := by
    simp [hs.1, hs.2]
  have hIntEq (y : Vec3) :
      (∫ s in Set.Icc t₁ t₂, Q y s ∂(volume : Measure ℝ)) =
        ∫ s in t₁..t₂, G (y, s) := by
    calc
      (∫ s in Set.Icc t₁ t₂, Q y s ∂(volume : Measure ℝ)) =
          ∫ s in Set.Icc t₁ t₂, G (y, s) ∂(volume : Measure ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        simp [Q, hclamp s hs]
      _ = ∫ s in Set.Ioc t₁ t₂, G (y, s) ∂(volume : Measure ℝ) :=
        integral_Icc_eq_integral_Ioc
      _ = ∫ s in t₁..t₂, G (y, s) := by
        rw [← intervalIntegral.integral_of_le ht₁₂.le]
  have hGInt : Continuous (fun y : Vec3 => ∫ s in t₁..t₂, G (y, s)) :=
    hQint.congr fun y => hIntEq y
  have hu₁ : Continuous (fun y : Vec3 => u (y, t₁)) :=
    regularisedR12TimeSeparation_slice_continuous hu t₁ ht₁
  have hu₂ : Continuous (fun y : Vec3 => u (y, t₂)) :=
    regularisedR12TimeSeparation_slice_continuous hu t₂ ht₂
  let R : Vec3 → Vec3 := fun y => u (y, t₂) - u (y, t₁) -
    (∫ s in t₁..t₂, G (y, s))
  have hR : Continuous R := by
    exact hu₂.sub hu₁ |>.sub hGInt
  let F : Vec3 × ℝ → Vec3 := fun z => R z.1
  have hFcont : ContinuousOn F (Set.univ ×ˢ Set.Ioo 0 T) := by
    exact (hR.comp continuous_fst).continuousOn
  have hFzero : ∀ η : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) η →
      HasCompactSupport η → ∀ t : ℝ, t ∈ Set.Ioo 0 T →
      ∫ y : Vec3, ∑ i : Fin 3, F (y, t) i * η y i = 0 := by
    intro η hη hηc t ht
    simpa [F, R] using hzero η hη hηc t₁ t₂ ht₁₂ ht₁ ht₂
  have hRzero := regularisedR12TimeSeparation_eq_zero_of_tests
    T hFcont hFzero (x, t₁) ⟨Set.mem_univ _, ht₁⟩
  exact sub_eq_zero.mp hRzero

end CKN.Leray

end
