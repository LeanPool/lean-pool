/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupCompactnessBoundary
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Mathlib.MeasureTheory.Function.UniformIntegrable

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS


/-- Local strong `L²` convergence below time zero and a uniform
`L^(10/3)` bound imply strong `L³` convergence on a bounded cylinder with
open top. This is the boundary-strip step of `prop:blowup-limit`. -/
theorem blowup_strong_Lthree_to_time_zero
    (A : Set Vec3) (hA : MeasurableSet A) (hAfin : volume A < ⊤)
    (a : ℝ)
    (f : ℕ → Vec3 × ℝ → Vec3) (g : Vec3 × ℝ → Vec3)
    (hf : ∀ k, MemLp (f k) (10 / 3 : ℝ≥0∞)
      ((volume.prod volume).restrict (A ×ˢ Ioo a 0)))
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ k, eLpNorm (f k) (10 / 3 : ℝ≥0∞)
        ((volume.prod volume).restrict (A ×ˢ Ioo a 0)) ≤ B)
    (hlocal : ∀ b : ℝ, b < 0 →
      Tendsto (fun k => eLpNorm (fun z => f k z - g z) 2
        ((volume.prod volume).restrict (A ×ˢ Ioo a b)))
        atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (fun z => f k z - g z) 3
      ((volume.prod volume).restrict (A ×ˢ Ioo a 0)))
      atTop (nhds 0) := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume.prod volume).restrict (A ×ˢ Ioo a 0)
  have : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    change (volume.prod volume : Measure (Vec3 × ℝ))
      (A ×ˢ Ioo a 0) ≠ ⊤
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top hAfin (by simp : volume (Ioo a 0) < ⊤)).ne
  have hmeasure : TendstoInMeasure μ f atTop g :=
    blowup_tendstoInMeasure_to_time_zero_of_local_Ltwo
      A hA hAfin a f g hlocal
  obtain ⟨B, hB, hBbound⟩ := hbound
  have hGbound : eLpNorm g (10 / 3 : ℝ≥0∞) μ ≤ B :=
    eLpNorm_le_of_tendstoInMeasure
      (Filter.Eventually.of_forall hBbound) hmeasure
      (fun k => (hf k).aestronglyMeasurable)
  have hGhigh : MemLp g (10 / 3 : ℝ≥0∞) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hGbound hB
  have hpr : (3 : ℝ≥0∞) ≤ 10 / 3 := by
    apply (ENNReal.le_div_iff_mul_le (a := 3) (b := 3) (c := 10)
      (by norm_num) (by norm_num)).2
    norm_num
  have hG : MemLp g 3 μ :=
    hGhigh.mono_exponent hpr
  have hF : ∀ k, MemLp (f k) 3 μ := fun k =>
    (hf k).mono_exponent hpr
  have hUi : UnifIntegrable f 3 μ := by
    rw [unifIntegrable_iff]
    intro ε hε
    have hsmall : Tendsto (fun δ : ℝ≥0∞ => B * δ ^ (1 / 30 : ℝ))
        (nhds 0) (nhds 0) :=
      ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hB.ne (by norm_num)
    have hev : ∀ᶠ δ in nhds (0 : ℝ≥0∞),
        B * δ ^ (1 / 30 : ℝ) ≤ ε :=
      (ENNReal.tendsto_nhds_zero.mp hsmall) ε hε
    obtain ⟨δ, hδpos, hδsmall⟩ :=
      ENNReal.nhds_zero_basis_Iic.eventually_iff.mp hev
    refine ⟨δ, hδpos, fun k s hs => ?_⟩
    have hrestrict : (μ.restrict s) Set.univ = μ s :=
      Measure.restrict_apply_univ (μ := μ) (s := s)
    calc
      eLpNorm (f k) 3 (μ.restrict s) ≤
          eLpNorm (f k) (10 / 3 : ℝ≥0∞) (μ.restrict s) *
            (μ.restrict s Set.univ) ^ (1 / 30 : ℝ) := by
        convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
          (μ := μ.restrict s) (f := f k)
          (p := (3 : ℝ≥0∞)) (q := (10 / 3 : ℝ≥0∞))
          hpr (by norm_num) using 1
        norm_num
      _ ≤ B * (μ s) ^ (1 / 30 : ℝ) := by
        rw [hrestrict]
        gcongr
        exact (eLpNorm_mono_measure (f k) Measure.restrict_le_self).trans
          (hBbound k)
      _ ≤ ε := hδsmall hs
  exact (tendstoInMeasure_iff_tendsto_Lp_finite
    (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    (by finiteness : (3 : ℝ≥0∞) ≠ ⊤) hF hG).mp ⟨hmeasure, hUi⟩

/-- The same strong-convergence upgrade applies when the common high-exponent
bound starts only after a finite index. -/
theorem blowup_strong_Lthree_to_time_zero_eventually
    (A : Set Vec3) (hA : MeasurableSet A) (hAfin : volume A < ⊤)
    (a : ℝ)
    (f : ℕ → Vec3 × ℝ → Vec3) (g : Vec3 × ℝ → Vec3)
    (hhigh : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ k in atTop,
      MemLp (f k) (10 / 3 : ℝ≥0∞)
        ((volume.prod volume).restrict (A ×ˢ Ioo a 0)) ∧
      eLpNorm (f k) (10 / 3 : ℝ≥0∞)
        ((volume.prod volume).restrict (A ×ˢ Ioo a 0)) ≤ B)
    (hlocal : ∀ b : ℝ, b < 0 →
      Tendsto (fun k => eLpNorm (fun z => f k z - g z) 2
        ((volume.prod volume).restrict (A ×ˢ Ioo a b)))
        atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (fun z => f k z - g z) 3
      ((volume.prod volume).restrict (A ×ˢ Ioo a 0)))
      atTop (nhds 0) := by
  obtain ⟨B, hB, hBev⟩ := hhigh
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hBev
  let f' : ℕ → Vec3 × ℝ → Vec3 := fun n => f (n + K)
  have hhigh' (n : ℕ) :
      MemLp (f' n) (10 / 3 : ℝ≥0∞)
        ((volume.prod volume).restrict (A ×ˢ Ioo a 0)) ∧
      eLpNorm (f' n) (10 / 3 : ℝ≥0∞)
        ((volume.prod volume).restrict (A ×ˢ Ioo a 0)) ≤ B :=
    hK (n + K) (Nat.le_add_left K n)
  have hlocal' (b : ℝ) (hb : b < 0) :
      Tendsto (fun n => eLpNorm (fun z => f' n z - g z) 2
        ((volume.prod volume).restrict (A ×ˢ Ioo a b)))
        atTop (nhds 0) :=
    (hlocal b hb).comp (tendsto_add_atTop_nat K)
  have hconv := blowup_strong_Lthree_to_time_zero
    A hA hAfin a f' g (fun n => (hhigh' n).1)
    ⟨B, hB, fun n => (hhigh' n).2⟩ hlocal'
  exact (tendsto_add_atTop_iff_nat K).1 hconv

/-- The open-top `L³` upgrade stated with the parabolic volume used by the
rescaled Navier–Stokes fields. -/
theorem blowup_strong_Lthree_to_time_zero_parabolic
    (A : Set Vec3) (hA : MeasurableSet A) (hAfin : volume A < ⊤)
    (a : ℝ)
    (f : ℕ → ParabolicPoint → Vec3) (g : ParabolicPoint → Vec3)
    (hhigh : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ k in atTop,
      MemLp (f k) (10 / 3 : ℝ≥0∞)
        (volume.restrict (A ×ˢ Ioo a 0)) ∧
      eLpNorm (f k) (10 / 3 : ℝ≥0∞)
        (volume.restrict (A ×ˢ Ioo a 0)) ≤ B)
    (hlocal : ∀ b : ℝ, b < 0 →
      Tendsto (fun k => eLpNorm (fun z => f k z - g z) 2
        (volume.restrict (A ×ˢ Ioo a b))) atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm (fun z => f k z - g z) 3
      (volume.restrict (A ×ˢ Ioo a 0))) atTop (nhds 0) := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    at hhigh hlocal ⊢
  exact blowup_strong_Lthree_to_time_zero_eventually
    A hA hAfin a f g hhigh hlocal

end ESS
