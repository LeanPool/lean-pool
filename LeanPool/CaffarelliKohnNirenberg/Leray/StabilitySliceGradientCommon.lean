/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionCore
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Stability Slice Gradient Common

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Metric Filter Topology Set
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- A slice integration-by-parts identity known separately for each spatial
test function holds simultaneously for all tests outside one null set. -/
theorem stability_ae_slice_weak_partial_of_forall_test
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω)
    {u g : ParabolicPoint → ℝ} (j : Fin 3)
    (hloc : ∀ᵐ s ∂(volume.restrict I),
      LocallyIntegrableOn (fun x : Vec3 => u (x, s)) Ω volume ∧
      LocallyIntegrableOn (fun x : Vec3 => g (x, s)) Ω volume)
    (hslice : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∀ᵐ s ∂(volume.restrict I),
        ∫ x in Ω, (u (x, s) * (fderiv ℝ ψ x) (CKN.basisVec j) +
          g (x, s) * ψ x) ∂volume = 0) :
    ∀ᵐ s ∂(volume.restrict I),
      CKN.HasWeakPartialDerivOn Ω j (fun x => u (x, s))
        (fun x => g (x, s)) := by
  classical
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense Vec3
  let : Countable Q := hQcount.to_subtype
  have hfam : ∀ᵐ s ∂(volume.restrict I), ∀ q : Q × ℕ,
      closedBall (q.1 : Vec3) (CKN.sliceRadius q.2) ⊆ Ω →
      ∫ x in Ω,
        (u (x, s) *
            (fderiv ℝ (fun z : Vec3 => CKN.mollifier
              (CKN.sliceRadius q.2) (CKN.sliceRadius_pos q.2)
              (z - (q.1 : Vec3))) x) (CKN.basisVec j) +
          g (x, s) * CKN.mollifier
            (CKN.sliceRadius q.2) (CKN.sliceRadius_pos q.2)
              (x - (q.1 : Vec3))) ∂volume = 0 := by
    rw [ae_all_iff]
    rintro ⟨y, n⟩
    by_cases hb : closedBall (y : Vec3) (CKN.sliceRadius n) ⊆ Ω
    · have hts : tsupport (fun z : Vec3 =>
          CKN.mollifier (CKN.sliceRadius n) (CKN.sliceRadius_pos n)
            (z - (y : Vec3))) ⊆ Ω := by
        rw [CKN.tsupport_mollifier_sub_eq]
        exact hb
      filter_upwards [hslice _ (CKN.contDiff_mollifier_sub
        (CKN.sliceRadius_pos n) (y : Vec3))
        (CKN.hasCompactSupport_mollifier_sub (CKN.sliceRadius_pos n)
          (y : Vec3)) hts] with s hs _
      exact hs
    · filter_upwards with s hcon
      exact absurd hcon hb
  filter_upwards [hfam, hloc] with s hs hsloc
  intro ψ hψ hψc hψΩ
  let κ : ℕ → Bool → Vec3 → ℝ := fun n b z =>
    if b then CKN.mollifier (CKN.sliceRadius n) (CKN.sliceRadius_pos n) z
    else (fderiv ℝ (CKN.mollifier (CKN.sliceRadius n)
      (CKN.sliceRadius_pos n)) z) (CKN.basisVec j)
  let F : Vec3 → Bool → ℝ := fun x b => if b then g (x, s) else u (x, s)
  let T : Bool → Vec3 → ℝ := fun b x =>
    if b then ψ x else (fderiv ℝ ψ x) (CKN.basisVec j)
  have hsum : ∫ x in Ω, ∑ b : Bool, F x b * T b x ∂volume = 0 := by
    refine CKN.slice_pairing_zero_of_mollifier_family hΩ hQdense
      (g := F) (κ := κ) (T := T) ?_ ?_ ?_
      hψ.continuous hψc hψΩ ?_ ?_ ?_ ?_
    · intro b
      cases b
      · simpa [F] using hsloc.1
      · simpa [F] using hsloc.2
    · intro n b
      cases b
      · simpa [κ] using CKN.continuous_fderiv_mollifier_apply
          (CKN.sliceRadius_pos n) j
      · simpa [κ] using (CKN.mollifier_contDiff (n := 0)
          (CKN.sliceRadius_pos n)).continuous
    · intro n b z hz
      cases b
      · simpa [κ] using CKN.fderiv_mollifier_apply_eq_zero
          (CKN.sliceRadius_pos n) hz j
      · simpa [κ] using CKN.mollifier_eq_zero_of_lt_norm
          (CKN.sliceRadius_pos n) hz
    · intro b
      cases b
      · simpa [T] using (hψ.continuous_fderiv (by simp)).clm_apply
          continuous_const
      · simpa [T] using hψ.continuous
    · intro b x hx
      cases b
      · simp only [T, Bool.false_eq_true, ↓reduceIte]
        rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
        simp
      · simpa [T] using image_eq_zero_of_notMem_tsupport hx
    · intro n b x
      cases b
      · simpa [κ, T] using CKN.integral_mul_fderiv_mollifier_sub
          hψ j (CKN.sliceRadius_pos n) x
      · simpa [κ, T] using CKN.integral_mul_mollifier_sub ψ
          (CKN.sliceRadius_pos n) x
    · intro y hy n hn
      have h := hs (⟨y, hy⟩, n) hn
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [F, κ, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
      rw [CKN.fderiv_mollifier_sub_apply (CKN.sliceRadius_pos n)]
      ring
  have hsum' : ∫ x in Ω, u (x, s) * (fderiv ℝ ψ x) (CKN.basisVec j) +
      g (x, s) * ψ x ∂volume = 0 := by
    simpa [F, T, Fintype.sum_bool, add_comm] using hsum
  have hmul (f t : Vec3 → ℝ) (hf : LocallyIntegrableOn f Ω volume)
      (ht : Continuous t) (htc : HasCompactSupport t)
      (htΩ : tsupport t ⊆ Ω) :
      IntegrableOn (fun x => f x * t x) Ω volume := by
    have hm := hf.mul_continuousOn ht.continuousOn hΩ.isLocallyClosed
    have hk := hm.integrableOn_compact_subset htΩ htc.isCompact
    have hg := hk.integrable_of_forall_notMem_eq_zero (by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])
    exact hg.integrableOn
  have hd : Continuous (fun x => (fderiv ℝ ψ x) (CKN.basisVec j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun x => (fderiv ℝ ψ x) (CKN.basisVec j)) :=
    hψc.mono' (subset_closure.trans
      (tsupport_fderiv_apply_subset ℝ (CKN.basisVec j)))
  have hdΩ : tsupport (fun x => (fderiv ℝ ψ x) (CKN.basisVec j)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (CKN.basisVec j)).trans hψΩ
  have huInt : IntegrableOn (fun x : Vec3 =>
      u (x, s) * (fderiv ℝ ψ x) (CKN.basisVec j)) Ω volume :=
    hmul _ _ hsloc.1 hd hdc hdΩ
  have hgInt : IntegrableOn (fun x : Vec3 => g (x, s) * ψ x) Ω volume :=
    hmul _ _ hsloc.2 hψ.continuous hψc hψΩ
  rw [integral_add huInt hgInt] at hsum'
  exact eq_neg_of_add_eq_zero_left hsum'

end CKN
