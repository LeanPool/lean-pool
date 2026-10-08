/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointRep

/-!
# Joint continuity of the smooth slice representatives

`lem:lps-Bochner-joint-smooth`: if the slices of a space-time field form
`L²`-continuous curves of all-order Sobolev families, the smooth slice
representatives depend continuously on time uniformly in space, together with
every ordered derivative.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The `H^{k+2}` norm squared of the difference of two slice families tends to zero
with the time difference, given `L²` continuity of every slot
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_sobolevNormSq_curve_tendsto {a b : ℝ} {Z : ℝ → List (Fin 3) → Vec3 → ℝ}
    (hfam : ∀ t ∈ Icc a b, ∀ m : ℕ, IsSobolevFamilyOn m univ (Z t []) (Z t))
    (hcont : ∀ (α : List (Fin 3)), ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z s α - Z t α) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    Tendsto (fun s => sobolevNormSqOn (k + 2) univ (fun β y => Z t β y - Z s β y))
      (𝓝[Icc a b] t) (𝓝 0) := by
  have hmem : ∀ s ∈ Icc a b, ∀ β : List (Fin 3), β.length ≤ k + 2 →
      MemLp (Z s β) 2 volume := by
    intro s hs β hβ
    simpa only [Measure.restrict_univ] using (hfam s hs (k + 2)).memL2 β hβ
  have hterm : ∀ β ∈ sobolevWords (k + 2),
      Tendsto (fun s => ∫ y, (Z t β y - Z s β y) ^ 2) (𝓝[Icc a b] t) (𝓝 0) := by
    intro β hβ
    have hβl := mem_sobolevWords.mp hβ
    have hreal : Tendsto (fun s => (eLpNorm (Z s β - Z t β) 2 volume).toReal)
        (𝓝[Icc a b] t) (𝓝 0) := by
      have h0 := hcont β t ht
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
      simpa only [Function.comp_def, ENNReal.toReal_zero] using this
    have hsq := hreal.pow 2
    rw [zero_pow (by norm_num)] at hsq
    refine hsq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hm : MemLp (fun y => Z t β y - Z s β y) 2 volume :=
      (hmem t ht β hβl).sub (hmem s hs β hβl)
    rw [vl_integral_sq_eq hm]
    have : (fun y => Z t β y - Z s β y) = -(Z s β - Z t β) := by
      funext y
      simp
    rw [this, eLpNorm_neg]
  have hsum := tendsto_finsetSum (sobolevWords (k + 2)) hterm
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with s
  unfold sobolevNormSqOn
  simp only [Measure.restrict_univ]

/-- The difference of two smooth slice representatives is controlled in every ordered
derivative by the Sobolev distance of the slices (`lem:lps-Bochner-joint-smooth`). -/
theorem lps_smooth_rep_diff_bound {f₁ f₂ g₁ g₂ : Vec3 → ℝ}
    {D₁ D₂ : List (Fin 3) → Vec3 → ℝ}
    (h₁ : ∀ m : ℕ, IsSobolevFamilyOn m univ f₁ D₁)
    (h₂ : ∀ m : ℕ, IsSobolevFamilyOn m univ f₂ D₂)
    (hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁) (hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂)
    (e₁ : g₁ =ᵐ[volume] f₁) (e₂ : g₂ =ᵐ[volume] f₂)
    (k : ℕ) (α : List (Fin 3)) (hα : α.length ≤ k) (x : Vec3) :
    |wordDeriv α g₁ x - wordDeriv α g₂ x| ≤
      lpsEmbC k * Real.sqrt (sobolevNormSqOn (k + 2) univ (fun β y => D₁ β y - D₂ β y)) := by
  have hfam : IsSobolevFamilyOn (k + 2) univ (fun y => f₁ y - f₂ y)
      (fun β y => D₁ β y - D₂ β y) := by
    have := (h₁ (k + 2)).add ((h₂ (k + 2)).const_mul (-1))
    refine this.congr_ae ?_ ?_
    · exact Eventually.of_forall fun y => by simp [sub_eq_add_neg]
    · intro β _
      exact Eventually.of_forall fun y => by simp [sub_eq_add_neg]
  obtain ⟨g, hgC, hgf, -, hgB⟩ :=
    (Classical.choose_spec (lps_sobolevFamily_contDiff_rep k)).2 _ _ hfam
  have hgeq : g = fun y => g₁ y - g₂ y := by
    refine lps_eq_of_continuous_ae_eq (hgC.continuous)
      ((hg₁.continuous).sub (hg₂.continuous)) ?_
    have hs : (fun y => g₁ y - g₂ y) =ᵐ[volume] fun y => f₁ y - f₂ y := by
      filter_upwards [e₁, e₂] with y hy1 hy2
      rw [hy1, hy2]
    have hgf' : g =ᵐ[volume] fun y => f₁ y - f₂ y := by
      simpa only [Measure.restrict_univ] using hgf
    exact hgf'.trans hs.symm
  have := hgB α hα x
  rw [hgeq, lps_wordDeriv_sub hg₁ hg₂] at this
  exact this

/-- Joint continuity in space and time of every ordered derivative of the smooth slice
representatives (`lem:lps-Bochner-joint-smooth`). -/
theorem lps_wordDeriv_rep_jointContinuousOn {a b : ℝ}
    {Z : ℝ → List (Fin 3) → Vec3 → ℝ} {B : ℝ → Vec3 → ℝ}
    (hfam : ∀ t ∈ Icc a b, ∀ m : ℕ, IsSobolevFamilyOn m univ (Z t []) (Z t))
    (hcont : ∀ (α : List (Fin 3)), ∀ t ∈ Icc a b,
      Tendsto (fun s => eLpNorm (Z s α - Z t α) 2 volume) (𝓝[Icc a b] t) (𝓝 0))
    (hBs : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (B t) ∧ B t =ᵐ[volume] Z t [])
    (α : List (Fin 3)) :
    ContinuousOn (fun z : Vec3 × ℝ => wordDeriv α (B z.2) z.1)
      ((univ : Set Vec3) ×ˢ Icc a b) := by
  intro z₀ hz₀
  obtain ⟨-, ht₀⟩ := hz₀
  let S : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Icc a b
  have hN := lps_sobolevNormSq_curve_tendsto hfam hcont α.length ht₀
  have hbase : Tendsto (fun z : Vec3 × ℝ => lpsEmbC α.length * Real.sqrt
      (sobolevNormSqOn (α.length + 2) univ (fun β y => Z z₀.2 β y - Z z.2 β y)))
      (𝓝[S] z₀) (𝓝 0) := by
    have hcomp : Tendsto (fun z : Vec3 × ℝ => z.2) (𝓝[S] z₀) (𝓝[Icc a b] z₀.2) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (continuous_snd.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz using hz.2
    have := ((hN.comp hcomp).sqrt).const_mul (lpsEmbC α.length)
    simpa using this
  have hdiff : Tendsto (fun z : Vec3 × ℝ =>
      wordDeriv α (B z.2) z.1 - wordDeriv α (B z₀.2) z.1) (𝓝[S] z₀) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbase
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzt : z.2 ∈ Icc a b := hz.2
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact lps_smooth_rep_diff_bound (hfam z₀.2 ht₀) (hfam z.2 hzt)
      (hBs z₀.2 ht₀).1 (hBs z.2 hzt).1 (hBs z₀.2 ht₀).2 (hBs z.2 hzt).2
      α.length α le_rfl z.1
  have hx : Tendsto (fun z : Vec3 × ℝ => wordDeriv α (B z₀.2) z.1) (𝓝[S] z₀)
      (𝓝 (wordDeriv α (B z₀.2) z₀.1)) := by
    have hc : Continuous (wordDeriv α (B z₀.2)) :=
      (contDiff_wordDeriv (hBs z₀.2 ht₀).1 α).continuous
    exact ((hc.continuousAt.tendsto).comp continuous_fst.continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have := hdiff.add hx
  simp only [zero_add, sub_add_cancel] at this
  exact this

end ESS
