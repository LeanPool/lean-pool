/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatCutoffKernels
public import LeanPool.CIVAxisymmetric.Closure.CutoffExistence
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.SpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Extending the cutoff-times-slice product by zero

For a window `B_bar(x, ρ) × [s - ρ², s]` compactly contained in an open set `O` on which `w` is
smooth, there is a globally smooth, compactly supported `ζ` agreeing with `serrinCutoff x s ρ · w`
for every `z` with `z.2 ≤ s`. The construction multiplies `w` by an auxiliary cutoff equal to `1`
on a slightly larger window, chosen (using a positive margin from the compactness of the window
inside the open `O`) small enough that its support still lies in `O`; since `serrinCutoff`
already vanishes off the window for `z.2 ≤ s`, the auxiliary cutoff's exact values elsewhere are
immaterial. This is the extension-by-zero step of the proof of `lem:aniso:annulus`.
-/

public section

open Set MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



private theorem eventuallyEq_zero_nhds_of_notMem_tsupport_spaceTime {κ : Vec3 × ℝ → ℝ} {z : Vec3
    × ℝ}
    (hz : z ∉ tsupport κ) : κ =ᶠ[nhds z] fun _ : Vec3 × ℝ => (0 : ℝ) := by
  filter_upwards [(isClosed_tsupport κ).isOpen_compl.mem_nhds hz] with y hy
  exact image_eq_zero_of_notMem_tsupport hy

/-- A smooth, compactly supported cutoff `κ` whose support lies in an open set `O` turns a
function `w` that is smooth only on `O` into a globally smooth, compactly supported product. -/
private theorem contDiff_mul_of_contDiffOn {κ w : Vec3 × ℝ → ℝ} {O : Set (Vec3 × ℝ)}
    (hO : IsOpen O) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκs : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ O) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w O) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => κ z * w z) ∧ HasCompactSupport (fun z => κ z * w z) := by
  refine ⟨?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport κ
    · exact hκ.contDiffAt.mul (hw.contDiffAt (hO.mem_nhds (hsupp hz)))
    · have heq : (fun y : Vec3 × ℝ => κ y * w y) =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [eventuallyEq_zero_nhds_of_notMem_tsupport_spaceTime hz] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · refine HasCompactSupport.intro hκs (fun z hz => ?_)
    simp [image_eq_zero_of_notMem_tsupport hz]

theorem HB2b_cutoff_extension {w : ParabolicPoint → ℝ} {O : Set ParabolicPoint} {x : Vec3}
    {s ρ : ℝ} (hO : IsOpen (X := Vec3 × ℝ) O) (hρ : 0 < ρ)
    (hwin : {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s ⊆ O)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z) O) :
    ∃ ζ : ParabolicPoint → ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ζ z) ∧
      HasCompactSupport (fun z : Vec3 × ℝ => ζ z) ∧
      ∀ z : ParabolicPoint, z.2 ≤ s → ζ z = serrinCutoff x s ρ z * w z := by
  set Wx : Set Vec3 := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} with hWxdef
  set Wt : Set ℝ := Icc (s - ρ ^ 2) s with hWtdef
  have hWxcompact : IsCompact Wx := by
    rw [hWxdef, ← closure_vec3Ball hρ]
    exact isCompact_closure_vec3Ball hρ
  have hWtcompact : IsCompact Wt := isCompact_Icc
  have hWcompact : IsCompact (Wx ×ˢ Wt) := hWxcompact.prod hWtcompact
  obtain ⟨δ, hδpos, hδsub⟩ := hWcompact.exists_thickening_subset_open hO hwin
  set Rspace : ℝ := ρ + δ / 2 with hRspacedef
  have hRspace : ρ < Rspace := by rw [hRspacedef]; linarith only [hδpos]
  have hRtimeSqPos : (0:ℝ) ≤ ρ ^ 2 + δ / 2 := by positivity
  set Rtime : ℝ := Real.sqrt (ρ ^ 2 + δ / 2) with hRtimedef
  have hRtimeSq : Rtime ^ 2 = ρ ^ 2 + δ / 2 := Real.sq_sqrt hRtimeSqPos
  have hRtime : ρ < Rtime := by
    rw [hRtimedef, Real.lt_sqrt hρ.le]
    linarith only [hδpos]
  set κ : Vec3 × ℝ → ℝ := fun z => CKN.canonicalBallCutoff x ρ Rspace z.1 *
      CKN.timeCutoff s ρ Rtime z.2 with hκdef
  have hκsmooth : ContDiff ℝ (⊤ : ℕ∞) κ := by
    rw [hκdef]
    exact (CKN.canonicalBallCutoff_smooth x hρ.le hRspace).comp contDiff_fst |>.mul
      ((CKN.timeCutoff_smooth hρ.le hRtime).comp contDiff_snd)
  have hRspacepos : 0 < Rspace := lt_trans hρ hRspace
  have hsub : Function.support κ ⊆
      (CKN.euclideanBall x Rspace) ×ˢ (Ioo (s - Rtime ^ 2) (s + (Rtime ^ 2 - ρ ^ 2))) := by
    intro z hz
    have hz' : CKN.canonicalBallCutoff x ρ Rspace z.1 ≠ 0 ∧
        CKN.timeCutoff s ρ Rtime z.2 ≠ 0 := by
      rw [hκdef] at hz
      exact mul_ne_zero_iff.mp hz
    exact ⟨CKN.canonicalBallCutoff_tsupport_subset_outer hρ.le hRspace (subset_tsupport _ hz'.1),
      CKN.timeCutoff_support_subset hρ.le hRtime hz'.2⟩
  have hboxeq : (CKN.euclideanBall x Rspace) ×ˢ (Ioo (s - Rtime ^ 2) (s + (Rtime ^ 2 - ρ ^ 2))) ⊆
      vec3Ball x Rspace ×ˢ Ioo (s - Rtime ^ 2) (s + (Rtime ^ 2 - ρ ^ 2)) := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hRspacepos]
  set WxOuter : Set Vec3 := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ Rspace} with hWxOuterdef
  set WtOuter : Set ℝ := Icc (s - Rtime ^ 2) (s + (Rtime ^ 2 - ρ ^ 2)) with hWtOuterdef
  have hκsuppSubset : tsupport κ ⊆ WxOuter ×ˢ WtOuter := by
    calc tsupport κ = closure (Function.support κ) := rfl
      _ ⊆ closure (vec3Ball x Rspace ×ˢ Ioo (s - Rtime ^ 2) (s + (Rtime ^ 2 - ρ ^ 2))) :=
          closure_mono (hsub.trans hboxeq)
      _ = closure (vec3Ball x Rspace) ×ˢ closure (Ioo (s - Rtime ^ 2) (s + (Rtime ^ 2 - ρ ^ 2))) :=
          closure_prod_eq
      _ ⊆ WxOuter ×ˢ WtOuter := by
          rw [closure_vec3Ball hRspacepos, hWxOuterdef, hWtOuterdef]
          exact Set.prod_mono (le_refl _) (closure_minimal Ioo_subset_Icc_self isClosed_Icc)
  have hboxCompact : IsCompact (WxOuter ×ˢ WtOuter) := by
    apply IsCompact.prod _ isCompact_Icc
    rw [hWxOuterdef, ← closure_vec3Ball hRspacepos]
    exact isCompact_closure_vec3Ball hRspacepos
  have hκcs : HasCompactSupport κ :=
    hboxCompact.of_isClosed_subset (isClosed_tsupport κ) hκsuppSubset
  have hxWx : x ∈ Wx := by
    rw [hWxdef, mem_ofPred_eq, sub_self]
    unfold vec3EuclideanNorm
    simpa using hρ.le
  have hsWt : s ∈ Wt := by
    rw [hWtdef, mem_Icc]
    exact ⟨by nlinarith only [sq_nonneg ρ], le_refl _⟩
  have hspaceStep : ∀ y : Vec3, y ∈ WxOuter →
      ∃ y₀ ∈ Wx, ‖y - y₀‖ ≤ δ / 2 := by
    intro y hy
    rw [hWxOuterdef, mem_ofPred_eq] at hy
    by_cases hcase : vec3EuclideanNorm (y - x) ≤ ρ
    · exact ⟨y, by rw [hWxdef, mem_ofPred_eq]; exact hcase, by simp; linarith only [hδpos]⟩
    · push Not at hcase
      have hnormpos : 0 < vec3EuclideanNorm (y - x) := lt_trans hρ hcase
      set c : ℝ := ρ / vec3EuclideanNorm (y - x) with hcdef
      have hcpos : 0 < c := by positivity
      have hcle1 : c ≤ 1 := by
        rw [hcdef, div_le_one hnormpos]; exact hcase.le
      refine ⟨x + c • (y - x), ?_, ?_⟩
      · rw [hWxdef, mem_ofPred_eq, show x + c • (y - x) - x = c • (y - x) by abel,
          vec3EuclideanNorm_smul, abs_of_pos hcpos, hcdef,
          div_mul_cancel₀ _ hnormpos.ne']
      · have hdiff : y - (x + c • (y - x)) = (1 - c) • (y - x) := by module
        calc ‖y - (x + c • (y - x))‖ ≤ vec3EuclideanNorm (y - (x + c • (y - x))) :=
              norm_le_vec3EuclideanNorm _
          _ = (1 - c) * vec3EuclideanNorm (y - x) := by
              rw [hdiff, vec3EuclideanNorm_smul, abs_of_nonneg (by linarith only [hcle1])]
          _ = vec3EuclideanNorm (y - x) - ρ := by
              rw [hcdef, sub_mul, one_mul, div_mul_cancel₀ _ hnormpos.ne']
          _ ≤ Rspace - ρ := by linarith only [hy]
          _ = δ / 2 := by rw [hRspacedef]; ring
  have htimeStep : ∀ t : ℝ, t ∈ WtOuter → ∃ t₀ ∈ Wt, |t - t₀| ≤ δ / 2 := by
    intro t ht
    rw [hWtOuterdef, mem_Icc] at ht
    by_cases hc1 : t < s - ρ ^ 2
    · refine ⟨s - ρ ^ 2, ?_, ?_⟩
      · rw [hWtdef, mem_Icc]; exact ⟨le_refl _, by nlinarith only [sq_nonneg ρ]⟩
      · rw [abs_of_neg (by linarith only [hc1])]
        nlinarith only [ht.1, hRtimeSq]
    · by_cases hc2 : s < t
      · refine ⟨s, ?_, ?_⟩
        · rw [hWtdef, mem_Icc]; exact ⟨by nlinarith only [sq_nonneg ρ], le_refl _⟩
        · rw [abs_of_pos (by linarith only [hc2])]
          nlinarith only [ht.2, hRtimeSq]
      · push Not at hc1 hc2
        exact ⟨t, by rw [hWtdef, mem_Icc]; exact ⟨hc1, hc2⟩, by simp; linarith only [hδpos]⟩
  have hκsupp : tsupport κ ⊆ O := by
    refine hκsuppSubset.trans (fun p hp => hδsub ?_)
    rw [Metric.mem_thickening_iff]
    obtain ⟨y, t⟩ := p
    obtain ⟨hy, ht⟩ := hp
    obtain ⟨y₀, hy₀mem, hy₀dist⟩ := hspaceStep y hy
    obtain ⟨t₀, ht₀mem, ht₀dist⟩ := htimeStep t ht
    refine ⟨(y₀, t₀), ⟨hy₀mem, ht₀mem⟩, ?_⟩
    rw [Prod.dist_eq]
    refine max_lt_iff.mpr ⟨?_, ?_⟩
    · calc dist y y₀ = ‖y - y₀‖ := dist_eq_norm _ _
        _ ≤ δ / 2 := hy₀dist
        _ < δ := by linarith only [hδpos]
    · calc dist t t₀ = |t - t₀| := Real.dist_eq _ _
        _ ≤ δ / 2 := ht₀dist
        _ < δ := by linarith only [hδpos]
  obtain ⟨hζ0smooth, hζ0cs⟩ :=
    contDiff_mul_of_contDiffOn hO hκsmooth hκcs hκsupp hw
  refine ⟨fun z => serrinCutoff x s ρ z * (κ z * w z), ?_, ?_, ?_⟩
  · exact (contDiff_serrinCutoff x hρ).mul hζ0smooth
  · exact hζ0cs.mul_left
  · intro z hz2
    by_cases hc1 : vec3EuclideanNorm (z.1 - x) < ρ
    · by_cases hc2 : s - ρ ^ 2 ≤ z.2
      · have hκ0 : κ z = CKN.canonicalBallCutoff x ρ Rspace z.1 *
            CKN.timeCutoff s ρ Rtime z.2 := rfl
        have hκ1 : κ z = 1 := by
          have h1 : CKN.canonicalBallCutoff x ρ Rspace z.1 = 1 := by
            apply CKN.canonicalBallCutoff_eq_one_on_inner hρ.le hRspace
            rw [CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ,
              ← vec3EuclideanNorm_eq_vecEuclideanNorm]
            exact hc1
          have h2 : CKN.timeCutoff s ρ Rtime z.2 = 1 :=
            CKN.timeCutoff_eq_one_on hρ.le hRtime ⟨hc2, hz2⟩
          rw [hκ0, h1, h2, one_mul]
        change serrinCutoff x s ρ z * (κ z * w z) = serrinCutoff x s ρ z * w z
        rw [hκ1, one_mul]
      · push Not at hc2
        have hz0 : serrinCutoff x s ρ z = 0 := by
          unfold serrinCutoff
          rw [(serrinTimeBump_support (s := s) hρ z.2).2.1 hc2.le, mul_zero]
        change serrinCutoff x s ρ z * (κ z * w z) = serrinCutoff x s ρ z * w z
        rw [hz0]; ring
    · push Not at hc1
      have hz0 : serrinCutoff x s ρ z = 0 := by
        unfold serrinCutoff
        rw [(serrinBallCutoff_support x hρ z.1).2.1 hc1, zero_mul]
      change serrinCutoff x s ρ z * (κ z * w z) = serrinCutoff x s ρ z * w z
      rw [hz0]; ring

end CIV
