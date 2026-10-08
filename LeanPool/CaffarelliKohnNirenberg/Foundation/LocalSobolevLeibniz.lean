/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative.Product
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Leibniz rules for local Sobolev families

Smooth scalar multipliers act on the ordered weak derivative families used to
define the local integer Sobolev spaces.
-/

public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Leibniz family of a product; the first letter of the word is applied first. -/
@[expose]
def sobolevLeibnizFamily : List (Fin 3) → (List (Fin 3) → Vec3 → ℝ) →
    (List (Fin 3) → Vec3 → ℝ) → Vec3 → ℝ
  | [], A, B => fun x => A [] x * B [] x
  | j :: α, A, B => fun x =>
      sobolevLeibnizFamily α (fun β => A (j :: β)) B x +
        sobolevLeibnizFamily α A (fun β => B (j :: β)) x

private theorem localSobolev_memLp_compact {U : Set Vec3} {g : Vec3 → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp g 2 (volume.restrict U) := by
  exact (hg.memLp_of_hasCompactSupport (p := 2) hgc).mono_measure
    Measure.restrict_le_self

private theorem localSobolev_memLp_spatialDeriv_compact {U : Set Vec3}
    {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (j : Fin 3) : MemLp (spatialDeriv g j) 2 (volume.restrict U) := by
  have hcont : Continuous (spatialDeriv g j) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact : HasCompactSupport (spatialDeriv g j) := by
    change HasCompactSupport (fun x => (fderiv ℝ g x) (basisVec j))
    exact hgc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  exact localSobolev_memLp_compact hcont hcompact

private theorem localSobolev_bounded_mul_memLp {μ : Measure Vec3}
    {a b : Vec3 → ℝ} {L : ℝ} (hb : MemLp b 2 μ)
    (ha : AEStronglyMeasurable a μ) (hL : ∀ x, |a x| ≤ L) :
    MemLp (fun x => a x * b x) 2 μ := by
  apply MemLp.of_le_mul hb (ha.mul hb.aestronglyMeasurable)
  · filter_upwards [] with x
    change |a x * b x| ≤ L * |b x|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hL x) (abs_nonneg (b x))

private theorem weakPartial_mul_smooth_local {U : Set Vec3}
    {j : Fin 3} {f g χ : Vec3 → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (hweak : HasWeakPartialDerivOn U j f g)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχb : ∃ L : ℝ, ∀ x, |χ x| ≤ L)
    (hχjb : ∃ L : ℝ, ∀ x, |spatialDeriv χ j x| ≤ L) :
    HasWeakPartialDerivOn U j (fun x => χ x * f x)
      (fun x => χ x * g x + f x * spatialDeriv χ j x) := by
  intro φ hφ hφc hφU
  let dφ : Vec3 → ℝ := fun x => (fderiv ℝ φ x) (basisVec j)
  let dχ : Vec3 → ℝ := fun x => (fderiv ℝ χ x) (basisVec j)
  have hφd : ContDiff ℝ (⊤ : ℕ∞) dφ := by
    dsimp [dφ]
    exact (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hχd : ContDiff ℝ (⊤ : ℕ∞) dχ := by
    dsimp [dχ]
    exact (hχ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hφdC : Continuous dφ := hφd.continuous
  have hχdC : Continuous dχ := hχd.continuous
  have hφdCompact : HasCompactSupport dφ := by
    dsimp [dφ]
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hχφC : Continuous (fun x => χ x * φ x) := hχ.continuous.mul hφ.continuous
  have hχφCompact : HasCompactSupport (fun x => χ x * φ x) :=
    hφc.mul_left (f := χ)
  have hχφU : tsupport (fun x => χ x * φ x) ⊆ U := by
    exact (tsupport_mul_subset_right (f := χ) (g := φ)).trans hφU
  have hχφSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * φ x) := hχ.mul hφ
  have hχφWeak := hweak (fun x => χ x * φ x) hχφSmooth hχφCompact hχφU
  have hderivId : ∀ x,
      dχ x * φ x + χ x * dφ x =
        (fderiv ℝ (fun y => χ y * φ y) x) (basisVec j) := by
    intro x
    have hmul := congrArg (fun T : Vec3 →L[ℝ] ℝ => T (basisVec j))
      (fderiv_mul
        (hχ.differentiable (by simp) x)
        (hφ.differentiable (by simp) x))
    have hfun : (fun y => χ y * φ y) = χ * φ := by
      funext y
      rfl
    calc
      dχ x * φ x + χ x * dφ x =
          χ x * dφ x + φ x * dχ x := by ring
      _ = (fderiv ℝ (fun y => χ y * φ y) x) (basisVec j) := by
        simpa [dχ, dφ, hfun, smul_eq_mul, Pi.mul_apply] using hmul.symm
  have hmain :
      (∫ x, f x * (dχ x * φ x + χ x * dφ x) ∂volume.restrict U) =
        -(∫ x, g x * (χ x * φ x) ∂volume.restrict U) := by
    calc
      _ = ∫ x, f x * (fderiv ℝ (fun y => χ y * φ y) x) (basisVec j)
            ∂volume.restrict U := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change f x * (dχ x * φ x + χ x * dφ x) = _
            rw [hderivId x]
      _ = _ := hχφWeak
  have hχdφLp : MemLp (fun x => dχ x * φ x) 2 (volume.restrict U) := by
    rcases hχjb with ⟨L, hL⟩
    exact localSobolev_bounded_mul_memLp
      (localSobolev_memLp_compact hφ.continuous hφc)
      (hχdC.aestronglyMeasurable) hL
  have hχdφInt : Integrable (fun x => f x * (dχ x * φ x)) (volume.restrict U) :=
    hf.integrable_mul hχdφLp
  have hχφLp : MemLp (fun x => χ x * φ x) 2 (volume.restrict U) :=
    localSobolev_memLp_compact hχφC hχφCompact
  have hχgφInt : Integrable (fun x => g x * (χ x * φ x)) (volume.restrict U) :=
    hg.integrable_mul hχφLp
  have hχdφInt' : Integrable (fun x => χ x * (dφ x * f x))
      (volume.restrict U) := by
    rcases hχb with ⟨L, hL⟩
    have hχdφLp' : MemLp (fun x => χ x * dφ x) 2 (volume.restrict U) :=
      localSobolev_bounded_mul_memLp
        (localSobolev_memLp_compact hφdC hφdCompact)
        (hχ.continuous.aestronglyMeasurable) hL
    have hint : Integrable (fun x => χ x * dφ x * f x) (volume.restrict U) :=
      hχdφLp'.integrable_mul hf
    refine hint.congr ?_
    filter_upwards [] with x
    ring
  change (∫ x, (χ x * f x) * dφ x ∂volume.restrict U) =
    -(∫ x, (χ x * g x + f x * dχ x) * φ x ∂volume.restrict U)
  calc
    (∫ x, (χ x * f x) * dφ x ∂volume.restrict U) =
        ∫ x, f x * (χ x * dφ x) ∂volume.restrict U := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by ring
    _ = ∫ x, χ x * (dφ x * f x) ∂volume.restrict U := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by ring
    _ = (∫ x, f x * (dχ x * φ x) + χ x * (dφ x * f x)
          ∂volume.restrict U) -
          ∫ x, f x * (dχ x * φ x) ∂volume.restrict U := by
          rw [integral_add hχdφInt hχdφInt']
          abel
    _ = (∫ x, f x * (dχ x * φ x + χ x * dφ x) ∂volume.restrict U) -
          ∫ x, f x * (dχ x * φ x) ∂volume.restrict U := by
          congr 1
          apply integral_congr_ae
          exact ae_of_all _ fun x => by ring
    _ = (-(∫ x, g x * (χ x * φ x) ∂volume.restrict U)) -
          ∫ x, f x * (dχ x * φ x) ∂volume.restrict U := by
          rw [hmain]
    _ = -(∫ x, (χ x * g x + f x * dχ x) * φ x ∂volume.restrict U) := by
          have hsum :
              (∫ x, g x * (χ x * φ x) ∂volume.restrict U) +
                ∫ x, f x * (dχ x * φ x) ∂volume.restrict U =
                ∫ x, (χ x * g x + f x * dχ x) * φ x ∂volume.restrict U := by
            calc
              _ = ∫ x, g x * (χ x * φ x) + f x * (dχ x * φ x)
                    ∂volume.restrict U :=
                  (integral_add hχgφInt hχdφInt).symm
              _ = _ := by
                apply integral_congr_ae
                exact ae_of_all _ fun x => by ring
          calc
            -(∫ x, g x * (χ x * φ x) ∂volume.restrict U) -
                ∫ x, f x * (dχ x * φ x) ∂volume.restrict U =
                -((∫ x, g x * (χ x * φ x) ∂volume.restrict U) +
                    ∫ x, f x * (dχ x * φ x) ∂volume.restrict U) := by ring
            _ = _ := by rw [hsum]

private theorem wordDeriv_spatialDeriv (α : List (Fin 3)) (j : Fin 3)
    (χ : Vec3 → ℝ) :
    wordDeriv α (spatialDeriv χ j) = wordDeriv (j :: α) χ := by
  rfl

private theorem isSobolevFamilyOn_zero_smooth_mul {U : Set Vec3} {χ f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχb : ∃ L : ℝ, ∀ x, |χ x| ≤ L)
    (h : IsSobolevFamilyOn 0 U f D) :
    IsSobolevFamilyOn 0 U (fun x => χ x * f x)
      (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β χ) D) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h.zero] with x hx
    simp [sobolevLeibnizFamily, wordDeriv, hx]
  · intro α hα
    cases α with
    | nil =>
        rcases hχb with ⟨L, hL⟩
        exact localSobolev_bounded_mul_memLp (h.memL2 [] (by simp))
          hχ.continuous.aestronglyMeasurable hL
    | cons j α => simp at hα
  · intro α j hα
    omega

/-- Multiplication by a smooth function with bounded derivatives preserves a
local Sobolev family, with the ordered Leibniz formula for every derivative. -/
theorem IsSobolevFamilyOn.smooth_mul {m : ℕ} {U : Set Vec3} (hU : IsOpen U)
    {χ f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχb : ∀ α : List (Fin 3), α.length ≤ m →
      ∃ L : ℝ, ∀ x, |wordDeriv α χ x| ≤ L)
    (h : IsSobolevFamilyOn m U f D) :
    IsSobolevFamilyOn m U (fun x => χ x * f x)
      (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β χ) D) := by
  induction m generalizing U χ f D with
  | zero =>
      exact isSobolevFamilyOn_zero_smooth_mul hχ (hχb [] (by simp)) h
  | succ m ih =>
      have hLow : IsSobolevFamilyOn m U f D := h.of_le (Nat.le_succ m)
      have hZero : IsSobolevFamilyOn 0 U f D := h.of_le (Nat.zero_le _)
      have hχbLow : ∀ α : List (Fin 3), α.length ≤ m →
          ∃ L : ℝ, ∀ x, |wordDeriv α χ x| ≤ L := by
        intro α hα
        exact hχb α (hα.trans (Nat.le_succ m))
      have hOutZero := isSobolevFamilyOn_zero_smooth_mul
        hχ (hχb [] (by simp)) hZero
      apply (isSobolevFamilyOn_succ_iff).2
      refine ⟨hOutZero, ?_⟩
      intro j
      have hdecomp := (isSobolevFamilyOn_succ_iff).mp h
      have hDerivFamily : IsSobolevFamilyOn m U (D [j])
          (fun α => D (j :: α)) := (hdecomp.2 j).2
      have hχj : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv χ j) := by
        have h' := contDiff_wordDeriv hχ [j]
        simpa [wordDeriv] using h'
      have hχjb : ∀ α : List (Fin 3), α.length ≤ m →
          ∃ L : ℝ, ∀ x, |wordDeriv α (spatialDeriv χ j) x| ≤ L := by
        intro α hα
        rw [wordDeriv_spatialDeriv]
        exact hχb (j :: α) (by simp only [List.length_cons]; omega)
      have hFirst := ih hU hχj hχjb hLow
      have hSecond := ih hU hχ hχbLow hDerivFamily
      refine ⟨?_, ?_⟩
      · have hweak := weakPartial_mul_smooth_local
          (h.memL2 [] (by simp)) (h.memL2 [j] (by simp))
          (h.weak [] j (by simp)) hχ (hχb [] (by simp)) (hχb [j] (by simp))
        simpa [sobolevLeibnizFamily, wordDeriv, spatialDeriv,
          add_comm, mul_comm, mul_left_comm] using hweak
      · have hsum := hFirst.add hSecond
        have hbase :
            (fun x => spatialDeriv χ j x * f x + χ x * D [j] x) =ᵐ[volume.restrict U]
              (fun x => sobolevLeibnizFamily [j]
                (fun β => wordDeriv β χ) D x) := by
          filter_upwards [h.zero] with x hx
          simp [sobolevLeibnizFamily, wordDeriv, hx]
        exact hsum.congr_ae hbase (by
          intro α hα
          simp [sobolevLeibnizFamily, wordDeriv_spatialDeriv])

private theorem support_spatialDeriv_subset_tsupport {χ : Vec3 → ℝ} (j : Fin 3) :
    Function.support (spatialDeriv χ j) ⊆ tsupport χ := by
  intro x hx
  by_contra hxt
  have hχzero : χ =ᶠ[nhds x] 0 :=
    (isClosed_tsupport (f := χ)).isOpen_compl.eventually_mem hxt |>.mono
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  have hderivzero := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hχzero
  change (fderiv ℝ χ x) (basisVec j) ≠ 0 at hx
  apply hx
  rw [hderivzero]
  simp

private theorem tsupport_spatialDeriv_subset_tsupport {χ : Vec3 → ℝ} (j : Fin 3) :
    tsupport (spatialDeriv χ j) ⊆ tsupport χ := by
  apply closure_minimal (support_spatialDeriv_subset_tsupport j)
  exact isClosed_tsupport (f := χ)

private theorem memLp_smooth_mul_zeroExtend {U : Set Vec3} (hU : IsOpen U)
    {χ f : Vec3 → ℝ} (hχ : Continuous χ) (hχU : tsupport χ ⊆ U)
    (hχb : ∃ L : ℝ, ∀ x, |χ x| ≤ L)
    (hf : MemLp f 2 (volume.restrict U)) : MemLp (fun x => χ x * f x) 2 volume := by
  rcases hχb with ⟨L, hL⟩
  have hmul : MemLp (fun x => χ x * f x) 2 (volume.restrict U) :=
    localSobolev_bounded_mul_memLp hf hχ.aestronglyMeasurable hL
  have hglob : MemLp (U.indicator (fun x => χ x * f x)) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).2 hmul
  have heq : U.indicator (fun x => χ x * f x) = fun x => χ x * f x := by
    funext x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
    · have hχ0 : χ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hxt => hx (hχU hxt))
      simp [hχ0]
  rw [heq] at hglob
  exact hglob

private theorem locallyIntegrableOn_of_memLp_two_restrict {U : Set Vec3} {f : Vec3 → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) : LocallyIntegrableOn f U volume := by
  exact locallyIntegrableOn_of_locallyIntegrable_restrict
    (hf.locallyIntegrable (by norm_num))

private theorem isSobolevFamilyOn_zero_smooth_mul_univ {U : Set Vec3} (hU : IsOpen U)
    {χ f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχU : tsupport χ ⊆ U)
    (hχb : ∃ L : ℝ, ∀ x, |χ x| ≤ L) (h : IsSobolevFamilyOn 0 U f D) :
    IsSobolevFamilyOn 0 univ (fun x => χ x * f x)
      (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β χ) D) := by
  refine ⟨?_, ?_, ?_⟩
  · have hzero :
        (fun x => sobolevLeibnizFamily [] (fun β => wordDeriv β χ) D x) =ᵐ[volume]
          (fun x => χ x * f x) := by
      have hzeroU : ∀ᵐ x ∂volume, x ∈ U → D [] x = f x :=
        (ae_restrict_iff' hU.measurableSet).1 h.zero
      filter_upwards [hzeroU] with x hx
      by_cases hxu : x ∈ U
      · simp [sobolevLeibnizFamily, wordDeriv, hx hxu]
      · have hχ0 : χ x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hxt => hxu (hχU hxt))
        simp [sobolevLeibnizFamily, wordDeriv, hχ0]
    simpa only [Measure.restrict_univ] using hzero
  · intro α hα
    cases α with
    | nil =>
        simpa only [sobolevLeibnizFamily, wordDeriv, Measure.restrict_univ] using
          memLp_smooth_mul_zeroExtend hU hχ.continuous hχU hχb
            (h.memL2 [] (by simp))
    | cons j α => simp at hα
  · intro α j hα
    omega

private theorem contDiff_spatialDeriv {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv χ j) := by
  have h' := contDiff_wordDeriv hχ [j]
  simpa [wordDeriv] using h'

private theorem hasCompactSupport_spatialDeriv {χ : Vec3 → ℝ}
    (hχc : HasCompactSupport χ) (j : Fin 3) : HasCompactSupport (spatialDeriv χ j) := by
  change HasCompactSupport (fun x => (fderiv ℝ χ x) (basisVec j))
  exact hχc.fderiv_apply (𝕜 := ℝ) (basisVec j)

private theorem hasCompactSupport_wordDeriv {χ : Vec3 → ℝ}
    (hχc : HasCompactSupport χ) (α : List (Fin 3)) :
    HasCompactSupport (wordDeriv α χ) := by
  induction α generalizing χ hχc with
  | nil => exact hχc
  | cons j α ih =>
      exact ih (χ := spatialDeriv χ j) (hasCompactSupport_spatialDeriv hχc j)

private theorem exists_abs_bound_of_continuous_compact {g : Vec3 → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ L : ℝ, ∀ x, |g x| ≤ L := by
  rcases hg.bounded_above_of_compact_support hgc with ⟨L, hL⟩
  exact ⟨L, fun x => by simpa only [Real.norm_eq_abs] using hL x⟩

/-- A compactly supported smooth multiplier supported in an open set produces a
whole-space Sobolev family by zero extension. -/
theorem IsSobolevFamilyOn.smooth_mul_univ {m : ℕ} {U : Set Vec3} (hU : IsOpen U)
    {χ f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (h : IsSobolevFamilyOn m U f D) :
    IsSobolevFamilyOn m univ (fun x => χ x * f x)
      (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β χ) D) := by
  induction m generalizing U χ f D with
  | zero =>
      exact isSobolevFamilyOn_zero_smooth_mul_univ hU hχ hχU
        (exists_abs_bound_of_continuous_compact hχ.continuous hχc) h
  | succ m ih =>
      have hLow : IsSobolevFamilyOn m U f D := h.of_le (Nat.le_succ m)
      have hZero : IsSobolevFamilyOn 0 U f D := h.of_le (Nat.zero_le _)
      have hχbLow : ∀ α : List (Fin 3), α.length ≤ m →
          ∃ L : ℝ, ∀ x, |wordDeriv α χ x| ≤ L := by
        intro α hα
        exact exists_abs_bound_of_continuous_compact
          (contDiff_wordDeriv hχ α).continuous (hasCompactSupport_wordDeriv hχc α)
      have hOutZero := isSobolevFamilyOn_zero_smooth_mul_univ hU hχ hχU
        (hχbLow [] (by simp)) hZero
      apply (isSobolevFamilyOn_succ_iff).2
      refine ⟨hOutZero, ?_⟩
      intro j
      have hdecomp := (isSobolevFamilyOn_succ_iff).mp h
      have hDerivFamily : IsSobolevFamilyOn m U (D [j])
          (fun α => D (j :: α)) := (hdecomp.2 j).2
      have hχj : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv χ j) :=
        contDiff_spatialDeriv hχ j
      have hχjc : HasCompactSupport (spatialDeriv χ j) :=
        hasCompactSupport_spatialDeriv hχc j
      have hχjU : tsupport (spatialDeriv χ j) ⊆ U :=
        (tsupport_spatialDeriv_subset_tsupport j).trans hχU
      have hχjb : ∀ α : List (Fin 3), α.length ≤ m →
          ∃ L : ℝ, ∀ x, |wordDeriv α (spatialDeriv χ j) x| ≤ L := by
        intro α hα
        exact exists_abs_bound_of_continuous_compact
          (contDiff_wordDeriv hχj α).continuous (hasCompactSupport_wordDeriv hχjc α)
      have hFirst := ih hU hχj hχjc hχjU hLow
      have hSecond := ih hU hχ hχc hχU hDerivFamily
      refine ⟨?_, ?_⟩
      · have hweak := HasWeakPartialDerivOn.mul_smooth_zeroExtend hU
          (locallyIntegrableOn_of_memLp_two_restrict (h.memL2 [] (by simp)))
          (locallyIntegrableOn_of_memLp_two_restrict (h.memL2 [j] (by simp)))
          (h.weak [] j (by simp)) hχ hχc hχU
        simpa [sobolevLeibnizFamily, wordDeriv, spatialDeriv,
          add_comm, mul_comm, mul_left_comm] using hweak
      · have hsum := hFirst.add hSecond
        have hbase :
            (fun x => spatialDeriv χ j x * f x + χ x * D [j] x) =ᵐ[volume]
              (fun x => sobolevLeibnizFamily [j]
                (fun β => wordDeriv β χ) D x) := by
          have hzeroU : ∀ᵐ x ∂volume, x ∈ U → D [] x = f x :=
            (ae_restrict_iff' hU.measurableSet).1 h.zero
          filter_upwards [hzeroU] with x hx
          by_cases hxu : x ∈ U
          · simp [sobolevLeibnizFamily, wordDeriv, hx hxu]
          · have hχ0 : χ x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun hxt => hxu (hχU hxt))
            have hχj0 : spatialDeriv χ j x = 0 := by
              have hxt : x ∉ tsupport χ := fun hxt => hxu (hχU hxt)
              have hz := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ)
                ((isClosed_tsupport (f := χ)).isOpen_compl.eventually_mem hxt |>.mono
                  (fun y hy => image_eq_zero_of_notMem_tsupport hy))
              simpa [spatialDeriv] using congrArg (fun T : Vec3 →L[ℝ] ℝ => T (basisVec j)) hz
            simp [sobolevLeibnizFamily, wordDeriv, hχ0, hχj0]
        exact hsum.congr_ae (by simpa only [Measure.restrict_univ] using hbase) (by
          intro α hα
          simp [sobolevLeibnizFamily, wordDeriv_spatialDeriv])

private theorem sobolevLeibnizFamily_abs_le {α : List (Fin 3)}
    {A B : List (Fin 3) → Vec3 → ℝ} {x : Vec3} {L M : ℝ}
    (hA : ∀ β : List (Fin 3), β.length ≤ α.length → |A β x| ≤ L)
    (hB : ∀ β : List (Fin 3), β.length ≤ α.length → |B β x| ≤ M) :
    |sobolevLeibnizFamily α A B x| ≤ (2 : ℝ) ^ α.length * L * M := by
  induction α generalizing A B x L M with
  | nil =>
      have hL0 : 0 ≤ L := le_trans (abs_nonneg (A [] x)) (hA [] (by simp))
      calc
        |sobolevLeibnizFamily [] A B x| = |A [] x| * |B [] x| := by
          simp [sobolevLeibnizFamily, abs_mul]
        _ ≤ L * M :=
          mul_le_mul (hA [] (by simp)) (hB [] (by simp)) (abs_nonneg _) hL0
        _ = (2 : ℝ) ^ ([] : List (Fin 3)).length * L * M := by simp
  | cons j α ih =>
      have hAleft : ∀ β : List (Fin 3), β.length ≤ α.length →
          |A (j :: β) x| ≤ L := by
        intro β hβ
        exact hA (j :: β) (by simp only [List.length_cons]; omega)
      have hBleft : ∀ β : List (Fin 3), β.length ≤ α.length →
          |B β x| ≤ M := by
        intro β hβ
        exact hB β (by simp only [List.length_cons]; omega)
      have hAright : ∀ β : List (Fin 3), β.length ≤ α.length →
          |A β x| ≤ L := by
        intro β hβ
        exact hA β (by simp only [List.length_cons]; omega)
      have hBright : ∀ β : List (Fin 3), β.length ≤ α.length →
          |B (j :: β) x| ≤ M := by
        intro β hβ
        exact hB (j :: β) (by simp only [List.length_cons]; omega)
      calc
        |sobolevLeibnizFamily (j :: α) A B x| ≤
            |sobolevLeibnizFamily α (fun β => A (j :: β)) B x| +
              |sobolevLeibnizFamily α A (fun β => B (j :: β)) x| := by
                simp only [sobolevLeibnizFamily]
                exact abs_add_le _ _
        _ ≤ (2 : ℝ) ^ α.length * L * M + (2 : ℝ) ^ α.length * L * M :=
              add_le_add (ih hAleft hBleft) (ih hAright hBright)
        _ = (2 : ℝ) ^ (j :: α).length * L * M := by
              simp only [List.length_cons, pow_succ]
              ring

private theorem sobolevLeibnizFamily_memLp_of_length {μ : Measure Vec3}
    {A B : List (Fin 3) → Vec3 → ℝ} {L : ℝ} {α : List (Fin 3)}
    (hAmeas : ∀ β : List (Fin 3), β.length ≤ α.length → AEStronglyMeasurable (A β) μ)
    (hAbound : ∀ β : List (Fin 3), β.length ≤ α.length → ∀ x, |A β x| ≤ L)
    (hB : ∀ β : List (Fin 3), β.length ≤ α.length → MemLp (B β) 2 μ) :
    MemLp (sobolevLeibnizFamily α A B) 2 μ := by
  induction α generalizing A B with
  | nil =>
      exact localSobolev_bounded_mul_memLp (hB [] (by simp))
        (hAmeas [] (by simp)) (hAbound [] (by simp))
  | cons j α ih =>
      have hAleft : ∀ β : List (Fin 3), β.length ≤ α.length →
          AEStronglyMeasurable (A (j :: β)) μ := by
        intro β hβ
        exact hAmeas (j :: β) (by simp only [List.length_cons]; omega)
      have hAleftBound : ∀ β : List (Fin 3), β.length ≤ α.length →
          ∀ x, |A (j :: β) x| ≤ L := by
        intro β hβ x
        exact hAbound (j :: β) (by simp only [List.length_cons]; omega) x
      have hBleft : ∀ β : List (Fin 3), β.length ≤ α.length → MemLp (B β) 2 μ := by
        intro β hβ
        exact hB β (by simp only [List.length_cons] at *; omega)
      have hAright : ∀ β : List (Fin 3), β.length ≤ α.length →
          AEStronglyMeasurable (A β) μ := by
        intro β hβ
        exact hAmeas β (by simp only [List.length_cons]; omega)
      have hArightBound : ∀ β : List (Fin 3), β.length ≤ α.length →
          ∀ x, |A β x| ≤ L := by
        intro β hβ x
        exact hAbound β (by simp only [List.length_cons]; omega) x
      have hBrightLp : ∀ β : List (Fin 3), β.length ≤ α.length →
          MemLp (B (j :: β)) 2 μ := by
        intro β hβ
        exact hB (j :: β) (by simp only [List.length_cons]; omega)
      have hleft := ih (A := fun β => A (j :: β)) (B := B)
        hAleft hAleftBound hBleft
      have hright := ih (A := A) (B := fun β => B (j :: β))
        hAright hArightBound hBrightLp
      have hadd := hleft.add hright
      exact (memLp_congr_ae (ae_of_all _ fun x => rfl)).2 hadd

private theorem sobolevLeibnizFamily_zero_of_A_zero {U : Set Vec3}
    {A B : List (Fin 3) → Vec3 → ℝ} {α : List (Fin 3)}
    (hAzero : ∀ β : List (Fin 3), β.length ≤ α.length → ∀ x, x ∉ U → A β x = 0)
    {x : Vec3} (hx : x ∉ U) :
    sobolevLeibnizFamily α A B x = 0 := by
  induction α generalizing A B with
  | nil =>
      simp [sobolevLeibnizFamily, hAzero [] (by simp) x hx]
  | cons j α ih =>
      have hAleft : ∀ β : List (Fin 3), β.length ≤ α.length → ∀ y, y ∉ U → A (j :: β) y = 0 := by
        intro β hβ y hy
        exact hAzero (j :: β) (by simp only [List.length_cons]; omega) y hy
      have hAright : ∀ β : List (Fin 3), β.length ≤ α.length → ∀ y, y ∉ U → A β y = 0 := by
        intro β hβ y hy
        exact hAzero β (by simp only [List.length_cons]; omega) y hy
      simp only [sobolevLeibnizFamily]
      rw [ih hAleft, ih hAright, add_zero]

private theorem pow_two_nat_eq_four_pow (m : ℕ) :
    ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hpow2 : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := pow_succ (2 : ℝ) m
      calc
        ((2 : ℝ) ^ (m + 1)) ^ 2 = ((2 : ℝ) ^ m * 2) ^ 2 := by rw [hpow2]
        _ = ((2 : ℝ) ^ m) ^ 2 * 4 := by ring
        _ = (4 : ℝ) ^ m * 4 := by rw [ih]
        _ = (4 : ℝ) ^ (m + 1) := (pow_succ (4 : ℝ) m).symm

private theorem sobolevLeibnizFamily_sq_le {m : ℕ}
    {A B : List (Fin 3) → Vec3 → ℝ} {L : ℝ}
    (hAbound : ∀ α : List (Fin 3), α.length ≤ m → ∀ x, |A α x| ≤ L)
    {α : List (Fin 3)} (hα : α.length ≤ m) (x : Vec3) :
    sobolevLeibnizFamily α A B x ^ 2 ≤
      (4 : ℝ) ^ m * L ^ 2 * (sobolevWords m).card *
        (∑ β ∈ sobolevWords m, B β x ^ 2) := by
  let M : ℝ := ∑ β ∈ sobolevWords m, |B β x|
  have hL0 : 0 ≤ L := le_trans (abs_nonneg (A [] x)) (hAbound [] (by simp) x)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun β hβ => abs_nonneg _
  have hMb : ∀ β : List (Fin 3), β.length ≤ m → |B β x| ≤ M := by
    intro β hβ
    dsimp [M]
    exact Finset.single_le_sum (fun γ hγ => abs_nonneg (B γ x))
      (mem_sobolevWords.mpr hβ)
  have hpoint := sobolevLeibnizFamily_abs_le
    (fun β hβ => hAbound β (hβ.trans hα) x)
    (fun β hβ => hMb β (hβ.trans hα))
  have hpow : (2 : ℝ) ^ α.length ≤ (2 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num) hα
  have habs : |sobolevLeibnizFamily α A B x| ≤ (2 : ℝ) ^ m * L * M := by
    calc
      _ ≤ (2 : ℝ) ^ α.length * L * M := hpoint
      _ ≤ (2 : ℝ) ^ m * L * M := by gcongr
  have hupper0 : 0 ≤ (2 : ℝ) ^ m * L * M := by positivity
  have hsquare :
      sobolevLeibnizFamily α A B x ^ 2 ≤ ((2 : ℝ) ^ m * L * M) ^ 2 := by
    calc
      _ = |sobolevLeibnizFamily α A B x| ^ 2 := (sq_abs _).symm
      _ ≤ ((2 : ℝ) ^ m * L * M) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hupper0).2 habs
  have hcs : M ^ 2 ≤ (sobolevWords m).card *
      (∑ β ∈ sobolevWords m, B β x ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (sobolevWords m)
      (fun β => |B β x|) (fun _ => (1 : ℝ))
    calc
      M ^ 2 ≤ (∑ β ∈ sobolevWords m, |B β x| ^ 2) *
          (∑ β ∈ sobolevWords m, (1 : ℝ) ^ 2) := by
            simpa only [M, mul_one] using h
      _ = (sobolevWords m).card *
          (∑ β ∈ sobolevWords m, B β x ^ 2) := by
            simp [sq_abs, mul_comm]
  calc
    sobolevLeibnizFamily α A B x ^ 2 ≤ ((2 : ℝ) ^ m * L * M) ^ 2 := hsquare
    _ = ((2 : ℝ) ^ m) ^ 2 * L ^ 2 * M ^ 2 := by ring
    _ ≤ ((2 : ℝ) ^ m) ^ 2 * L ^ 2 *
          ((sobolevWords m).card * (∑ β ∈ sobolevWords m, B β x ^ 2)) := by
          gcongr
    _ = (4 : ℝ) ^ m * L ^ 2 * (sobolevWords m).card *
          (∑ β ∈ sobolevWords m, B β x ^ 2) := by
          rw [pow_two_nat_eq_four_pow]
          ring

/-- The squared Sobolev norm of a Leibniz family is controlled by the squared
norm of its second factor when all derivatives of the first factor are bounded
and supported in `U`. -/
theorem sobolevLeibnizFamily_normSq_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U V : Set Vec3) (A B : List (Fin 3) → Vec3 → ℝ) (L : ℝ),
      MeasurableSet U → MeasurableSet V → U ⊆ V →
      (∀ α : List (Fin 3), α.length ≤ m → ∀ x, |A α x| ≤ L) →
      (∀ α : List (Fin 3), α.length ≤ m → ∀ x, x ∉ U → A α x = 0) →
      (∀ α : List (Fin 3), α.length ≤ m → AEStronglyMeasurable (A α) (volume.restrict V)) →
      (∀ α : List (Fin 3), α.length ≤ m → MemLp (B α) 2 (volume.restrict V)) →
      sobolevNormSqOn m V (fun α => sobolevLeibnizFamily α A B) ≤
        C * L ^ 2 * sobolevNormSqOn m (U ∩ V) B := by
  classical
  let W := sobolevWords m
  let C : ℝ := (4 : ℝ) ^ m * (W.card : ℝ) ^ 2
  refine ⟨C, by positivity, ?_⟩
  intro U V A B L hU hV hUV hAbound hAzero hAmeas hBmem
  let Q : Vec3 → ℝ := fun x => ∑ β ∈ W, B β x ^ 2
  let c : ℝ := (4 : ℝ) ^ m * L ^ 2 * (W.card : ℝ)
  have hQint : Integrable Q (volume.restrict V) := by
    dsimp [Q]
    apply integrable_finsetSum
    intro β hβ
    exact (hBmem β (mem_sobolevWords.mp (by simpa [W] using hβ))).integrable_sq
  have hIntQ :
      (∫ x in U ∩ V, Q x) = ∑ β ∈ W, ∫ x in U ∩ V, B β x ^ 2 := by
    dsimp [Q]
    exact integral_finsetSum W (fun β hβ => by
      have hβm : β.length ≤ m := mem_sobolevWords.mp (by simpa [W] using hβ)
      exact (hBmem β hβm).integrable_sq.mono_measure
        (Measure.restrict_mono (by intro x hx; exact hx.2) le_rfl))
  have hRightInt : Integrable (U.indicator (fun x => c * Q x)) (volume.restrict V) :=
    (hQint.const_mul c).indicator hU
  have hterm (α : List (Fin 3)) (hα : α.length ≤ m) :
      (∫ x in V, sobolevLeibnizFamily α A B x ^ 2) ≤
        c * (∫ x in U ∩ V, Q x) := by
    have hαW : α ∈ W := by simpa [W] using (mem_sobolevWords.mpr hα)
    have hOutMem : MemLp (sobolevLeibnizFamily α A B) 2 (volume.restrict V) :=
      sobolevLeibnizFamily_memLp_of_length
        (fun β hβ => hAmeas β (hβ.trans (mem_sobolevWords.mp (by simpa [W] using hαW))))
        (fun β hβ x => hAbound β
          (hβ.trans (mem_sobolevWords.mp (by simpa [W] using hαW))) x)
        (fun β hβ => hBmem β
          (hβ.trans (mem_sobolevWords.mp (by simpa [W] using hαW))) )
    have hOutInt : Integrable (fun x => sobolevLeibnizFamily α A B x ^ 2)
        (volume.restrict V) := hOutMem.integrable_sq
    have hpoint : ∀ x,
        sobolevLeibnizFamily α A B x ^ 2 ≤ U.indicator (fun y => c * Q y) x := by
      intro x
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx]
        exact sobolevLeibnizFamily_sq_le hAbound hα x
      · have hzero := sobolevLeibnizFamily_zero_of_A_zero (B := B)
          (fun β hβ y hy => hAzero β
            (hβ.trans (mem_sobolevWords.mp (by simpa [W] using hαW))) y hy) hx
        simp [hx, hzero]
    calc
      (∫ x in V, sobolevLeibnizFamily α A B x ^ 2) =
          ∫ x, sobolevLeibnizFamily α A B x ^ 2 ∂volume.restrict V := rfl
      _ ≤ ∫ x, U.indicator (fun y => c * Q y) x ∂volume.restrict V :=
            integral_mono_ae hOutInt hRightInt (ae_of_all _ hpoint)
      _ = ∫ x in V ∩ U, c * Q x := by
            simpa only [Set.inter_comm] using setIntegral_indicator (μ := volume)
              (s := V) (t := U) hU
      _ = c * (∫ x in U ∩ V, Q x) := by
            rw [Set.inter_comm V U]
            rw [integral_const_mul]
  change (∑ α ∈ W, ∫ x in V, sobolevLeibnizFamily α A B x ^ 2) ≤
    C * L ^ 2 * (∑ α ∈ W, ∫ x in U ∩ V, B α x ^ 2)
  calc
    (∑ α ∈ W, ∫ x in V, sobolevLeibnizFamily α A B x ^ 2) ≤
        ∑ α ∈ W, c * (∫ x in U ∩ V, Q x) := by
          apply Finset.sum_le_sum
          intro α hα
          exact hterm α (mem_sobolevWords.mp (by simpa [W] using hα))
    _ = (W.card : ℝ) * (c * (∫ x in U ∩ V, Q x)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
    _ = C * L ^ 2 * (∑ α ∈ W, ∫ x in U ∩ V, B α x ^ 2) := by
          rw [hIntQ]
          dsimp [C, c]
          ring

end CKN
