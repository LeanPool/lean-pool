/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.SobolevEmbeddingR3
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevLeibniz
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Smooth product estimates at the two vorticity bootstrap levels

The componentwise estimates used to prove `lem:vorticity-products`.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace ESS

private theorem vorticityProducts_leibniz_zero (α : List (Fin 3))
    {A B : List (Fin 3) → Vec3 → ℝ} {x : Vec3} (hA : ∀ β, A β x = 0) :
    sobolevLeibnizFamily α A B x = 0 := by
  induction α generalizing A B with
  | nil => simp [sobolevLeibnizFamily, hA []]
  | cons j α ih =>
      simp only [sobolevLeibnizFamily]
      rw [ih (A := fun β => A (j :: β)) (fun β => hA (j :: β)), ih hA, add_zero]

/-- A compactly supported multiplier transfers the local Leibniz square-norm
bound to the whole space. Used for the local form of `lem:vorticity-products`. -/
theorem vorticityProducts_leibniz_univ_normSq_le {m : ℕ} {C L : ℝ}
    (hC : ∀ (U V : Set Vec3) (A B : List (Fin 3) → Vec3 → ℝ) (L : ℝ),
      MeasurableSet U → MeasurableSet V → U ⊆ V →
      (∀ α : List (Fin 3), α.length ≤ m → ∀ x, |A α x| ≤ L) →
      (∀ α : List (Fin 3), α.length ≤ m → ∀ x, x ∉ U → A α x = 0) →
      (∀ α : List (Fin 3), α.length ≤ m →
        AEStronglyMeasurable (A α) (volume.restrict V)) →
      (∀ α : List (Fin 3), α.length ≤ m → MemLp (B α) 2 (volume.restrict V)) →
      sobolevNormSqOn m V (fun α => sobolevLeibnizFamily α A B) ≤
        C * L ^ 2 * sobolevNormSqOn m (U ∩ V) B)
    (hC0 : 0 ≤ C) {U T : Set Vec3} (hU : IsOpen U) (hT : IsClosed T) (hTU : T ⊆ U)
    {g f : Vec3 → ℝ} {B : List (Fin 3) → Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgb : ∀ α : List (Fin 3), α.length ≤ m → ∀ x, |wordDeriv α g x| ≤ L)
    (hg0 : ∀ α : List (Fin 3), ∀ x, x ∉ T → wordDeriv α g x = 0)
    (hB : IsSobolevFamilyOn m U f B) :
    sobolevNormSqOn m univ
      (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β g) B) ≤
      C * L ^ 2 * sobolevNormSqOn m U B := by
  have hzero (α : List (Fin 3)) (x : Vec3) (hx : x ∉ T) :
      sobolevLeibnizFamily α (fun β => wordDeriv β g) B x = 0 :=
    vorticityProducts_leibniz_zero α (fun β => hg0 β x hx)
  have huniv : sobolevNormSqOn m univ
      (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β g) B) =
      sobolevNormSqOn m U (fun α => sobolevLeibnizFamily α (fun β => wordDeriv β g) B) := by
    unfold sobolevNormSqOn
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Measure.restrict_univ]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      change sobolevLeibnizFamily α (fun β => wordDeriv β g) B x ^ 2 = 0
      rw [hzero α x (fun h => hx (hTU h))]; ring).symm
  rw [huniv]
  have h := hC T U (fun β => wordDeriv β g) B L hT.measurableSet hU.measurableSet hTU
    hgb (fun α _ x hx => hg0 α x hx)
    (fun α _ => (contDiff_wordDeriv hg α).continuous.aestronglyMeasurable)
    (fun α hα => hB.memL2 α hα)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (sq_nonneg L)))
  exact Finset.sum_le_sum fun α hα =>
    setIntegral_mono_set (hB.memL2 α (mem_sobolevWords.mp hα)).integrable_sq
      (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ Set.inter_subset_right)

private theorem vorticityProducts_cross_numeric
    {a b Mu Mw Hu Hw : ℝ} (hb : 0 ≤ b)
    (hMu : 0 ≤ Mu) (hMw : 0 ≤ Mw) (hHu : 0 ≤ Hu) (hHw : 0 ≤ Hw)
    (hau : a ^ 2 ≤ 28 * Mu ^ 2 * Hu)
    (hbw : b ^ 2 ≤ 28 * Mw ^ 2 * Hw) :
    a * b ≤ 18 * (Mu ^ 2 * Hw + Mw ^ 2 * Hu) := by
  let su := Real.sqrt Hu
  let sw := Real.sqrt Hw
  have hsu : 0 ≤ su := Real.sqrt_nonneg _
  have hsw : 0 ≤ sw := Real.sqrt_nonneg _
  have hsu2 : su ^ 2 = Hu := Real.sq_sqrt hHu
  have hsw2 : sw ^ 2 = Hw := Real.sq_sqrt hHw
  have hA : a ≤ 6 * Mu * su := by
    have hA2 : a ^ 2 ≤ (6 * Mu * su) ^ 2 := by
      calc
        a ^ 2 ≤ 28 * Mu ^ 2 * Hu := hau
        _ ≤ 36 * Mu ^ 2 * Hu := by
          have h : 0 ≤ Mu ^ 2 * Hu := mul_nonneg (sq_nonneg _) hHu
          nlinarith only [h]
        _ = (6 * Mu * su) ^ 2 := by rw [mul_pow, hsu2]; ring
    have hBound0 : 0 ≤ 6 * Mu * su := by positivity
    nlinarith only [hA2, hBound0]
  have hB : b ≤ 6 * Mw * sw := by
    have hB2 : b ^ 2 ≤ (6 * Mw * sw) ^ 2 := by
      calc
        b ^ 2 ≤ 28 * Mw ^ 2 * Hw := hbw
        _ ≤ 36 * Mw ^ 2 * Hw := by
          have h : 0 ≤ Mw ^ 2 * Hw := mul_nonneg (sq_nonneg _) hHw
          nlinarith only [h]
        _ = (6 * Mw * sw) ^ 2 := by rw [mul_pow, hsw2]; ring
    have hBound0 : 0 ≤ 6 * Mw * sw := by positivity
    nlinarith only [hB2, hBound0]
  calc
    a * b ≤ (6 * Mu * su) * (6 * Mw * sw) := by gcongr
    _ = 36 * (Mu * sw) * (Mw * su) := by ring
    _ ≤ 18 * ((Mu * sw) ^ 2 + (Mw * su) ^ 2) := by
      nlinarith only [sq_nonneg (Mu * sw - Mw * su)]
    _ = 18 * (Mu ^ 2 * Hw + Mw ^ 2 * Hu) := by
      rw [mul_pow, mul_pow, hsw2, hsu2]

/-- The mixed gradient term in the order-two product rule is controlled by
the two bounded factors and their second derivatives. -/
theorem gradProduct_integral_le_smooth
    (f g : Vec3 → ℝ) (Mf Mg : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg) :
    Integrable (fun x => (∑ j : Fin 3, spatialDeriv f j x ^ 2) *
      (∑ j : Fin 3, spatialDeriv g j x ^ 2)) volume ∧
      ∫ x, (∑ j : Fin 3, spatialDeriv f j x ^ 2) *
        (∑ j : Fin 3, spatialDeriv g j x ^ 2) ≤
      18 * (Mf ^ 2 * (∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
          spatialDeriv (spatialDeriv g j) k x ^ 2) +
        Mg ^ 2 * (∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
          spatialDeriv (spatialDeriv f j) k x ^ 2)) := by
  let A : Vec3 → ℝ := fun x => ∑ j : Fin 3, spatialDeriv f j x ^ 2
  let B : Vec3 → ℝ := fun x => ∑ j : Fin 3, spatialDeriv g j x ^ 2
  let Hu : Vec3 → ℝ := fun x => ∑ j : Fin 3, ∑ k : Fin 3,
    spatialDeriv (spatialDeriv f j) k x ^ 2
  let Hw : Vec3 → ℝ := fun x => ∑ j : Fin 3, ∑ k : Fin 3,
    spatialDeriv (spatialDeriv g j) k x ^ 2
  obtain ⟨hA2int, hHuint, hAbound⟩ :=
    gradL4_sq_le_smooth_scalar f Mf hf hfc hMf
  obtain ⟨hB2int, hHwint, hBbound⟩ :=
    gradL4_sq_le_smooth_scalar g Mg hg hgc hMg
  have hAc : Continuous A :=
    (ContDiff.sum fun j _ =>
      (contDiff_spatialDeriv_smooth hf j).pow 2).continuous
  have hBc : Continuous B :=
    (ContDiff.sum fun j _ =>
      (contDiff_spatialDeriv_smooth hg j).pow 2).continuous
  have hAmem : MemLp A (2 : ℝ≥0∞) volume :=
    (memLp_two_iff_integrable_sq hAc.aestronglyMeasurable).2 hA2int
  have hBmem : MemLp B (2 : ℝ≥0∞) volume :=
    (memLp_two_iff_integrable_sq hBc.aestronglyMeasurable).2 hB2int
  have hnnA (x : Vec3) : 0 ≤ A x := by dsimp [A]; positivity
  have hnnB (x : Vec3) : 0 ≤ B x := by dsimp [B]; positivity
  have h22 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hHolder : ∫ x, A x * B x ≤
      Real.sqrt (∫ x, A x ^ 2) * Real.sqrt (∫ x, B x ^ 2) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg h22
      (ae_of_all volume hnnA) (ae_of_all volume hnnB)
      (by simpa using hAmem) (by simpa using hBmem)
    simp_rw [Real.rpow_two] at h
    simpa only [Real.sqrt_eq_rpow] using h
  have hMf0 : 0 ≤ Mf := (abs_nonneg (f 0)).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (abs_nonneg (g 0)).trans (hMg 0)
  have hHu0 : 0 ≤ ∫ x, Hu x := integral_nonneg fun x => by dsimp [Hu]; positivity
  have hHw0 : 0 ≤ ∫ x, Hw x := integral_nonneg fun x => by dsimp [Hw]; positivity
  have hA0 : 0 ≤ ∫ x, A x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ ∫ x, B x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hAeq : (Real.sqrt (∫ x, A x ^ 2)) ^ 2 = ∫ x, A x ^ 2 := Real.sq_sqrt hA0
  have hBeq : (Real.sqrt (∫ x, B x ^ 2)) ^ 2 = ∫ x, B x ^ 2 := Real.sq_sqrt hB0
  have hnum := vorticityProducts_cross_numeric
    (Real.sqrt_nonneg _) hMf0 hMg0 hHu0 hHw0
    (by rw [hAeq]; exact hAbound) (by rw [hBeq]; exact hBbound)
  refine ⟨hAmem.integrable_mul hBmem, ?_⟩
  simpa only [A, B, Hu, Hw] using hHolder.trans hnum

private theorem vorticityProducts_contDiff_wordDeriv
    {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 3)) : ContDiff ℝ (⊤ : ℕ∞) (wordDeriv α f) := by
  induction α generalizing f with
  | nil => simpa only [wordDeriv] using hf
  | cons j α ih =>
      simpa only [wordDeriv] using ih (contDiff_spatialDeriv_smooth hf j)

private theorem vorticityProducts_compact_wordDeriv
    {f : Vec3 → ℝ} (hfc : HasCompactSupport f)
    (α : List (Fin 3)) : HasCompactSupport (wordDeriv α f) := by
  induction α generalizing f with
  | nil => simpa only [wordDeriv] using hfc
  | cons j α ih =>
      change HasCompactSupport (wordDeriv α (spatialDeriv f j))
      exact ih (hfc.fderiv_apply (𝕜 := ℝ) (basisVec j))

private theorem vorticityProducts_integrable_word_sq
    {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (α : List (Fin 3)) :
    Integrable (fun x => wordDeriv α f x ^ 2) volume := by
  have hcont := vorticityProducts_contDiff_wordDeriv hf α
  have hc := vorticityProducts_compact_wordDeriv hfc α
  have hsupport : HasCompactSupport (fun x : Vec3 => wordDeriv α f x ^ 2) := by
    have h : HasCompactSupport ((wordDeriv α f) * (wordDeriv α f)) := hc.mul_right
    change HasCompactSupport (fun x : Vec3 => wordDeriv α f x * wordDeriv α f x) at h
    simpa only [pow_two] using h
  exact (hcont.continuous.pow 2).integrable_of_hasCompactSupport hsupport

private theorem vorticityProducts_sobolevWords_two_card :
    (sobolevWords 2).card = 13 := by decide

private theorem vorticityProducts_word_integral_le_norm
    {f : Vec3 → ℝ} {α : List (Fin 3)} (hα : α.length ≤ 2) :
    ∫ x, wordDeriv α f x ^ 2 ≤
      sobolevNormSqOn 2 univ (fun β => wordDeriv β f) := by
  simp only [sobolevNormSqOn, Measure.restrict_univ]
  exact Finset.single_le_sum
    (f := fun β : List (Fin 3) => ∫ x, wordDeriv β f x ^ 2)
    (s := sobolevWords 2)
    (fun β _ => integral_nonneg fun x => sq_nonneg _)
    (mem_sobolevWords.mpr hα)

private theorem vorticityProducts_sq_two_le (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith only [sq_nonneg (a - b)]

private theorem vorticityProducts_H2_scalar
    (f g : Vec3 → ℝ) (Mf Mg : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hMf : ∀ x, |f x| ≤ Mf) (hMg : ∀ x, |g x| ≤ Mg) :
    sobolevNormSqOn 2 univ (fun α => wordDeriv α (fun x => f x * g x)) ≤
      16900 * (Mf ^ 2 * sobolevNormSqOn 2 univ (fun α => wordDeriv α g) +
        Mg ^ 2 * sobolevNormSqOn 2 univ (fun α => wordDeriv α f)) := by
  let Hf : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α f)
  let Hg : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α g)
  let T : ℝ := Mf ^ 2 * Hg + Mg ^ 2 * Hf
  have hHf0 : 0 ≤ Hf := by
    dsimp [Hf, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hHg0 : 0 ≤ Hg := by
    dsimp [Hg, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hMf0 : 0 ≤ Mf := (abs_nonneg (f 0)).trans (hMf 0)
  have hMg0 : 0 ≤ Mg := (abs_nonneg (g 0)).trans (hMg 0)
  have hfg : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * g x) := hf.mul hg
  have hfgc : HasCompactSupport (fun x => f x * g x) := hfc.mul_right
  let A : Vec3 → ℝ := fun x => ∑ j : Fin 3, spatialDeriv f j x ^ 2
  let B : Vec3 → ℝ := fun x => ∑ j : Fin 3, spatialDeriv g j x ^ 2
  obtain ⟨hcrossInt, hcross⟩ :=
    gradProduct_integral_le_smooth f g Mf Mg hf hfc hg hgc hMf hMg
  have hfirstF (j : Fin 3) : ∫ x, spatialDeriv f j x ^ 2 ≤ Hf := by
    simpa only [Hf, wordDeriv] using
      (vorticityProducts_word_integral_le_norm (f := f) (α := [j]) (by simp))
  have hfirstG (j : Fin 3) : ∫ x, spatialDeriv g j x ^ 2 ≤ Hg := by
    simpa only [Hg, wordDeriv] using
      (vorticityProducts_word_integral_le_norm (f := g) (α := [j]) (by simp))
  have hsecondF (j k : Fin 3) :
      ∫ x, spatialDeriv (spatialDeriv f j) k x ^ 2 ≤ Hf := by
    simpa only [Hf, wordDeriv] using
      (vorticityProducts_word_integral_le_norm (f := f) (α := [j, k]) (by simp))
  have hsecondG (j k : Fin 3) :
      ∫ x, spatialDeriv (spatialDeriv g j) k x ^ 2 ≤ Hg := by
    simpa only [Hg, wordDeriv] using
      (vorticityProducts_word_integral_le_norm (f := g) (α := [j, k]) (by simp))
  have hsecondFsum :
      ∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv f j) k x ^ 2 ≤ 9 * Hf := by
    have hjk (j k : Fin 3) : Integrable
        (fun x => spatialDeriv (spatialDeriv f j) k x ^ 2) volume := by
      simpa only [wordDeriv] using
        (vorticityProducts_integrable_word_sq hf hfc [j, k])
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hjk j k]
    simp_rw [integral_finsetSum _ fun k _ => hjk _ k]
    calc
      _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, Hf :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hsecondF j k
      _ = 9 * Hf := by simp only [Fin.sum_univ_three]; ring
  have hsecondGsum :
      ∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv g j) k x ^ 2 ≤ 9 * Hg := by
    have hjk (j k : Fin 3) : Integrable
        (fun x => spatialDeriv (spatialDeriv g j) k x ^ 2) volume := by
      simpa only [wordDeriv] using
        (vorticityProducts_integrable_word_sq hg hgc [j, k])
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hjk j k]
    simp_rw [integral_finsetSum _ fun k _ => hjk _ k]
    calc
      _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, Hg :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hsecondG j k
      _ = 9 * Hg := by simp only [Fin.sum_univ_three]; ring
  have hcrossT : ∫ x, A x * B x ≤ 162 * T := by
    calc
      ∫ x, A x * B x ≤ 18 * (Mf ^ 2 *
          (∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
            spatialDeriv (spatialDeriv g j) k x ^ 2) +
          Mg ^ 2 * (∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
            spatialDeriv (spatialDeriv f j) k x ^ 2)) := hcross
      _ ≤ 18 * (Mf ^ 2 * (9 * Hg) + Mg ^ 2 * (9 * Hf)) := by gcongr
      _ = 162 * T := by dsimp [T]; ring
  have hword (α : List (Fin 3)) (hα : α.length ≤ 2) :
      ∫ x, wordDeriv α (fun y => f y * g y) x ^ 2 ≤ 1300 * T := by
    cases α with
    | nil =>
        have hprod : ∀ x, (f x * g x) ^ 2 ≤ Mf ^ 2 * g x ^ 2 := by
          intro x
          exact vorticityDivCurlSmooth_mul_sq_le (hMf x)
        have hbound : ∫ x, (f x * g x) ^ 2 ≤ Mf ^ 2 * ∫ x, g x ^ 2 := by
          have hint := vorticityProducts_integrable_word_sq hfg hfgc []
          have hgint := vorticityProducts_integrable_word_sq hg hgc []
          simpa only [wordDeriv, integral_const_mul] using
            (integral_mono hint (hgint.const_mul _) hprod)
        have hsingle : ∫ x, g x ^ 2 ≤ Hg := by
          simpa only [Hg, wordDeriv] using
            (vorticityProducts_word_integral_le_norm (f := g) (α := []) (by simp))
        simp only [wordDeriv]
        calc
          ∫ x, (f x * g x) ^ 2 ≤ Mf ^ 2 * ∫ x, g x ^ 2 := hbound
          _ ≤ Mf ^ 2 * Hg := by gcongr
          _ ≤ T := le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hHf0)
          _ ≤ 1300 * T := by nlinarith only [hT0]
    | cons j α =>
        cases α with
        | nil =>
            have hdiff (x : Vec3) :
                spatialDeriv (fun y => f y * g y) j x =
                  spatialDeriv f j x * g x + f x * spatialDeriv g j x :=
              spatialDeriv_mul ((hf.differentiable (by simp)) x)
                ((hg.differentiable (by simp)) x) j
            have hpt (x : Vec3) :
                (spatialDeriv (fun y => f y * g y) j x) ^ 2 ≤
                  2 * (Mg ^ 2 * spatialDeriv f j x ^ 2 +
                    Mf ^ 2 * spatialDeriv g j x ^ 2) := by
              rw [hdiff]
              have h1 := vorticityDivCurlSmooth_mul_sq_le (hMg x)
                (v := spatialDeriv f j x)
              have h2 := vorticityDivCurlSmooth_mul_sq_le (hMf x)
                (v := spatialDeriv g j x)
              have hsum := vorticityProducts_sq_two_le
                (spatialDeriv f j x * g x) (f x * spatialDeriv g j x)
              nlinarith only [h1, h2, hsum]
            have hint := vorticityProducts_integrable_word_sq hfg hfgc [j]
            have hfint := vorticityProducts_integrable_word_sq hf hfc [j]
            have hgint := vorticityProducts_integrable_word_sq hg hgc [j]
            have hfint' : Integrable (fun x => spatialDeriv f j x ^ 2) volume := by
              simpa only [wordDeriv] using hfint
            have hgint' : Integrable (fun x => spatialDeriv g j x ^ 2) volume := by
              simpa only [wordDeriv] using hgint
            have hI : ∫ x, (spatialDeriv (fun y => f y * g y) j x) ^ 2 ≤
                2 * (Mg ^ 2 * (∫ x, spatialDeriv f j x ^ 2) +
                  Mf ^ 2 * (∫ x, spatialDeriv g j x ^ 2)) := by
              have hmono := integral_mono
                (show Integrable (fun x =>
                  (spatialDeriv (fun y => f y * g y) j x) ^ 2) volume from by
                  simpa only [wordDeriv] using hint)
                (((hfint'.const_mul _).add (hgint'.const_mul _)).const_mul _) hpt
              have hsum : ∫ x,
                  Mg ^ 2 * spatialDeriv f j x ^ 2 +
                    Mf ^ 2 * spatialDeriv g j x ^ 2 =
                  Mg ^ 2 * (∫ x, spatialDeriv f j x ^ 2) +
                    Mf ^ 2 * (∫ x, spatialDeriv g j x ^ 2) := by
                have h := integral_add (hfint'.const_mul (Mg ^ 2))
                  (hgint'.const_mul (Mf ^ 2))
                simpa only [integral_const_mul] using h
              calc
                _ ≤ ∫ x, 2 * (Mg ^ 2 * spatialDeriv f j x ^ 2 +
                    Mf ^ 2 * spatialDeriv g j x ^ 2) := hmono
                _ = _ := by rw [integral_const_mul, hsum]
            have hIf := mul_le_mul_of_nonneg_left (hfirstF j) (sq_nonneg Mg)
            have hIg := mul_le_mul_of_nonneg_left (hfirstG j) (sq_nonneg Mf)
            simpa only [wordDeriv] using
              (calc
                ∫ x, (spatialDeriv (fun y => f y * g y) j x) ^ 2 ≤
                    2 * (Mg ^ 2 * (∫ x, spatialDeriv f j x ^ 2) +
                      Mf ^ 2 * (∫ x, spatialDeriv g j x ^ 2)) := hI
                _ ≤ 2 * T := by dsimp [T]; linarith only [hIf, hIg]
                _ ≤ 1300 * T := by nlinarith only [hT0])
        | cons k tail =>
            cases tail with
            | nil =>
                have hfirst : spatialDeriv (fun y => f y * g y) j =
                    fun y => spatialDeriv f j y * g y + f y * spatialDeriv g j y := by
                  funext y
                  exact spatialDeriv_mul ((hf.differentiable (by simp)) y)
                    ((hg.differentiable (by simp)) y) j
                have hdf : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv f j) :=
                  contDiff_spatialDeriv_smooth hf j
                have hdg : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) :=
                  contDiff_spatialDeriv_smooth hg j
                have hdiff (x : Vec3) :
                    wordDeriv [j, k] (fun y => f y * g y) x =
                      spatialDeriv (spatialDeriv f j) k x * g x +
                        spatialDeriv f j x * spatialDeriv g k x +
                        spatialDeriv f k x * spatialDeriv g j x +
                        f x * spatialDeriv (spatialDeriv g j) k x := by
                  change spatialDeriv (spatialDeriv (fun y => f y * g y) j) k x = _
                  rw [hfirst]
                  have hadd := spatialDeriv_add
                    (f := fun y => spatialDeriv f j y * g y)
                    (g := fun y => f y * spatialDeriv g j y)
                    (((hdf.differentiable (by simp)) x).mul ((hg.differentiable (by simp)) x))
                    (((hf.differentiable (by simp)) x).mul ((hdg.differentiable (by simp)) x)) k
                  rw [hadd,
                    spatialDeriv_mul ((hdf.differentiable (by simp)) x)
                      ((hg.differentiable (by simp)) x),
                    spatialDeriv_mul ((hf.differentiable (by simp)) x)
                      ((hdg.differentiable (by simp)) x)]
                  ring
                have hApoint (x : Vec3) :
                    spatialDeriv f j x ^ 2 ≤ A x ∧
                    spatialDeriv f k x ^ 2 ≤ A x := by
                  constructor <;> exact Finset.single_le_sum
                    (fun i _ => sq_nonneg (spatialDeriv f i x)) (Finset.mem_univ _)
                have hBpoint (x : Vec3) :
                    spatialDeriv g j x ^ 2 ≤ B x ∧
                    spatialDeriv g k x ^ 2 ≤ B x := by
                  constructor <;> exact Finset.single_le_sum
                    (fun i _ => sq_nonneg (spatialDeriv g i x)) (Finset.mem_univ _)
                have hpt (x : Vec3) :
                    wordDeriv [j, k] (fun y => f y * g y) x ^ 2 ≤
                      4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 +
                        4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2 +
                        8 * A x * B x := by
                  rw [hdiff]
                  have h1 : (spatialDeriv (spatialDeriv f j) k x * g x) ^ 2 ≤
                      Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 := by
                    simpa only [mul_comm] using
                      (vorticityDivCurlSmooth_mul_sq_le (hMg x)
                        (v := spatialDeriv (spatialDeriv f j) k x))
                  have h4 := vorticityDivCurlSmooth_mul_sq_le (hMf x)
                    (v := spatialDeriv (spatialDeriv g j) k x)
                  have h2 : (spatialDeriv f j x * spatialDeriv g k x) ^ 2 ≤
                      A x * B x := by
                    rw [mul_pow]
                    exact mul_le_mul (hApoint x).1 (hBpoint x).2
                      (sq_nonneg _) (by dsimp [A]; positivity)
                  have h3 : (spatialDeriv f k x * spatialDeriv g j x) ^ 2 ≤
                      A x * B x := by
                    rw [mul_pow]
                    exact mul_le_mul (hApoint x).2 (hBpoint x).1
                      (sq_nonneg _) (by dsimp [A]; positivity)
                  have hsum := vorticitySobolevSmooth_four_sq
                    (a := (1 : ℝ)) (b := 1) (c := 1) (d := 1) (M := 1)
                    (p := spatialDeriv (spatialDeriv f j) k x * g x)
                    (q := spatialDeriv f j x * spatialDeriv g k x)
                    (s := spatialDeriv f k x * spatialDeriv g j x)
                    (t := f x * spatialDeriv (spatialDeriv g j) k x)
                    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
                  simp only [one_mul, one_pow] at hsum
                  linarith only [h1, h2, h3, h4, hsum]
                have hint := vorticityProducts_integrable_word_sq hfg hfgc [j, k]
                have hfint := vorticityProducts_integrable_word_sq hf hfc [j, k]
                have hgint := vorticityProducts_integrable_word_sq hg hgc [j, k]
                have hfint' : Integrable
                    (fun x => spatialDeriv (spatialDeriv f j) k x ^ 2) volume := by
                  simpa only [wordDeriv] using hfint
                have hgint' : Integrable
                    (fun x => spatialDeriv (spatialDeriv g j) k x ^ 2) volume := by
                  simpa only [wordDeriv] using hgint
                have hI : ∫ x, wordDeriv [j, k] (fun y => f y * g y) x ^ 2 ≤
                    4 * Mg ^ 2 * (∫ x, spatialDeriv (spatialDeriv f j) k x ^ 2) +
                      4 * Mf ^ 2 * (∫ x, spatialDeriv (spatialDeriv g j) k x ^ 2) +
                      8 * ∫ x, A x * B x := by
                  have hcrossInt' : Integrable (fun x => 8 * A x * B x) volume := by
                    have h : Integrable (fun x => 8 * (A x * B x)) volume :=
                      hcrossInt.const_mul 8
                    convert h using 1
                    funext x
                    ring
                  have hrhsInt : Integrable (fun x =>
                      4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 +
                        4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2 +
                        8 * A x * B x) volume :=
                    ((hfint'.const_mul _).add (hgint'.const_mul _)).add
                      hcrossInt'
                  have hmono := integral_mono hint
                    hrhsInt hpt
                  have heq : ∫ x,
                      4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 +
                        4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2 +
                        8 * A x * B x =
                      4 * Mg ^ 2 * (∫ x, spatialDeriv (spatialDeriv f j) k x ^ 2) +
                        4 * Mf ^ 2 * (∫ x, spatialDeriv (spatialDeriv g j) k x ^ 2) +
                        8 * ∫ x, A x * B x := by
                    have hint12 : Integrable (fun x =>
                        4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 +
                          4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2) volume :=
                      (hfint'.const_mul (4 * Mg ^ 2)).add
                        (hgint'.const_mul (4 * Mf ^ 2))
                    have houter : ∫ x,
                        (4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 +
                          4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2) +
                          8 * A x * B x =
                        (∫ x, 4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 +
                          4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2) +
                          ∫ x, 8 * A x * B x := integral_add hint12 hcrossInt'
                    have hinner : ∫ x,
                        4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2 +
                          4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2 =
                        (∫ x, 4 * Mg ^ 2 * spatialDeriv (spatialDeriv f j) k x ^ 2) +
                          ∫ x, 4 * Mf ^ 2 * spatialDeriv (spatialDeriv g j) k x ^ 2 :=
                      integral_add (hfint'.const_mul _) (hgint'.const_mul _)
                    have hcrossEq : (∫ x, 8 * A x * B x) = 8 * ∫ x, A x * B x := by
                      have h := integral_const_mul (μ := volume) (8 : ℝ)
                        (fun x => A x * B x)
                      convert h using 1
                      congr 1
                      funext x
                      ring
                    rw [houter, hinner, hcrossEq, integral_const_mul, integral_const_mul]
                  exact hmono.trans_eq heq
                have hIf := mul_le_mul_of_nonneg_left (hsecondF j k)
                  (by positivity : 0 ≤ 4 * Mg ^ 2)
                have hIg := mul_le_mul_of_nonneg_left (hsecondG j k)
                  (by positivity : 0 ≤ 4 * Mf ^ 2)
                have hIc := mul_le_mul_of_nonneg_left hcrossT
                  (by norm_num : 0 ≤ (8 : ℝ))
                calc
                  ∫ x, wordDeriv [j, k] (fun y => f y * g y) x ^ 2 ≤
                      4 * Mg ^ 2 * (∫ x, spatialDeriv (spatialDeriv f j) k x ^ 2) +
                        4 * Mf ^ 2 * (∫ x, spatialDeriv (spatialDeriv g j) k x ^ 2) +
                        8 * ∫ x, A x * B x := hI
                  _ ≤ 4 * Mg ^ 2 * Hf + 4 * Mf ^ 2 * Hg + 8 * (162 * T) := by
                    linarith only [hIf, hIg, hIc]
                  _ = 1300 * T := by dsimp [T]; ring
            | cons l tail =>
                simp only [List.length_cons] at hα
                omega
  change (∑ α ∈ sobolevWords 2,
    ∫ x in univ, wordDeriv α (fun y => f y * g y) x ^ 2) ≤ 16900 * T
  simp only [Measure.restrict_univ]
  have hsum := Finset.sum_le_sum
    (s := sobolevWords 2) (fun α hα => hword α (mem_sobolevWords.mp hα))
  calc
    _ ≤ ∑ α ∈ sobolevWords 2, 1300 * T := hsum
    _ = 13 * (1300 * T) := by simp [vorticityProducts_sobolevWords_two_card]
    _ = 16900 * T := by ring

/-- The bilinear order-two product estimate for smooth compactly supported
vector fields (`lem:vorticity-products`). -/
theorem vorticityProducts_H2_smooth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u w : Fin 3 → Vec3 → ℝ) (Mu Mw : ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) → (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) → (∀ i, HasCompactSupport (w i)) →
      (∀ x, Real.sqrt (∑ i, u i x ^ 2) ≤ Mu) →
      (∀ x, Real.sqrt (∑ i, w i x ^ 2) ≤ Mw) →
      ∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ
          (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x)) ≤
        C * (Mu ^ 2 * ∑ i, sobolevNormSqOn 2 univ (fun α => wordDeriv α (w i)) +
          Mw ^ 2 * ∑ i, sobolevNormSqOn 2 univ (fun α => wordDeriv α (u i))) := by
  refine ⟨152100, by norm_num, ?_⟩
  intro u w Mu Mw hu huc hw hwc hMu hMw
  let Su : ℝ := ∑ i : Fin 3, sobolevNormSqOn 2 univ
    (fun α => wordDeriv α (u i))
  let Sw : ℝ := ∑ i : Fin 3, sobolevNormSqOn 2 univ
    (fun α => wordDeriv α (w i))
  let T : ℝ := Mu ^ 2 * Sw + Mw ^ 2 * Su
  have hUnn (i : Fin 3) : 0 ≤ sobolevNormSqOn 2 univ
      (fun α => wordDeriv α (u i)) := by
    dsimp [sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hWnn (i : Fin 3) : 0 ≤ sobolevNormSqOn 2 univ
      (fun α => wordDeriv α (w i)) := by
    dsimp [sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hUle (i : Fin 3) :
      sobolevNormSqOn 2 univ (fun α => wordDeriv α (u i)) ≤ Su :=
    Finset.single_le_sum (fun j _ => hUnn j) (Finset.mem_univ i)
  have hWle (i : Fin 3) :
      sobolevNormSqOn 2 univ (fun α => wordDeriv α (w i)) ≤ Sw :=
    Finset.single_le_sum (fun j _ => hWnn j) (Finset.mem_univ i)
  have huBound (i : Fin 3) (x : Vec3) : |u i x| ≤ Mu := by
    have hsq : u i x ^ 2 ≤ ∑ j : Fin 3, u j x ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j x)) (Finset.mem_univ i)
    exact (Real.abs_le_sqrt hsq).trans (hMu x)
  have hwBound (i : Fin 3) (x : Vec3) : |w i x| ≤ Mw := by
    have hsq : w i x ^ 2 ≤ ∑ j : Fin 3, w j x ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (w j x)) (Finset.mem_univ i)
    exact (Real.abs_le_sqrt hsq).trans (hMw x)
  have hpair (ij : Fin 3 × Fin 3) :
      sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x)) ≤ 16900 * T := by
    have hsc := vorticityProducts_H2_scalar (u ij.1) (w ij.2) Mu Mw
      (hu ij.1) (huc ij.1) (hw ij.2) (hwc ij.2)
      (huBound ij.1) (hwBound ij.2)
    have hleft := mul_le_mul_of_nonneg_left (hWle ij.2) (sq_nonneg Mu)
    have hright := mul_le_mul_of_nonneg_left (hUle ij.1) (sq_nonneg Mw)
    calc
      _ ≤ 16900 * (Mu ^ 2 * sobolevNormSqOn 2 univ
            (fun α => wordDeriv α (w ij.2)) +
          Mw ^ 2 * sobolevNormSqOn 2 univ
            (fun α => wordDeriv α (u ij.1))) := hsc
      _ ≤ 16900 * T := by dsimp [T]; linarith only [hleft, hright]
  change (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ
    (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤ 152100 * T
  calc
    _ ≤ ∑ _ij : Fin 3 × Fin 3, 16900 * T :=
      Finset.sum_le_sum fun ij _ => hpair ij
    _ = 9 * (16900 * T) := by simp
    _ = 152100 * T := by ring

private theorem vorticityProducts_wordDeriv_add
    (α : List (Fin 3)) (f g : Vec3 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    wordDeriv α (fun x => f x + g x) =
      fun x => wordDeriv α f x + wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hdiff : spatialDeriv (fun x => f x + g x) j =
          fun x => spatialDeriv f j x + spatialDeriv g j x := by
        funext x
        exact spatialDeriv_add ((hf.differentiable (by simp)) x)
          ((hg.differentiable (by simp)) x) j
      simp only [wordDeriv, hdiff]
      exact ih (spatialDeriv f j) (spatialDeriv g j)
        (contDiff_spatialDeriv_smooth hf j)
        (contDiff_spatialDeriv_smooth hg j)

private theorem vorticityProducts_H2_add_le
    (f g : Vec3 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    sobolevNormSqOn 2 univ (fun α => wordDeriv α (fun x => f x + g x)) ≤
      2 * (sobolevNormSqOn 2 univ (fun α => wordDeriv α f) +
        sobolevNormSqOn 2 univ (fun α => wordDeriv α g)) := by
  have hfg : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x + g x) := hf.add hg
  have hfgc : HasCompactSupport (fun x => f x + g x) := hfc.add hgc
  have hword (α : List (Fin 3)) :
      ∫ x, wordDeriv α (fun y => f y + g y) x ^ 2 ≤
        2 * ((∫ x, wordDeriv α f x ^ 2) +
          (∫ x, wordDeriv α g x ^ 2)) := by
    have hint := vorticityProducts_integrable_word_sq hfg hfgc α
    have hfint := vorticityProducts_integrable_word_sq hf hfc α
    have hgint := vorticityProducts_integrable_word_sq hg hgc α
    have hpt (x : Vec3) :
        wordDeriv α (fun y => f y + g y) x ^ 2 ≤
          2 * (wordDeriv α f x ^ 2 + wordDeriv α g x ^ 2) := by
      rw [vorticityProducts_wordDeriv_add α f g hf hg]
      exact vorticityProducts_sq_two_le _ _
    have hmono := integral_mono hint ((hfint.add hgint).const_mul 2) hpt
    have heq : ∫ x, 2 * (wordDeriv α f x ^ 2 + wordDeriv α g x ^ 2) =
        2 * ((∫ x, wordDeriv α f x ^ 2) +
          (∫ x, wordDeriv α g x ^ 2)) := by
      rw [integral_const_mul]
      have h := integral_add hfint hgint
      rw [h]
    exact hmono.trans_eq heq
  simp only [sobolevNormSqOn, Measure.restrict_univ]
  calc
    (∑ α ∈ sobolevWords 2,
        ∫ x, wordDeriv α (fun y => f y + g y) x ^ 2) ≤
      ∑ α ∈ sobolevWords 2,
        2 * ((∫ x, wordDeriv α f x ^ 2) +
          (∫ x, wordDeriv α g x ^ 2)) :=
      Finset.sum_le_sum fun α _ => hword α
    _ = 2 * ((∑ α ∈ sobolevWords 2, ∫ x, wordDeriv α f x ^ 2) +
          (∑ α ∈ sobolevWords 2, ∫ x, wordDeriv α g x ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

private theorem vorticityProducts_H2_deriv_le_H3
    (f : Vec3 → ℝ) (j : Fin 3) :
    sobolevNormSqOn 2 univ (fun α => wordDeriv α (spatialDeriv f j)) ≤
      13 * sobolevNormSqOn 3 univ (fun α => wordDeriv α f) := by
  let N : ℝ := sobolevNormSqOn 3 univ (fun α => wordDeriv α f)
  have hterm (α : List (Fin 3)) (hα : α ∈ sobolevWords 2) :
      ∫ x, wordDeriv α (spatialDeriv f j) x ^ 2 ≤ N := by
    have hlen := mem_sobolevWords.mp hα
    have hsingle : ∫ x, wordDeriv (j :: α) f x ^ 2 ≤ N := by
      dsimp [N, sobolevNormSqOn]
      simp only [Measure.restrict_univ]
      exact Finset.single_le_sum
        (f := fun β : List (Fin 3) => ∫ x, wordDeriv β f x ^ 2)
        (s := sobolevWords 3)
        (fun β _ => integral_nonneg fun x => sq_nonneg _)
        (mem_sobolevWords.mpr (by simp only [List.length_cons]; omega))
    exact hsingle
  change (∑ α ∈ sobolevWords 2,
    ∫ x in univ, wordDeriv α (spatialDeriv f j) x ^ 2) ≤ 13 * N
  simp only [Measure.restrict_univ]
  calc
    (∑ α ∈ sobolevWords 2, ∫ x, wordDeriv α (spatialDeriv f j) x ^ 2) ≤
      ∑ _α ∈ sobolevWords 2, N := Finset.sum_le_sum hterm
    _ = 13 * N := by simp [vorticityProducts_sobolevWords_two_card]

private theorem vorticityProducts_H2_le_H3 (f : Vec3 → ℝ) :
    sobolevNormSqOn 2 univ (fun α => wordDeriv α f) ≤
      13 * sobolevNormSqOn 3 univ (fun α => wordDeriv α f) := by
  let N : ℝ := sobolevNormSqOn 3 univ (fun α => wordDeriv α f)
  have hterm (α : List (Fin 3)) (hα : α ∈ sobolevWords 2) :
      ∫ x, wordDeriv α f x ^ 2 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    simp only [Measure.restrict_univ]
    exact Finset.single_le_sum
      (f := fun β : List (Fin 3) => ∫ x, wordDeriv β f x ^ 2)
      (s := sobolevWords 3)
      (fun β _ => integral_nonneg fun x => sq_nonneg _)
      (mem_sobolevWords.mpr (by have := mem_sobolevWords.mp hα; omega))
  change (∑ α ∈ sobolevWords 2,
    ∫ x in univ, wordDeriv α f x ^ 2) ≤ 13 * N
  simp only [Measure.restrict_univ]
  calc
    (∑ α ∈ sobolevWords 2, ∫ x, wordDeriv α f x ^ 2) ≤
      ∑ _α ∈ sobolevWords 2, N := Finset.sum_le_sum hterm
    _ = 13 * N := by simp [vorticityProducts_sobolevWords_two_card]

private theorem vorticityProducts_H2_embedding_product
    (C : ℝ)
    (hC : ∀ h : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h →
      ∀ x, |h x| ≤ C * Real.sqrt
        (sobolevNormSqOn 2 univ (fun α => wordDeriv α h)))
    (f g : Vec3 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    sobolevNormSqOn 2 univ (fun α => wordDeriv α (fun x => f x * g x)) ≤
      33800 * C ^ 2 * sobolevNormSqOn 2 univ (fun α => wordDeriv α f) *
        sobolevNormSqOn 2 univ (fun α => wordDeriv α g) := by
  let Hf : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α f)
  let Hg : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α g)
  have hHf0 : 0 ≤ Hf := by
    dsimp [Hf, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hHg0 : 0 ≤ Hg := by
    dsimp [Hg, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hsc := vorticityProducts_H2_scalar f g
    (C * Real.sqrt Hf) (C * Real.sqrt Hg) hf hfc hg hgc
    (hC f hf hfc) (hC g hg hgc)
  have hfsq : (C * Real.sqrt Hf) ^ 2 = C ^ 2 * Hf := by
    rw [mul_pow, Real.sq_sqrt hHf0]
  have hgsq : (C * Real.sqrt Hg) ^ 2 = C ^ 2 * Hg := by
    rw [mul_pow, Real.sq_sqrt hHg0]
  calc
    _ ≤ 16900 * ((C * Real.sqrt Hf) ^ 2 * Hg +
        (C * Real.sqrt Hg) ^ 2 * Hf) := hsc
    _ = 33800 * C ^ 2 * Hf * Hg := by rw [hfsq, hgsq]; ring

private theorem vorticityProducts_sobolevWords_three_card :
    (sobolevWords 3).card = 40 := by decide

private theorem vorticityProducts_H3_scalar
    (C : ℝ)
    (hC : ∀ h : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h →
      ∀ x, |h x| ≤ C * Real.sqrt
        (sobolevNormSqOn 2 univ (fun α => wordDeriv α h)))
    (f g : Vec3 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    sobolevNormSqOn 3 univ (fun α => wordDeriv α (fun x => f x * g x)) ≤
      35152000 * C ^ 2 *
        (sobolevNormSqOn 3 univ (fun α => wordDeriv α f) *
            sobolevNormSqOn 2 univ (fun α => wordDeriv α g) +
          sobolevNormSqOn 2 univ (fun α => wordDeriv α f) *
            sobolevNormSqOn 3 univ (fun α => wordDeriv α g)) := by
  let F₂ : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α f)
  let G₂ : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α g)
  let F₃ : ℝ := sobolevNormSqOn 3 univ (fun α => wordDeriv α f)
  let G₃ : ℝ := sobolevNormSqOn 3 univ (fun α => wordDeriv α g)
  let T : ℝ := F₃ * G₂ + F₂ * G₃
  have hF₂0 : 0 ≤ F₂ := by
    dsimp [F₂, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hG₂0 : 0 ≤ G₂ := by
    dsimp [G₂, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hF₃0 : 0 ≤ F₃ := by
    dsimp [F₃, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hG₃0 : 0 ≤ G₃ := by
    dsimp [G₃, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hF₂le : F₂ ≤ 13 * F₃ := vorticityProducts_H2_le_H3 f
  have hG₂le : G₂ ≤ 13 * G₃ := vorticityProducts_H2_le_H3 g
  have hfg : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * g x) := hf.mul hg
  have hfgc : HasCompactSupport (fun x => f x * g x) := hfc.mul_right
  have hbase := vorticityProducts_H2_embedding_product C hC f g hf hfc hg hgc
  have hword (α : List (Fin 3)) (hα : α ∈ sobolevWords 3) :
      ∫ x, wordDeriv α (fun y => f y * g y) x ^ 2 ≤ 878800 * C ^ 2 * T := by
    cases α with
    | nil =>
        have h0 : ∫ x, (f x * g x) ^ 2 ≤
            sobolevNormSqOn 2 univ (fun β => wordDeriv β (fun y => f y * g y)) := by
          simpa only [wordDeriv] using
            (vorticityProducts_word_integral_le_norm
              (f := fun y => f y * g y) (α := []) (by simp))
        have hmul := mul_le_mul_of_nonneg_right hF₂le hG₂0
        have hterm : F₂ * G₂ ≤ 13 * F₃ * G₂ := hmul
        have hterm' : 13 * F₃ * G₂ ≤ 13 * T := by
          dsimp [T]
          have h : 0 ≤ F₂ * G₃ := mul_nonneg hF₂0 hG₃0
          nlinarith only [h]
        simp only [wordDeriv]
        calc
          ∫ x, (f x * g x) ^ 2 ≤
              sobolevNormSqOn 2 univ (fun β => wordDeriv β (fun y => f y * g y)) := h0
          _ ≤ 33800 * C ^ 2 * F₂ * G₂ := hbase
          _ = (33800 * C ^ 2) * (F₂ * G₂) := by ring
          _ ≤ (33800 * C ^ 2) * (13 * F₃ * G₂) :=
            mul_le_mul_of_nonneg_left hterm (by positivity)
          _ ≤ 33800 * C ^ 2 * (13 * T) :=
            mul_le_mul_of_nonneg_left hterm' (by positivity)
          _ ≤ 878800 * C ^ 2 * T := by
            have hct : 0 ≤ C ^ 2 * T := mul_nonneg (sq_nonneg _) hT0
            nlinarith only [hct]
    | cons j β =>
        have hβ : β.length ≤ 2 := by
          have hlen := mem_sobolevWords.mp hα
          simp only [List.length_cons] at hlen
          omega
        let df : Vec3 → ℝ := spatialDeriv f j
        let dg : Vec3 → ℝ := spatialDeriv g j
        have hdf : ContDiff ℝ (⊤ : ℕ∞) df := contDiff_spatialDeriv_smooth hf j
        have hdg : ContDiff ℝ (⊤ : ℕ∞) dg := contDiff_spatialDeriv_smooth hg j
        have hdfc : HasCompactSupport df :=
          hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)
        have hdgc : HasCompactSupport dg :=
          hgc.fderiv_apply (𝕜 := ℝ) (basisVec j)
        let Fd₂ : ℝ := sobolevNormSqOn 2 univ (fun γ => wordDeriv γ df)
        let Gd₂ : ℝ := sobolevNormSqOn 2 univ (fun γ => wordDeriv γ dg)
        have hFd₂le : Fd₂ ≤ 13 * F₃ := vorticityProducts_H2_deriv_le_H3 f j
        have hGd₂le : Gd₂ ≤ 13 * G₃ := vorticityProducts_H2_deriv_le_H3 g j
        have hfirst : spatialDeriv (fun y => f y * g y) j =
            fun y => df y * g y + f y * dg y := by
          funext y
          exact spatialDeriv_mul ((hf.differentiable (by simp)) y)
            ((hg.differentiable (by simp)) y) j
        have hterm : ∫ x, wordDeriv (j :: β) (fun y => f y * g y) x ^ 2 ≤
            sobolevNormSqOn 2 univ (fun γ => wordDeriv γ
              (fun y => df y * g y + f y * dg y)) := by
          simpa only [wordDeriv, hfirst] using
            (vorticityProducts_word_integral_le_norm
              (f := fun y => df y * g y + f y * dg y) (α := β) hβ)
        have hfg1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => df y * g y) := hdf.mul hg
        have hfg1c : HasCompactSupport (fun y => df y * g y) := hdfc.mul_right
        have hfg2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => f y * dg y) := hf.mul hdg
        have hfg2c : HasCompactSupport (fun y => f y * dg y) := hfc.mul_right
        have hadd := vorticityProducts_H2_add_le
          (fun y => df y * g y) (fun y => f y * dg y) hfg1 hfg1c hfg2 hfg2c
        have hprod1 := vorticityProducts_H2_embedding_product C hC df g
          hdf hdfc hg hgc
        have hprod2 := vorticityProducts_H2_embedding_product C hC f dg
          hf hfc hdg hdgc
        have hFd₂0 : 0 ≤ Fd₂ := by
          dsimp [Fd₂, sobolevNormSqOn]
          exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
        have hGd₂0 : 0 ≤ Gd₂ := by
          dsimp [Gd₂, sobolevNormSqOn]
          exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
        have hbound1 : Fd₂ * G₂ ≤ 13 * F₃ * G₂ :=
          mul_le_mul_of_nonneg_right hFd₂le hG₂0
        have hbound2 : F₂ * Gd₂ ≤ F₂ * (13 * G₃) :=
          mul_le_mul_of_nonneg_left hGd₂le hF₂0
        have hC₂0 : 0 ≤ C ^ 2 := sq_nonneg _
        have hsum : Fd₂ * G₂ + F₂ * Gd₂ ≤ 13 * T := by
          dsimp [T]
          linarith only [hbound1, hbound2]
        calc
          ∫ x, wordDeriv (j :: β) (fun y => f y * g y) x ^ 2 ≤
              sobolevNormSqOn 2 univ (fun γ => wordDeriv γ
                (fun y => df y * g y + f y * dg y)) := hterm
          _ ≤ 2 * (sobolevNormSqOn 2 univ (fun γ => wordDeriv γ
                (fun y => df y * g y)) +
              sobolevNormSqOn 2 univ (fun γ => wordDeriv γ
                (fun y => f y * dg y))) := hadd
          _ ≤ 2 * (33800 * C ^ 2 * Fd₂ * G₂ +
              33800 * C ^ 2 * F₂ * Gd₂) := by gcongr
          _ = 67600 * C ^ 2 * (Fd₂ * G₂ + F₂ * Gd₂) := by ring
          _ ≤ 67600 * C ^ 2 * (13 * T) := by gcongr
          _ = 878800 * C ^ 2 * T := by ring
  change (∑ α ∈ sobolevWords 3,
    ∫ x in univ, wordDeriv α (fun y => f y * g y) x ^ 2) ≤
      35152000 * C ^ 2 * T
  simp only [Measure.restrict_univ]
  calc
    _ ≤ ∑ _α ∈ sobolevWords 3, 878800 * C ^ 2 * T :=
      Finset.sum_le_sum hword
    _ = 40 * (878800 * C ^ 2 * T) := by
      simp [vorticityProducts_sobolevWords_three_card]
    _ = 35152000 * C ^ 2 * T := by ring

/-- The bilinear order-three product estimate for smooth compactly supported
vector fields (`lem:vorticity-products`). -/
theorem vorticityProducts_H3_smooth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) → (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) → (∀ i, HasCompactSupport (w i)) →
      ∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 3 univ
          (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x)) ≤
        C * ((∑ i, sobolevNormSqOn 2 univ (fun α => wordDeriv α (u i))) *
              (∑ i, sobolevNormSqOn 3 univ (fun α => wordDeriv α (w i))) +
            (∑ i, sobolevNormSqOn 3 univ (fun α => wordDeriv α (u i))) *
              (∑ i, sobolevNormSqOn 2 univ (fun α => wordDeriv α (w i)))) := by
  obtain ⟨C₀, hC₀, hEmbed⟩ := abs_le_sobolevTwo_smooth
  refine ⟨316368000 * C₀ ^ 2, by positivity, ?_⟩
  intro u w hu huc hw hwc
  let U₂ : ℝ := ∑ i : Fin 3, sobolevNormSqOn 2 univ
    (fun α => wordDeriv α (u i))
  let U₃ : ℝ := ∑ i : Fin 3, sobolevNormSqOn 3 univ
    (fun α => wordDeriv α (u i))
  let W₂ : ℝ := ∑ i : Fin 3, sobolevNormSqOn 2 univ
    (fun α => wordDeriv α (w i))
  let W₃ : ℝ := ∑ i : Fin 3, sobolevNormSqOn 3 univ
    (fun α => wordDeriv α (w i))
  let T : ℝ := U₂ * W₃ + U₃ * W₂
  have hNnn (m : ℕ) (f : Vec3 → ℝ) :
      0 ≤ sobolevNormSqOn m univ (fun α => wordDeriv α f) := by
    dsimp [sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hU₂nn (i : Fin 3) : 0 ≤ sobolevNormSqOn 2 univ
      (fun α => wordDeriv α (u i)) := hNnn 2 (u i)
  have hU₃nn (i : Fin 3) : 0 ≤ sobolevNormSqOn 3 univ
      (fun α => wordDeriv α (u i)) := hNnn 3 (u i)
  have hW₂nn (i : Fin 3) : 0 ≤ sobolevNormSqOn 2 univ
      (fun α => wordDeriv α (w i)) := hNnn 2 (w i)
  have hW₃nn (i : Fin 3) : 0 ≤ sobolevNormSqOn 3 univ
      (fun α => wordDeriv α (w i)) := hNnn 3 (w i)
  have hU₂0 : 0 ≤ U₂ := Finset.sum_nonneg fun i _ => hU₂nn i
  have hU₃0 : 0 ≤ U₃ := Finset.sum_nonneg fun i _ => hU₃nn i
  have hU₂le (i : Fin 3) :
      sobolevNormSqOn 2 univ (fun α => wordDeriv α (u i)) ≤ U₂ :=
    Finset.single_le_sum (fun j _ => hU₂nn j) (Finset.mem_univ i)
  have hU₃le (i : Fin 3) :
      sobolevNormSqOn 3 univ (fun α => wordDeriv α (u i)) ≤ U₃ :=
    Finset.single_le_sum (fun j _ => hU₃nn j) (Finset.mem_univ i)
  have hW₂le (i : Fin 3) :
      sobolevNormSqOn 2 univ (fun α => wordDeriv α (w i)) ≤ W₂ :=
    Finset.single_le_sum (fun j _ => hW₂nn j) (Finset.mem_univ i)
  have hW₃le (i : Fin 3) :
      sobolevNormSqOn 3 univ (fun α => wordDeriv α (w i)) ≤ W₃ :=
    Finset.single_le_sum (fun j _ => hW₃nn j) (Finset.mem_univ i)
  have hpair (ij : Fin 3 × Fin 3) :
      sobolevNormSqOn 3 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x)) ≤
          35152000 * C₀ ^ 2 * T := by
    have hs := vorticityProducts_H3_scalar C₀ hEmbed
      (u ij.1) (w ij.2) (hu ij.1) (huc ij.1) (hw ij.2) (hwc ij.2)
    have hfirst :
        sobolevNormSqOn 3 univ (fun α => wordDeriv α (u ij.1)) *
          sobolevNormSqOn 2 univ (fun α => wordDeriv α (w ij.2)) ≤ U₃ * W₂ := by
      exact mul_le_mul (hU₃le ij.1) (hW₂le ij.2) (hW₂nn ij.2) hU₃0
    have hsecond :
        sobolevNormSqOn 2 univ (fun α => wordDeriv α (u ij.1)) *
          sobolevNormSqOn 3 univ (fun α => wordDeriv α (w ij.2)) ≤ U₂ * W₃ := by
      exact mul_le_mul (hU₂le ij.1) (hW₃le ij.2) (hW₃nn ij.2) hU₂0
    have hsum :
        sobolevNormSqOn 3 univ (fun α => wordDeriv α (u ij.1)) *
            sobolevNormSqOn 2 univ (fun α => wordDeriv α (w ij.2)) +
          sobolevNormSqOn 2 univ (fun α => wordDeriv α (u ij.1)) *
            sobolevNormSqOn 3 univ (fun α => wordDeriv α (w ij.2)) ≤ T := by
      dsimp [T]
      linarith only [hfirst, hsecond]
    calc
      _ ≤ 35152000 * C₀ ^ 2 *
          (sobolevNormSqOn 3 univ (fun α => wordDeriv α (u ij.1)) *
              sobolevNormSqOn 2 univ (fun α => wordDeriv α (w ij.2)) +
            sobolevNormSqOn 2 univ (fun α => wordDeriv α (u ij.1)) *
              sobolevNormSqOn 3 univ (fun α => wordDeriv α (w ij.2))) := hs
      _ ≤ 35152000 * C₀ ^ 2 * T :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
  change (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 3 univ
    (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
      316368000 * C₀ ^ 2 * T
  calc
    _ ≤ ∑ _ij : Fin 3 × Fin 3, 35152000 * C₀ ^ 2 * T :=
      Finset.sum_le_sum fun ij _ => hpair ij
    _ = 9 * (35152000 * C₀ ^ 2 * T) := by simp
    _ = 316368000 * C₀ ^ 2 * T := by ring

end ESS
