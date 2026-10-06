/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliIdentity
public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliProductCutoff
public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliAbsorption
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolev
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevSupport
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local energy estimate for a parabolic differential inequality

This file proves the estimate in `lem:caccioppoli`.
-/

public section

open CKN CKN.Foundation.Parabolic Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace ESS

/-- The local energy estimate for a vector field satisfying a backward parabolic
differential inequality (`lem:caccioppoli`). The integrals are real Bochner
integrals; the stated weak derivative and square-integrability hypotheses make
their integrands integrable on the indicated cylinders. -/
theorem caccioppoli
    (x : Vec3) (t r c₁ : ℝ) (hr : 0 < r) (hc₁ : 0 ≤ c₁)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (vec3Ball x (2 * r)) (Ioo t (t + 4 * r ^ 2))
      w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x (2 * r)) (Ioo t (t + 4 * r ^ 2)),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball x (2 * r)) (Ioo t (t + 4 * r ^ 2)))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (vec3EuclideanNorm (w z) + Real.sqrt (spatialGradientSq w Dw z))) :
    (∫ z in spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)),
      spatialGradientSq w Dw z ∂(volume : Measure ParabolicPoint)) ≤
      256 * (1 + c₁ ^ 2 + 1 / r ^ 2) *
        (∫ z in spaceTimeSet (vec3Ball x (2 * r)) (Ioo t (t + 4 * r ^ 2)),
          (vec3EuclideanNorm (w z)) ^ 2 ∂(volume : Measure ParabolicPoint)) := by
  classical
  let Ω : Set Vec3 := vec3Ball x (2 * r)
  let I : Set ℝ := Ioo t (t + 4 * r ^ 2)
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let V : Set (Vec3 × ℝ) := vec3Ball x r ×ˢ Ioo t (t + r ^ 2)
  let W : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
  let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
  let G : Vec3 × ℝ → ℝ := fun q => ∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2
  have hΩopen : IsOpen Ω := by
    simpa [Ω] using isOpen_vec3Ball x (2 * r)
  have hIopen : IsOpen I := by
    exact isOpen_Ioo
  have hUopen : IsOpen U := hΩopen.prod hIopen
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hVmeas : MeasurableSet V := by
    exact (vec3Ball_measurable x r).prod measurableSet_Ioo
  have hL2' : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    simpa [Ω, I] using hL2
  have hdata := zeroExtend_spaceTimeData_memLp hΩopen hIopen hderiv hL2'
  have hWfun : W = zeroExtendField U
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U <;> simp [W, zeroExtendField, hq]
  have hDfun : D = zeroExtendField U
      (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U <;> simp [D, zeroExtendField, hq]
  have hWdata : MemLp W 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hWfun]
    exact hdata.1
  have hDdata : MemLp D 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hDfun]
    exact hdata.2.1
  have hWnorm : MemLp (fun q => vec3EuclideanNorm (W q)) 2
      (volume : Measure (Vec3 × ℝ)) := by
    apply hWdata.norm.of_nnnorm_le_mul
      (continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hWdata.aestronglyMeasurable)
    filter_upwards [] with q
    have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    have hreal : vec3EuclideanNorm (W q) ≤ 2 * ‖W q‖ := by
      calc
        vec3EuclideanNorm (W q) ≤ Real.sqrt 3 * ‖W q‖ :=
          vec3EuclideanNorm_le_sqrt_three_mul_norm _
        _ ≤ 2 * ‖W q‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    have hreal' : (‖vec3EuclideanNorm (W q)‖₊ : ℝ) ≤
        2 * (‖‖W q‖‖₊ : ℝ) := by
      simpa only [coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (vec3EuclideanNorm_nonneg _),
        abs_of_nonneg (norm_nonneg _)] using hreal
    exact_mod_cast hreal'
  have hDcomp (i j : Fin 3) : MemLp (fun q => D q i j) 2
      (volume : Measure (Vec3 × ℝ)) :=
    memLp_pi_component (memLp_pi_component hDdata i) j
  have hGint : Integrable G (volume : Measure (Vec3 × ℝ)) := by
    change Integrable (fun q => ∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2) _
    exact integrable_finsetSum Finset.univ fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => (hDcomp i j).integrable_sq
  have hGnonneg (q : Vec3 × ℝ) : 0 ≤ G q := by
    dsimp [G]
    positivity
  have hWsqInt : Integrable (fun q => (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)) := hWnorm.integrable_sq
  have hcoreSubOuter : V ⊆ U := by
    intro q hq
    have hx : q.1 ∈ vec3Ball x (2 * r) :=
      vec3Ball_mono (by nlinarith only [hr]) hq.1
    have ht : q.2 ∈ Ioo t (t + 4 * r ^ 2) := by
      constructor
      · exact hq.2.1
      · have hrSq : r ^ 2 ≤ 4 * r ^ 2 := by nlinarith only [sq_nonneg r]
        exact lt_of_lt_of_le hq.2.2 (by nlinarith only [hrSq])
    exact ⟨hx, ht⟩
  have hGcoreInt : IntegrableOn G V (volume : Measure (Vec3 × ℝ)) :=
    hGint.integrableOn.mono_set hcoreSubOuter
  have himageCore : parabolicHomeomorph ''
      spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)) = V := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hq
      exact ⟨parabolicHomeomorph.symm q, hq,
        parabolicHomeomorph.apply_symm_apply q⟩
  have hcoreComposed : IntegrableOn
      (fun p : ParabolicPoint => G (parabolicHomeomorph p))
      (spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)))
      (volume : Measure ParabolicPoint) := by
    apply (parabolicHomeomorph_measurePreserving.integrableOn_image
      parabolicHomeomorph.measurableEmbedding (f := G)
      (s := spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)))).mp
    simpa [himageCore] using hGcoreInt
  have hpointCast (p : ParabolicPoint) : ((p.1, p.2) : ParabolicPoint) = p := by
    change parabolicHomeomorph.symm (p.1, p.2) = p
    rw [← parabolicHomeomorph_apply]
    exact parabolicHomeomorph.left_inv p
  have hcoreEqOn : EqOn
      (fun p : ParabolicPoint => G (parabolicHomeomorph p))
      (fun p => spatialGradientSq w Dw p)
      (spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2))) := by
    intro p hp
    change p.1 ∈ vec3Ball x r ∧ p.2 ∈ Ioo t (t + r ^ 2) at hp
    have hq : parabolicHomeomorph p ∈ U := by
      change (parabolicHomeomorph p).1 ∈ Ω ∧ (parabolicHomeomorph p).2 ∈ I
      simpa only [parabolicHomeomorph_apply] using
        ⟨vec3Ball_mono (by nlinarith only [hr]) hp.1,
          ⟨hp.2.1,
            lt_of_lt_of_le hp.2.2 (by nlinarith only [sq_nonneg r])⟩⟩
    have hDval (i j : Fin 3) :
        D (parabolicHomeomorph p) i j = Dw p i j := by
      change (U.indicator (fun y => Dw (parabolicHomeomorph.symm y))
        (parabolicHomeomorph p)) i j = Dw p i j
      rw [Set.indicator_of_mem hq]
      simp
      rw [hpointCast p]
    change G (parabolicHomeomorph p) = spatialGradientSq w Dw p
    simp only [G, hDval, spatialGradientSq]
  have hcoreIntegrable : IntegrableOn
      (fun p : ParabolicPoint => spatialGradientSq w Dw p)
      (spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)))
      (volume : Measure ParabolicPoint) :=
    hcoreComposed.congr_fun hcoreEqOn
      ((isOpen_spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2))
      (by exact isOpen_vec3Ball x r) isOpen_Ioo).measurableSet)
  have himageOuter : parabolicHomeomorph '' spaceTimeSet Ω I = U := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hq
      exact ⟨parabolicHomeomorph.symm q, hq,
        parabolicHomeomorph.apply_symm_apply q⟩
  have houterComposed : IntegrableOn
      (fun p : ParabolicPoint => (vec3EuclideanNorm (W (parabolicHomeomorph p))) ^ 2)
      (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) := by
    apply (parabolicHomeomorph_measurePreserving.integrableOn_image
      parabolicHomeomorph.measurableEmbedding
      (f := fun q : Vec3 × ℝ => (vec3EuclideanNorm (W q)) ^ 2)
      (s := spaceTimeSet Ω I)).mp
    simpa [himageOuter] using hWsqInt.integrableOn
  have houterEqOn : EqOn
      (fun p : ParabolicPoint => (vec3EuclideanNorm (W (parabolicHomeomorph p))) ^ 2)
      (fun p => (vec3EuclideanNorm (w p)) ^ 2) (spaceTimeSet Ω I) := by
    intro p hp
    change p.1 ∈ Ω ∧ p.2 ∈ I at hp
    have hq : parabolicHomeomorph p ∈ U := by
      change (parabolicHomeomorph p).1 ∈ Ω ∧ (parabolicHomeomorph p).2 ∈ I
      simpa only [parabolicHomeomorph_apply] using hp
    have hWval : W (parabolicHomeomorph p) = w p := by
      change U.indicator (fun y => w (parabolicHomeomorph.symm y))
        (parabolicHomeomorph p) = w p
      rw [Set.indicator_of_mem hq]
      simp
      rw [hpointCast p]
    change (vec3EuclideanNorm (W (parabolicHomeomorph p))) ^ 2 =
      (vec3EuclideanNorm (w p)) ^ 2
    rw [hWval]
  have houterIntegrable : IntegrableOn
      (fun p : ParabolicPoint => (vec3EuclideanNorm (w p)) ^ 2)
      (spaceTimeSet Ω I) (volume : Measure ParabolicPoint) :=
    houterComposed.congr_fun houterEqOn
      ((isOpen_spaceTimeSet Ω I hΩopen hIopen).measurableSet)
  have houterProduct :
      (∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (w z)) ^ 2
        ∂(volume : Measure ParabolicPoint)) =
      ∫ q in U, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    calc
      _ = ∫ q in U, (vec3EuclideanNorm (w (parabolicHomeomorph.symm q))) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := setIntegral_parabolic_to_product
      _ = ∫ q in U, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ)) := by
        apply setIntegral_congr_ae hUmeas
        filter_upwards [] with q hq
        simp [W, U, hq]
  have houterGlobal :
      (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q in U, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ)) := by
    have hfun : (fun q : Vec3 × ℝ => (vec3EuclideanNorm (W q)) ^ 2) =
        U.indicator (fun q => (vec3EuclideanNorm (W q)) ^ 2) := by
      funext q
      by_cases hq : q ∈ U <;> simp [W, U, hq, vec3EuclideanNorm]
    calc
      _ = ∫ q : Vec3 × ℝ, U.indicator
          (fun q => (vec3EuclideanNorm (W q)) ^ 2) q
          ∂(volume : Measure (Vec3 × ℝ)) := by
        congr 1
      _ = _ := integral_indicator hUmeas
  have houterGlobalEq :
      (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (w z)) ^ 2
        ∂(volume : Measure ParabolicPoint) := houterGlobal.trans houterProduct.symm
  have hCsp : 0 ≤ 4 * (400 / 99 : ℝ) ^ 2 := by positivity
  let Csp : ℝ := 4 * (400 / 99 : ℝ) ^ 2
  let Ctime : ℝ := 1600 / 199
  have hcoefConst : 2 * (Csp + Ctime / 2) ≤ 256 := by
    norm_num [Csp, Ctime]
  have hradcoef : 2 * (Csp + Ctime / 2) / r ^ 2 ≤ 256 / r ^ 2 := by
    have hinv : 0 ≤ 1 / r ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hcoefConst hinv
    calc
      2 * (Csp + Ctime / 2) / r ^ 2 =
          (2 * (Csp + Ctime / 2)) * (1 / r ^ 2) := by ring
      _ ≤ 256 * (1 / r ^ 2) := hmul
      _ = 256 / r ^ 2 := by ring
  have hcoefBound :
      2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) ≤
        256 * (1 + c₁ ^ 2 + 1 / r ^ 2) := by
    have hlinear : 2 * c₁ ≤ 1 + c₁ ^ 2 := by
      nlinarith only [sq_nonneg (c₁ - 1)]
    have hcSq : 0 ≤ c₁ ^ 2 := sq_nonneg c₁
    have hrad := hradcoef
    have hfirst : 2 * (c₁ + c₁ ^ 2) ≤ 256 * (1 + c₁ ^ 2) := by
      nlinarith only [hlinear, hcSq]
    calc
      2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) =
          2 * (c₁ + c₁ ^ 2) + 2 * (Csp + Ctime / 2) / r ^ 2 := by ring
      _ ≤ 256 * (1 + c₁ ^ 2) + 256 / r ^ 2 := add_le_add hfirst hrad
      _ = 256 * (1 + c₁ ^ 2 + 1 / r ^ 2) := by ring
  have houterNonneg : 0 ≤
      (∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (w z)) ^ 2
        ∂(volume : Measure ParabolicPoint)) := by
    exact setIntegral_nonneg (isOpen_spaceTimeSet Ω I hΩopen hIopen).measurableSet
      fun z hz => sq_nonneg (vec3EuclideanNorm (w z))
  let ε : ℕ → ℝ := fun n => r ^ 2 / (16 * ((n : ℝ) + 1))
  let A : ℕ → Set (Vec3 × ℝ) := fun n =>
    vec3Ball x r ×ˢ Ioo (t + 2 * ε n) (t + r ^ 2)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεsmall (n : ℕ) : 4 * ε n < r ^ 2 := by
    change 4 * (r ^ 2 / (16 * ((n : ℝ) + 1))) < r ^ 2
    have hden : 0 < 16 * ((n : ℝ) + 1) := by positivity
    have hden' : 4 < 16 * ((n : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith only [hn]
    have hmult : 4 * r ^ 2 < r ^ 2 * (16 * ((n : ℝ) + 1)) := by
      calc
        4 * r ^ 2 < (16 * ((n : ℝ) + 1)) * r ^ 2 :=
          mul_lt_mul_of_pos_right hden' (sq_pos_of_pos hr)
        _ = _ := by ring
    calc
      4 * (r ^ 2 / (16 * ((n : ℝ) + 1))) =
          (4 * r ^ 2) / (16 * ((n : ℝ) + 1)) := by ring
      _ < r ^ 2 := (div_lt_iff₀ hden).2 hmult
  have hAsub (n : ℕ) : A n ⊆ V := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    constructor
    · have heps := hεpos n
      exact lt_trans (by nlinarith only [heps]) hq.2.1
    · exact hq.2.2
  have hAmeas (n : ℕ) : MeasurableSet (A n) := by
    exact (vec3Ball_measurable x r).prod measurableSet_Ioo
  have hAmono (n : ℕ) : A n ⊆ A (n + 1) := by
    intro q hq
    have hden : 16 * ((n : ℝ) + 1) ≤ 16 * (((n + 1 : ℕ) : ℝ) + 1) := by
      norm_num
    have hprod := mul_le_mul_of_nonneg_left hden (sq_nonneg r)
    have hεmono : ε (n + 1) ≤ ε n := by
      dsimp [ε]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hprod]
    refine ⟨hq.1, ?_⟩
    constructor
    · have hthreshold : t + 2 * ε (n + 1) ≤ t + 2 * ε n := by
        nlinarith only [hεmono]
      exact lt_of_le_of_lt hthreshold hq.2.1
    · exact hq.2.2
  have hAcover : ∀ q ∈ V, ∃ n, q ∈ A n := by
    intro q hq
    have hgap : 0 < q.2 - t := by linarith only [hq.2.1]
    obtain ⟨n, hn⟩ := exists_nat_gt (r ^ 2 / (8 * (q.2 - t)))
    have hden : 0 < 8 * (q.2 - t) := by positivity
    have hratio : r ^ 2 < 8 * (q.2 - t) * n := by
      have h := (div_lt_iff₀ hden).1 hn
      nlinarith only [h]
    have hden' : 0 < 8 * ((n : ℝ) + 1) := by positivity
    have hsmall : 2 * ε n < q.2 - t := by
      change 2 * (r ^ 2 / (16 * ((n : ℝ) + 1))) < q.2 - t
      rw [show 2 * (r ^ 2 / (16 * ((n : ℝ) + 1))) =
        r ^ 2 / (8 * ((n : ℝ) + 1)) by field_simp; ring]
      rw [div_lt_iff₀ hden']
      have hnle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith only
      have hmul := mul_le_mul_of_nonneg_left hnle (le_of_lt hgap)
      have hbound : 8 * (q.2 - t) * n ≤
          (q.2 - t) * (8 * ((n : ℝ) + 1)) := by nlinarith only [hmul]
      exact lt_of_lt_of_le hratio hbound
    refine ⟨n, ?_⟩
    refine ⟨hq.1, ?_⟩
    constructor
    · dsimp [ε]
      linarith only [hsmall]
    · exact hq.2.2
  have hweightedCore (n : ℕ) :
      (∫ q in A n, G q ∂(volume : Measure (Vec3 × ℝ))) ≤
        256 * (1 + c₁ ^ 2 + 1 / r ^ 2) *
          (∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (w z)) ^ 2
            ∂(volume : Measure ParabolicPoint)) := by
    let φ : Vec3 × ℝ → ℝ := caccioppoliSpaceTimeWeight x t r (ε n)
    rcases caccioppoliSpaceTimeWeight_properties (x₀ := x) (t := t) (r := r)
        (ε := ε n) hr (hεpos n) (hεsmall n) with
      ⟨hφsmooth, hφcompact, hφsupport, hφrange, hφspFormula,
        hφtimeEarly, hφtimeLate, hφplateau, hφspatial⟩
    have hsupportU : tsupport φ ⊆ U := by
      intro q hq
      have hs := hφsupport hq
      simpa [Ω, I, U] using hs
    have hKcompact : IsCompact (tsupport φ) := hφcompact.isCompact
    obtain ⟨δ, hδ, hthick⟩ := hKcompact.exists_cthickening_subset_open hUopen hsupportU
    let δ₀ : ℝ := δ / 8
    have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; linarith only [hδ]
    have hbuffer : ∀ q ∈ tsupport φ,
        Metric.closedBall q (4 * δ₀) ⊆ U := by
      intro q hq z hz
      apply hthick
      apply Metric.mem_cthickening_of_dist_le z q δ (tsupport φ) hq
      have hdist : dist z q ≤ δ / 2 := by
        have hz' := Metric.mem_closedBall.mp hz
        dsimp [δ₀] at hz'
        nlinarith only [hz']
      exact le_trans hdist (by nlinarith only [hδ])
    have htime (q : Vec3 × ℝ) :
        -Ctime / r ^ 2 ≤ (fderiv ℝ φ q) (0, 1) := by
      by_cases hq : q.2 ≤ t + r ^ 2
      · have h := hφtimeEarly q hq
        dsimp [Ctime]
        have hneg : - (1600 / 199 : ℝ) / r ^ 2 ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · norm_num
          · exact sq_nonneg r
        exact hneg.trans h
      · exact hφtimeLate q (le_of_not_ge hq)
    have hφmeas : AEStronglyMeasurable φ (volume : Measure (Vec3 × ℝ)) :=
      hφsmooth.continuous.aestronglyMeasurable
    have hφbound : ∀ q, ‖φ q‖ ≤ 1 := by
      intro q
      rw [Real.norm_eq_abs, abs_of_nonneg (hφrange q).1]
      exact hφrange q |>.2
    have hφGint : Integrable (fun q => φ q * G q)
        (volume : Measure (Vec3 × ℝ)) :=
      hGint.bdd_mul hφmeas (Filter.Eventually.of_forall hφbound)
    have hweighted := caccioppoliWeightedEnergyBound hΩopen hIopen r c₁ Csp Ctime
      hr hc₁ hCsp hderiv hL2' hineq hφsmooth hφcompact hδ₀ hbuffer hφrange
      hφspatial htime
    have hweighted' : (∫ q : Vec3 × ℝ, φ q * G q
        ∂(volume : Measure (Vec3 × ℝ))) ≤
        2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) *
          (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) := by
      simpa [Ω, I, U, W, D, G, φ] using hweighted
    have hplateauA (q : Vec3 × ℝ) (hq : q ∈ A n) : φ q = 1 := by
      apply hφplateau q
      · exact hq.1
      · exact le_of_lt hq.2.1
      · exact le_of_lt hq.2.2
    have hindicatorInt : Integrable ((A n).indicator G)
        (volume : Measure (Vec3 × ℝ)) := hGint.indicator (hAmeas n)
    have hpoint (q : Vec3 × ℝ) : (A n).indicator G q ≤ φ q * G q := by
      by_cases hq : q ∈ A n
      · simp [hq, hplateauA q hq]
      · simp [hq]
        exact mul_nonneg (hφrange q).1 (hGnonneg q)
    have hmono := integral_mono_ae hindicatorInt hφGint (Filter.Eventually.of_forall hpoint)
    have hset :
        (∫ q in A n, G q ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ q : Vec3 × ℝ, (A n).indicator G q
            ∂(volume : Measure (Vec3 × ℝ)) := by
      rw [integral_indicator (hAmeas n)]
    calc
      _ = ∫ q : Vec3 × ℝ, (A n).indicator G q
          ∂(volume : Measure (Vec3 × ℝ)) := hset
      _ ≤ ∫ q : Vec3 × ℝ, φ q * G q
          ∂(volume : Measure (Vec3 × ℝ)) := hmono
      _ ≤ 2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) *
          (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) := hweighted'
      _ ≤ 256 * (1 + c₁ ^ 2 + 1 / r ^ 2) *
          (∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (w z)) ^ 2
            ∂(volume : Measure ParabolicPoint)) := by
        rw [houterGlobalEq]
        exact mul_le_mul_of_nonneg_right hcoefBound houterNonneg
  have hDCT : Tendsto
      (fun n => ∫ q : Vec3 × ℝ, (A n).indicator G q
        ∂(volume : Measure (Vec3 × ℝ))) atTop
      (𝓝 (∫ q : Vec3 × ℝ, V.indicator G q
        ∂(volume : Measure (Vec3 × ℝ)))) := by
    apply tendsto_integral_of_dominated_convergence (bound := G)
    · intro n
      exact (hGint.indicator (hAmeas n)).aestronglyMeasurable
    · exact hGint
    · intro n
      filter_upwards [] with q
      by_cases hq : q ∈ A n
      · simp [hq, Real.norm_eq_abs, abs_of_nonneg (hGnonneg q)]
      · simp [hq]
        exact hGnonneg q
    · filter_upwards [] with q
      by_cases hq : q ∈ V
      · obtain ⟨N, hN⟩ := hAcover q hq
        have hevent : ∀ᶠ n : ℕ in atTop, q ∈ A n := by
          filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
          exact Nat.le_induction hN (fun m hm ih => hAmono m ih) n hn
        have heq (n : ℕ) (hn : q ∈ A n) :
            (A n).indicator G q = V.indicator G q := by
          rw [Set.indicator_of_mem hn, Set.indicator_of_mem (hAsub n hn)]
        exact Tendsto.congr' (hevent.mono fun n hn => (heq n hn).symm)
          tendsto_const_nhds
      · have hnever (n : ℕ) : q ∉ A n := by
          intro hmem
          exact hq (hAsub n hmem)
        have heq (n : ℕ) : (A n).indicator G q = V.indicator G q := by
          simp [hnever n, hq]
        exact Tendsto.congr'
          (Filter.Eventually.of_forall fun n => (heq n).symm)
          tendsto_const_nhds
  have hDCTset : Tendsto
      (fun n => ∫ q in A n, G q ∂(volume : Measure (Vec3 × ℝ))) atTop
      (𝓝 (∫ q in V, G q ∂(volume : Measure (Vec3 × ℝ)))) := by
    have hsetA (n : ℕ) :
        (∫ q : Vec3 × ℝ, (A n).indicator G q ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ q in A n, G q ∂(volume : Measure (Vec3 × ℝ)) := integral_indicator (hAmeas n)
    have hsetV :
        (∫ q : Vec3 × ℝ, V.indicator G q ∂(volume : Measure (Vec3 × ℝ))) =
          ∫ q in V, G q ∂(volume : Measure (Vec3 × ℝ)) := integral_indicator hVmeas
    convert hDCT using 1 <;> simp only [hsetA, hsetV]
  have hfullBound :
      (∫ q in V, G q ∂(volume : Measure (Vec3 × ℝ))) ≤
        256 * (1 + c₁ ^ 2 + 1 / r ^ 2) *
          (∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (w z)) ^ 2
            ∂(volume : Measure ParabolicPoint)) :=
    le_of_tendsto hDCTset (Filter.Eventually.of_forall hweightedCore)
  have hcoreProduct :
      (∫ z in spaceTimeSet (vec3Ball x r) (Ioo t (t + r ^ 2)),
        spatialGradientSq w Dw z ∂(volume : Measure ParabolicPoint)) =
      ∫ q in V, G q ∂(volume : Measure (Vec3 × ℝ)) := by
    calc
      _ = ∫ q in V, spatialGradientSq w Dw (parabolicHomeomorph.symm q)
          ∂(volume : Measure (Vec3 × ℝ)) := setIntegral_parabolic_to_product
      _ = ∫ q in V, G q ∂(volume : Measure (Vec3 × ℝ)) := by
        apply setIntegral_congr_ae hVmeas
        filter_upwards [] with q hq
        have hqU : q ∈ U := hcoreSubOuter hq
        simp [G, D, U, spatialGradientSq, hqU]
  calc
    _ = ∫ q in V, G q ∂(volume : Measure (Vec3 × ℝ)) := hcoreProduct
    _ ≤ 256 * (1 + c₁ ^ 2 + 1 / r ^ 2) *
        (∫ z in spaceTimeSet Ω I, (vec3EuclideanNorm (w z)) ^ 2
          ∂(volume : Measure ParabolicPoint)) := hfullBound
    _ = _ := by simp [Ω, I]

end ESS
