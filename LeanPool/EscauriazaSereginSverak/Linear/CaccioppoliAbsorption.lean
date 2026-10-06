/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliIdentity
public import LeanPool.EscauriazaSereginSverak.Linear.CaccioppoliProductCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.Real.Sqrt

/-!
# Absorption estimate for a localized energy identity

This module estimates the terms in the local identity from `lem:caccioppoli`.
-/

public section

open CKN CKN.Foundation.Parabolic Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace ESS

private theorem abs_sum_mul_le_sqrt_sumsq
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |∑ i ∈ s, f i * g i| ≤
      Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hupper := Real.sum_mul_le_sqrt_mul_sqrt s f g
  have hlowerRaw := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => -f i) g
  have hneg : (∑ i ∈ s, (-f i) * g i) = -(∑ i ∈ s, f i * g i) := by
    simp [Finset.sum_neg_distrib]
  have hsquare : (∑ i ∈ s, (-f i) ^ 2) = ∑ i ∈ s, f i ^ 2 := by
    simp
  rw [hneg, hsquare] at hlowerRaw
  rw [abs_le]
  exact ⟨by linarith only [hlowerRaw], hupper⟩

private theorem sqrt_mul_le_quarter_add {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (X * Y) ≤ X / 4 + Y := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith only [sq_nonneg (X / 4 - Y)]

private theorem abs_vec3_dot_le (u v : Vec3) :
    |∑ i : Fin 3, u i * v i| ≤ vec3EuclideanNorm u * vec3EuclideanNorm v := by
  have hinner :
      inner ℝ (WithLp.toLp 2 u) (WithLp.toLp 2 v) = ∑ i : Fin 3, u i * v i := by
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  rw [← hinner, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  exact abs_real_inner_le_norm _ _

/-- A compactly supported cutoff turns the differential inequality into a weighted
spatial energy estimate (`lem:caccioppoli`). -/
theorem caccioppoliWeightedEnergyBound
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (r c₁ Csp Ctime : ℝ)
    (hr : 0 < r) (hc₁ : 0 ≤ c₁) (hCsp : 0 ≤ Csp)
    {w : ParabolicPoint → Vec3} {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtw : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω I)),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z)))
    {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hbuffer : ∀ q ∈ tsupport φ,
      Metric.closedBall q (4 * δ₀) ⊆ Ω ×ˢ I)
    (hφrange : ∀ q, 0 ≤ φ q ∧ φ q ≤ 1)
    (hspatial : ∀ q, ∑ j : Fin 3,
      ((fderiv ℝ φ q) (basisVec j, 0)) ^ 2 ≤ Csp / r ^ 2 * φ q)
    (htime : ∀ q, -Ctime / r ^ 2 ≤ (fderiv ℝ φ q) (0, 1)) :
    let U : Set (Vec3 × ℝ) := Ω ×ˢ I
    let W : Vec3 × ℝ → Vec3 := fun q =>
      U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
    let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
      U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
    (∫ q : Vec3 × ℝ, φ q *
      (∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2)
      ∂(volume : Measure (Vec3 × ℝ))) ≤
      2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) *
        (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
  classical
  let U : Set (Vec3 × ℝ) := Ω ×ˢ I
  let W : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => w (parabolicHomeomorph.symm y)) q
  let D : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => Dw (parabolicHomeomorph.symm y)) q
  let H : Vec3 × ℝ → Fin 3 → Fin 3 → Fin 3 → ℝ := fun q =>
    U.indicator (fun y => D2w (parabolicHomeomorph.symm y)) q
  let T : Vec3 × ℝ → Vec3 := fun q =>
    U.indicator (fun y => Dtw (parabolicHomeomorph.symm y)) q
  let G : Vec3 × ℝ → ℝ := fun q => ∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2
  let Q : Vec3 × ℝ → ℝ := fun q => ∑ i : Fin 3, (W q i) ^ 2
  let L : Vec3 × ℝ → Vec3 := fun q => fun i => T q i + ∑ j : Fin 3, H q i j j
  have hSmeas : MeasurableSet (spaceTimeSet Ω I) :=
    (isOpen_spaceTimeSet Ω I hΩ hI).measurableSet
  have hdata := zeroExtend_spaceTimeData_memLp hΩ hI hderiv hL2
  have hWfun : W = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U
    · simp [W, U, zeroExtendField, hq]
    · simp [W, U, zeroExtendField, hq]
  have hDfun : D = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => Dw (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U
    · simp [D, U, zeroExtendField, hq]
    · simp [D, U, zeroExtendField, hq]
  have hHfun : H = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => D2w (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U
    · simp [H, U, zeroExtendField, hq]
    · simp [H, U, zeroExtendField, hq]
  have hTfun : T = zeroExtendField (Ω ×ˢ I)
      (fun q : Vec3 × ℝ => Dtw (parabolicHomeomorph.symm q)) := by
    funext q
    by_cases hq : q ∈ U
    · simp [T, U, zeroExtendField, hq]
    · simp [T, U, zeroExtendField, hq]
  have hWdata : MemLp W 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hWfun]
    exact hdata.1
  have hDdata : MemLp D 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hDfun]
    exact hdata.2.1
  have hHdata : MemLp H 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hHfun]
    exact hdata.2.2.1
  have hTdata : MemLp T 2 (volume : Measure (Vec3 × ℝ)) := by
    rw [hTfun]
    exact hdata.2.2.2
  have hWcomp (i : Fin 3) : MemLp (fun q => W q i) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component hWdata i
  have hDcomp (i j : Fin 3) : MemLp (fun q => D q i j) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component
        (memLp_pi_component hDdata i) j
  have hHcomp (i j k : Fin 3) : MemLp (fun q => H q i j k) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component
        (memLp_pi_component (memLp_pi_component hHdata i) j) k
  have hTcomp (i : Fin 3) : MemLp (fun q => T q i) 2
      (volume : Measure (Vec3 × ℝ)) := memLp_pi_component hTdata i
  have hWnorm : MemLp (fun q => vec3EuclideanNorm (W q)) 2
      (volume : Measure (Vec3 × ℝ)) := by
    apply hWdata.norm.of_nnnorm_le_mul
      ((continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hWdata.aestronglyMeasurable))
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
  have hineqFull : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      z ∈ spaceTimeSet Ω I →
        vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
          c₁ * (vec3EuclideanNorm (w z) + Real.sqrt (spatialGradientSq w Dw z)) :=
    (ae_restrict_iff' hSmeas).1 hineq
  have hineqProduct : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)), q ∈ U →
      vec3EuclideanNorm (fun i => Dtw (parabolicHomeomorph.symm q) i +
        ∑ j, D2w (parabolicHomeomorph.symm q) i j j) ≤
        c₁ * (vec3EuclideanNorm (w (parabolicHomeomorph.symm q)) +
          Real.sqrt (spatialGradientSq w Dw (parabolicHomeomorph.symm q))) := by
    have hmapped : ∀ᵐ q ∂(Measure.map parabolicHomeomorph
        (volume : Measure ParabolicPoint)), q ∈ U →
        vec3EuclideanNorm (fun i => Dtw (parabolicHomeomorph.symm q) i +
          ∑ j, D2w (parabolicHomeomorph.symm q) i j j) ≤
          c₁ * (vec3EuclideanNorm (w (parabolicHomeomorph.symm q)) +
            Real.sqrt (spatialGradientSq w Dw (parabolicHomeomorph.symm q))) := by
      apply parabolicHomeomorph.measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hineqFull] with z hz
      intro hzU
      have hzS : z ∈ spaceTimeSet Ω I := by
        change parabolicHomeomorph z ∈ Ω ×ˢ I at hzU
        change z ∈ Ω ×ˢ I
        exact hzU
      have hmain := hz hzS
      have hinv : parabolicHomeomorph.symm (parabolicHomeomorph z) = z :=
        parabolicHomeomorph.left_inv z
      rw [hinv]
      exact hmain
    rw [parabolicHomeomorph_measurePreserving.map_eq] at hmapped
    exact hmapped
  have hφbound : ∃ C : NNReal, ∀ q, ‖φ q‖₊ ≤ C :=
    continuous_hasCompactSupport_nnnorm_bound hφ.continuous hφc
  obtain ⟨Cφ, hCφ⟩ := hφbound
  have hφboundReal (q : Vec3 × ℝ) : ‖φ q‖ ≤ Cφ := by
    have hreal : (‖φ q‖₊ : ℝ) ≤ Cφ := by exact_mod_cast hCφ q
    simpa only [coe_nnnorm] using hreal
  have hφmeas : AEStronglyMeasurable φ (volume : Measure (Vec3 × ℝ)) :=
    hφ.continuous.aestronglyMeasurable
  let hd (j : Fin 3) : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (basisVec j, 0)
  let hdt : Vec3 × ℝ → ℝ := fun q => (fderiv ℝ φ q) (0, 1)
  have hdcont (j : Fin 3) : Continuous (hd j) := by
    dsimp only [hd]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdtcont : Continuous hdt := by
    dsimp only [hdt]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc (j : Fin 3) : HasCompactSupport (hd j) := by
    dsimp only [hd]
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec j, 0)
  have hdtc : HasCompactSupport hdt := by
    dsimp only [hdt]
    exact hφc.fderiv_apply (𝕜 := ℝ) (0, 1)
  have hdbound (j : Fin 3) : ∃ C : NNReal, ∀ q, ‖hd j q‖₊ ≤ C :=
    continuous_hasCompactSupport_nnnorm_bound (hdcont j) (hdc j)
  have hdtbound : ∃ C : NNReal, ∀ q, ‖hdt q‖₊ ≤ C :=
    continuous_hasCompactSupport_nnnorm_bound hdtcont hdtc
  obtain ⟨Ct, hCt⟩ := hdtbound
  have hdtboundReal (q : Vec3 × ℝ) : ‖hdt q‖ ≤ Ct := by
    have hreal : (‖hdt q‖₊ : ℝ) ≤ Ct := by exact_mod_cast hCt q
    simpa only [coe_nnnorm] using hreal
  have hφGint : Integrable (fun q => φ q * G q) (volume : Measure (Vec3 × ℝ)) := by
    have hGint : Integrable G (volume : Measure (Vec3 × ℝ)) := by
      change Integrable (fun q => ∑ i : Fin 3, ∑ j : Fin 3, (D q i j) ^ 2) _
      exact integrable_finsetSum Finset.univ fun i hi =>
        integrable_finsetSum Finset.univ fun j hj => (hDcomp i j).integrable_sq
    exact hGint.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hWsqInt : Integrable (fun q => (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)) := hWnorm.integrable_sq
  have hφWsqInt : Integrable (fun q => φ q * (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)) :=
    hWsqInt.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hsourceInt (i : Fin 3) : Integrable
      (fun q => φ q * (W q i * T q i)) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_mul (hTcomp i)
    exact hbase.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hlapInt (i j : Fin 3) : Integrable
      (fun q => φ q * (W q i * H q i j j)) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_mul (hHcomp i j j)
    exact hbase.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have htimeInt (i : Fin 3) : Integrable
      (fun q => hdt q * (W q i) ^ 2) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_sq
    simpa only [mul_comm] using hbase.bdd_mul hdtcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdtboundReal)
  have hcrossInt (i j : Fin 3) : Integrable
      (fun q => hd j q * W q i * D q i j) (volume : Measure (Vec3 × ℝ)) := by
    have hbase := (hWcomp i).integrable_mul (hDcomp i j)
    obtain ⟨Cj, hCj⟩ := hdbound j
    have hboundReal (q : Vec3 × ℝ) : ‖hd j q‖ ≤ Cj := by
      have hreal : (‖hd j q‖₊ : ℝ) ≤ Cj := by exact_mod_cast hCj q
      simpa only [coe_nnnorm] using hreal
    have hweighted := hbase.bdd_mul (hdcont j).aestronglyMeasurable
      (Filter.Eventually.of_forall hboundReal)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hsourcePoint : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)),
      -(∑ i : Fin 3, W q i * T q i * φ q) -
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j) ≤
        (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
          (1 / 4 : ℝ) * φ q * G q := by
    filter_upwards [hineqProduct] with q hq
    by_cases hqU : q ∈ U
    · have hineqq := hq hqU
      have hWq : W q = w (parabolicHomeomorph.symm q) := by simp [W, U, hqU]
      have hTq : T q = Dtw (parabolicHomeomorph.symm q) := by simp [T, U, hqU]
      have hHq : H q = D2w (parabolicHomeomorph.symm q) := by simp [H, U, hqU]
      have hDq : D q = Dw (parabolicHomeomorph.symm q) := by simp [D, U, hqU]
      have hGq : G q = spatialGradientSq w Dw (parabolicHomeomorph.symm q) := by
        simp [G, hDq, spatialGradientSq]
      have hLq : L q = fun i => Dtw (parabolicHomeomorph.symm q) i +
          ∑ j : Fin 3, D2w (parabolicHomeomorph.symm q) i j j := by
        funext i
        simp [L, hTq, hHq]
      have hLnorm : vec3EuclideanNorm (L q) ≤
          c₁ * (vec3EuclideanNorm (W q) + Real.sqrt (G q)) := by
        simpa [hWq, hGq, hLq] using hineqq
      have hdot := abs_vec3_dot_le (W q) (L q)
      have ha0 : 0 ≤ vec3EuclideanNorm (W q) := vec3EuclideanNorm_nonneg _
      have hb0 : 0 ≤ Real.sqrt (G q) := Real.sqrt_nonneg _
      have hG0 : 0 ≤ G q := by
        dsimp [G]
        positivity
      have hdotLower : -(∑ i : Fin 3, W q i * L q i) ≤
          vec3EuclideanNorm (W q) * vec3EuclideanNorm (L q) := by
        exact (neg_le_abs _).trans hdot
      have hsourceDot : -(φ q) *
          (∑ i : Fin 3, W q i * L q i) ≤
          φ q * (vec3EuclideanNorm (W q) * vec3EuclideanNorm (L q)) := by
        calc
          _ = φ q * (-(∑ i : Fin 3, W q i * L q i)) := by ring
          _ ≤ φ q * (vec3EuclideanNorm (W q) * vec3EuclideanNorm (L q)) :=
            mul_le_mul_of_nonneg_left hdotLower (hφrange q).1
      have hLbound : vec3EuclideanNorm (L q) ≤
          c₁ * (vec3EuclideanNorm (W q) + Real.sqrt (G q)) := hLnorm
      have hproduct : vec3EuclideanNorm (W q) * vec3EuclideanNorm (L q) ≤
          c₁ * vec3EuclideanNorm (W q) *
            (vec3EuclideanNorm (W q) + Real.sqrt (G q)) := by
        calc
          _ ≤ vec3EuclideanNorm (W q) *
              (c₁ * (vec3EuclideanNorm (W q) + Real.sqrt (G q))) :=
            mul_le_mul_of_nonneg_left hLbound ha0
          _ = _ := by ring
      have hyoung : c₁ * vec3EuclideanNorm (W q) * Real.sqrt (G q) ≤
          (1 / 4 : ℝ) * (Real.sqrt (G q)) ^ 2 +
            c₁ ^ 2 * (vec3EuclideanNorm (W q)) ^ 2 := by
        nlinarith only [sq_nonneg
          (Real.sqrt (G q) / 2 - c₁ * vec3EuclideanNorm (W q))]
      have hsourceLocal : -(φ q) *
          (∑ i : Fin 3, W q i * L q i) ≤
          (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
            (1 / 4 : ℝ) * φ q * G q := by
        have hsplit := mul_le_mul_of_nonneg_left hyoung (hφrange q).1
        have hpart := mul_le_mul_of_nonneg_left hproduct (hφrange q).1
        have hsqrtSq : (Real.sqrt (G q)) ^ 2 = G q := Real.sq_sqrt hG0
        calc
          _ ≤ φ q * (vec3EuclideanNorm (W q) * vec3EuclideanNorm (L q)) := hsourceDot
          _ ≤ φ q * (c₁ * vec3EuclideanNorm (W q) *
              (vec3EuclideanNorm (W q) + Real.sqrt (G q))) := hpart
          _ = φ q * (c₁ * (vec3EuclideanNorm (W q)) ^ 2 +
              c₁ * vec3EuclideanNorm (W q) * Real.sqrt (G q)) := by ring
          _ ≤ φ q * (c₁ * (vec3EuclideanNorm (W q)) ^ 2 +
              (1 / 4 : ℝ) * (Real.sqrt (G q)) ^ 2 +
                c₁ ^ 2 * (vec3EuclideanNorm (W q)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (by linarith only [hyoung]) (hφrange q).1
          _ = _ := by rw [hsqrtSq]; ring
      have hsourceEq :
          (∑ i : Fin 3, W q i * T q i * φ q) +
            (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j) =
              φ q * (∑ i : Fin 3, W q i * L q i) := by
        calc
          _ = ∑ i : Fin 3,
              (W q i * T q i * φ q + ∑ j : Fin 3, φ q * W q i * H q i j j) := by
            rw [← Finset.sum_add_distrib]
          _ = ∑ i : Fin 3, φ q * W q i *
                (T q i + ∑ j : Fin 3, H q i j j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum]
            ring
          _ = φ q * (∑ i : Fin 3, W q i *
                (T q i + ∑ j : Fin 3, H q i j j)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = φ q * (∑ i : Fin 3, W q i * L q i) := by
            rfl
      calc
        _ = -((∑ i : Fin 3, W q i * T q i * φ q) +
              (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)) := by ring
        _ = -(φ q * (∑ i : Fin 3, W q i * L q i)) := by rw [hsourceEq]
        _ = -(φ q) * (∑ i : Fin 3, W q i * L q i) := by ring
        _ ≤ (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
              (1 / 4 : ℝ) * φ q * G q := hsourceLocal
    · have hWzero (i : Fin 3) : W q i = 0 := by simp [W, U, hqU]
      have hTzero (i : Fin 3) : T q i = 0 := by simp [T, U, hqU]
      have hHzero (i j k : Fin 3) : H q i j k = 0 := by simp [H, U, hqU]
      have hDzero (i j : Fin 3) : D q i j = 0 := by simp [D, U, hqU]
      have hWq : W q = 0 := funext hWzero
      have hDq : D q = 0 := by
        funext i j
        exact hDzero i j
      simp [hWq, hTzero, hHzero, hDq, G, vec3EuclideanNorm]
  have hcrossPoint : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)),
      -∑ i : Fin 3, ∑ j : Fin 3, hd j q * W q i * D q i j ≤
        (1 / 4 : ℝ) * φ q * G q + Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2 := by
    filter_upwards [] with q
    let a : ℝ := vec3EuclideanNorm (W q)
    let d : Fin 3 → ℝ := fun j => hd j q
    let col : Fin 3 → ℝ := fun j => ∑ i : Fin 3, W q i * D q i j
    have hcol (j : Fin 3) : (col j) ^ 2 ≤
        (∑ i : Fin 3, (W q i) ^ 2) * (∑ i : Fin 3, (D q i j) ^ 2) := by
      simpa [col] using
        (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
          (fun i => W q i) (fun i => D q i j))
    have hcolSq : (∑ j : Fin 3, (col j) ^ 2) ≤
        (∑ i : Fin 3, (W q i) ^ 2) * G q := by
      calc
        _ ≤ ∑ j : Fin 3,
            (∑ i : Fin 3, (W q i) ^ 2) * (∑ i : Fin 3, (D q i j) ^ 2) :=
          Finset.sum_le_sum fun j hj => hcol j
        _ = (∑ i : Fin 3, (W q i) ^ 2) *
            (∑ j : Fin 3, ∑ i : Fin 3, (D q i j) ^ 2) := by
          rw [Finset.mul_sum]
        _ = (∑ i : Fin 3, (W q i) ^ 2) * G q := by
          congr 1
          unfold G
          exact Finset.sum_comm
    have haSq : a ^ 2 = ∑ i : Fin 3, (W q i) ^ 2 := by
      change Real.sqrt (∑ i : Fin 3, (W q i) ^ 2) ^ 2 = _
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (W q i))]
    have hcolSq' : (∑ j : Fin 3, (col j) ^ 2) ≤ a ^ 2 * G q := by
      rw [haSq]
      exact hcolSq
    have hsum := abs_sum_mul_le_sqrt_sumsq (Finset.univ : Finset (Fin 3)) d col
    have hcross : |∑ j : Fin 3, d j * col j| ≤
        Real.sqrt (∑ j : Fin 3, d j ^ 2) * Real.sqrt (a ^ 2 * G q) := by
      calc
        _ ≤ Real.sqrt (∑ j : Fin 3, d j ^ 2) *
            Real.sqrt (∑ j : Fin 3, (col j) ^ 2) := by
          simpa [d, col] using hsum
        _ ≤ Real.sqrt (∑ j : Fin 3, d j ^ 2) * Real.sqrt (a ^ 2 * G q) := by
          have hnonneg := Real.sqrt_nonneg (∑ j : Fin 3, d j ^ 2)
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcolSq') hnonneg
    have hGnonneg : 0 ≤ G q := by dsimp [G]; positivity
    have hsp := hspatial q
    have hspNonneg : 0 ≤ ∑ j : Fin 3, d j ^ 2 := by positivity
    have hcrossYoung :
        Real.sqrt ((Csp / r ^ 2 * φ q) * (a ^ 2 * G q)) ≤
          (1 / 4 : ℝ) * φ q * G q + Csp / r ^ 2 * a ^ 2 := by
      have hX : 0 ≤ φ q * G q := mul_nonneg (hφrange q).1 hGnonneg
      have hY : 0 ≤ Csp / r ^ 2 * a ^ 2 := by positivity
      have hEq : (Csp / r ^ 2 * φ q) * (a ^ 2 * G q) =
          (φ q * G q) * (Csp / r ^ 2 * a ^ 2) := by ring
      rw [hEq]
      calc
        _ ≤ φ q * G q / 4 + Csp / r ^ 2 * a ^ 2 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            sqrt_mul_le_quarter_add hX hY
        _ = (1 / 4 : ℝ) * φ q * G q + Csp / r ^ 2 * a ^ 2 := by ring
    have hDsum : ∑ j : Fin 3, d j ^ 2 ≤ Csp / r ^ 2 * φ q := by
      simpa only [d, hd] using hsp
    have hrad :
        Real.sqrt (∑ j : Fin 3, d j ^ 2) * Real.sqrt (a ^ 2 * G q) ≤
          Real.sqrt ((Csp / r ^ 2 * φ q) * (a ^ 2 * G q)) := by
      have hrad2 :
          (∑ j : Fin 3, d j ^ 2) * (a ^ 2 * G q) ≤
            (Csp / r ^ 2 * φ q) * (a ^ 2 * G q) :=
        mul_le_mul_of_nonneg_right hDsum (mul_nonneg (sq_nonneg a) hGnonneg)
      rw [← Real.sqrt_mul hspNonneg]
      exact Real.sqrt_le_sqrt hrad2
    have hdotExpr : (∑ i : Fin 3, ∑ j : Fin 3,
        hd j q * W q i * D q i j) = ∑ j : Fin 3, d j * col j := by
      simp only [d, col]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hfinal : |∑ i : Fin 3, ∑ j : Fin 3,
        hd j q * W q i * D q i j| ≤
        (1 / 4 : ℝ) * φ q * G q + Csp / r ^ 2 * a ^ 2 := by
      rw [hdotExpr]
      exact hcross.trans (hrad.trans hcrossYoung)
    have hto : -(∑ i : Fin 3, ∑ j : Fin 3,
        hd j q * W q i * D q i j) ≤
        (1 / 4 : ℝ) * φ q * G q + Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2 := by
      have hfinal' : |∑ i : Fin 3, ∑ j : Fin 3,
          hd j q * W q i * D q i j| ≤
          (1 / 4 : ℝ) * φ q * G q + Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2 := by
        simpa [a] using hfinal
      have hlower' := (abs_le.mp hfinal').1
      linarith only [hlower']
    exact hto
  have hQint : Integrable Q (volume : Measure (Vec3 × ℝ)) := by
    change Integrable (fun q => ∑ i : Fin 3, (W q i) ^ 2) _
    exact integrable_finsetSum Finset.univ fun i hi => (hWcomp i).integrable_sq
  have hQnonneg (q : Vec3 × ℝ) : 0 ≤ Q q := by
    dsimp [Q]
    positivity
  have hnormSq (q : Vec3 × ℝ) : (vec3EuclideanNorm (W q)) ^ 2 = Q q := by
    change Real.sqrt (∑ i : Fin 3, (W q i) ^ 2) ^ 2 = _
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (W q i))]
  have hdtQint : Integrable (fun q => hdt q * Q q)
      (volume : Measure (Vec3 × ℝ)) := by
    have h := hQint.bdd_mul hdtcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hdtboundReal)
    simpa only [mul_comm] using h
  have htimeSumEq :
      (∑ i : Fin 3, ∫ q : Vec3 × ℝ, (W q i) ^ 2 * hdt q
        ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q : Vec3 × ℝ, hdt q * Q q ∂(volume : Measure (Vec3 × ℝ)) := by
    calc
      _ = ∫ q : Vec3 × ℝ, ∑ i : Fin 3, (W q i) ^ 2 * hdt q
          ∂(volume : Measure (Vec3 × ℝ)) := by
        symm
        exact integral_finsetSum Finset.univ fun i hi => by
          simpa only [mul_comm] using htimeInt i
      _ = ∫ q : Vec3 × ℝ, hdt q * Q q ∂(volume : Measure (Vec3 × ℝ)) := by
        congr 1
        funext q
        simp only [Q, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have htimePoint (q : Vec3 × ℝ) :
      -(1 / 2 : ℝ) * (hdt q * Q q) ≤ Ctime / (2 * r ^ 2) * Q q := by
    have hmul := mul_le_mul_of_nonneg_right (htime q) (hQnonneg q)
    calc
      _ = -(1 / 2 : ℝ) * (hdt q * Q q) := by ring
      _ ≤ -(1 / 2 : ℝ) * ((-Ctime / r ^ 2) * Q q) :=
        mul_le_mul_of_nonpos_left hmul (by norm_num)
      _ = Ctime / (2 * r ^ 2) * Q q := by ring
  have htimePointAE : ∀ᵐ q ∂(volume : Measure (Vec3 × ℝ)),
      -(1 / 2 : ℝ) * (hdt q * Q q) ≤ Ctime / (2 * r ^ 2) * Q q :=
    Filter.Eventually.of_forall htimePoint
  have htimeUpperInt : Integrable
      (fun q => Ctime / (2 * r ^ 2) * Q q) (volume : Measure (Vec3 × ℝ)) :=
    hQint.const_mul (Ctime / (2 * r ^ 2)) |>.congr
      (Filter.Eventually.of_forall fun q => by ring)
  have htimeIntegralBound :
      -(1 / 2 : ℝ) *
        (∑ i : Fin 3, ∫ q : Vec3 × ℝ, (W q i) ^ 2 * hdt q
          ∂(volume : Measure (Vec3 × ℝ))) ≤
      Ctime / (2 * r ^ 2) *
        (∫ q : Vec3 × ℝ, Q q ∂(volume : Measure (Vec3 × ℝ))) := by
    calc
      _ = ∫ q : Vec3 × ℝ, -(1 / 2 : ℝ) * (hdt q * Q q)
          ∂(volume : Measure (Vec3 × ℝ)) := by
        rw [integral_const_mul, htimeSumEq]
      _ ≤ ∫ q : Vec3 × ℝ, Ctime / (2 * r ^ 2) * Q q
          ∂(volume : Measure (Vec3 × ℝ)) :=
        integral_mono_ae (hdtQint.const_mul (-(1 / 2 : ℝ))) htimeUpperInt htimePointAE
      _ = Ctime / (2 * r ^ 2) *
          (∫ q : Vec3 × ℝ, Q q ∂(volume : Measure (Vec3 × ℝ))) := by
        rw [integral_const_mul]
  have hsourceSumInt : Integrable
      (fun q => ∑ i : Fin 3, W q i * T q i * φ q)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    simpa [mul_assoc, mul_comm, mul_left_comm] using hsourceInt i
  have hlapRowInt (i : Fin 3) : Integrable
      (fun q => ∑ j : Fin 3, φ q * W q i * H q i j j)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    simpa only [mul_assoc] using hlapInt i j
  have hlapTotalInt : Integrable
      (fun q => ∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)
      (volume : Measure (Vec3 × ℝ)) := by
    exact integrable_finsetSum Finset.univ fun i hi => hlapRowInt i
  have hsourceNegativeInt : Integrable
      (fun q => -(∑ i : Fin 3, W q i * T q i * φ q) -
        (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j))
      (volume : Measure (Vec3 × ℝ)) := hsourceSumInt.neg.sub hlapTotalInt
  have hsourceRightInt : Integrable
      (fun q => (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
        (1 / 4 : ℝ) * φ q * G q) (volume : Measure (Vec3 × ℝ)) := by
    have hleft := hφWsqInt.const_mul (c₁ + c₁ ^ 2)
    have hright := hφGint.const_mul (1 / 4 : ℝ)
    apply (hleft.add hright).congr
    filter_upwards [] with q
    change (c₁ + c₁ ^ 2) * (φ q * (vec3EuclideanNorm (W q)) ^ 2) +
        (1 / 4 : ℝ) * (φ q * G q) = _
    ring
  have hsourceBound :
      -(∑ i : Fin 3, ∫ q : Vec3 × ℝ, W q i * T q i * φ q
        ∂(volume : Measure (Vec3 × ℝ))) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, φ q * W q i * H q i j j
          ∂(volume : Measure (Vec3 × ℝ))) ≤
      (c₁ + c₁ ^ 2) *
        (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) +
      (1 / 4 : ℝ) *
        (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) := by
    have hmono := integral_mono_ae hsourceNegativeInt hsourceRightInt hsourcePoint
    have hleft :
        (∫ q : Vec3 × ℝ, -(∑ i : Fin 3, W q i * T q i * φ q) -
          (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)
          ∂(volume : Measure (Vec3 × ℝ))) =
        -(∑ i : Fin 3, ∫ q : Vec3 × ℝ, W q i * T q i * φ q
          ∂(volume : Measure (Vec3 × ℝ))) -
          (∑ i : Fin 3, ∑ j : Fin 3,
            ∫ q : Vec3 × ℝ, φ q * W q i * H q i j j
              ∂(volume : Measure (Vec3 × ℝ))) := by
      calc
        _ = (∫ q : Vec3 × ℝ, -(∑ i : Fin 3, W q i * T q i * φ q)
              ∂(volume : Measure (Vec3 × ℝ))) -
            (∫ q : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3,
              φ q * W q i * H q i j j ∂(volume : Measure (Vec3 × ℝ))) :=
          integral_sub hsourceSumInt.neg hlapTotalInt
        _ = -(∫ q : Vec3 × ℝ, ∑ i : Fin 3, W q i * T q i * φ q
              ∂(volume : Measure (Vec3 × ℝ))) -
            (∫ q : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3,
              φ q * W q i * H q i j j ∂(volume : Measure (Vec3 × ℝ))) := by
          rw [integral_neg]
        _ = -(∑ i : Fin 3, ∫ q : Vec3 × ℝ, W q i * T q i * φ q
              ∂(volume : Measure (Vec3 × ℝ))) -
            (∑ i : Fin 3, ∫ q : Vec3 × ℝ,
              ∑ j : Fin 3, φ q * W q i * H q i j j
                ∂(volume : Measure (Vec3 × ℝ))) := by
          rw [integral_finsetSum Finset.univ (fun i hi => by
            simpa [mul_assoc, mul_comm, mul_left_comm] using hsourceInt i)]
          rw [integral_finsetSum Finset.univ (fun i hi => hlapRowInt i)]
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simpa only [mul_assoc] using
            (integral_finsetSum Finset.univ (fun j hj => hlapInt i j))
    have hright :
        (∫ q : Vec3 × ℝ,
          (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
            (1 / 4 : ℝ) * φ q * G q ∂(volume : Measure (Vec3 × ℝ))) =
        (c₁ + c₁ ^ 2) *
          (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) +
        (1 / 4 : ℝ) *
          (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) := by
      calc
        _ = ∫ q : Vec3 × ℝ,
              (c₁ + c₁ ^ 2) * (φ q * (vec3EuclideanNorm (W q)) ^ 2) +
                (1 / 4 : ℝ) * (φ q * G q)
                ∂(volume : Measure (Vec3 × ℝ)) := by
          apply integral_congr_ae
          filter_upwards [] with q
          ring
        _ = (∫ q : Vec3 × ℝ,
              (c₁ + c₁ ^ 2) * (φ q * (vec3EuclideanNorm (W q)) ^ 2)
                ∂(volume : Measure (Vec3 × ℝ))) +
            (∫ q : Vec3 × ℝ,
              (1 / 4 : ℝ) * (φ q * G q)
                ∂(volume : Measure (Vec3 × ℝ))) :=
          integral_add (hφWsqInt.const_mul (c₁ + c₁ ^ 2))
            (hφGint.const_mul (1 / 4 : ℝ))
        _ = _ := by
          rw [integral_const_mul, integral_const_mul]
    calc
      _ = ∫ q : Vec3 × ℝ, -(∑ i : Fin 3, W q i * T q i * φ q) -
            (∑ i : Fin 3, ∑ j : Fin 3, φ q * W q i * H q i j j)
            ∂(volume : Measure (Vec3 × ℝ)) := hleft.symm
      _ ≤ ∫ q : Vec3 × ℝ,
            (c₁ + c₁ ^ 2) * φ q * (vec3EuclideanNorm (W q)) ^ 2 +
              (1 / 4 : ℝ) * φ q * G q ∂(volume : Measure (Vec3 × ℝ)) := hmono
      _ = _ := hright
  have hcrossTotalInt : Integrable
      (fun q => ∑ i : Fin 3, ∑ j : Fin 3, hd j q * W q i * D q i j)
      (volume : Measure (Vec3 × ℝ)) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hcrossInt i j
  have hcrossRightInt : Integrable
      (fun q => (1 / 4 : ℝ) * φ q * G q +
        Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2)
      (volume : Measure (Vec3 × ℝ)) := by
    have hleft := hφGint.const_mul (1 / 4 : ℝ)
    have hright := hWsqInt.const_mul (Csp / r ^ 2)
    apply (hleft.add hright).congr
    filter_upwards [] with q
    change (1 / 4 : ℝ) * (φ q * G q) +
        (Csp / r ^ 2) * (vec3EuclideanNorm (W q)) ^ 2 = _
    ring
  have hcrossBound :
      -(∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, hd j q * W q i * D q i j
          ∂(volume : Measure (Vec3 × ℝ))) ≤
      (1 / 4 : ℝ) *
        (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) +
      Csp / r ^ 2 *
        (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
    have hmono := integral_mono_ae hcrossTotalInt.neg hcrossRightInt hcrossPoint
    have hleft :
        (∫ q : Vec3 × ℝ, -∑ i : Fin 3, ∑ j : Fin 3,
          hd j q * W q i * D q i j ∂(volume : Measure (Vec3 × ℝ))) =
        -(∑ i : Fin 3, ∑ j : Fin 3,
          ∫ q : Vec3 × ℝ, hd j q * W q i * D q i j
          ∂(volume : Measure (Vec3 × ℝ))) := by
      calc
        _ = -(∫ q : Vec3 × ℝ,
              ∑ i : Fin 3, ∑ j : Fin 3, hd j q * W q i * D q i j
                ∂(volume : Measure (Vec3 × ℝ))) := integral_neg _
        _ = -(∑ i : Fin 3, ∫ q : Vec3 × ℝ,
              ∑ j : Fin 3, hd j q * W q i * D q i j
                ∂(volume : Measure (Vec3 × ℝ))) := by
          congr 1
          exact integral_finsetSum Finset.univ (fun i hi => by
            apply integrable_finsetSum Finset.univ
            intro j hj
            exact hcrossInt i j)
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact integral_finsetSum Finset.univ (fun j hj => hcrossInt i j)
    have hright :
        (∫ q : Vec3 × ℝ,
          (1 / 4 : ℝ) * φ q * G q +
            Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) =
        (1 / 4 : ℝ) *
          (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) +
        Csp / r ^ 2 *
          (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) := by
      calc
        _ = ∫ q : Vec3 × ℝ,
              (1 / 4 : ℝ) * (φ q * G q) +
                (Csp / r ^ 2) * (vec3EuclideanNorm (W q)) ^ 2
                ∂(volume : Measure (Vec3 × ℝ)) := by
          apply integral_congr_ae
          filter_upwards [] with q
          ring
        _ = (∫ q : Vec3 × ℝ,
              (1 / 4 : ℝ) * (φ q * G q)
                ∂(volume : Measure (Vec3 × ℝ))) +
            (∫ q : Vec3 × ℝ,
              (Csp / r ^ 2) * (vec3EuclideanNorm (W q)) ^ 2
                ∂(volume : Measure (Vec3 × ℝ))) :=
          integral_add (hφGint.const_mul (1 / 4 : ℝ))
            (hWsqInt.const_mul (Csp / r ^ 2))
        _ = _ := by
          rw [integral_const_mul, integral_const_mul]
    calc
      _ = ∫ q : Vec3 × ℝ, -∑ i : Fin 3, ∑ j : Fin 3,
            hd j q * W q i * D q i j ∂(volume : Measure (Vec3 × ℝ)) := hleft.symm
      _ ≤ ∫ q : Vec3 × ℝ,
            (1 / 4 : ℝ) * φ q * G q +
              Csp / r ^ 2 * (vec3EuclideanNorm (W q)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ)) := hmono
      _ = _ := hright
  have hgradTermInt (i j : Fin 3) : Integrable
      (fun q => φ q * (D q i j) ^ 2) (volume : Measure (Vec3 × ℝ)) := by
    have h := (hDcomp i j).integrable_sq
    simpa only [mul_comm] using
      h.bdd_mul hφmeas (Filter.Eventually.of_forall hφboundReal)
  have hgradSumEq :
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, φ q * (D q i j) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ)) := by
    calc
      _ = ∑ i : Fin 3, ∫ q : Vec3 × ℝ,
          ∑ j : Fin 3, φ q * (D q i j) ^ 2
            ∂(volume : Measure (Vec3 × ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        symm
        exact integral_finsetSum Finset.univ fun j hj => hgradTermInt i j
      _ = ∫ q : Vec3 × ℝ,
          ∑ i : Fin 3, ∑ j : Fin 3, φ q * (D q i j) ^ 2
            ∂(volume : Measure (Vec3 × ℝ)) := by
        symm
        apply integral_finsetSum Finset.univ
        intro i hi
        exact integrable_finsetSum Finset.univ fun j hj => hgradTermInt i j
      _ = ∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ)) := by
        congr 1
        funext q
        dsimp [G]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  have hidentity := localizedEnergyIdentity hΩ hI hderiv hL2 hφ hφc hδ₀ hbuffer
  have henergyIdentity :
      (∑ i : Fin 3,
        ∫ q : Vec3 × ℝ,
          W q i * T q i * φ q ∂(volume : Measure (Vec3 × ℝ))) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, φ q * W q i * H q i j j
          ∂(volume : Measure (Vec3 × ℝ))) =
      -(1 / 2 : ℝ) *
        (∑ i : Fin 3,
          ∫ q : Vec3 × ℝ, (W q i) ^ 2 * hdt q
            ∂(volume : Measure (Vec3 × ℝ))) -
      (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ q : Vec3 × ℝ, hd j q * W q i * D q i j
          ∂(volume : Measure (Vec3 × ℝ))) := by
    simpa only [W, T, H, D, hd, hdt, U, hgradSumEq] using hidentity
  have hphiEnergyBound :
      (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) ≤
      (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))) := by
    apply integral_mono_ae hφWsqInt hWsqInt
    filter_upwards [] with q
    calc
      φ q * (vec3EuclideanNorm (W q)) ^ 2 ≤
          1 * (vec3EuclideanNorm (W q)) ^ 2 :=
        mul_le_mul_of_nonneg_right (hφrange q).2 (sq_nonneg _)
      _ = (vec3EuclideanNorm (W q)) ^ 2 := by ring
  have hQintegralEq :
      (∫ q : Vec3 × ℝ, Q q ∂(volume : Measure (Vec3 × ℝ))) =
        (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
    apply integral_congr_ae
    filter_upwards [] with q
    exact (hnormSq q).symm
  have henergyBound :
      (∫ q : Vec3 × ℝ, φ q * G q ∂(volume : Measure (Vec3 × ℝ))) ≤
      2 * (c₁ + c₁ ^ 2 + (Csp + Ctime / 2) / r ^ 2) *
        (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
          ∂(volume : Measure (Vec3 × ℝ))) := by
    let E : ℝ := ∫ q : Vec3 × ℝ, φ q * G q
        ∂(volume : Measure (Vec3 × ℝ))
    let N : ℝ := ∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
        ∂(volume : Measure (Vec3 × ℝ))
    have hEeq : E =
        -(∑ i : Fin 3, ∫ q : Vec3 × ℝ, W q i * T q i * φ q
          ∂(volume : Measure (Vec3 × ℝ))) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ q : Vec3 × ℝ, φ q * W q i * H q i j j
            ∂(volume : Measure (Vec3 × ℝ))) -
        (1 / 2 : ℝ) *
          (∑ i : Fin 3,
            ∫ q : Vec3 × ℝ, (W q i) ^ 2 * hdt q
              ∂(volume : Measure (Vec3 × ℝ))) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ q : Vec3 × ℝ, hd j q * W q i * D q i j
            ∂(volume : Measure (Vec3 × ℝ))) := by
      dsimp [E]
      linarith only [henergyIdentity]
    have hhalfE :
        (1 / 2 : ℝ) * E ≤ (c₁ + c₁ ^ 2) *
            (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
              ∂(volume : Measure (Vec3 × ℝ))) +
          Csp / r ^ 2 * N + Ctime / (2 * r ^ 2) * N := by
      dsimp [E, N] at hEeq hsourceBound hcrossBound htimeIntegralBound ⊢
      rw [hQintegralEq] at htimeIntegralBound
      linarith only [hEeq, hsourceBound, hcrossBound, htimeIntegralBound]
    have hcoef : 0 ≤ 2 * (c₁ + c₁ ^ 2) := by positivity
    have hweighted :
        (c₁ + c₁ ^ 2) *
            (∫ q : Vec3 × ℝ, φ q * (vec3EuclideanNorm (W q)) ^ 2
              ∂(volume : Measure (Vec3 × ℝ))) +
          Csp / r ^ 2 * N + Ctime / (2 * r ^ 2) * N ≤
        (c₁ + c₁ ^ 2 + Csp / r ^ 2 + Ctime / (2 * r ^ 2)) * N := by
      calc
        _ ≤ (c₁ + c₁ ^ 2) * N + Csp / r ^ 2 * N +
            Ctime / (2 * r ^ 2) * N := by
          exact add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hphiEnergyBound (by positivity)) le_rfl)
            le_rfl
        _ = _ := by ring
    have hscaled : (1 / 2 : ℝ) * E ≤
        (c₁ + c₁ ^ 2 + Csp / r ^ 2 + Ctime / (2 * r ^ 2)) * N :=
      hhalfE.trans hweighted
    have hdouble : E ≤
        2 * (c₁ + c₁ ^ 2 + Csp / r ^ 2 + Ctime / (2 * r ^ 2)) * N := by
      linarith only [hscaled]
    dsimp [E, N] at hdouble ⊢
    calc
      _ ≤ 2 * (c₁ + c₁ ^ 2 + Csp / r ^ 2 + Ctime / (2 * r ^ 2)) *
          (∫ q : Vec3 × ℝ, (vec3EuclideanNorm (W q)) ^ 2
            ∂(volume : Measure (Vec3 × ℝ))) := hdouble
      _ = _ := by ring
  exact henergyBound

end ESS
