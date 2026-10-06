/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityChain
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityFatou

/-!
# The product bound at the third level

The product of the squared velocity gradient with the squared second derivatives of the velocity
and first derivatives of the vorticity is integrable, with a bound by the data (the `H³` product
estimate of `lem:vorticity-products`, in the form used by `thm:vorticity-regularity`): at every
time the gradient of a smooth approximation is bounded by the `H²` embedding and the chain of
div–curl estimates, and Fatou's lemma passes the bound to the limit.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Euclidean balls of equal radii have equal volume. -/
theorem vorticity_volume_vec3Ball (x₀ : Vec3) (r : ℝ) :
    volume (vec3Ball x₀ r) = volume (vec3Ball (0 : Vec3) r) := by
  have h : vec3Ball x₀ r = (fun y : Vec3 => y + -x₀) ⁻¹' vec3Ball (0 : Vec3) r := by
    ext y
    simp [vec3Ball, sub_eq_add_neg]
  rw [h, measure_preimage_add_right]

/-- A bounded function has square integral on a ball at most the squared bound times the
volume. -/
theorem vorticity_setIntegral_sq_le_of_bound {x₀ : Vec3} {r M : ℝ} {f : Vec3 → ℝ}
    (hf : Continuous f) (hM : ∀ x, |f x| ≤ M) :
    ∫ x in vec3Ball x₀ r, f x ^ 2 ≤ M ^ 2 * (volume (vec3Ball (0 : Vec3) r)).toReal := by
  have hbd : ∀ x, f x ^ 2 ≤ M ^ 2 := fun x => by
    have h0 := abs_nonneg (f x)
    have h1 := hM x
    nlinarith only [h0, h1, sq_abs (f x)]
  have hfin : volume (vec3Ball x₀ r) < ⊤ :=
    (Metric.isBounded_closedBall.subset (vorticityHeatSmooth_vec3Ball_subset x₀ r)).measure_lt_top
  calc
    ∫ x in vec3Ball x₀ r, f x ^ 2 ≤ ∫ _x in vec3Ball x₀ r, M ^ 2 := by
      apply setIntegral_mono_on (vorticityHeatSmooth_integrableOn_ball (hf.pow 2) x₀ r)
        (integrableOn_const hfin.ne) (isOpen_vec3Ball x₀ r).measurableSet
      exact fun x _ => hbd x
    _ = M ^ 2 * (volume (vec3Ball (0 : Vec3) r)).toReal := by
      rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def, vorticity_volume_vec3Ball]

private theorem vorticityLevelThree_integratedProductEstimate
    {x₀ a t₀ Q Cc K0 K2 K3 : ℝ} (hCc : 0 ≤ Cc) (hQ : 0 ≤ Q)
    (Sf Df Of Tf Ef : ℕ → Vec3 × ℝ → ℝ)
    (cSf : ∀ n, Continuous (Sf n)) (cDf : ∀ n, Continuous (Df n))
    (cOf : ∀ n, Continuous (Of n)) (cTf : ∀ n, Continuous (Tf n))
    (cEf : ∀ n, Continuous (Ef n))
    (hSf0 : ∀ n z, 0 ≤ Sf n z) (hDf0 : ∀ n z, 0 ≤ Df n z)
    (hOf0 : ∀ n z, 0 ≤ Of n z) (hTf0 : ∀ n z, 0 ≤ Tf n z)
    (hbox : ∀ (f : Vec3 × ℝ → ℝ) (r b : ℝ), Continuous f →
      IntegrableOn f (vec3Ball x₀ r ×ˢ Ioo b t₀))
    (hmonoW : ∀ (f : Vec3 × ℝ → ℝ) {r b : ℝ}, Continuous f → (∀ z, 0 ≤ f z) →
      r ≤ 48 / 64 → a ≤ b →
      ∫ z in vec3Ball x₀ r ×ˢ Ioo b t₀, f z ≤
        ∫ z in (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀), f z)
    (hper : ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀,
      (∫ x in vec3Ball x₀ (43 / 64), Df n (x, t) + Of n (x, t) ≤ Q) ∧
      (∀ x, vec3EuclideanNorm (x - x₀) ≤ 43 / 64 →
        Sf n (x, t) ≤ Cc * ∫ y in vec3Ball x₀ (44 / 64),
          Sf n (y, t) + Df n (y, t) + Ef n (y, t)) ∧
      (∫ x in vec3Ball x₀ (44 / 64), Ef n (x, t) ≤
        Cc * ∫ x in vec3Ball x₀ (45 / 64), Tf n (x, t) + Df n (x, t)))
    (hGn : ∀ᶠ n in atTop, ∫ z in (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀), Sf n z ≤ |K0| + 1)
    (hDn : ∀ᶠ n in atTop, ∫ z in (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀), Df n z ≤ |K2| + 1)
    (hΩn : ∀ᶠ n in atTop, ∫ z in (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀), Tf n z ≤ |K3| + 1) :
    ∀ᶠ n in atTop, ∫ z in vec3Ball x₀ (43 / 64) ×ˢ Ioo (a + 1 / 32) t₀,
      Sf n z * (Df n z + Of n z) ≤
        Q * Cc * ((|K0| + 1) + (|K2| + 1) + Cc * ((|K3| + 1) + (|K2| + 1))) := by
  have hsl : ∀ h : Vec3 × ℝ → ℝ, Continuous h → ∀ t : ℝ,
      Continuous (fun x : Vec3 => h (x, t)) :=
    fun h hh t => hh.comp (continuous_id.prodMk continuous_const)
  have hib : ∀ (h : Vec3 → ℝ) (r : ℝ), Continuous h →
      IntegrableOn h (vec3Ball x₀ r) :=
    fun h r hh => vorticityHeatSmooth_integrableOn_ball hh x₀ r
    filter_upwards [hper, hevG, hevD, hevΩ] with n hpn hGn hDn hΩn
    have hIc : ∀ t ∈ Ioo (a + 1 / 32) t₀, t ∈ Icc (a + 1 / 64) t₀ := fun t ht =>
      ⟨by linarith only [ht.1], le_of_lt ht.2⟩
    -- the bound at each time
    have hstep : ∀ t ∈ Ioo (a + 1 / 32) t₀,
        ∫ x in vec3Ball x₀ (43 / 64), Sf n (x, t) * (Df n (x, t) + Of n (x, t)) ≤
          ∫ x in vec3Ball x₀ (44 / 64), Q * Cc * (Sf n (x, t) + Df n (x, t) + Ef n (x, t)) := by
      intro t ht
      obtain ⟨P1, P2, _⟩ := hpn t (hIc t ht)
      set Z : ℝ := Cc * ∫ y in vec3Ball x₀ (44 / 64), (Sf n (y, t) + Df n (y, t) + Ef n (y, t))
        with hZdef
      have hint44 : ∀ f : Vec3 × ℝ → ℝ, Continuous f →
          IntegrableOn (fun y : Vec3 => f (y, t)) (vec3Ball x₀ (44 / 64)) := fun f hf =>
        hib _ _ (hsl f hf t)
      have hZ0 : 0 ≤ Z := mul_nonneg hCc (setIntegral_nonneg (isOpen_vec3Ball x₀ _).measurableSet
        fun y _ => by positivity)
      have hSZ : ∀ x ∈ vec3Ball x₀ (43 / 64), Sf n (x, t) ≤ Z := by
        intro x hx
        have hx' : vec3EuclideanNorm (x - x₀) ≤ 43 / 64 := le_of_lt hx
        calc
          Sf n (x, t) ≤ Cc * ∫ y in vec3Ball x₀ (44 / 64),
              Sf n (y, t) + Df n (y, t) + Ef n (y, t) := P2 x hx'
          _ = Z := by rw [hZdef]
      calc
        ∫ x in vec3Ball x₀ (43 / 64), Sf n (x, t) * (Df n (x, t) + Of n (x, t)) ≤
            ∫ x in vec3Ball x₀ (43 / 64), Z * (Df n (x, t) + Of n (x, t)) := by
          apply setIntegral_mono_on (hib _ _ ((hsl _ (cSf n) t).mul
            ((hsl _ (cDf n) t).add (hsl _ (cOf n) t))))
            (hib _ _ (continuous_const.mul ((hsl _ (cDf n) t).add (hsl _ (cOf n) t))))
            (isOpen_vec3Ball x₀ _).measurableSet
          intro x hx
          exact mul_le_mul_of_nonneg_right (hSZ x hx) (add_nonneg
            (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
              Finset.sum_nonneg fun k _ => sq_nonneg _)
            (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _))
        _ = Z * ∫ x in vec3Ball x₀ (43 / 64), (Df n (x, t) + Of n (x, t)) := integral_const_mul _ _
        _ ≤ Z * Q := mul_le_mul_of_nonneg_left P1 hZ0
        _ = ∫ x in vec3Ball x₀ (44 / 64), Q * Cc * (Sf n (x, t) + Df n (x, t) + Ef n (x, t)) := by
          rw [integral_const_mul, hZdef]
          ring
    have h2 := vorticity_setIntegral_prod_time_mono measurableSet_Ioo
      (hbox _ _ _ ((cSf n).mul ((cDf n).add (cOf n))))
      (hbox _ _ _ (continuous_const.mul (((cSf n).add (cDf n)).add (cEf n)))) hstep
    have hstepE : ∀ t ∈ Ioo (a + 1 / 32) t₀,
        ∫ x in vec3Ball x₀ (44 / 64), Ef n (x, t) ≤
          ∫ x in vec3Ball x₀ (45 / 64), Cc * (Tf n (x, t) + Df n (x, t)) := by
      intro t ht
      rw [integral_const_mul]
      exact (hpn t (hIc t ht)).2.2
    have h3 := vorticity_setIntegral_prod_time_mono measurableSet_Ioo
      (hbox _ _ _ (cEf n)) (hbox _ _ _ (continuous_const.mul ((cTf n).add (cDf n)))) hstepE
    have i1 := hbox _ (44 / 64) (a + 1 / 32) (cSf n)
    have i2 := hbox _ (44 / 64) (a + 1 / 32) (cDf n)
    have i3 := hbox _ (44 / 64) (a + 1 / 32) (cEf n)
    have i4 := hbox _ (45 / 64) (a + 1 / 32) (cTf n)
    have i5 := hbox _ (45 / 64) (a + 1 / 32) (cDf n)
    have hS44 : ∫ z in vec3Ball x₀ (44 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Sf n z ≤ |K0| + 1 :=
      (hmonoW _ (cSf n) (fun z => by simp only [Sf]; positivity) (by norm_num)
        (by linarith only)).trans hGn
    have hD44 : ∫ z in vec3Ball x₀ (44 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Df n z ≤ |K2| + 1 :=
      (hmonoW _ (cDf n) (fun z => by simp only [Df]; positivity) (by norm_num)
        (by linarith only)).trans hDn
    have hT45 : ∫ z in vec3Ball x₀ (45 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Tf n z ≤ |K3| + 1 :=
      (hmonoW _ (cTf n) (fun z => by simp only [Tf]; positivity) (by norm_num)
        (by linarith only)).trans hΩn
    have hD45 : ∫ z in vec3Ball x₀ (45 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Df n z ≤ |K2| + 1 :=
      (hmonoW _ (cDf n) (fun z => by simp only [Df]; positivity) (by norm_num)
        (by linarith only)).trans hDn
    have hE44 : ∫ z in vec3Ball x₀ (44 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Ef n z ≤
        Cc * ((|K3| + 1) + (|K2| + 1)) := by
      have e : ∫ z in vec3Ball x₀ (45 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Cc * (Tf n z + Df n z) =
          Cc * ((∫ z in vec3Ball x₀ (45 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Tf n z) +
            ∫ z in vec3Ball x₀ (45 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Df n z) := by
        rw [integral_const_mul]
        congr 1
        exact integral_add i4 i5
      exact h3.trans (e.le.trans (mul_le_mul_of_nonneg_left (add_le_add hT45 hD45) hCc))
    have e : ∫ z in vec3Ball x₀ (44 / 64) ×ˢ Ioo (a + 1 / 32) t₀,
        Q * Cc * (Sf n z + Df n z + Ef n z) =
        Q * Cc * ((∫ z in vec3Ball x₀ (44 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Sf n z) +
          (∫ z in vec3Ball x₀ (44 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Df n z) +
          ∫ z in vec3Ball x₀ (44 / 64) ×ˢ Ioo (a + 1 / 32) t₀, Ef n z) := by
      rw [integral_const_mul]
      congr 1
      exact (integral_add (i1.add i2) i3).trans (congrArg (· + _) (integral_add i1 i2))
    have hQC : 0 ≤ Q * Cc := mul_nonneg hQ hCc
    exact h2.trans (e.le.trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hS44 hD44) hE44) hQC))

private theorem vorticityLevelThree_timeSliceBounds
    (x₀ a t₀ M Ch Cc AU H4 H5 Q Kw K1 : ℝ) (hCc : 0 ≤ Cc)
    (hAU : 0 ≤ AU)
    (hAUdef : AU = 3 * (M ^ 2 * (volume (vec3Ball (0 : Vec3) (47 / 64))).toReal))
    (U : Fin 3 → Vec3 × ℝ → ℝ) (G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ)
    (hU : ∀ i, MemLp (U i) 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)))
    (hG : ∀ i j, MemLp (G i j) 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)))
    (hD2 : ∀ i j k, MemLp (D2 i j k) 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)))
    (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)))
    (hΩ2 : ∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)))
    (hw : ∀ i, MemLp (vorticityCurl G i) 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)))
    (hbmS : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)) → ∀ n, ContDiff ℝ (⊤ : ℕ∞) (bm f n))
    (hc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict
      (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)) → ∀ n, Continuous (bm f n))
    (hUn : ∀ n i z, |bm (U i) n z| ≤ M)
    (hsw : ∀ᶠ n in atTop, ∀ i : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (47 / 64), bm (vorticityCurl G i) n (x, t) ^ 2 ≤ Ch * |Kw| + 1)
    (hsΩ : ∀ᶠ n in atTop, ∀ i m : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (47 / 64), bm (Ω1 i m) n (x, t) ^ 2 ≤ Ch * |K1| + 1)
    (hsl : ∀ h : Vec3 × ℝ → ℝ, Continuous h → ∀ t : ℝ,
      Continuous (fun x : Vec3 => h (x, t)))
    (hib : ∀ (h : Vec3 → ℝ) (r : ℝ), Continuous h → IntegrableOn h (vec3Ball x₀ r))
    (hmonoB : ∀ (h : Vec3 → ℝ) {r₁ r₂ : ℝ}, Continuous h → (∀ x, 0 ≤ h x) → r₁ ≤ r₂ →
      ∫ x in vec3Ball x₀ r₁, h x ≤ ∫ x in vec3Ball x₀ r₂, h x)
    (hchainSlice : ∀ n t, t ∈ Icc (a + 1 / 64) t₀ →
      (∫ x in vec3Ball x₀ (46 / 64), ∑ i : Fin 3, ∑ j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ Cc * ∫ x in vec3Ball x₀ (47 / 64),
          (∑ l : Fin 3, bm (vorticityCurl G l) n (x, t) ^ 2 +
            ∑ i : Fin 3, bm (U i) n (x, t) ^ 2)) ∧
      (∫ x in vec3Ball x₀ (45 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (D2 i j k) n (x, t) ^ 2 ≤ Cc * ∫ x in vec3Ball x₀ (46 / 64),
          (∑ l : Fin 3, ∑ m : Fin 3, bm (Ω1 l m) n (x, t) ^ 2 +
            ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n (x, t) ^ 2)) ∧
      (∫ x in vec3Ball x₀ (44 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3,
        spatialPartial (bm (D2 i j k) n) c (x, t) ^ 2 ≤ Cc * ∫ x in vec3Ball x₀ (45 / 64),
          (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, bm (Ω2 l j k) n (x, t) ^ 2 +
            ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, bm (D2 i j k) n (x, t) ^ 2)) ∧
      (∀ x, vec3EuclideanNorm (x - x₀) ≤ 43 / 64 → ∀ i j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ Cc * ∫ y in vec3Ball x₀ (44 / 64),
          (bm (G i j) n (y, t) ^ 2 + ∑ k : Fin 3, bm (D2 i j k) n (y, t) ^ 2 +
            ∑ k : Fin 3, ∑ c : Fin 3, spatialPartial (bm (D2 i j k) n) c (y, t) ^ 2))) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀,
      (∫ x in vec3Ball x₀ (43 / 64), ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          bm (D2 i j k) n (x, t) ^ 2) + ∑ i : Fin 3, ∑ j : Fin 3, bm (Ω1 i j) n (x, t) ^ 2) ≤ Q) ∧
      (∀ x, vec3EuclideanNorm (x - x₀) ≤ 43 / 64 → ∀ i j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ Cc * ∫ y in vec3Ball x₀ (44 / 64), (bm (G i j) n (y, t) ^ 2 +
          ∑ k : Fin 3, bm (D2 i j k) n (y, t) ^ 2 +
            ∑ k : Fin 3, ∑ c : Fin 3, spatialPartial (bm (D2 i j k) n) c (y, t) ^ 2)) ∧
      (∫ x in vec3Ball x₀ (44 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3,
          spatialPartial (bm (D2 i j k) n) c (x, t) ^ 2 ≤
        Cc * ∫ x in vec3Ball x₀ (45 / 64), (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          bm (Ω2 l j k) n (x, t) ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            bm (D2 i j k) n (x, t) ^ 2)) := by
    filter_upwards [hsw, hsΩ] with n hn1 hn2 t ht
    obtain ⟨c1, c2, c3, c4⟩ := hchainSlice n t (hIc t ht)
    refine ⟨?_, c4, c3⟩
    have cw : ∀ l, Continuous (fun x : Vec3 => bm (vorticityCurl G l) n (x, t) ^ 2) := fun l =>
      (hsl _ (hc _ (hw l) n) t).pow 2
    have cU : ∀ i, Continuous (fun x : Vec3 => bm (U i) n (x, t) ^ 2) := fun i =>
      (hsl _ (hc _ (hU i) n) t).pow 2
    have cG : ∀ i j, Continuous (fun x : Vec3 => bm (G i j) n (x, t) ^ 2) := fun i j =>
      (hsl _ (hc _ (hG i j) n) t).pow 2
    have cΩ : ∀ i j, Continuous (fun x : Vec3 => bm (Ω1 i j) n (x, t) ^ 2) := fun i j =>
      (hsl _ (hc _ (hΩ1 i j) n) t).pow 2
    have cD : ∀ i j k, Continuous (fun x : Vec3 => bm (D2 i j k) n (x, t) ^ 2) := fun i j k =>
      (hsl _ (hc _ (hD2 i j k) n) t).pow 2
    have sG : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => cG i j
    have sΩ : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, bm (Ω1 i j) n (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => cΩ i j
    have sD : Continuous (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (D2 i j k) n (x, t) ^ 2) :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_finsetSum _ fun k _ => cD i j k
    -- the vorticity and velocity at this time
    have A1 : ∫ x in vec3Ball x₀ (47 / 64), (∑ l : Fin 3, bm (vorticityCurl G l) n (x, t) ^ 2 +
        ∑ i : Fin 3, bm (U i) n (x, t) ^ 2) ≤ 3 * (Ch * |Kw| + 1) + AU := by
      rw [integral_add (integrable_finsetSum _ fun l _ => hib _ _ (cw l))
          (integrable_finsetSum _ fun i _ => hib _ _ (cU i)),
        integral_finsetSum _ fun l _ => hib _ _ (cw l),
        integral_finsetSum _ fun i _ => hib _ _ (cU i)]
      apply add_le_add
      · calc
          _ ≤ ∑ _l : Fin 3, (Ch * |Kw| + 1) := Finset.sum_le_sum fun l _ => hn1 l t ht
          _ = 3 * (Ch * |Kw| + 1) := by simp; ring
      · calc
          _ ≤ ∑ _i : Fin 3, M ^ 2 * (volume (vec3Ball (0 : Vec3) (47 / 64))).toReal :=
            Finset.sum_le_sum fun i _ => vorticity_setIntegral_sq_le_of_bound
              (hsl _ (hc _ (hU i) n) t) (fun x => hUn n i (x, t))
          _ = AU := by simp [hAUdef]
    have A2 : ∫ x in vec3Ball x₀ (46 / 64), ∑ i : Fin 3, ∑ j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ H4 :=
      c1.trans (mul_le_mul_of_nonneg_left A1 hCc)
    have A3 : ∫ x in vec3Ball x₀ (46 / 64), (∑ l : Fin 3, ∑ m : Fin 3,
        bm (Ω1 l m) n (x, t) ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n (x, t) ^ 2) ≤
        9 * (Ch * |K1| + 1) + H4 := by
      rw [integral_add (hib _ _ sΩ) (hib _ _ sG)]
      apply add_le_add _ A2
      rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => hib _ _ (cΩ l m)]
      calc
        _ ≤ ∑ _l : Fin 3, ∑ _m : Fin 3, (Ch * |K1| + 1) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [integral_finsetSum _ fun m _ => hib _ _ (cΩ l m)]
          exact Finset.sum_le_sum fun m _ =>
            (hmonoB _ (cΩ l m) (fun x => sq_nonneg _) (by norm_num)).trans (hn2 l m t ht)
        _ = 9 * (Ch * |K1| + 1) := by simp; ring
    have A4 : ∫ x in vec3Ball x₀ (45 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (D2 i j k) n (x, t) ^ 2 ≤ H5 :=
      c2.trans (mul_le_mul_of_nonneg_left A3 hCc)
    rw [integral_add (hib _ _ sD) (hib _ _ sΩ)]
    apply add_le_add
    · exact (hmonoB _ sD (fun x => by positivity) (by norm_num)).trans A4
    · rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => hib _ _ (cΩ l m)]
      calc
        _ ≤ ∑ _l : Fin 3, ∑ _m : Fin 3, (Ch * |K1| + 1) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [integral_finsetSum _ fun m _ => hib _ _ (cΩ l m)]
          exact Finset.sum_le_sum fun m _ =>
            (hmonoB _ (cΩ l m) (fun x => sq_nonneg _) (by norm_num)).trans (hn2 l m t ht)
        _ = 9 * (Ch * |K1| + 1) := by simp; ring

private theorem vorticityLevelThree_eventualSquareBounds
    {W : Set (Vec3 × ℝ)} (bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ)
    (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 (volume.restrict W))
    (hD2 : ∀ i j k, MemLp (D2 i j k) 2 (volume.restrict W))
    (hΩ2 : ∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict W))
    (hc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n, Continuous (bm f n))
    (hWb : Bornology.IsBounded W)
    (htend : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      Tendsto (fun n => ∫ z in W, bm f n z ^ 2) atTop (𝓝 (∫ z in W, f z ^ 2)))
    (hK0 : ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 ≤ K0)
    (hK2 : ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k z ^ 2 ≤ K2)
    (hK3 : ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2 ≤ K3) :
    (∀ᶠ n in atTop, ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n z ^ 2 ≤
      |K0| + 1) ∧
    (∀ᶠ n in atTop, ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      bm (D2 i j k) n z ^ 2 ≤ |K2| + 1) ∧
    (∀ᶠ n in atTop, ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      bm (Ω2 i j k) n z ^ 2 ≤ |K3| + 1) := by
  have hsqW : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      IntegrableOn (fun z => f z ^ 2) W := fun f hf =>
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hsum2 : ∀ f : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
      (∀ i j, MemLp (f i j) 2 (volume.restrict W)) →
      ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, f i j z ^ 2 =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in W, f i j z ^ 2 := fun f hf => by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hsqW _ (hf i j)]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hsqW _ (hf i j)
  have hsum3 : ∀ f : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
      (∀ i j k, MemLp (f i j k) 2 (volume.restrict W)) →
      ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k z ^ 2 =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in W, f i j k z ^ 2 := fun f hf => by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => hsqW _ (hf i j k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hsqW _ (hf i j k)]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hsqW _ (hf i j k)
  have hevG : ∀ᶠ n in atTop, ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3,
      bm (G i j) n z ^ 2 ≤ |K0| + 1 := by
    have hlim : Tendsto (fun n => ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3,
        bm (G i j) n z ^ 2) atTop (𝓝 (∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2)) := by
      rw [hsum2 G hG]
      refine (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        htend _ (hG i j)).congr fun n => ?_
      exact (hsum2 (fun i j => bm (G i j) n) fun i j =>
        vorticity_memLp_two_of_continuous_bounded (hc _ (hG i j) n) hWb).symm
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_of_le_of_lt (hK0.trans (le_abs_self K0))
      (lt_add_one _)))] with n hn
    exact le_of_lt hn
  have hevD : ∀ᶠ n in atTop, ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      bm (D2 i j k) n z ^ 2 ≤ |K2| + 1 := by
    have hlim : Tendsto (fun n => ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (D2 i j k) n z ^ 2) atTop
        (𝓝 (∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k z ^ 2)) := by
      rw [hsum3 D2 hD2]
      refine (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        tendsto_finsetSum _ fun k _ => htend _ (hD2 i j k)).congr fun n => ?_
      exact (hsum3 (fun i j k => bm (D2 i j k) n) fun i j k =>
        vorticity_memLp_two_of_continuous_bounded (hc _ (hD2 i j k) n) hWb).symm
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_of_le_of_lt (hK2.trans (le_abs_self K2))
      (lt_add_one _)))] with n hn
    exact le_of_lt hn
  have hevΩ : ∀ᶠ n in atTop, ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      bm (Ω2 i j k) n z ^ 2 ≤ |K3| + 1 := by
    have hlim : Tendsto (fun n => ∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (Ω2 i j k) n z ^ 2) atTop
        (𝓝 (∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2)) := by
      rw [hsum3 Ω2 hΩ2]
      refine (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        tendsto_finsetSum _ fun k _ => htend _ (hΩ2 i j k)).congr fun n => ?_
      exact (hsum3 (fun i j k => bm (Ω2 i j k) n) fun i j k =>
        vorticity_memLp_two_of_continuous_bounded (hc _ (hΩ2 i j k) n) hWb).symm
    filter_upwards [hlim.eventually (gt_mem_nhds (lt_of_le_of_lt (hK3.trans (le_abs_self K3))
      (lt_add_one _)))] with n hn
    exact le_of_lt hn
  exact ⟨hevG, hevD, hevΩ⟩

/-- The third-level product bound. -/
theorem vorticityLevelThree_SP (M Kw K1 K0 K2 K3 : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
      (G Ω1 F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
      (D2 Ω2 F' : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    a + 1 / 32 < t₀ → t₀ ≤ a + 1 →
    (∀ i, MemLp (U i) 2 (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀))) →
    (∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀)), ∀ i, |U i z| ≤ M) →
    (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j k, MemLp (D2 i j k) 2 (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j, MemLp (Ω1 i j) 2 (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j, MemLp (F i j) 2 (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j m, MemLp (F' i j m) 2 (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀))) →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, U i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, G i j y * ψ y) →
    (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, G i j y * spatialPartial ψ k y =
        -∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, D2 i j k y * ψ y) →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, vorticityCurl G i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, Ω1 i j y * ψ y) →
    (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, Ω1 i j y * spatialPartial ψ k y =
        -∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, Ω2 i j k y * ψ y) →
    (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, ∑ i : Fin 3, U i y * spatialPartial ψ i y = 0) →
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀,
          vorticityCurl G i y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, ∑ j : Fin 3, F i j y * spatialPartial ψ j y) →
    (∀ i m : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀,
          Ω1 i m y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, F' i j m y * spatialPartial ψ j y) →
    (∀ i, ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀,
      (vorticityCurl G i y ^ 2 + ∑ j : Fin 3, F i j y ^ 2) ≤ Kw) →
    (∀ i m, ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀,
      (Ω1 i m y ^ 2 + ∑ j : Fin 3, F' i j m y ^ 2) ≤ K1) →
    ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀, ∑ i : Fin 3, ∑ j : Fin 3, G i j y ^ 2 ≤ K0 →
    ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀,
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k y ^ 2 ≤ K2 →
    ∫ y in vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀,
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k y ^ 2 ≤ K3 →
    Integrable (fun y => (∑ i : Fin 3, ∑ j : Fin 3, G i j y ^ 2) *
        ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k y ^ 2) +
          ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j y ^ 2))
        (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ Ioo (a + 1 / 32) t₀)) ∧
      ∫ y in vec3Ball x₀ (43 / 64) ×ˢ Ioo (a + 1 / 32) t₀,
        (∑ i : Fin 3, ∑ j : Fin 3, G i j y ^ 2) *
          ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k y ^ 2) +
            ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j y ^ 2) ≤ K := by
  obtain ⟨Ch, hCh, hsup⟩ := vorticity_heatSup_bm (r := 47 / 64) (R := 48 / 64) (κ := 1 / 64)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Cc, hCc, hchain⟩ := vorticityChain (ρ := 47 / 64) (by norm_num)
  set AU : ℝ := 3 * (M ^ 2 * (volume (vec3Ball (0 : Vec3) (47 / 64))).toReal) with hAUdef
  have hAU : 0 ≤ AU := by positivity
  set H4 : ℝ := Cc * (3 * (Ch * |Kw| + 1) + AU) with hH4def
  set H5 : ℝ := Cc * (9 * (Ch * |K1| + 1) + H4) with hH5def
  set Q : ℝ := H5 + 9 * (Ch * |K1| + 1) with hQdef
  have ⟨hH4, hH5, hQ⟩ : 0 ≤ H4 ∧ 0 ≤ H5 ∧ 0 ≤ Q := by positivity
  refine ⟨Q * Cc * ((|K0| + 1) + (|K2| + 1) + Cc * ((|K3| + 1) + (|K2| + 1))), by positivity, ?_⟩
  intro x₀ a t₀ U G Ω1 F D2 Ω2 F' hat hta hU hUb hG hD2 hΩ1 hΩ2 hF hF' hdU hdG hdw hdΩ1 hdiv
    hheatw hheatΩ hKw hK1 hK0 hK2 hK3
  set W := (vec3Ball x₀ (48 / 64) ×ˢ Ioo a t₀ : Set (Vec3 × ℝ)) with hWdef
  have hWo : IsOpen W := vorticityBox_isOpen x₀ _ a t₀
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ _ _ (Metric.isBounded_Ioo a t₀)
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hint : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → IntegrableOn f W :=
    fun f hf => hf.integrable (by norm_num)
  have hloc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) := fun f hf =>
    ((integrable_indicator_iff hWm).2 (hint f hf)).locallyIntegrable
  have hw := vorticityCurl_memLp hG
  obtain ⟨ε, hεpos, hεlim, hεle⟩ := vorticity_engine_radii (show (0 : ℝ) < 1 / 768 by norm_num)
  set bm : (Vec3 × ℝ → ℝ) → ℕ → Vec3 × ℝ → ℝ :=
    fun f n => vorticityBackMollify W f (ε n) (hεpos n) with hbmdef
  have hbmS : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n,
      ContDiff ℝ (⊤ : ℕ∞) (bm f n) := fun f hf n =>
    vorticityBackMollify_contDiff (hεpos n) (hloc f hf)
  have hball : ∀ n, ∀ z ∈ vec3Ball x₀ (47 / 64) ×ˢ Ioc (a + 1 / 128) t₀,
      Metric.closedBall (z - vorticityBackShift (ε n)) (ε n) ⊆ W := fun n z hz =>
    vorticityBackBall_subset (hεpos n) (by have := hεle n; linarith only [this])
      (by have := hεle n; linarith only [this]) hz
  have hrel := fun n z hz => vorticitySmoothRelations hWo hWb hU hG hD2 hΩ1 hΩ2 hdU hdG hdw hdΩ1
    hdiv (hεpos n) (hball n z hz)
  have hUn : ∀ n i z, |bm (U i) n z| ≤ M := fun n i z =>
    vorticityBackMollify_abs_le (hεpos n)
      (vorticity_indicator_bound hWm hM (by filter_upwards [hUb] with z hz using hz i)) z
  -- uniform-in-time bounds of the vorticity and its first derivatives
  have hsw : ∀ᶠ n in atTop, ∀ i : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (47 / 64), bm (vorticityCurl G i) n (x, t) ^ 2 ≤ Ch * |Kw| + 1 := by
    rw [eventually_all]
    intro i
    filter_upwards [(hsup x₀ a t₀ (vorticityCurl G i) (F i) (by linarith only [hat]) hta (hw i)
      (hF i) (hheatw i) ε hεpos hεlim).1] with n hn t ht
    refine (hn t ht).trans ?_
    gcongr
    exact (hKw i).trans (le_abs_self Kw)
  have hsΩ : ∀ᶠ n in atTop, ∀ i m : Fin 3, ∀ t ∈ Icc (a + 1 / 64) t₀,
      ∫ x in vec3Ball x₀ (47 / 64), bm (Ω1 i m) n (x, t) ^ 2 ≤ Ch * |K1| + 1 := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro m
    filter_upwards [(hsup x₀ a t₀ (Ω1 i m) (fun j => F' i j m) (by linarith only [hat]) hta
      (hΩ1 i m) (fun j => hF' i j m) (hheatΩ i m) ε hεpos hεlim).1] with n hn t ht
    refine (hn t ht).trans ?_
    gcongr
    exact (hK1 i m).trans (le_abs_self K1)
  -- helpers on balls
  have hsl : ∀ h : Vec3 × ℝ → ℝ, Continuous h → ∀ t : ℝ, Continuous (fun x : Vec3 => h (x, t)) :=
    fun h hh t => hh.comp (continuous_id.prodMk continuous_const)
  have hib : ∀ (h : Vec3 → ℝ) (r : ℝ), Continuous h → IntegrableOn h (vec3Ball x₀ r) :=
    fun h r hh => vorticityHeatSmooth_integrableOn_ball hh x₀ r
  have hmonoB : ∀ (h : Vec3 → ℝ) {r₁ r₂ : ℝ}, Continuous h → (∀ x, 0 ≤ h x) → r₁ ≤ r₂ →
      ∫ x in vec3Ball x₀ r₁, h x ≤ ∫ x in vec3Ball x₀ r₂, h x := fun h r₁ r₂ hh h0 hr =>
    setIntegral_mono_set (hib h r₂ hh) (Eventually.of_forall h0)
      (Eventually.of_forall (vec3Ball_mono hr))
  have hc : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → ∀ n,
      Continuous (bm f n) := fun f hf n => (hbmS f hf n).continuous
  -- the chain at each time
  have hchainSlice : ∀ n t, t ∈ Icc (a + 1 / 64) t₀ →
      (∫ x in vec3Ball x₀ (46 / 64), ∑ i : Fin 3, ∑ j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ Cc * ∫ x in vec3Ball x₀ (47 / 64),
          (∑ l : Fin 3, bm (vorticityCurl G l) n (x, t) ^ 2 +
            ∑ i : Fin 3, bm (U i) n (x, t) ^ 2)) ∧
      (∫ x in vec3Ball x₀ (45 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        bm (D2 i j k) n (x, t) ^ 2 ≤ Cc * ∫ x in vec3Ball x₀ (46 / 64),
          (∑ l : Fin 3, ∑ m : Fin 3, bm (Ω1 l m) n (x, t) ^ 2 +
            ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n (x, t) ^ 2)) ∧
      (∫ x in vec3Ball x₀ (44 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3,
        spatialPartial (bm (D2 i j k) n) c (x, t) ^ 2 ≤ Cc * ∫ x in vec3Ball x₀ (45 / 64),
          (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, bm (Ω2 l j k) n (x, t) ^ 2 +
            ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, bm (D2 i j k) n (x, t) ^ 2)) ∧
      (∀ x, vec3EuclideanNorm (x - x₀) ≤ 43 / 64 → ∀ i j : Fin 3,
        bm (G i j) n (x, t) ^ 2 ≤ Cc * ∫ y in vec3Ball x₀ (44 / 64),
          (bm (G i j) n (y, t) ^ 2 + ∑ k : Fin 3, bm (D2 i j k) n (y, t) ^ 2 +
            ∑ k : Fin 3, ∑ c : Fin 3, spatialPartial (bm (D2 i j k) n) c (y, t) ^ 2)) := by
    intro n t ht
    have hreg : ∀ x ∈ vec3Ball x₀ (47 / 64),
        (x, t) ∈ vec3Ball x₀ (47 / 64) ×ˢ Ioc (a + 1 / 128) t₀ := fun x hx =>
      ⟨hx, by linarith only [ht.1], ht.2⟩
    obtain ⟨c1, c2, c3, c4⟩ := hchain x₀ t (fun i => bm (U i) n)
      (fun i => bm (vorticityCurl G i) n) (fun i j => bm (G i j) n) (fun i j => bm (Ω1 i j) n)
      (fun i j k => bm (D2 i j k) n) (fun i j k => bm (Ω2 i j k) n)
      (fun i => hbmS _ (hU i) n) (fun i j => hbmS _ (hG i j) n)
      (fun i j k => hbmS _ (hD2 i j k) n) (fun i => hc _ (hw i) n) (fun i j => hc _ (hΩ1 i j) n)
      (fun i j k => hc _ (hΩ2 i j k) n)
      (fun x hx => (hrel n _ (hreg x hx)).1) (fun x hx => (hrel n _ (hreg x hx)).2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.1) (fun x hx => (hrel n _ (hreg x hx)).2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.2.2.1)
      (fun x hx => (hrel n _ (hreg x hx)).2.2.2.2.2.2.2.1)
    have e1 : (47 / 64 : ℝ) - 1 / 64 = 46 / 64 := by norm_num
    have e2 : (47 / 64 : ℝ) - 2 / 64 = 45 / 64 := by norm_num
    have e3 : (47 / 64 : ℝ) - 3 / 64 = 44 / 64 := by norm_num
    have e4 : (47 / 64 : ℝ) - 4 / 64 = 43 / 64 := by norm_num
    rw [e1] at c1 c2
    rw [e2] at c2 c3
    rw [e3] at c3 c4
    rw [e4] at c4
    exact ⟨c1, c2, c3, c4⟩
  have hper := vorticityLevelThree_timeSliceBounds x₀ a t₀ M Ch Cc AU H4 H5 Q Kw K1
    hCc hAU hAUdef U G Ω1 D2 Ω2 bm hU hG hD2 hΩ1 hΩ2 hw hbmS hc hUn hsw hsΩ hsl hib hmonoB
    hchainSlice
  -- convergence of the integrals of squares on the box
  have htend : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) →
      Tendsto (fun n => ∫ z in W, bm f n z ^ 2) atTop (𝓝 (∫ z in W, f z ^ 2)) := fun f hf =>
    vorticity_tendsto_integral_sq (fun n => vorticity_memLp_two_of_continuous_bounded
      (hc f hf n) hWb) hf (vorticityBackMollify_tendsto_restrict hWm hWm subset_rfl hf hεlim hεpos)
  have ⟨hevG, hevD, hevΩ⟩ := vorticityLevelThree_eventualSquareBounds bm G D2 Ω2 hG hD2 hΩ2
    hc hWb htend hK0 hK2 hK3
  -- continuity of the smooth integrands
  set Sf : ℕ → Vec3 × ℝ → ℝ := fun n z => ∑ i : Fin 3, ∑ j : Fin 3, bm (G i j) n z ^ 2
    with hSfdef
  set Df : ℕ → Vec3 × ℝ → ℝ := fun n z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    bm (D2 i j k) n z ^ 2 with hDfdef
  set Of : ℕ → Vec3 × ℝ → ℝ := fun n z => ∑ i : Fin 3, ∑ j : Fin 3, bm (Ω1 i j) n z ^ 2
    with hOfdef
  set Tf : ℕ → Vec3 × ℝ → ℝ := fun n z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    bm (Ω2 i j k) n z ^ 2 with hTfdef
  set Ef : ℕ → Vec3 × ℝ → ℝ := fun n z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3,
    spatialPartial (bm (D2 i j k) n) c z ^ 2 with hEfdef
  have cSf : ∀ n, Continuous (Sf n) := fun n => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (hc _ (hG i j) n).pow 2
  have cDf : ∀ n, Continuous (Df n) := fun n => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => (hc _ (hD2 i j k) n).pow 2
  have cOf : ∀ n, Continuous (Of n) := fun n => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (hc _ (hΩ1 i j) n).pow 2
  have cTf : ∀ n, Continuous (Tf n) := fun n => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => (hc _ (hΩ2 i j k) n).pow 2
  have cEf : ∀ n, Continuous (Ef n) := fun n => continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      continuous_finsetSum _ fun c _ =>
        (CKN.spatialPartial_contDiff (hbmS _ (hD2 i j k) n) c).continuous.pow 2
  have hbox : ∀ (f : Vec3 × ℝ → ℝ) (r b : ℝ), Continuous f →
      IntegrableOn f (vec3Ball x₀ r ×ˢ Ioo b t₀) := fun f r b hf =>
    vorticityHeatSmooth_integrableOn_box hf x₀ r b t₀
  have hsubW : ∀ {r b : ℝ}, r ≤ 48 / 64 → a ≤ b → vec3Ball x₀ r ×ˢ Ioo b t₀ ⊆ W := by
    intro r b hr hb z hz
    exact ⟨vec3Ball_mono hr hz.1, lt_of_le_of_lt hb hz.2.1, hz.2.2⟩
  have hmonoW : ∀ (f : Vec3 × ℝ → ℝ) {r b : ℝ}, Continuous f → (∀ z, 0 ≤ f z) → r ≤ 48 / 64 →
      a ≤ b → ∫ z in vec3Ball x₀ r ×ˢ Ioo b t₀, f z ≤ ∫ z in W, f z := fun f r b hf h0 hr hb =>
    setIntegral_mono_set (vorticity_integrableOn_of_continuous_bounded hf hWb)
      (Eventually.of_forall h0) (Eventually.of_forall (hsubW hr hb))
  have hperAgg : ∀ᶠ n in atTop, ∀ t ∈ Icc (a + 1 / 64) t₀,
      (∫ x in vec3Ball x₀ (43 / 64), Df n (x, t) + Of n (x, t) ≤ Q) ∧
      (∀ x, vec3EuclideanNorm (x - x₀) ≤ 43 / 64 →
        Sf n (x, t) ≤ Cc * ∫ y in vec3Ball x₀ (44 / 64),
          Sf n (y, t) + Df n (y, t) + Ef n (y, t)) ∧
      (∫ x in vec3Ball x₀ (44 / 64), Ef n (x, t) ≤
        Cc * ∫ x in vec3Ball x₀ (45 / 64), Tf n (x, t) + Df n (x, t)) := by
    filter_upwards [hper] with n hn t ht
    obtain ⟨h1, h2, h3⟩ := hn t ht
    exact ⟨by simpa [Df, Of] using h1,
      by simpa [Sf, Df, Ef] using h2,
      by simpa [Ef, Tf, Df] using h3⟩
  have hEv := vorticityLevelThree_integratedProductEstimate hCc hQ Sf Df Of Tf Ef
    cSf cDf cOf cTf cEf
    (fun n z => by simp only [Sf]; positivity)
    (fun n z => by simp only [Df]; positivity)
    (fun n z => by simp only [Of]; positivity)
    (fun n z => by simp only [Tf]; positivity)
    hbox hmonoW hperAgg hevG hevD hevΩ
  -- Fatou
  set W' := (vec3Ball x₀ (43 / 64) ×ˢ Ioo (a + 1 / 32) t₀ : Set (Vec3 × ℝ)) with hW'def
  have hW'W : W' ⊆ W := hsubW (by norm_num) (by linarith only)
  have hW'm : MeasurableSet W' := (vorticityBox_isOpen x₀ _ _ t₀).measurableSet
  have hW'b : Bornology.IsBounded W' := hWb.subset hW'W
  let ι := (Fin 3 × Fin 3) ⊕ ((Fin 3 × Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3))
  let A : ι → Vec3 × ℝ → ℝ := Sum.elim (fun p => G p.1 p.2)
    (Sum.elim (fun p => D2 p.1 p.2.1 p.2.2) (fun p => Ω1 p.1 p.2))
  let an : ι → ℕ → Vec3 × ℝ → ℝ := fun p n => bm (A p) n
  have hA : ∀ p, MemLp (A p) 2 (volume.restrict W) := by
    rintro (⟨i, j⟩ | ⟨i, j, k⟩ | ⟨i, j⟩)
    · exact hG i j
    · exact hD2 i j k
    · exact hΩ1 i j
  have hfatou := vorticity_integral_le_of_L2_tendsto (μ := volume.restrict W') (ι := ι)
    (a := an) (A := A)
    (fun p n => vorticity_memLp_two_of_continuous_bounded (hc _ (hA p) n) hW'b)
    (fun p => (hA p).mono_measure (Measure.restrict_mono hW'W le_rfl))
    (fun p => vorticityBackMollify_tendsto_restrict hWm hW'm hW'W (hA p) hεlim hεpos)
    (H := fun v => (∑ i : Fin 3, ∑ j : Fin 3, v (Sum.inl (i, j)) ^ 2) *
      ((∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, v (Sum.inr (Sum.inl (i, j, k))) ^ 2) +
        ∑ i : Fin 3, ∑ j : Fin 3, v (Sum.inr (Sum.inr (i, j))) ^ 2))
    (by fun_prop) (fun v => by positivity)
    (fun n => vorticity_integrableOn_of_continuous_bounded ((cSf n).mul ((cDf n).add (cOf n)))
      hW'b)
    hEv
  exact hfatou

end ESS
