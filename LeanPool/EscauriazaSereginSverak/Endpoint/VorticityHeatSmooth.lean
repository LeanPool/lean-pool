/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityEnergyIntegrated
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreMixed
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Local energy estimate for smooth solutions of the heat equation

For a smooth solution of `∂ₜ w - Δ w = div F` on a cylinder `B_R × (a, b)`, a space-time cutoff
vanishing near the bottom of the cylinder gives the interior bound for the spatial `L²` norm of
`w` at every later time up to the top and for the spatial gradient of `w` in `L²`, in terms of
the `L²` norms of `w` and `F` on the cylinder. This is the smooth estimate behind the energy
levels of `thm:vorticity-regularity`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

section Calculus

variable {A B : Vec3 × ℝ → ℝ}

theorem vorticityHeatSmooth_spatialPartial_eq (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial A j p = fderiv ℝ A p (basisVec j, 0) :=
  spatialPartial_eq_product_fderiv (hA.differentiable (by simp) p) j

theorem vorticityHeatSmooth_timePartial_eq (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (p : Vec3 × ℝ) :
    timePartial A p = fderiv ℝ A p (0, 1) :=
  timePartial_eq_product_fderiv (hA.differentiable (by simp) p)

theorem vorticityHeatSmooth_spatialPartial_contDiff (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => spatialPartial A j p) := by
  have h : (fun p : Vec3 × ℝ => spatialPartial A j p) =
      fun p => fderiv ℝ A p (basisVec j, 0) :=
    funext (vorticityHeatSmooth_spatialPartial_eq hA j)
  rw [h]
  exact (hA.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem vorticityHeatSmooth_timePartial_contDiff (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => timePartial A p) := by
  have h : (fun p : Vec3 × ℝ => timePartial A p) = fun p => fderiv ℝ A p (0, 1) :=
    funext (vorticityHeatSmooth_timePartial_eq hA)
  rw [h]
  exact (hA.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem vorticityHeatSmooth_spatialPartial_mul (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => A q * B q) j p =
      A p * spatialPartial B j p + B p * spatialPartial A j p := by
  rw [vorticityHeatSmooth_spatialPartial_eq (hA.mul hB),
    vorticityHeatSmooth_spatialPartial_eq hA, vorticityHeatSmooth_spatialPartial_eq hB,
    fderiv_fun_mul (hA.differentiable (by simp) p) (hB.differentiable (by simp) p)]
  simp [smul_eq_mul]

theorem vorticityHeatSmooth_timePartial_mul (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (p : Vec3 × ℝ) :
    timePartial (fun q : Vec3 × ℝ => A q * B q) p =
      A p * timePartial B p + B p * timePartial A p := by
  rw [vorticityHeatSmooth_timePartial_eq (hA.mul hB),
    vorticityHeatSmooth_timePartial_eq hA, vorticityHeatSmooth_timePartial_eq hB,
    fderiv_fun_mul (hA.differentiable (by simp) p) (hB.differentiable (by simp) p)]
  simp [smul_eq_mul]

theorem vorticityHeatSmooth_spatialPartial_add (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => A q + B q) j p =
      spatialPartial A j p + spatialPartial B j p := by
  rw [vorticityHeatSmooth_spatialPartial_eq (hA.add hB),
    vorticityHeatSmooth_spatialPartial_eq hA, vorticityHeatSmooth_spatialPartial_eq hB,
    fderiv_fun_add (hA.differentiable (by simp) p) (hB.differentiable (by simp) p)]
  simp

theorem vorticityHeatSmooth_spatialPartial_sub (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => A q - B q) j p =
      spatialPartial A j p - spatialPartial B j p := by
  rw [vorticityHeatSmooth_spatialPartial_eq (hA.sub hB),
    vorticityHeatSmooth_spatialPartial_eq hA, vorticityHeatSmooth_spatialPartial_eq hB,
    fderiv_fun_sub (hA.differentiable (by simp) p) (hB.differentiable (by simp) p)]
  simp

theorem vorticityHeatSmooth_spatialPartial_const_mul (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (c : ℝ) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => c * A q) j p = c * spatialPartial A j p := by
  rw [vorticityHeatSmooth_spatialPartial_eq (contDiff_const.mul hA),
    vorticityHeatSmooth_spatialPartial_eq hA,
    fderiv_const_mul (hA.differentiable (by simp) p)]
  simp

/-- The residual of the localized heat equation: the product `η w` solves the heat equation with
the flux `η F - 2 w ∇η`, up to lower-order cutoff terms and `η` times the residual of `w`. -/
theorem vorticityHeatSmooth_residual {η w : Vec3 × ℝ → ℝ} {F : Fin 3 → Vec3 × ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hF : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j)) (p : Vec3 × ℝ) :
    timePartial (fun q : Vec3 × ℝ => η q * w q) p
        - ∑ j : Fin 3, spatialSecondPartial (fun q : Vec3 × ℝ => η q * w q) j j p
        - ∑ j : Fin 3, spatialPartial
            (fun q : Vec3 × ℝ => η q * F j q - 2 * (w q * spatialPartial η j q)) j p =
      w p * (timePartial η p + ∑ j : Fin 3, spatialSecondPartial η j j p)
        - ∑ j : Fin 3, spatialPartial η j p * F j p
        + η p * (timePartial w p - ∑ j : Fin 3, spatialSecondPartial w j j p
            - ∑ j : Fin 3, spatialPartial (F j) j p) := by
  have hηj (j : Fin 3) := vorticityHeatSmooth_spatialPartial_contDiff hη j
  have hwj (j : Fin 3) := vorticityHeatSmooth_spatialPartial_contDiff hw j
  have hsecond (j : Fin 3) :
      spatialSecondPartial (fun q : Vec3 × ℝ => η q * w q) j j p =
        η p * spatialSecondPartial w j j p + spatialPartial w j p * spatialPartial η j p +
          (w p * spatialSecondPartial η j j p + spatialPartial η j p * spatialPartial w j p) := by
    have hfun : (fun q : Vec3 × ℝ => spatialPartial (fun q : Vec3 × ℝ => η q * w q) j q) =
        fun q => η q * spatialPartial w j q + w q * spatialPartial η j q := by
      funext q
      exact vorticityHeatSmooth_spatialPartial_mul hη hw j q
    change spatialPartial (fun q : Vec3 × ℝ =>
      spatialPartial (fun q : Vec3 × ℝ => η q * w q) j q) j p = _
    rw [hfun, vorticityHeatSmooth_spatialPartial_add (hη.mul (hwj j)) (hw.mul (hηj j)),
      vorticityHeatSmooth_spatialPartial_mul hη (hwj j),
      vorticityHeatSmooth_spatialPartial_mul hw (hηj j)]
    rfl
  have hflux (j : Fin 3) :
      spatialPartial
          (fun q : Vec3 × ℝ => η q * F j q - 2 * (w q * spatialPartial η j q)) j p =
        (η p * spatialPartial (F j) j p + F j p * spatialPartial η j p) -
          2 * (w p * spatialSecondPartial η j j p + spatialPartial η j p *
            spatialPartial w j p) := by
    rw [vorticityHeatSmooth_spatialPartial_sub (hη.mul (hF j))
      (contDiff_const.mul (hw.mul (hηj j))),
      vorticityHeatSmooth_spatialPartial_mul hη (hF j),
      vorticityHeatSmooth_spatialPartial_const_mul (hw.mul (hηj j)),
      vorticityHeatSmooth_spatialPartial_mul hw (hηj j)]
    rfl
  rw [vorticityHeatSmooth_timePartial_mul hη hw]
  simp only [hsecond, hflux, Fin.sum_univ_three]
  ring

end Calculus

section Integrals

/-- Euclidean balls lie in the closed coordinate balls of the same radius. -/
theorem vorticityHeatSmooth_vec3Ball_subset (x₀ : Vec3) (R : ℝ) :
    vec3Ball x₀ R ⊆ Metric.closedBall x₀ R := by
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact ((norm_le_vec3EuclideanNorm (y - x₀)).trans_lt hy).le

/-- Continuous functions are integrable on bounded boxes. -/
theorem vorticityHeatSmooth_integrableOn_box {h : Vec3 × ℝ → ℝ} (hh : Continuous h)
    (x₀ : Vec3) (R a b : ℝ) :
    IntegrableOn h (vec3Ball x₀ R ×ˢ Ioo a b) :=
  (hh.continuousOn.integrableOn_compact
    ((isCompact_closedBall x₀ R).prod isCompact_Icc)).mono_set
    (prod_mono (vorticityHeatSmooth_vec3Ball_subset x₀ R) Ioo_subset_Icc_self)

/-- Continuous functions are integrable on Euclidean balls. -/
theorem vorticityHeatSmooth_integrableOn_ball {h : Vec3 → ℝ} (hh : Continuous h)
    (x₀ : Vec3) (R : ℝ) :
    IntegrableOn h (vec3Ball x₀ R) :=
  (hh.continuousOn.integrableOn_compact (isCompact_closedBall x₀ R)).mono_set
    (vorticityHeatSmooth_vec3Ball_subset x₀ R)

/-- Fubini on a space-time box, with the time integral outside. -/
theorem vorticityHeatSmooth_boxIntegral {S : Set Vec3} {I : Set ℝ}
    {h : Vec3 × ℝ → ℝ} (hh : IntegrableOn h (S ×ˢ I)) :
    (∫ z in S ×ˢ I, h z) = (∫ s in I, ∫ x in S, h (x, s)) ∧
      IntegrableOn (fun s => ∫ x in S, h (x, s)) I := by
  have hmeas : (volume : Measure (Vec3 × ℝ)).restrict (S ×ˢ I) =
      ((volume : Measure Vec3).restrict S).prod ((volume : Measure ℝ).restrict I) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hh' : Integrable h (((volume : Measure Vec3).restrict S).prod
      ((volume : Measure ℝ).restrict I)) := by
    rw [← hmeas]
    exact hh
  refine ⟨?_, hh'.integral_prod_right⟩
  rw [hmeas]
  exact integral_prod_symm h hh'

/-- A continuous function vanishing outside a compact spatial set has integrable spatial slices
and a continuous spatial integral. -/
theorem vorticityHeatSmooth_slice {Q : Vec3 × ℝ → ℝ} (hQ : Continuous Q)
    {K : Set Vec3} (hK : IsCompact K) (hzero : ∀ x s, x ∉ K → Q (x, s) = 0) :
    (∀ s, Integrable (fun x => Q (x, s))) ∧ Continuous (fun s => ∫ x, Q (x, s)) := by
  refine ⟨fun s => ?_, ?_⟩
  · have hc : HasCompactSupport (fun x => Q (x, s)) := by
      apply HasCompactSupport.of_support_subset_isCompact hK
      intro x hx
      by_contra hxK
      exact hx (hzero x s hxK)
    exact (hQ.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hc
  · have h := continuousOn_integral_of_compact_support (μ := (volume : Measure Vec3))
      (s := univ) (k := K) (f := fun s x => Q (x, s)) hK
      ((hQ.comp continuous_swap).continuousOn) (fun s x _ hx => hzero x s hx)
    simpa using h

end Integrals

section Cutoff

/-- Spatial derivative of a separated product `G(x) c(t)`. -/
theorem vorticityHeatSmooth_spatialPartial_sep {G : Vec3 → ℝ} (hG : Differentiable ℝ G)
    (c : ℝ → ℝ) (j : Fin 3) (q : Vec3 × ℝ) :
    spatialPartial (fun p : Vec3 × ℝ => G p.1 * c p.2) j q = spatialDeriv G j q.1 * c q.2 := by
  change (fderiv ℝ (fun x : Vec3 => G x * c q.2) q.1) (basisVec j) = _
  rw [fderiv_mul_const (hG q.1)]
  simp [spatialDeriv, mul_comm]

/-- Time derivative of a separated product `G(x) c(t)`. -/
theorem vorticityHeatSmooth_timePartial_sep (G : Vec3 → ℝ) {c : ℝ → ℝ}
    (hc : Differentiable ℝ c) (q : Vec3 × ℝ) :
    timePartial (fun p : Vec3 × ℝ => G p.1 * c p.2) q = G q.1 * deriv c q.2 := by
  change (fderiv ℝ (fun s : ℝ => G q.1 * c s) q.2) 1 = _
  rw [fderiv_const_mul (hc q.2)]
  simp

/-- Outside the topological support, a function and its first two coordinate derivatives
vanish. -/
theorem vorticityHeatSmooth_notMem_tsupport {ψ : Vec3 → ℝ} {x : Vec3}
    (hx : x ∉ tsupport ψ) (j k : Fin 3) :
    ψ x = 0 ∧ spatialDeriv ψ j x = 0 ∧ spatialDeriv (spatialDeriv ψ j) k x = 0 := by
  have h1 : tsupport (spatialDeriv ψ j) ⊆ tsupport ψ :=
    tsupport_fderiv_apply_subset ℝ (basisVec j)
  have h2 : tsupport (spatialDeriv (spatialDeriv ψ j) k) ⊆ tsupport ψ :=
    (tsupport_fderiv_apply_subset ℝ (basisVec k)).trans h1
  exact ⟨image_eq_zero_of_notMem_tsupport hx,
    image_eq_zero_of_notMem_tsupport (fun h => hx (h1 h)),
    image_eq_zero_of_notMem_tsupport (fun h => hx (h2 h))⟩

/-- The pointwise algebra of the localized energy: the localized flux and residual are
controlled by the solution and its flux, given bounds for the cutoff and its derivatives. -/
theorem vorticityHeatSmooth_pointwise {L η W T : ℝ} {S F : Fin 3 → ℝ} (hL : 0 ≤ L)
    (hη : |η| ≤ 1) (hS : ∀ j, |S j| ≤ L) (hT : |T| ≤ 4 * L) :
    2 * (∑ j : Fin 3, ∑ _i : Fin 3, (η * F j - 2 * (W * S j)) ^ 2) +
        ∑ _i : Fin 3, (W * T - ∑ j : Fin 3, S j * F j) ^ 2 ≤
      (12 + 336 * L ^ 2) * (W ^ 2 + ∑ j : Fin 3, F j ^ 2) := by
  have hη2 : η ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ (abs_nonneg η) hη 2
    simpa [sq_abs] using this
  have hflux (j : Fin 3) : (η * F j - 2 * (W * S j)) ^ 2 ≤ 2 * F j ^ 2 + 8 * L ^ 2 * W ^ 2 := by
    have hS2 : S j ^ 2 ≤ L ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (S j)) (hS j) 2
      simpa [sq_abs] using this
    have hsplit : (η * F j - 2 * (W * S j)) ^ 2 ≤ 2 * (η * F j) ^ 2 + 2 * (2 * (W * S j)) ^ 2 := by
      nlinarith only [sq_nonneg (η * F j + 2 * (W * S j))]
    have ha : (η * F j) ^ 2 ≤ F j ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hη2
    have hb : (2 * (W * S j)) ^ 2 ≤ 4 * L ^ 2 * W ^ 2 := by
      have hW2 := sq_nonneg W
      calc (2 * (W * S j)) ^ 2 = 4 * W ^ 2 * S j ^ 2 := by ring
        _ ≤ 4 * W ^ 2 * L ^ 2 := by gcongr
        _ = 4 * L ^ 2 * W ^ 2 := by ring
    linarith only [hsplit, ha, hb]
  have hres : (W * T - ∑ j : Fin 3, S j * F j) ^ 2 ≤
      64 * L ^ 2 * (W ^ 2 + ∑ j : Fin 3, F j ^ 2) := by
    have habs : |W * T - ∑ j : Fin 3, S j * F j| ≤
        L * (4 * |W| + |F 0| + |F 1| + |F 2|) := by
      have h0 : |S 0 * F 0| ≤ L * |F 0| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hS 0) (abs_nonneg _)
      have h1 : |S 1 * F 1| ≤ L * |F 1| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hS 1) (abs_nonneg _)
      have h2 : |S 2 * F 2| ≤ L * |F 2| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hS 2) (abs_nonneg _)
      have hWT : |W * T| ≤ 4 * L * |W| := by
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hT (abs_nonneg _)
      rw [Fin.sum_univ_three]
      calc |W * T - (S 0 * F 0 + S 1 * F 1 + S 2 * F 2)|
          ≤ |W * T| + |S 0 * F 0| + |S 1 * F 1| + |S 2 * F 2| := by
            have e1 := abs_sub (W * T) (S 0 * F 0 + S 1 * F 1 + S 2 * F 2)
            have e2 := abs_add_three (S 0 * F 0) (S 1 * F 1) (S 2 * F 2)
            linarith only [e1, e2]
        _ ≤ L * (4 * |W| + |F 0| + |F 1| + |F 2|) := by
            linarith only [h0, h1, h2, hWT]
    have hnn : 0 ≤ L * (4 * |W| + |F 0| + |F 1| + |F 2|) := by positivity
    have hsq : (W * T - ∑ j : Fin 3, S j * F j) ^ 2 ≤
        (L * (4 * |W| + |F 0| + |F 1| + |F 2|)) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa [sq_abs] using this
    have hcs : (4 * |W| + |F 0| + |F 1| + |F 2|) ^ 2 ≤
        4 * (16 * |W| ^ 2 + |F 0| ^ 2 + |F 1| ^ 2 + |F 2| ^ 2) := by
      nlinarith only [sq_nonneg (4 * |W| - |F 0|), sq_nonneg (4 * |W| - |F 1|),
        sq_nonneg (4 * |W| - |F 2|), sq_nonneg (|F 0| - |F 1|), sq_nonneg (|F 0| - |F 2|),
        sq_nonneg (|F 1| - |F 2|)]
    simp only [Fin.sum_univ_three] at hsq ⊢
    simp only [sq_abs] at hcs
    have hL2 := sq_nonneg L
    calc (W * T - (S 0 * F 0 + S 1 * F 1 + S 2 * F 2)) ^ 2
        ≤ L ^ 2 * (4 * |W| + |F 0| + |F 1| + |F 2|) ^ 2 := by rw [← mul_pow]; exact hsq
      _ ≤ L ^ 2 * (4 * (16 * W ^ 2 + F 0 ^ 2 + F 1 ^ 2 + F 2 ^ 2)) := by gcongr
      _ ≤ 64 * L ^ 2 * (W ^ 2 + (F 0 ^ 2 + F 1 ^ 2 + F 2 ^ 2)) := by
          nlinarith only [hL2, sq_nonneg (F 0), sq_nonneg (F 1), sq_nonneg (F 2),
            mul_nonneg hL2 (add_nonneg (add_nonneg (sq_nonneg (F 0)) (sq_nonneg (F 1)))
              (sq_nonneg (F 2)))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  simp only [Fin.sum_univ_three] at hres ⊢
  have h0 := hflux 0
  have h1 := hflux 1
  have h2 := hflux 2
  have hW2 := sq_nonneg W
  have hL2W := mul_nonneg (sq_nonneg L) hW2
  have hL2F := mul_nonneg (sq_nonneg L)
    (add_nonneg (add_nonneg (sq_nonneg (F 0)) (sq_nonneg (F 1))) (sq_nonneg (F 2)))
  nlinarith only [h0, h1, h2, hres, hW2, hL2W, hL2F]

end Cutoff

/-- Local energy estimate for smooth solutions of `∂ₜ w - Δ w = div F` on `B_R(x₀) × (a, b)`:
the spatial `L²` norm on the inner ball at every time from `a + κ` to the top, and the spatial
gradient in `L²` on the inner cylinder, are bounded by the `L²` norms of `w` and `F` on the whole
cylinder. The constant depends only on the radii and on `κ` (`thm:vorticity-regularity`). -/
theorem vorticityHeatSmooth_localEnergy {r R κ : ℝ} (hr : 0 < r) (hrR : r < R) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (a b : ℝ) (w : Vec3 × ℝ → ℝ)
      (F : Fin 3 → Vec3 × ℝ → ℝ),
      a + κ ≤ b → b ≤ a + 1 → ContDiff ℝ (⊤ : ℕ∞) w → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (F j)) →
      (∀ z ∈ vec3Ball x₀ R ×ˢ Ioo a b,
        timePartial w z - ∑ j : Fin 3, spatialSecondPartial w j j z =
          ∑ j : Fin 3, spatialPartial (F j) j z) →
      (∀ t ∈ Icc (a + κ) b,
        ∫ x in vec3Ball x₀ r, w (x, t) ^ 2 ≤
          C * ∫ z in vec3Ball x₀ R ×ˢ Ioo a b, (w z ^ 2 + ∑ j : Fin 3, F j z ^ 2)) ∧
      ∫ z in vec3Ball x₀ r ×ˢ Ioo (a + κ) b, ∑ j : Fin 3, spatialPartial w j z ^ 2 ≤
        C * ∫ z in vec3Ball x₀ R ×ˢ Ioo a b, (w z ^ 2 + ∑ j : Fin 3, F j z ^ 2) := by
  obtain ⟨φ, hφ, hφc, hφsupp, hφone, hφ0, hφ1⟩ := vorticitySpatialCutoff_exists hr hrR
  obtain ⟨Lφ, hLφ, hLφ1, hLφ2⟩ := vorticitySmooth_derivative_bounds hφ hφc
  obtain ⟨θ, hθ, hθzero, hθone, hθ0, hθ1, Lθ, hLθ, hLθb⟩ := vorticityTimeCutoff_exists hκ
  have hL : 0 ≤ Lφ + Lθ := add_nonneg hLφ hLθ
  have hK : 0 ≤ 12 + 336 * (Lφ + Lθ) ^ 2 := by positivity
  refine ⟨(Real.exp 1 + 1) * (12 + 336 * (Lφ + Lθ) ^ 2), by positivity, ?_⟩
  intro x₀ a b w F hab hb1 hw hF heqn
  have hab' : a ≤ b := by linarith only [hab, hκ]
  -- the cutoff `η(x, t) = φ(x - x₀) θ(t - a)` and its derivatives
  let ψ : Vec3 → ℝ := fun x => φ (x - x₀)
  let c : ℝ → ℝ := fun s => θ (s - a)
  let η : Vec3 × ℝ → ℝ := fun q => ψ q.1 * c q.2
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_id.sub contDiff_const)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := hθ.comp (contDiff_id.sub contDiff_const)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η := (hψ.comp contDiff_fst).mul (hc.comp contDiff_snd)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.subRight x₀)
  have hψsupp : tsupport ψ ⊆ vec3Ball x₀ R := by
    intro x hx
    have hx2 : x ∈ tsupport (φ ∘ Homeomorph.subRight x₀) := hx
    rw [tsupport_comp_eq_preimage φ (Homeomorph.subRight x₀)] at hx2
    have h := hφsupp hx2
    simpa [vec3Ball] using h
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hspη : ∀ j (q : Vec3 × ℝ), spatialPartial η j q = spatialDeriv ψ j q.1 * c q.2 :=
    fun j q => vorticityHeatSmooth_spatialPartial_sep hψd c j q
  have hsspη : ∀ j (q : Vec3 × ℝ), spatialSecondPartial η j j q =
      spatialDeriv (spatialDeriv ψ j) j q.1 * c q.2 := by
    intro j q
    have hfun : (fun p : Vec3 × ℝ => spatialPartial η j p) =
        fun p => spatialDeriv ψ j p.1 * c p.2 := funext (hspη j)
    change spatialPartial (fun p : Vec3 × ℝ => spatialPartial η j p) j q = _
    rw [hfun]
    exact vorticityHeatSmooth_spatialPartial_sep
      ((contDiff_spatialDeriv_smooth hψ j).differentiable (by simp)) c j q
  have htpη : ∀ q : Vec3 × ℝ, timePartial η q = ψ q.1 * deriv c q.2 :=
    fun q => vorticityHeatSmooth_timePartial_sep ψ hcd q
  have hDψ : ∀ x j, |spatialDeriv ψ j x| ≤ Lφ := by
    intro x j
    rw [vorticitySpatialDeriv_translate]
    exact hLφ1 _ _
  have hD2ψ : ∀ x j k, |spatialDeriv (spatialDeriv ψ j) k x| ≤ Lφ := by
    intro x j k
    have hfun : spatialDeriv ψ j = fun y => spatialDeriv φ j (y - x₀) :=
      funext fun y => vorticitySpatialDeriv_translate φ x₀ y j
    rw [hfun, vorticitySpatialDeriv_translate]
    exact hLφ2 _ _ _
  have hdc : ∀ s, |deriv c s| ≤ Lθ := by
    intro s
    have h : deriv c s = deriv θ (s - a) := deriv_comp_sub_const θ a s
    rw [h]
    exact hLθb _
  have hηb : ∀ q, |η q| ≤ 1 := by
    intro q
    have h0 : 0 ≤ η q := mul_nonneg (hφ0 _) (hθ0 _)
    rw [abs_of_nonneg h0]
    have := mul_le_mul (hφ1 (q.1 - x₀)) (hθ1 (q.2 - a)) (hθ0 _) zero_le_one
    change ψ q.1 * c q.2 ≤ 1
    linarith only [this]
  have hSb : ∀ j (q : Vec3 × ℝ), |spatialPartial η j q| ≤ Lφ + Lθ := by
    intro j q
    rw [hspη, abs_mul, abs_of_nonneg (hθ0 _)]
    have := mul_le_mul (hDψ q.1 j) (hθ1 (q.2 - a)) (hθ0 _) hLφ
    linarith only [this, hLθ]
  have hTb : ∀ q : Vec3 × ℝ, |timePartial η q + ∑ j : Fin 3, spatialSecondPartial η j j q| ≤
      4 * (Lφ + Lθ) := by
    intro q
    have ht : |timePartial η q| ≤ Lθ := by
      rw [htpη, abs_mul, abs_of_nonneg (hφ0 _)]
      have := mul_le_mul (hφ1 (q.1 - x₀)) (hdc q.2) (abs_nonneg _) zero_le_one
      linarith only [this]
    have hs (j : Fin 3) : |spatialSecondPartial η j j q| ≤ Lφ := by
      rw [hsspη, abs_mul, abs_of_nonneg (hθ0 _)]
      have := mul_le_mul (hD2ψ q.1 j j) (hθ1 (q.2 - a)) (hθ0 _) hLφ
      linarith only [this]
    rw [Fin.sum_univ_three]
    have e1 := abs_add_le (timePartial η q)
      (spatialSecondPartial η 0 0 q + spatialSecondPartial η 1 1 q +
        spatialSecondPartial η 2 2 q)
    have e2 := abs_add_three (spatialSecondPartial η 0 0 q) (spatialSecondPartial η 1 1 q)
      (spatialSecondPartial η 2 2 q)
    have h0 := hs 0
    have h1 := hs 1
    have h2 := hs 2
    linarith only [e1, e2, ht, h0, h1, h2, hLφ, hLθ]
  have hout : ∀ x, x ∉ tsupport ψ → ∀ s, η (x, s) = 0 ∧
      (∀ j, spatialPartial η j (x, s) = 0) ∧
      (∀ j, spatialSecondPartial η j j (x, s) = 0) ∧ timePartial η (x, s) = 0 := by
    intro x hx s
    have h := fun j => vorticityHeatSmooth_notMem_tsupport hx j j
    refine ⟨?_, fun j => ?_, fun j => ?_, ?_⟩
    · change ψ x * c s = 0
      rw [(h 0).1, zero_mul]
    · refine (hspη j (x, s)).trans ?_
      change spatialDeriv ψ j x * c s = 0
      rw [(h j).2.1, zero_mul]
    · refine (hsspη j (x, s)).trans ?_
      change spatialDeriv (spatialDeriv ψ j) j x * c s = 0
      rw [(h j).2.2, zero_mul]
    · refine (htpη (x, s)).trans ?_
      change ψ x * deriv c s = 0
      rw [(h 0).1, zero_mul]
  -- the localized field, its flux and the residual
  let Z : Vec3 × ℝ → ℝ := fun q => η q * w q
  let Fp : Fin 3 → Vec3 × ℝ → ℝ := fun j q => η q * F j q - 2 * (w q * spatialPartial η j q)
  let G : Vec3 × ℝ → ℝ := fun q => timePartial (fun q : Vec3 × ℝ => η q * w q) q
      - ∑ j : Fin 3, spatialSecondPartial (fun q : Vec3 × ℝ => η q * w q) j j q
      - ∑ j : Fin 3, spatialPartial
          (fun q : Vec3 × ℝ => η q * F j q - 2 * (w q * spatialPartial η j q)) j q
  have hGres : ∀ q, G q = w q * (timePartial η q + ∑ j : Fin 3, spatialSecondPartial η j j q)
      - ∑ j : Fin 3, spatialPartial η j q * F j q
      + η q * (timePartial w q - ∑ j : Fin 3, spatialSecondPartial w j j q
          - ∑ j : Fin 3, spatialPartial (F j) j q) :=
    fun q => vorticityHeatSmooth_residual hη hw hF q
  have hGstrip : ∀ x s, s ∈ Ioo a b → G (x, s) =
      w (x, s) * (timePartial η (x, s) + ∑ j : Fin 3, spatialSecondPartial η j j (x, s))
        - ∑ j : Fin 3, spatialPartial η j (x, s) * F j (x, s) := by
    intro x s hs
    rw [hGres]
    have hzero : η (x, s) * (timePartial w (x, s) - ∑ j : Fin 3, spatialSecondPartial w j j (x, s)
        - ∑ j : Fin 3, spatialPartial (F j) j (x, s)) = 0 := by
      by_cases hx : x ∈ vec3Ball x₀ R
      · rw [heqn (x, s) ⟨hx, hs⟩, sub_self, mul_zero]
      · rw [(hout x (fun h => hx (hψsupp h)) s).1, zero_mul]
    rw [hzero, add_zero]
  have hGout : ∀ x, x ∉ tsupport ψ → ∀ s, G (x, s) = 0 := by
    intro x hx s
    obtain ⟨h1, h2, h3, h4⟩ := hout x hx s
    rw [hGres, h1, h4]
    simp [h2, h3]
  have hFpout : ∀ x, x ∉ tsupport ψ → ∀ s j, Fp j (x, s) = 0 := by
    intro x hx s j
    obtain ⟨h1, h2, -, -⟩ := hout x hx s
    change η (x, s) * F j (x, s) - 2 * (w (x, s) * spatialPartial η j (x, s)) = 0
    rw [h1, h2 j]
    ring
  have hZ : ContDiff ℝ (⊤ : ℕ∞) Z := hη.mul hw
  have hηj := vorticityHeatSmooth_spatialPartial_contDiff hη
  have hFp : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fp j) :=
    fun j => (hη.mul (hF j)).sub (contDiff_const.mul (hw.mul (hηj j)))
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    have h1 := vorticityHeatSmooth_timePartial_contDiff hZ
    have h2 : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialSecondPartial Z j j q) :=
      fun j => vorticityHeatSmooth_spatialPartial_contDiff
        (vorticityHeatSmooth_spatialPartial_contDiff hZ j) j
    have h3 : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialPartial (Fp j) j q) := fun j =>
      vorticityHeatSmooth_spatialPartial_contDiff (hFp j) j
    exact (h1.sub (ContDiff.sum fun j _ => h2 j)).sub (ContDiff.sum fun j _ => h3 j)
  -- application of the smooth Gronwall energy bound
  let zv : Vec3 × ℝ → Vec3 := fun q _ => Z q
  let Fv : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun q j _ => Fp j q
  let gv : Vec3 × ℝ → Vec3 := fun q _ => G q
  let v0 : Vec3 × ℝ → Vec3 := fun _ => 0
  have hcommon : ∃ K : Set Vec3, IsCompact K ∧ ∀ x, x ∉ K → ∀ t,
      zv (x, t) = 0 ∧ (∀ j i, Fv (x, t) j i = 0) ∧ gv (x, t) = 0 := by
    refine ⟨tsupport ψ, hψc, fun x hx t => ⟨?_, fun j _ => hFpout x hx t j, ?_⟩⟩
    · funext i
      change η (x, t) * w (x, t) = 0
      rw [(hout x hx t).1, zero_mul]
    · funext i
      exact hGout x hx t
  have heq : ∀ (x : Vec3) (t : ℝ) (i : Fin 3),
      CKN.timePartial (fun w' : Vec3 × ℝ => zv w' i) (x, t) -
        ∑ j : Fin 3, CKN.spatialSecondPartial
          (show ParabolicPoint → ℝ from fun w' => zv w' i) j j (x, t) =
      -(∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w' =>
            v0 w' j * zv w' i - zv w' j * v0 w' i) j (x, t)) +
        ∑ j : Fin 3, CKN.spatialPartial
          (show ParabolicPoint → ℝ from fun w' => Fv w' j i) j (x, t) +
        gv (x, t) i := by
    intro x t i
    have hv : ∀ j, CKN.spatialPartial (show ParabolicPoint → ℝ from fun w' =>
        v0 w' j * zv w' i - zv w' j * v0 w' i) j (x, t) = 0 := by
      intro j
      have hfun : (show ParabolicPoint → ℝ from fun w' =>
          v0 w' j * zv w' i - zv w' j * v0 w' i) = fun _ => 0 := by
        funext w'
        simp [v0]
      rw [hfun]
      simp [spatialPartial]
    simp only [hv, Finset.sum_const_zero, neg_zero, zero_add]
    have hGdef : gv (x, t) i = timePartial Z (x, t) - ∑ j : Fin 3, spatialSecondPartial Z j j (x, t)
        - ∑ j : Fin 3, spatialPartial (Fp j) j (x, t) := rfl
    rw [hGdef]
    change timePartial Z (x, t) - ∑ j : Fin 3, spatialSecondPartial Z j j (x, t) =
      ∑ j : Fin 3, spatialPartial (Fp j) j (x, t) + (timePartial Z (x, t) -
        ∑ j : Fin 3, spatialSecondPartial Z j j (x, t) -
          ∑ j : Fin 3, spatialPartial (Fp j) j (x, t))
    ring
  have hvbound : ∀ x t, vec3EuclideanNorm (v0 (x, t)) ≤ 0 := by
    intro x t
    simp [v0, vec3EuclideanNorm_zero]
  have hinit : (∫ x : Vec3, ∑ i : Fin 3, (zv (x, a) i) ^ 2) ≤ 0 := by
    have hca : c a = 0 := by
      change θ (a - a) = 0
      rw [sub_self]
      exact hθzero 0 (half_pos hκ).le
    have hfun : (fun x : Vec3 => ∑ i : Fin 3, (zv (x, a) i) ^ 2) = fun _ => 0 := by
      funext x
      change ∑ _i : Fin 3, (ψ x * c a * w (x, a)) ^ 2 = 0
      simp [hca]
    rw [hfun, integral_zero]
  have hgr := smoothVorticityEnergyGronwall (a := a) (b := b) (M := 0) (e₀ := 0) (v := v0)
    (z := zv) (F := Fv) (g := gv) hab' le_rfl contDiff_const (contDiff_pi.2 fun _ => hZ)
    (fun j _ => hFp j) (contDiff_pi.2 fun _ => hG) hcommon heq hvbound hinit
  -- the forcing integral
  let f : ℝ → ℝ := fun s => 2 * (∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3, (Fv (x, s) j i) ^ 2)
    + ∫ x : Vec3, ∑ i : Fin 3, (gv (x, s) i) ^ 2
  have hgr1 : ∀ t ∈ Icc a b, (∫ x : Vec3, ∑ i : Fin 3, (zv (x, t) i) ^ 2) ≤
      Real.exp ((72 * 0 ^ 2 + 1) * (b - a)) * (0 + ∫ s in a..b, f s) := hgr.1
  have hgr2 : (∫ t in a..b, ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
      (CKN.spatialPartial (fun w' : Vec3 × ℝ => zv w' i) j (x, t)) ^ 2) ≤
      0 + (72 * 0 ^ 2 + 1) * (b - a) *
        (Real.exp ((72 * 0 ^ 2 + 1) * (b - a)) * (0 + ∫ s in a..b, f s)) +
          ∫ s in a..b, f s := hgr.2
  have hQ1 := vorticityHeatSmooth_slice
    (Q := fun q => ∑ j : Fin 3, ∑ i : Fin 3, (Fv q j i) ^ 2)
    (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
      ((hFp j).continuous).pow 2) hψc
    (fun x s hx => by simp [Fv, hFpout x hx s])
  have hQ2 := vorticityHeatSmooth_slice (Q := fun q => ∑ i : Fin 3, (gv q i) ^ 2)
    (continuous_finsetSum _ fun i _ => (hG.continuous).pow 2) hψc
    (fun x s hx => by simp [gv, hGout x hx s])
  have hfcont : Continuous f := (continuous_const.mul hQ1.2).add hQ2.2
  have hf0 : ∀ s, 0 ≤ f s := by
    intro s
    have h1 : 0 ≤ ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3, (Fv (x, s) j i) ^ 2 :=
      integral_nonneg fun x => by positivity
    have h2 : 0 ≤ ∫ x : Vec3, ∑ i : Fin 3, (gv (x, s) i) ^ 2 :=
      integral_nonneg fun x => by positivity
    change 0 ≤ 2 * _ + _
    linarith only [h1, h2]
  have hhcont : Continuous (fun q : Vec3 × ℝ => w q ^ 2 + ∑ j : Fin 3, F j q ^ 2) :=
    (hw.continuous.pow 2).add (continuous_finsetSum _ fun j _ => (hF j).continuous.pow 2)
  have hbox := vorticityHeatSmooth_boxIntegral
    (vorticityHeatSmooth_integrableOn_box hhcont x₀ R a b)
  have hballMeas : ∀ ρ, MeasurableSet (vec3Ball x₀ ρ) :=
    fun ρ => (isOpen_vec3Ball x₀ ρ).measurableSet
  have hfbound : ∀ s ∈ Ioo a b, f s ≤ (12 + 336 * (Lφ + Lθ) ^ 2) *
      ∫ x in vec3Ball x₀ R, (w (x, s) ^ 2 + ∑ j : Fin 3, F j (x, s) ^ 2) := by
    intro s hs
    have hA := hQ1.1 s
    have hB := hQ2.1 s
    have hsl : Continuous fun x : Vec3 => w (x, s) ^ 2 + ∑ j : Fin 3, F j (x, s) ^ 2 :=
      hhcont.comp (continuous_id.prodMk continuous_const)
    calc f s = ∫ x : Vec3, (2 * ∑ j : Fin 3, ∑ i : Fin 3, (Fv (x, s) j i) ^ 2
          + ∑ i : Fin 3, (gv (x, s) i) ^ 2) := by
          rw [integral_add (hA.const_mul 2) hB, integral_const_mul]
      _ ≤ ∫ x : Vec3, (vec3Ball x₀ R).indicator (fun x => (12 + 336 * (Lφ + Lθ) ^ 2) *
          (w (x, s) ^ 2 + ∑ j : Fin 3, F j (x, s) ^ 2)) x := by
          have hInd : IntegrableOn (fun x : Vec3 => (12 + 336 * (Lφ + Lθ) ^ 2) *
              (w (x, s) ^ 2 + ∑ j : Fin 3, F j (x, s) ^ 2)) (vec3Ball x₀ R) :=
            (vorticityHeatSmooth_integrableOn_ball hsl x₀ R).const_mul _
          apply integral_mono ((hA.const_mul 2).add hB) (hInd.integrable_indicator (hballMeas R))
          intro x
          simp only [Pi.add_apply]
          by_cases hx : x ∈ vec3Ball x₀ R
          · rw [Set.indicator_of_mem hx]
            have hgv : ∀ i, gv (x, s) i = w (x, s) * (timePartial η (x, s) +
                ∑ j : Fin 3, spatialSecondPartial η j j (x, s)) -
                ∑ j : Fin 3, spatialPartial η j (x, s) * F j (x, s) :=
              fun _ => hGstrip x s hs
            have hFv : ∀ j i, Fv (x, s) j i =
                η (x, s) * F j (x, s) - 2 * (w (x, s) * spatialPartial η j (x, s)) :=
              fun _ _ => rfl
            have hp := vorticityHeatSmooth_pointwise (η := η (x, s)) (W := w (x, s))
              (T := timePartial η (x, s) + ∑ j : Fin 3, spatialSecondPartial η j j (x, s))
              (S := fun j => spatialPartial η j (x, s)) (F := fun j => F j (x, s)) hL
              (hηb _) (fun j => hSb j _) (hTb _)
            have key : 2 * ∑ j : Fin 3, ∑ i : Fin 3, Fv (x, s) j i ^ 2 +
                ∑ i : Fin 3, gv (x, s) i ^ 2 =
                2 * ∑ j : Fin 3, ∑ _i : Fin 3, (η (x, s) * F j (x, s) -
                  2 * (w (x, s) * spatialPartial η j (x, s))) ^ 2 +
                ∑ _i : Fin 3, (w (x, s) * (timePartial η (x, s) +
                  ∑ j : Fin 3, spatialSecondPartial η j j (x, s)) -
                  ∑ j : Fin 3, spatialPartial η j (x, s) * F j (x, s)) ^ 2 := by
              simp only [hFv, hgv]
            rw [key]
            exact hp
          · rw [Set.indicator_of_notMem hx]
            have hxs : x ∉ tsupport ψ := fun h => hx (hψsupp h)
            simp [Fv, gv, hFpout x hxs s, hGout x hxs s]
      _ = (12 + 336 * (Lφ + Lθ) ^ 2) *
          ∫ x in vec3Ball x₀ R, (w (x, s) ^ 2 + ∑ j : Fin 3, F j (x, s) ^ 2) := by
          rw [integral_indicator (hballMeas R), integral_const_mul]
  have hfint : ∫ s in a..b, f s ≤ (12 + 336 * (Lφ + Lθ) ^ 2) *
      ∫ z in vec3Ball x₀ R ×ˢ Ioo a b, (w z ^ 2 + ∑ j : Fin 3, F j z ^ 2) := by
    rw [intervalIntegral.integral_of_le hab', integral_Ioc_eq_integral_Ioo, hbox.1,
      ← integral_const_mul]
    exact setIntegral_mono_on (hfcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (hbox.2.const_mul _) measurableSet_Ioo hfbound
  have hfint0 : 0 ≤ ∫ s in a..b, f s :=
    intervalIntegral.integral_nonneg hab' fun s _ => hf0 s
  have hQ0 : 0 ≤ ∫ z in vec3Ball x₀ R ×ˢ Ioo a b, (w z ^ 2 + ∑ j : Fin 3, F j z ^ 2) :=
    setIntegral_nonneg ((hballMeas R).prod measurableSet_Ioo) fun z _ => by positivity
  have hba : (72 * (0 : ℝ) ^ 2 + 1) * (b - a) = b - a := by ring
  have hexp : Real.exp ((72 * 0 ^ 2 + 1) * (b - a)) ≤ Real.exp 1 := by
    rw [hba]
    exact Real.exp_le_exp.2 (by linarith only [hb1])
  have hexp0 : 0 ≤ Real.exp ((72 * 0 ^ 2 + 1) * (b - a)) := (Real.exp_pos _).le
  have hexp1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hKQ := mul_nonneg hK hQ0
  have hmain : Real.exp ((72 * 0 ^ 2 + 1) * (b - a)) * (∫ s in a..b, f s) ≤
      Real.exp 1 * ((12 + 336 * (Lφ + Lθ) ^ 2) *
        ∫ z in vec3Ball x₀ R ×ˢ Ioo a b, (w z ^ 2 + ∑ j : Fin 3, F j z ^ 2)) :=
    mul_le_mul hexp hfint hfint0 hexp1.le
  refine ⟨fun t ht => ?_, ?_⟩
  · -- the spatial `L²` bound at time `t`
    have ht' : t ∈ Icc a b := ⟨by linarith only [ht.1, hκ], ht.2⟩
    have he := hgr1 t ht'
    have hZsl := vorticityHeatSmooth_slice (Q := fun q => Z q ^ 2) (hZ.continuous.pow 2) hψc
      (fun x s hx => by
        change (η (x, s) * w (x, s)) ^ 2 = 0
        rw [(hout x hx s).1]
        ring)
    have hEeq : (∫ x : Vec3, ∑ i : Fin 3, (zv (x, t) i) ^ 2) = 3 * ∫ x : Vec3, Z (x, t) ^ 2 := by
      rw [← integral_const_mul]
      congr 1
      funext x
      simp [zv, Finset.sum_const]
    have hball : ∫ x in vec3Ball x₀ r, w (x, t) ^ 2 = ∫ x in vec3Ball x₀ r, Z (x, t) ^ 2 := by
      apply setIntegral_congr_fun (hballMeas r)
      intro x hx
      have hψ1 : ψ x = 1 := hφone _ (le_of_lt hx)
      have hc1 : c t = 1 := hθone _ (by linarith only [ht.1])
      change w (x, t) ^ 2 = (ψ x * c t * w (x, t)) ^ 2
      rw [hψ1, hc1]
      ring
    have hle : ∫ x in vec3Ball x₀ r, Z (x, t) ^ 2 ≤ ∫ x : Vec3, Z (x, t) ^ 2 :=
      setIntegral_le_integral (hZsl.1 t) (Eventually.of_forall fun x => sq_nonneg _)
    rw [hball]
    rw [hEeq, zero_add] at he
    nlinarith only [hle, he, hmain, hKQ, hexp1]
  · -- the gradient bound
    let D : ℝ → ℝ := fun s => ∫ x : Vec3, ∑ j : Fin 3, spatialPartial Z j (x, s) ^ 2
    have hspZ : ∀ j (q : Vec3 × ℝ), spatialPartial Z j q =
        η q * spatialPartial w j q + w q * spatialPartial η j q :=
      fun j q => vorticityHeatSmooth_spatialPartial_mul hη hw j q
    have hDsl := vorticityHeatSmooth_slice (Q := fun q => ∑ j : Fin 3, spatialPartial Z j q ^ 2)
      (continuous_finsetSum _ fun j _ =>
        ((vorticityHeatSmooth_spatialPartial_contDiff hZ j).continuous).pow 2) hψc
      (fun x s hx => by
        obtain ⟨h1, h2, -, -⟩ := hout x hx s
        simp [hspZ, h1, h2])
    have hDcont : Continuous D := hDsl.2
    have hwcont : Continuous (fun q : Vec3 × ℝ => ∑ j : Fin 3, spatialPartial w j q ^ 2) :=
      continuous_finsetSum _ fun j _ =>
        ((vorticityHeatSmooth_spatialPartial_contDiff hw j).continuous).pow 2
    have hLbox := vorticityHeatSmooth_boxIntegral
      (vorticityHeatSmooth_integrableOn_box hwcont x₀ r (a + κ) b)
    have hstep1 : ∫ s in Ioo (a + κ) b, ∫ x in vec3Ball x₀ r,
        ∑ j : Fin 3, spatialPartial w j (x, s) ^ 2 ≤ ∫ s in Ioo (a + κ) b, D s := by
      apply setIntegral_mono_on hLbox.2
        (hDcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo
      intro s hs
      have heqball : ∫ x in vec3Ball x₀ r, ∑ j : Fin 3, spatialPartial w j (x, s) ^ 2 =
          ∫ x in vec3Ball x₀ r, ∑ j : Fin 3, spatialPartial Z j (x, s) ^ 2 := by
        apply setIntegral_congr_fun (hballMeas r)
        intro x hx
        have hψ1 : ψ x = 1 := hφone _ (le_of_lt hx)
        have hc1 : c s = 1 := hθone _ (by linarith only [hs.1])
        have hDψ0 : ∀ j, spatialDeriv ψ j x = 0 := by
          intro j
          rw [vorticitySpatialDeriv_translate]
          have hopen : IsOpen {y : Vec3 | vec3EuclideanNorm y < r} :=
            isOpen_lt CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm continuous_const
          have hev : φ =ᶠ[nhds (x - x₀)] fun _ => 1 := by
            filter_upwards [hopen.mem_nhds hx] with y hy
            exact hφone y (le_of_lt hy)
          unfold spatialDeriv
          rw [hev.fderiv_eq]
          simp
        apply Finset.sum_congr rfl
        intro j _
        rw [hspZ, hspη]
        change spatialPartial w j (x, s) ^ 2 =
          (ψ x * c s * spatialPartial w j (x, s) + w (x, s) * (spatialDeriv ψ j x * c s)) ^ 2
        rw [hψ1, hc1, hDψ0 j]
        ring
      rw [heqball]
      exact setIntegral_le_integral (hDsl.1 s) (Eventually.of_forall fun x => by positivity)
    have hstep2 : ∫ s in Ioo (a + κ) b, D s ≤ ∫ s in Ioo a b, D s := by
      apply setIntegral_mono_set (hDcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      · exact Eventually.of_forall fun s => integral_nonneg fun x => by positivity
      · exact (Ioo_subset_Ioo_left (by linarith only [hκ])).eventuallyLE
    have hdeq : (∫ t in a..b, ∫ x : Vec3, ∑ j : Fin 3, ∑ i : Fin 3,
        (CKN.spatialPartial (fun w' : Vec3 × ℝ => zv w' i) j (x, t)) ^ 2) =
        3 * ∫ s in Ioo a b, D s := by
      rw [intervalIntegral.integral_of_le hab', integral_Ioc_eq_integral_Ioo,
        ← integral_const_mul]
      congr 1
      funext t
      rw [← integral_const_mul]
      congr 1
      funext x
      have hzvi : ∀ i, (fun w' : Vec3 × ℝ => zv w' i) = Z := fun _ => rfl
      simp only [hzvi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat, Finset.mul_sum]
    rw [hdeq] at hgr2
    rw [hLbox.1]
    have hlast : (72 * (0 : ℝ) ^ 2 + 1) * (b - a) *
        (Real.exp ((72 * 0 ^ 2 + 1) * (b - a)) * (∫ s in a..b, f s)) ≤
        Real.exp ((72 * 0 ^ 2 + 1) * (b - a)) * (∫ s in a..b, f s) := by
      rw [hba]
      have h1 : b - a ≤ 1 := by linarith only [hb1]
      exact mul_le_of_le_one_left (mul_nonneg (Real.exp_pos _).le hfint0) h1
    rw [zero_add, zero_add] at hgr2
    have hEKQ := mul_nonneg hexp1.le hKQ
    linarith only [hstep1, hstep2, hgr2, hlast, hmain, hfint, hKQ, hEKQ]

end ESS
