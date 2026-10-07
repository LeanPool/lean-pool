/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticEquation
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitDerivative

/-!
# The mollified strong equation

Testing the strong equation of a strong solution against a translated kernel
times a function of time gives, at every point of space and for almost every
time, an identity between kernel convolutions of the specified fields
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- Fubini for an integrable slab field against a separated bounded weight. -/
theorem lps_slab_integral_sep_L1 {a τ : ℝ} {g : Vec3 × ℝ → ℝ}
    (hg : Integrable g (volume.restrict (vlSlab a τ))) {k : Vec3 → ℝ} (hk : IsVlKernel k)
    (x : Vec3) {η : ℝ → ℝ} (hη : Continuous η) (hηb : ∃ C, ∀ s, |η s| ≤ C) :
    Integrable (fun p : Vec3 × ℝ => g p * (k (x - p.1) * η p.2))
        (volume.restrict (vlSlab a τ)) ∧
      ∫ p in vlSlab a τ, g p * (k (x - p.1) * η p.2) =
        ∫ s in Ioo a τ, η s * vlConvT k g x s := by
  obtain ⟨C, hC⟩ := hηb
  obtain ⟨Ck, hCk⟩ := hk.continuous.bounded_above_of_compact_support hk.2
  have hmeas : AEStronglyMeasurable (fun p : Vec3 × ℝ => k (x - p.1) * η p.2)
      (volume.restrict (vlSlab a τ)) :=
    ((hk.continuous.comp (continuous_const.sub continuous_fst)).mul
      (hη.comp continuous_snd)).aestronglyMeasurable
  have hint : Integrable (fun p : Vec3 × ℝ => g p * (k (x - p.1) * η p.2))
      (volume.restrict (vlSlab a τ)) := by
    have h := hg.mul_bdd hmeas (c := Ck * C) (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |k (x - p.1)| ≤ Ck := by simpa [Real.norm_eq_abs] using hCk (x - p.1)
      exact mul_le_mul h1 (hC _) (abs_nonneg _) ((abs_nonneg _).trans h1))
    exact h.congr (Eventually.of_forall fun p => by ring)
  refine ⟨hint, ?_⟩
  have hint' := hint
  rw [vlSlab_measure] at hint'
  rw [vlSlab_measure, integral_prod_symm _ hint']
  refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
  simp only [vlConvT, vlConv_apply_swap]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem lps_convT_integrableOn_L1 {a τ : ℝ} {g : Vec3 × ℝ → ℝ}
    (hg : Integrable g (volume.restrict (vlSlab a τ))) {k : Vec3 → ℝ} (hk : IsVlKernel k)
    (x : Vec3) : IntegrableOn (fun s => vlConvT k g x s) (Ioo a τ) volume := by
  obtain ⟨Ck, hCk⟩ := hk.continuous.bounded_above_of_compact_support hk.2
  have hmeas : AEStronglyMeasurable (fun p : Vec3 × ℝ => k (x - p.1))
      (volume.restrict (vlSlab a τ)) :=
    (hk.continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable
  have hint : Integrable (fun p : Vec3 × ℝ => g p * k (x - p.1))
      (volume.restrict (vlSlab a τ)) := by
    have h := hg.mul_bdd hmeas (c := Ck) (Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using hCk (x - p.1))
    exact h.congr (Eventually.of_forall fun p => by ring)
  rw [vlSlab_measure] at hint
  have h := hint.integral_prod_right
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [vlConvT, vlConv_apply_swap]

/-- The mollified strong equation: at every point of space, for almost every
time, the convolutions of the specified fields satisfy the momentum equation
in the `i`-th component (`prop:lps-local-strong`). -/
theorem lps_strong_mollified_equation
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : ∀ i, MemLp (fun z : Vec3 × ℝ => u z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hD2 : ∀ i j, MemLp (fun z : Vec3 × ℝ => D2u z i j j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hDt : ∀ i, MemLp (fun z : Vec3 × ℝ => Dtu z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hp : MemLp p 2 (volume.restrict (vlSlab t₀ T)))
    (i : Fin 3) {κ : Vec3 → ℝ} (hκ : IsVlKernel κ) (x : Vec3) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)),
      vlConvT κ (fun z : Vec3 × ℝ => Dtu z i) x t +
        ∑ j : Fin 3, vlConvT (vlDeriv κ j) (fun z : Vec3 × ℝ => u z i * u z j) x t -
        ∑ j : Fin 3, vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t +
        vlConvT (vlDeriv κ i) p x t = 0 := by
  have hF : ∀ j, Integrable (fun z : Vec3 × ℝ => u z i * u z j)
      (volume.restrict (vlSlab t₀ T)) := fun j => (hu i).integrable_mul (hu j)
  set G : ℝ → ℝ := fun t =>
    vlConvT κ (fun z : Vec3 × ℝ => Dtu z i) x t +
        ∑ j : Fin 3, vlConvT (vlDeriv κ j) (fun z : Vec3 × ℝ => u z i * u z j) x t -
        ∑ j : Fin 3, vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t +
        vlConvT (vlDeriv κ i) p x t with hG
  have hAint := vlConvT_integrableOn (hDt i) hκ x
  have hBint : ∀ j, IntegrableOn (fun t => vlConvT (vlDeriv κ j)
      (fun z : Vec3 × ℝ => u z i * u z j) x t) (Ioo t₀ T) volume := fun j =>
    lps_convT_integrableOn_L1 (hF j) (hκ.deriv j) x
  have hCint : ∀ j, IntegrableOn (fun t => vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t)
      (Ioo t₀ T) volume := fun j => vlConvT_integrableOn (hD2 i j) hκ x
  have hDint := vlConvT_integrableOn hp (hκ.deriv i) x
  have hGint : IntegrableOn G (Ioo t₀ T) volume :=
    (((hAint.add (integrable_finsetSum _ fun j _ => hBint j)).sub
      (integrable_finsetSum _ fun j _ => hCint j)).add hDint)
  have hfull : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo t₀ T → ∫ t, θ t • G t ∂(volume : Measure ℝ) = 0 := by
    intro θ hθ hθc hθI
    have hθt : IsIntervalTest (Ioo t₀ T) θ := ⟨hθ, hθc, hθI⟩
    have hθcont : Continuous θ := hθ.continuous
    have hθb := hθcont.bounded_above_of_compact_support hθc
    have hθb' : ∃ C, ∀ s, |θ s| ≤ C := by
      obtain ⟨C, hC⟩ := hθb
      exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩
    have hE := lps_strong_scalar_equation hU hDerivs hu hDu hD2 hDt hp i (vlTest_mem hκ x hθt)
    -- the five integrals against the separated test
    have sA := vlSlab_integral_sep (hDt i) hκ x hθcont hθb'
    have sB := fun j : Fin 3 => lps_slab_integral_sep_L1 (hF j) (hκ.deriv j) x hθcont hθb'
    have sC := fun j : Fin 3 => vlSlab_integral_sep (hD2 i j) hκ x hθcont hθb'
    have sD := vlSlab_integral_sep hp (hκ.deriv i) x hθcont hθb'
    have hpt : ∀ z : Vec3 × ℝ,
        (Dtu z i * vlTest κ x θ z - ∑ j : Fin 3, u z i * u z j *
            spatialPartial (vlTest κ x θ) j z
          - (∑ j : Fin 3, D2u z i j j) * vlTest κ x θ z -
            p z * spatialPartial (vlTest κ x θ) i z) =
          Dtu z i * (κ (x - z.1) * θ z.2) +
            ∑ j : Fin 3, (u z i * u z j) * (vlDeriv κ j (x - z.1) * θ z.2) -
            ∑ j : Fin 3, D2u z i j j * (κ (x - z.1) * θ z.2) +
            p z * (vlDeriv κ i (x - z.1) * θ z.2) := by
      intro z
      simp only [vlTest_spatialPartial hκ x θ, vlTest, Finset.sum_mul, mul_neg,
        Finset.sum_neg_distrib]
      ring
    have hE' : ∫ z in vlSlab t₀ T,
        (Dtu z i * (κ (x - z.1) * θ z.2) +
            ∑ j : Fin 3, (u z i * u z j) * (vlDeriv κ j (x - z.1) * θ z.2) -
            ∑ j : Fin 3, D2u z i j j * (κ (x - z.1) * θ z.2) +
            p z * (vlDeriv κ i (x - z.1) * θ z.2)) = 0 := by
      rw [← hE]
      exact integral_congr_ae (Eventually.of_forall fun z => (hpt z).symm)
    have iB : Integrable (fun z : Vec3 × ℝ =>
        ∑ j : Fin 3, (u z i * u z j) * (vlDeriv κ j (x - z.1) * θ z.2))
        (volume.restrict (vlSlab t₀ T)) :=
      integrable_finsetSum _ fun j _ => (sB j).1
    have iC : Integrable (fun z : Vec3 × ℝ =>
        ∑ j : Fin 3, D2u z i j j * (κ (x - z.1) * θ z.2)) (volume.restrict (vlSlab t₀ T)) :=
      integrable_finsetSum _ fun j _ => (sC j).1
    have i1 : Integrable (fun z : Vec3 × ℝ => Dtu z i * (κ (x - z.1) * θ z.2) +
        ∑ j : Fin 3, (u z i * u z j) * (vlDeriv κ j (x - z.1) * θ z.2))
        (volume.restrict (vlSlab t₀ T)) := sA.1.add iB
    have i2 : Integrable (fun z : Vec3 × ℝ => Dtu z i * (κ (x - z.1) * θ z.2) +
        ∑ j : Fin 3, (u z i * u z j) * (vlDeriv κ j (x - z.1) * θ z.2) -
        ∑ j : Fin 3, D2u z i j j * (κ (x - z.1) * θ z.2))
        (volume.restrict (vlSlab t₀ T)) := i1.sub iC
    rw [integral_add i2 sD.1, integral_sub i1 iC, integral_add sA.1 iB,
      integral_finsetSum _ (fun j _ => (sB j).1), integral_finsetSum _ (fun j _ => (sC j).1),
      sA.2, sD.2] at hE'
    simp only [fun j => (sB j).2, fun j => (sC j).2] at hE'
    have hθG : ∫ t, θ t • G t ∂(volume : Measure ℝ) = ∫ t in Ioo t₀ T, θ t * G t := by
      have hcompl : ∀ t ∉ Ioo t₀ T, θ t • G t = 0 := by
        intro t ht
        have : θ t = 0 := by
          by_contra hne
          exact ht (hθI ((subset_tsupport θ) (Function.mem_support.mpr hne)))
        simp [this]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
      simp only [smul_eq_mul]
    have hθint : ∀ (H : ℝ → ℝ), IntegrableOn H (Ioo t₀ T) volume →
        IntegrableOn (fun t => θ t * H t) (Ioo t₀ T) volume := by
      intro H hH
      obtain ⟨C, hC⟩ := hθb'
      exact hH.bdd_mul (c := C) hθcont.aestronglyMeasurable
        (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hC s)
    rw [hθG]
    have hsum : ∫ t in Ioo t₀ T, θ t * G t =
        (∫ t in Ioo t₀ T, θ t * vlConvT κ (fun z : Vec3 × ℝ => Dtu z i) x t) +
          (∑ j : Fin 3, ∫ t in Ioo t₀ T, θ t *
            vlConvT (vlDeriv κ j) (fun z : Vec3 × ℝ => u z i * u z j) x t) -
          (∑ j : Fin 3, ∫ t in Ioo t₀ T, θ t *
            vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t) +
          ∫ t in Ioo t₀ T, θ t * vlConvT (vlDeriv κ i) p x t := by
      have hpt2 : ∀ t, θ t * G t =
          θ t * vlConvT κ (fun z : Vec3 × ℝ => Dtu z i) x t +
            ∑ j : Fin 3, θ t * vlConvT (vlDeriv κ j)
              (fun z : Vec3 × ℝ => u z i * u z j) x t -
            ∑ j : Fin 3, θ t * vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t +
            θ t * vlConvT (vlDeriv κ i) p x t := by
        intro t
        simp only [hG, mul_add, mul_sub, Finset.mul_sum]
      have jB : ∀ j : Fin 3, IntegrableOn (fun t => θ t * vlConvT (vlDeriv κ j)
          (fun z : Vec3 × ℝ => u z i * u z j) x t) (Ioo t₀ T) volume :=
        fun j => hθint _ (hBint j)
      have jC : ∀ j : Fin 3, IntegrableOn (fun t => θ t *
          vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t) (Ioo t₀ T) volume :=
        fun j => hθint _ (hCint j)
      have jA := hθint _ hAint
      have jD := hθint _ hDint
      have jBs : IntegrableOn (fun t => ∑ j : Fin 3, θ t * vlConvT (vlDeriv κ j)
          (fun z : Vec3 × ℝ => u z i * u z j) x t) (Ioo t₀ T) volume :=
        integrable_finsetSum _ fun j _ => jB j
      have jCs : IntegrableOn (fun t => ∑ j : Fin 3, θ t *
          vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t) (Ioo t₀ T) volume :=
        integrable_finsetSum _ fun j _ => jC j
      have j1 : IntegrableOn (fun t => θ t * vlConvT κ (fun z : Vec3 × ℝ => Dtu z i) x t +
          ∑ j : Fin 3, θ t * vlConvT (vlDeriv κ j)
            (fun z : Vec3 × ℝ => u z i * u z j) x t) (Ioo t₀ T) volume := jA.add jBs
      have j2 : IntegrableOn (fun t => θ t * vlConvT κ (fun z : Vec3 × ℝ => Dtu z i) x t +
          ∑ j : Fin 3, θ t * vlConvT (vlDeriv κ j)
            (fun z : Vec3 × ℝ => u z i * u z j) x t -
          ∑ j : Fin 3, θ t * vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t)
          (Ioo t₀ T) volume := j1.sub jCs
      simp only [hpt2]
      rw [integral_add j2 jD, integral_sub j1 jCs, integral_add jA jBs,
        integral_finsetSum _ (fun j _ => jB j), integral_finsetSum _ (fun j _ => jC j)]
    rw [hsum]
    linarith only [hE']
  have hzero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hGint.locallyIntegrableOn hfull
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hzero] with s hs hsI
  exact hs hsI

end ESS.LPS

end
