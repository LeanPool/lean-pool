/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyTest
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyTime

/-!
# The time derivative of a spatial convolution of a weak heat solution

Let `w` solve `∂ₜ w - Δw = div H + f` in distributions on `ℝ³ × (a, τ)`, with
`w, H, f ∈ L²`, and let its pairings with spatial tests have continuous
versions whose value at `a` is the pairing with `w₀`. Then for every smooth
compact kernel `k` and every point `x`, the convolution `(k ⋆ w(s))(x)`
agrees for almost every `s` with the primitive
`(k ⋆ w₀)(x) + ∫ₐˢ ((Δk) ⋆ w + (∂ⱼk) ⋆ Hⱼ + k ⋆ f)(x)`.
This is the time step of `lem:localized-vorticity-energy` of the
Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set Filter

noncomputable section

namespace CKN

open CKN.Foundation.Parabolic

/-- The space-time slab `ℝ³ × (a, τ)`. -/
@[expose]
def vlSlab (a τ : ℝ) : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioo a τ

/-- A distributional solution of `∂ₜ w - Δw = div H + f` on `ℝ³ × (a, τ)` with
square-integrable data, whose initial trace is `w₀`: every pairing with a
spatial test has a continuous version on `[a, τ]` whose value at `a` is the
pairing with `w₀`. -/
structure VlHeatSolution (a τ : ℝ) (w : Vec3 × ℝ → ℝ) (H : Fin 3 → Vec3 × ℝ → ℝ)
    (f : Vec3 × ℝ → ℝ) (w₀ : Vec3 → ℝ) : Prop where
  lt : a < τ
  w_meas : StronglyMeasurable w
  H_meas : ∀ j, StronglyMeasurable (H j)
  f_meas : StronglyMeasurable f
  w_L2 : MemLp w 2 (volume.restrict (vlSlab a τ))
  H_L2 : ∀ j, MemLp (H j) 2 (volume.restrict (vlSlab a τ))
  f_L2 : MemLp f 2 (volume.restrict (vlSlab a τ))
  w₀_L2 : MemLp w₀ 2 volume
  weak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ),
    ∫ p in vlSlab a τ, w p * (-CKN.timePartial φ p -
        ∑ j : Fin 3, CKN.spatialSecondPartial φ j j p) =
      ∫ p in vlSlab a τ, (-(∑ j : Fin 3, H j p * CKN.spatialPartial φ j p) + f p * φ p)
  trace : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∃ c : ℝ → ℝ, ContinuousOn c (Icc a τ) ∧ c a = ∫ x, w₀ x * ψ x ∧
      ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = ∫ x, w (x, t) * ψ x

/-- The convolution of the time slice at `s`. -/
@[expose]
def vlConvT (k : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ) (x : Vec3) (s : ℝ) : ℝ :=
  vlConv k (fun y => w (y, s)) x

/-- The convolved source `((Δk) ⋆ w + (∂ⱼk) ⋆ Hⱼ + k ⋆ f)(x, s)`. -/
@[expose]
def vlSource (k : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ) (H : Fin 3 → Vec3 × ℝ → ℝ)
    (f : Vec3 × ℝ → ℝ) (x : Vec3) (s : ℝ) : ℝ :=
  ∑ j : Fin 3, vlConvT (vlDeriv (vlDeriv k j) j) w x s +
    ∑ j : Fin 3, vlConvT (vlDeriv k j) (H j) x s + vlConvT k f x s

/-- The primitive from the convolved initial trace. -/
@[expose]
def vlPrim (a : ℝ) (k : Vec3 → ℝ) (w₀ : Vec3 → ℝ) (w : Vec3 × ℝ → ℝ)
    (H : Fin 3 → Vec3 × ℝ → ℝ) (f : Vec3 × ℝ → ℝ) (x : Vec3) (t : ℝ) : ℝ :=
  vlConv k w₀ x + ∫ s in a..t, vlSource k w H f x s

theorem vlConv_apply_swap (k h : Vec3 → ℝ) (x : Vec3) :
    vlConv k h x = ∫ y, h y * k (x - y) := by
  rw [vlConv, convolution_eq_swap]
  simp [mul_comm]

theorem vlSlab_measure (a τ : ℝ) :
    (volume : Measure (Vec3 × ℝ)).restrict (vlSlab a τ) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a τ)) := by
  rw [vlSlab, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- A shifted kernel is square integrable on the slab. -/
theorem vlSlab_memLp_shift {k : Vec3 → ℝ} (hk : IsVlKernel k) (x : Vec3) (a τ : ℝ) :
    MemLp (fun p : Vec3 × ℝ => k (x - p.1)) 2 (volume.restrict (vlSlab a τ)) := by
  obtain ⟨C, hC⟩ := hk.continuous.bounded_above_of_compact_support hk.2
  set K : Set Vec3 := (fun y : Vec3 => x - y) ⁻¹' tsupport k with hK_def
  have hKc : IsCompact K := by
    have himg : K = (fun y : Vec3 => x - y) '' tsupport k := by
      ext y
      simp only [hK_def, mem_preimage, mem_image]
      constructor
      · intro hy
        exact ⟨x - y, hy, by simp⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
    rw [himg]
    exact hk.2.isCompact.image (continuous_const.sub continuous_id)
  have hKm : MeasurableSet (K ×ˢ (univ : Set ℝ)) :=
    hKc.isClosed.measurableSet.prod MeasurableSet.univ
  have hfin : (volume.restrict (vlSlab a τ)) (K ×ˢ (univ : Set ℝ)) ≠ ⊤ := by
    rw [vlSlab_measure, Measure.prod_prod]
    exact ENNReal.mul_ne_top hKc.measure_lt_top.ne
      (by simp [Real.volume_Ioo])
  have hind := memLp_indicator_const (μ := volume.restrict (vlSlab a τ)) 2 hKm C (Or.inr hfin)
  refine hind.of_le ?_ ?_
  · exact (hk.continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable
  · filter_upwards [] with p
    by_cases hp : p ∈ K ×ˢ (univ : Set ℝ)
    · rw [indicator_of_mem hp]
      exact (hC _).trans (le_abs_self C) |>.trans_eq (Real.norm_eq_abs C).symm
    · have hpK : x - p.1 ∉ tsupport k := fun h => hp ⟨h, mem_univ _⟩
      rw [indicator_of_notMem hp, image_eq_zero_of_notMem_tsupport hpK]

/-- Fubini for a slab field against a separated weight. -/
theorem vlSlab_integral_sep {a τ : ℝ} {g : Vec3 × ℝ → ℝ} {k : Vec3 → ℝ}
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) (hk : IsVlKernel k) (x : Vec3)
    {η : ℝ → ℝ} (hη : Continuous η) (hηb : ∃ C, ∀ s, |η s| ≤ C) :
    Integrable (fun p : Vec3 × ℝ => g p * (k (x - p.1) * η p.2))
        (volume.restrict (vlSlab a τ)) ∧
      ∫ p in vlSlab a τ, g p * (k (x - p.1) * η p.2) =
        ∫ s in Ioo a τ, η s * vlConvT k g x s := by
  obtain ⟨C, hC⟩ := hηb
  have hshift := vlSlab_memLp_shift hk x a τ
  have hweight : MemLp (fun p : Vec3 × ℝ => k (x - p.1) * η p.2) 2
      (volume.restrict (vlSlab a τ)) := by
    refine (hshift.const_mul C).of_le ?_ ?_
    · exact ((hk.continuous.comp (continuous_const.sub continuous_fst)).mul
        (hη.comp continuous_snd)).aestronglyMeasurable
    · filter_upwards [] with p
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, mul_comm (|k (x - p.1)|)]
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
      rw [abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
  have hint : Integrable (fun p : Vec3 × ℝ => g p * (k (x - p.1) * η p.2))
      (volume.restrict (vlSlab a τ)) := hg.integrable_mul hweight
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

/-- The convolved time slice is integrable in time. -/
theorem vlConvT_integrableOn {a τ : ℝ} {g : Vec3 × ℝ → ℝ} {k : Vec3 → ℝ}
    (hg : MemLp g 2 (volume.restrict (vlSlab a τ))) (hk : IsVlKernel k) (x : Vec3) :
    IntegrableOn (fun s => vlConvT k g x s) (Ioo a τ) volume := by
  have hint : Integrable (fun p : Vec3 × ℝ => g p * k (x - p.1))
      (volume.restrict (vlSlab a τ)) := hg.integrable_mul (vlSlab_memLp_shift hk x a τ)
  rw [vlSlab_measure] at hint
  have h := hint.integral_prod_right
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [vlConvT, vlConv_apply_swap]

theorem vlSource_integrableOn {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ}
    {w₀ : Vec3 → ℝ} (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ} (hk : IsVlKernel k)
    (x : Vec3) :
    IntegrableOn (fun s => vlSource k w H f x s) (Ioo a τ) volume := by
  unfold vlSource
  refine (Integrable.add ?_ ?_).add (vlConvT_integrableOn sol.f_L2 hk x)
  · exact integrable_finsetSum _ fun j _ =>
      vlConvT_integrableOn sol.w_L2 ((hk.deriv j).deriv j) x
  · exact integrable_finsetSum _ fun j _ =>
      vlConvT_integrableOn (sol.H_L2 j) (hk.deriv j) x

/-- The convolution of a weak heat solution has the convolved source as its weak
time derivative. -/
theorem vlConvT_hasWeakDeriv {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ}
    {w₀ : Vec3 → ℝ} (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ} (hk : IsVlKernel k)
    (x : Vec3) :
    HasWeakDerivOn (Ioo a τ) (fun s => vlConvT k w x s) (fun s => vlSource k w H f x s) := by
  intro θ hθ
  have hθc : Continuous θ := hθ.1.continuous
  have hθ'c : Continuous (deriv θ) := hθ.1.continuous_deriv (by simp)
  have hθb := hθc.bounded_above_of_compact_support hθ.2.1
  have hθ'b := hθ'c.bounded_above_of_compact_support (hθ.2.1.deriv (𝕜 := ℝ))
  have hθb' : ∃ C, ∀ s, |θ s| ≤ C := by
    obtain ⟨C, hC⟩ := hθb
    exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩
  have hθ'b' : ∃ C, ∀ s, |deriv θ s| ≤ C := by
    obtain ⟨C, hC⟩ := hθ'b
    exact ⟨C, fun s => by simpa [Real.norm_eq_abs] using hC s⟩
  have hweak := sol.weak (vlTest k x θ) (vlTest_mem hk x hθ)
  -- rewrite the test derivatives
  have hL : ∀ p : Vec3 × ℝ, w p * (-CKN.timePartial (vlTest k x θ) p -
        ∑ j : Fin 3, CKN.spatialSecondPartial (vlTest k x θ) j j p) =
      -(w p * (k (x - p.1) * deriv θ p.2)) -
        ∑ j : Fin 3, w p * (vlDeriv (vlDeriv k j) j (x - p.1) * θ p.2) := by
    intro p
    rw [vlTest_timePartial x hθ.1 p]
    simp_rw [vlTest_spatialSecondPartial hk x θ _ p]
    rw [mul_sub, mul_neg, Finset.mul_sum]
  have hR : ∀ p : Vec3 × ℝ, (-(∑ j : Fin 3, H j p * CKN.spatialPartial (vlTest k x θ) j p) +
        f p * vlTest k x θ p) =
      ∑ j : Fin 3, H j p * (vlDeriv k j (x - p.1) * θ p.2) +
        f p * (k (x - p.1) * θ p.2) := by
    intro p
    simp_rw [vlTest_spatialPartial hk x θ _ p]
    simp only [vlTest, mul_neg, Finset.sum_neg_distrib, neg_neg]
  simp_rw [hL, hR] at hweak
  -- separated integrals
  have hA := vlSlab_integral_sep sol.w_L2 hk x hθ'c hθ'b'
  have hB := fun j : Fin 3 =>
    vlSlab_integral_sep sol.w_L2 ((hk.deriv j).deriv j) x hθc hθb'
  have hC := fun j : Fin 3 => vlSlab_integral_sep (sol.H_L2 j) (hk.deriv j) x hθc hθb'
  have hD := vlSlab_integral_sep sol.f_L2 hk x hθc hθb'
  have hAneg : Integrable (fun p : Vec3 × ℝ => -(w p * (k (x - p.1) * deriv θ p.2)))
      (volume.restrict (vlSlab a τ)) := hA.1.neg
  have hBsum : Integrable (fun p : Vec3 × ℝ => ∑ j : Fin 3,
      w p * (vlDeriv (vlDeriv k j) j (x - p.1) * θ p.2)) (volume.restrict (vlSlab a τ)) :=
    integrable_finsetSum _ fun j _ => (hB j).1
  have hCsum : Integrable (fun p : Vec3 × ℝ => ∑ j : Fin 3,
      H j p * (vlDeriv k j (x - p.1) * θ p.2)) (volume.restrict (vlSlab a τ)) :=
    integrable_finsetSum _ fun j _ => (hC j).1
  have hLHS : ∫ p in vlSlab a τ, (-(w p * (k (x - p.1) * deriv θ p.2)) -
        ∑ j : Fin 3, w p * (vlDeriv (vlDeriv k j) j (x - p.1) * θ p.2)) =
      -(∫ s in Ioo a τ, deriv θ s * vlConvT k w x s) -
        ∑ j : Fin 3, ∫ s in Ioo a τ, θ s * vlConvT (vlDeriv (vlDeriv k j) j) w x s := by
    rw [integral_sub hAneg hBsum, integral_neg, integral_finsetSum _ fun j _ => (hB j).1,
      hA.2]
    congr 1
    exact Finset.sum_congr rfl fun j _ => (hB j).2
  have hRHS : ∫ p in vlSlab a τ, (∑ j : Fin 3, H j p * (vlDeriv k j (x - p.1) * θ p.2) +
        f p * (k (x - p.1) * θ p.2)) =
      (∑ j : Fin 3, ∫ s in Ioo a τ, θ s * vlConvT (vlDeriv k j) (H j) x s) +
        ∫ s in Ioo a τ, θ s * vlConvT k f x s := by
    rw [integral_add hCsum hD.1, integral_finsetSum _ fun j _ => (hC j).1, hD.2]
    congr 1
    exact Finset.sum_congr rfl fun j _ => (hC j).2
  rw [hLHS, hRHS] at hweak
  -- time integrals
  have hconvInt := vlConvT_integrableOn sol.w_L2 hk x
  have hconvθ' : IntegrableOn (fun s => deriv θ s * vlConvT k w x s) (Ioo a τ) volume := by
    obtain ⟨C, hC'⟩ := hθ'b'
    exact hconvInt.bdd_mul (c := C) hθ'c.aestronglyMeasurable
      (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hC' s)
  have hsθ : ∀ (g : Vec3 × ℝ → ℝ) (l : Vec3 → ℝ),
      MemLp g 2 (volume.restrict (vlSlab a τ)) → IsVlKernel l →
      IntegrableOn (fun s => θ s * vlConvT l g x s) (Ioo a τ) volume := by
    intro g l hg hl
    obtain ⟨C, hC'⟩ := hθb'
    exact (vlConvT_integrableOn hg hl x).bdd_mul (c := C) hθc.aestronglyMeasurable
      (Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hC' s)
  have hsum1 : ∫ s in Ioo a τ, ∑ j : Fin 3, θ s * vlConvT (vlDeriv (vlDeriv k j) j) w x s =
      ∑ j : Fin 3, ∫ s in Ioo a τ, θ s * vlConvT (vlDeriv (vlDeriv k j) j) w x s :=
    integral_finsetSum _ fun j _ => hsθ w _ sol.w_L2 ((hk.deriv j).deriv j)
  have hsum2 : ∫ s in Ioo a τ, ∑ j : Fin 3, θ s * vlConvT (vlDeriv k j) (H j) x s =
      ∑ j : Fin 3, ∫ s in Ioo a τ, θ s * vlConvT (vlDeriv k j) (H j) x s :=
    integral_finsetSum _ fun j _ => hsθ (H j) _ (sol.H_L2 j) (hk.deriv j)
  have hsrc : ∫ s in Ioo a τ, vlSource k w H f x s * θ s =
      (∑ j : Fin 3, ∫ s in Ioo a τ, θ s * vlConvT (vlDeriv (vlDeriv k j) j) w x s) +
        (∑ j : Fin 3, ∫ s in Ioo a τ, θ s * vlConvT (vlDeriv k j) (H j) x s) +
        ∫ s in Ioo a τ, θ s * vlConvT k f x s := by
    rw [← hsum1, ← hsum2, ← integral_add, ← integral_add]
    · refine setIntegral_congr_fun measurableSet_Ioo (fun s _ => ?_)
      simp only [vlSource]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    · exact (integrable_finsetSum _ fun j _ =>
        hsθ w _ sol.w_L2 ((hk.deriv j).deriv j)).add
        (integrable_finsetSum _ fun j _ => hsθ (H j) _ (sol.H_L2 j) (hk.deriv j))
    · exact hsθ f k sol.f_L2 hk
    · exact integrable_finsetSum _ fun j _ => hsθ w _ sol.w_L2 ((hk.deriv j).deriv j)
    · exact integrable_finsetSum _ fun j _ => hsθ (H j) _ (sol.H_L2 j) (hk.deriv j)
  have hlhs : ∫ s in Ioo a τ, vlConvT k w x s * deriv θ s =
      ∫ s in Ioo a τ, deriv θ s * vlConvT k w x s := by
    congr 1
    funext s
    ring
  rw [hlhs, hsrc]
  rw [← hsum1, ← hsum2] at hweak ⊢
  linarith only [hweak]

/-- The convolution of a weak heat solution is, for almost every time, the
primitive from its convolved initial trace. -/
theorem vlConvT_ae_eq_prim {a τ : ℝ} {w f : Vec3 × ℝ → ℝ} {H : Fin 3 → Vec3 × ℝ → ℝ}
    {w₀ : Vec3 → ℝ} (sol : VlHeatSolution a τ w H f w₀) {k : Vec3 → ℝ} (hk : IsVlKernel k)
    (x : Vec3) :
    ∀ᵐ t ∂(volume.restrict (Ioo a τ)), vlConvT k w x t = vlPrim a k w₀ w H f x t := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => k (x - y)) :=
    hk.1.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y : Vec3 => k (x - y)) := by
    have h := hk.2.comp_homeomorph (Homeomorph.subLeft x)
    exact h
  obtain ⟨c, hc, hca, hcf⟩ := sol.trace _ hψ hψc
  have hca' : c a = vlConv k w₀ x := by
    rw [hca, vlConv_apply_swap]
  have hcf' : ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = vlConvT k w x t := by
    filter_upwards [hcf] with t ht
    rw [ht, vlConvT, vlConv_apply_swap]
  have h := vlTime_eq_primitive_of_trace sol.lt (vlConvT_integrableOn sol.w_L2 hk x)
    (vlSource_integrableOn sol hk x) (vlConvT_hasWeakDeriv sol hk x) hc hca' hcf'
  filter_upwards [h.2] with t ht
  exact ht

end CKN

end
