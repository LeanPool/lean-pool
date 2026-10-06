/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainLeibniz

/-!
# The heat equation for a cutoff of a local solution

If `∂ₜ z - Δ z = G` in distributions on `U × I` and `η` is smooth and vanishes
for `x` outside a compact subset of `U`, then `w = ηz`, extended by zero,
solves `∂ₜ w - Δ w = ηG + (∂ₜη - Δη) z - 2 ∇η · ∇z` in distributions on
`ℝ³ × I` (`lem:local-heat-gain`, first step of the proof).
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

section Calculus

variable {A B : Vec3 × ℝ → ℝ}

/-- The second spatial derivative of a product of smooth fields. -/
theorem spatialSecondPartial_mul_of_contDiff (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (j : Fin 3) (p : Vec3 × ℝ) :
    spatialSecondPartial (fun q : Vec3 × ℝ => A q * B q) j j p =
      A p * spatialSecondPartial B j j p + 2 * (spatialPartial A j p * spatialPartial B j p) +
        B p * spatialSecondPartial A j j p := by
  have hAj := vorticityHeatSmooth_spatialPartial_contDiff hA j
  have hBj := vorticityHeatSmooth_spatialPartial_contDiff hB j
  have h1 : (fun q : Vec3 × ℝ => spatialPartial (fun r : Vec3 × ℝ => A r * B r) j q) =
      fun q => A q * spatialPartial B j q + B q * spatialPartial A j q :=
    funext (vorticityHeatSmooth_spatialPartial_mul hA hB j)
  show spatialPartial (fun q : Vec3 × ℝ =>
      spatialPartial (fun r : Vec3 × ℝ => A r * B r) j q) j p = _
  rw [h1, vorticityHeatSmooth_spatialPartial_add (hA.mul hBj) (hB.mul hAj),
    vorticityHeatSmooth_spatialPartial_mul hA hBj, vorticityHeatSmooth_spatialPartial_mul hB hAj]
  change A p * spatialSecondPartial B j j p + spatialPartial B j p * spatialPartial A j p +
      (B p * spatialSecondPartial A j j p + spatialPartial A j p * spatialPartial B j p) = _
  ring

end Calculus

/-- A product with a field vanishing outside `K × ℝ` has topological support
in `U × I` when the other factor is supported in `ℝ³ × I` and `K ⊆ U`. -/
theorem tsupport_mul_subset_of_compl {U K : Set Vec3} {I : Set ℝ} (hK : IsCompact K)
    (hKU : K ⊆ U) {f φ : Vec3 × ℝ → ℝ} (hf : ∀ p : Vec3 × ℝ, p.1 ∉ K → f p = 0)
    (hφ : tsupport φ ⊆ univ ×ˢ I) :
    tsupport (fun p => f p * φ p) ⊆ U ×ˢ I := by
  have hclosed : IsClosed ((K ×ˢ (univ : Set ℝ)) ∩ tsupport φ) :=
    (hK.isClosed.prod isClosed_univ).inter (isClosed_tsupport φ)
  have hsub : Function.support (fun p => f p * φ p) ⊆ (K ×ˢ (univ : Set ℝ)) ∩ tsupport φ := by
    intro p hp
    refine ⟨⟨?_, Set.mem_univ _⟩, subset_tsupport _ (fun h => hp (by simp [h]))⟩
    by_contra hpK
    exact hp (by simp [hf p hpK])
  refine (closure_minimal hsub hclosed).trans ?_
  rintro p ⟨⟨hpK, -⟩, hpφ⟩
  exact ⟨hKU hpK, (hφ hpφ).2⟩

/-- Set integrals over `ℝ³ × I` of integrands vanishing for `x ∉ U` are
integrals over `U × I`. -/
theorem setIntegral_univ_prod_eq {U : Set Vec3} {I : Set ℝ} (hI : MeasurableSet I)
    {F : Vec3 × ℝ → ℝ} (hF : ∀ p : Vec3 × ℝ, p.1 ∉ U → F p = 0) :
    ∫ p in (univ : Set Vec3) ×ˢ I, F p = ∫ p in U ×ˢ I, F p :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (MeasurableSet.univ.prod hI)
    (prod_mono (subset_univ U) subset_rfl) fun p hp => hF p fun hpU => hp.2 ⟨hpU, hp.1.2⟩

/-- The heat equation for a cutoff of a local distributional solution. -/
theorem heatCutoff_equation {U K : Set Vec3} {I : Set ℝ} (hIm : MeasurableSet I)
    (hK : IsCompact K) (hKU : K ⊆ U) {z G η : Vec3 × ℝ → ℝ} {Dz : Fin 3 → Vec3 × ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηK : ∀ x, x ∉ K → ∀ t, η (x, t) = 0)
    (hz : MemLp z 2 (volume.restrict (U ×ˢ I)))
    (hDz : ∀ j, MemLp (Dz j) 2 (volume.restrict (U ×ˢ I)))
    (hG : MemLp G 2 (volume.restrict (U ×ˢ I)))
    (hweak : ∀ j, IsSpaceTimeWeakPartial (U ×ˢ I) j z (Dz j))
    (hheat : IsHeatSolutionOn U I z G) :
    ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set Vec3) ×ˢ I →
      ∫ p in (univ : Set Vec3) ×ˢ I, η p * z p *
          (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
        ∫ p in (univ : Set Vec3) ×ˢ I,
          (η p * G p + (timePartial η p - ∑ j : Fin 3, spatialSecondPartial η j j p) * z p -
            2 * ∑ j : Fin 3, spatialPartial η j p * Dz j p) * φ p := by
  intro φ hφ hφc hφI
  -- vanishing of `η` and its derivatives outside `K`
  have hη0 : ∀ p : Vec3 × ℝ, p.1 ∉ K → η p = 0 := fun p hp => hηK p.1 hp p.2
  have hηt0 : ∀ p : Vec3 × ℝ, p.1 ∉ K → timePartial η p = 0 :=
    fun p hp => timePartial_eq_zero_of_compl hηK p.1 hp p.2
  have hηj0 (j : Fin 3) : ∀ p : Vec3 × ℝ, p.1 ∉ K → spatialPartial η j p = 0 :=
    fun p hp => spatialPartial_eq_zero_of_compl hK hηK j p.1 hp p.2
  have hηjj0 (j : Fin 3) : ∀ p : Vec3 × ℝ, p.1 ∉ K → spatialSecondPartial η j j p = 0 :=
    fun p hp => spatialPartial_eq_zero_of_compl hK
      (spatialPartial_eq_zero_of_compl hK hηK j) j p.1 hp p.2
  have hnotU (p : Vec3 × ℝ) (hp : p.1 ∉ U) : p.1 ∉ K := fun h => hp (hKU h)
  -- the two families of test functions
  let ψ : Vec3 × ℝ → ℝ := fun p => η p * φ p
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hη.mul hφ
  have hψc : HasCompactSupport ψ := hφc.mul_left
  have hψV : tsupport ψ ⊆ U ×ˢ I := tsupport_mul_subset_of_compl hK hKU hη0 hφI
  let ηj : Fin 3 → Vec3 × ℝ → ℝ := fun j p => spatialPartial η j p
  have hηj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ηj j) :=
    vorticityHeatSmooth_spatialPartial_contDiff hη j
  let ψj : Fin 3 → Vec3 × ℝ → ℝ := fun j p => ηj j p * φ p
  have hψj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψj j) := (hηj j).mul hφ
  have hψjc (j : Fin 3) : HasCompactSupport (ψj j) := hφc.mul_left
  have hψjV (j : Fin 3) : tsupport (ψj j) ⊆ U ×ˢ I :=
    tsupport_mul_subset_of_compl hK hKU (hηj0 j) hφI
  -- square integrability of the smooth compactly supported factors
  have hL2 {f : Vec3 × ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
      MemLp f 2 (volume.restrict (U ×ˢ I)) := memLp_two_restrict_of_test hf hfc (U ×ˢ I)
  have hηt : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => timePartial η q) :=
    vorticityHeatSmooth_timePartial_contDiff hη
  have hηjj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => spatialSecondPartial η j j q) :=
    vorticityHeatSmooth_spatialPartial_contDiff (hηj j) j
  have hφt : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => timePartial φ q) :=
    vorticityHeatSmooth_timePartial_contDiff hφ
  have hφjj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => spatialSecondPartial φ j j q) :=
    vorticityHeatSmooth_spatialPartial_contDiff
      (vorticityHeatSmooth_spatialPartial_contDiff hφ j) j
  -- the pointwise identity
  let T1 : Vec3 × ℝ → ℝ := fun p =>
    z p * (-timePartial ψ p - ∑ j : Fin 3, spatialSecondPartial ψ j j p)
  let T2 : Vec3 × ℝ → ℝ := fun p =>
    z p * ((timePartial η p - ∑ j : Fin 3, spatialSecondPartial η j j p) * φ p)
  let T3 : Fin 3 → Vec3 × ℝ → ℝ := fun j p => z p * spatialPartial (ψj j) j p
  have hpt (p : Vec3 × ℝ) :
      η p * z p * (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
        T1 p + T2 p + 2 * ∑ j : Fin 3, T3 j p := by
    have e1 : T1 p = z p * (-(η p * timePartial φ p + φ p * timePartial η p) -
        ∑ j : Fin 3, (η p * spatialSecondPartial φ j j p +
          2 * (spatialPartial η j p * spatialPartial φ j p) +
          φ p * spatialSecondPartial η j j p)) := by
      show z p * (-timePartial (fun q : Vec3 × ℝ => η q * φ q) p -
        ∑ j : Fin 3, spatialSecondPartial (fun q : Vec3 × ℝ => η q * φ q) j j p) = _
      rw [vorticityHeatSmooth_timePartial_mul hη hφ p,
        Finset.sum_congr rfl fun j _ => spatialSecondPartial_mul_of_contDiff hη hφ j p]
    have e3 (j : Fin 3) : T3 j p = z p * (spatialSecondPartial η j j p * φ p +
        spatialPartial η j p * spatialPartial φ j p) := by
      show z p * spatialPartial (fun q : Vec3 × ℝ => spatialPartial η j q * φ q) j p = _
      rw [vorticityHeatSmooth_spatialPartial_mul (hηj j) hφ j p]
      show z p * (spatialPartial η j p * spatialPartial φ j p +
        φ p * spatialSecondPartial η j j p) = _
      ring
    have e2 : T2 p = z p * ((timePartial η p - ∑ j : Fin 3, spatialSecondPartial η j j p) *
        φ p) := rfl
    rw [e1, e2, Finset.sum_congr rfl fun j _ => e3 j]
    simp only [Fin.sum_univ_three]
    ring
  -- integrability
  have hT1 : Integrable T1 (volume.restrict (U ×ˢ I)) := by
    have h1 : Continuous (fun p : Vec3 × ℝ => timePartial ψ p) :=
      (vorticityHeatSmooth_timePartial_contDiff hψ).continuous
    have h2 (j : Fin 3) : Continuous (fun p : Vec3 × ℝ => spatialSecondPartial ψ j j p) :=
      (vorticityHeatSmooth_spatialPartial_contDiff
        (vorticityHeatSmooth_spatialPartial_contDiff hψ j) j).continuous
    have hc : Continuous (fun p : Vec3 × ℝ =>
        -timePartial ψ p - ∑ j : Fin 3, spatialSecondPartial ψ j j p) :=
      h1.neg.sub (continuous_finsetSum _ fun j _ => h2 j)
    have hcs : HasCompactSupport (fun p : Vec3 × ℝ =>
        -timePartial ψ p - ∑ j : Fin 3, spatialSecondPartial ψ j j p) := by
      refine hψc.mono' fun p hp => ?_
      by_contra hpt
      apply hp
      simp only [CKN.timePartial_eq_zero_off_tsupport hpt,
        fun j => CKN.spatialSecondPartial_eq_zero_off_tsupport hpt j j,
        Finset.sum_const_zero, neg_zero, sub_zero]
    exact hz.integrable_mul (hL2 hc hcs)
  have hT2 : Integrable T2 (volume.restrict (U ×ˢ I)) := by
    refine hz.integrable_mul (hL2 ?_ hφc.mul_left)
    exact (hηt.continuous.sub (continuous_finsetSum _ fun j _ => (hηjj j).continuous)).mul
      hφ.continuous
  have hT3 (j : Fin 3) : Integrable (T3 j) (volume.restrict (U ×ˢ I)) :=
    hz.integrable_mul (hL2 (vorticityHeatSmooth_spatialPartial_contDiff (hψj j) j).continuous
      (CKN.hasCompactSupport_spatialPartial (hψjc j) j))
  have hGψ : Integrable (fun p => G p * ψ p) (volume.restrict (U ×ˢ I)) :=
    hG.integrable_mul (hL2 hψ.continuous hψc)
  have hDzψ (j : Fin 3) : Integrable (fun p => Dz j p * ψj j p) (volume.restrict (U ×ˢ I)) :=
    (hDz j).integrable_mul (hL2 (hψj j).continuous (hψjc j))
  -- the left side
  have hLHS : ∫ p in (univ : Set Vec3) ×ˢ I, η p * z p *
      (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
      (∫ p in U ×ˢ I, G p * ψ p) + (∫ p in U ×ˢ I, T2 p) -
        2 * ∑ j : Fin 3, ∫ p in U ×ˢ I, Dz j p * ψj j p := by
    rw [setIntegral_univ_prod_eq (U := U) hIm fun p hp => by simp [hη0 p (hnotU p hp)]]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    have h12 : Integrable (fun p => T1 p + T2 p) (volume.restrict (U ×ˢ I)) := hT1.add hT2
    have h33 : Integrable (fun p => 2 * ∑ j : Fin 3, T3 j p) (volume.restrict (U ×ˢ I)) :=
      (integrable_finsetSum _ fun j _ => hT3 j).const_mul 2
    rw [integral_add h12 h33, integral_add hT1 hT2, integral_const_mul,
      integral_finsetSum _ fun j _ => hT3 j]
    have h1 : ∫ p in U ×ˢ I, T1 p = ∫ p in U ×ˢ I, G p * ψ p := hheat ψ hψ hψc hψV
    have h3 (j : Fin 3) : ∫ p in U ×ˢ I, T3 j p = -∫ p in U ×ˢ I, Dz j p * ψj j p :=
      hweak j (ψj j) (hψj j) (hψjc j) (hψjV j)
    rw [h1, Finset.sum_congr rfl fun j _ => h3 j, Finset.sum_neg_distrib]
    ring
  -- the right side
  have hRHS : ∫ p in (univ : Set Vec3) ×ˢ I,
      (η p * G p + (timePartial η p - ∑ j : Fin 3, spatialSecondPartial η j j p) * z p -
        2 * ∑ j : Fin 3, spatialPartial η j p * Dz j p) * φ p =
      (∫ p in U ×ˢ I, G p * ψ p) + (∫ p in U ×ˢ I, T2 p) -
        2 * ∑ j : Fin 3, ∫ p in U ×ˢ I, Dz j p * ψj j p := by
    rw [setIntegral_univ_prod_eq (U := U) hIm fun p hp => by
      have hp' := hnotU p hp
      simp [hη0 p hp', hηt0 p hp', hηjj0 _ p hp', hηj0 _ p hp']]
    have hpt' (p : Vec3 × ℝ) :
        (η p * G p + (timePartial η p - ∑ j : Fin 3, spatialSecondPartial η j j p) * z p -
          2 * ∑ j : Fin 3, spatialPartial η j p * Dz j p) * φ p =
        G p * ψ p + T2 p - 2 * ∑ j : Fin 3, Dz j p * ψj j p := by
      simp only [T2, ψ, ψj, ηj, Finset.mul_sum]
      simp only [Fin.sum_univ_three]
      ring
    rw [integral_congr_ae (ae_of_all _ hpt')]
    have h12 : Integrable (fun p => G p * ψ p + T2 p) (volume.restrict (U ×ˢ I)) :=
      hGψ.add hT2
    have h33 : Integrable (fun p => 2 * ∑ j : Fin 3, Dz j p * ψj j p)
        (volume.restrict (U ×ˢ I)) :=
      (integrable_finsetSum _ fun j _ => hDzψ j).const_mul 2
    rw [integral_sub h12 h33, integral_add hGψ hT2, integral_const_mul,
      integral_finsetSum _ fun j _ => hDzψ j]
  rw [hLHS, hRHS]

/-- Sums of space-time derivative families. -/
theorem IsSpaceTimeFamily.add {n : ℕ} {V : Set (Vec3 × ℝ)} {B₁ B₂ : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h₁ : IsSpaceTimeFamily n V B₁) (h₂ : IsSpaceTimeFamily n V B₂) :
    IsSpaceTimeFamily n V (fun α p => B₁ α p + B₂ α p) := by
  refine ⟨fun α hα => (h₁.memL2 α hα).add (h₂.memL2 α hα), fun α j hα => ?_⟩
  have hα' : (α ++ [j]).length ≤ n := by
    simp only [List.length_append, List.length_singleton]; omega
  exact (h₁.weak α j hα).add (h₂.weak α j hα) (h₁.memL2 α hα.le) (h₂.memL2 α hα.le)
    (h₁.memL2 _ hα') (h₂.memL2 _ hα')

/-- Constant multiples of space-time derivative families. -/
theorem IsSpaceTimeFamily.const_mul {n : ℕ} {V : Set (Vec3 × ℝ)}
    {B : List (Fin 3) → Vec3 × ℝ → ℝ} (h : IsSpaceTimeFamily n V B) (c : ℝ) :
    IsSpaceTimeFamily n V (fun α p => c * B α p) := by
  refine ⟨fun α hα => (h.memL2 α hα).const_mul c, fun α j hα φ hφ hφc hφV => ?_⟩
  have e1 : (fun p => c * B α p * spatialPartial φ j p) =
      fun p => c * (B α p * spatialPartial φ j p) := by
    funext p
    ring
  have e2 : (fun p => c * B (α ++ [j]) p * φ p) = fun p => c * (B (α ++ [j]) p * φ p) := by
    funext p
    ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h.weak α j hα φ hφ hφc hφV]
  ring

/-- Almost everywhere modifications of space-time derivative families. -/
theorem IsSpaceTimeFamily.congr_ae {n : ℕ} {V : Set (Vec3 × ℝ)}
    {B B' : List (Fin 3) → Vec3 × ℝ → ℝ} (h : IsSpaceTimeFamily n V B)
    (hBB' : ∀ α : List (Fin 3), α.length ≤ n → B α =ᵐ[volume.restrict V] B' α) :
    IsSpaceTimeFamily n V B' := by
  refine ⟨fun α hα => (h.memL2 α hα).ae_eq (hBB' α hα), fun α j hα φ hφ hφc hφV => ?_⟩
  have hα' : (α ++ [j]).length ≤ n := by
    simp only [List.length_append, List.length_singleton]; omega
  have h1 : ∫ p in V, B' α p * spatialPartial φ j p = ∫ p in V, B α p * spatialPartial φ j p :=
    integral_congr_ae (by
      filter_upwards [hBB' α hα.le] with p hp
      rw [hp])
  have h2 : ∫ p in V, B' (α ++ [j]) p * φ p = ∫ p in V, B (α ++ [j]) p * φ p :=
    integral_congr_ae (by
      filter_upwards [hBB' _ hα'] with p hp
      rw [hp])
  rw [h1, h2]
  exact h.weak α j hα φ hφ hφc hφV

/-- A space-time derivative family on `U × I` whose members vanish for `x`
outside a compact `K ⊆ U` is a family on `ℝ³ × I`. The cutoff `κ` equals one
near `K`. -/
theorem IsSpaceTimeFamily.extend_univ {n : ℕ} {U K N : Set Vec3} {I : Set ℝ}
    (hIm : MeasurableSet I) (hUm : MeasurableSet U) (hKU : K ⊆ U)
    (hN : IsOpen N) (hKN : K ⊆ N) {κ : Vec3 → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) (hκU : tsupport κ ⊆ U) (hκN : ∀ x ∈ N, κ x = 1)
    {F : List (Fin 3) → Vec3 × ℝ → ℝ} (hF : IsSpaceTimeFamily n (U ×ˢ I) F)
    (hFK : ∀ α : List (Fin 3), α.length ≤ n → ∀ p : Vec3 × ℝ, p.1 ∉ K → F α p = 0) :
    IsSpaceTimeFamily n ((univ : Set Vec3) ×ˢ I) F := by
  have hsub : U ×ˢ I ⊆ (univ : Set Vec3) ×ˢ I := prod_mono (subset_univ U) subset_rfl
  have hUIm : MeasurableSet (U ×ˢ I) := hUm.prod hIm
  have hFU (α : List (Fin 3)) (hα : α.length ≤ n) (p : Vec3 × ℝ) (hp : p.1 ∉ U) :
      F α p = 0 := hFK α hα p fun h => hp (hKU h)
  refine ⟨fun α hα => ?_, fun α j hα φ hφ hφc hφV => ?_⟩
  · have hind : F α =ᵐ[volume.restrict ((univ : Set Vec3) ×ˢ I)] (U ×ˢ I).indicator (F α) := by
      refine (ae_restrict_iff' (MeasurableSet.univ.prod hIm)).2 (ae_of_all _ fun p hp => ?_)
      by_cases hpUI : p ∈ U ×ˢ I
      · rw [Set.indicator_of_mem hpUI]
      · rw [Set.indicator_of_notMem hpUI]
        exact hFU α hα p fun hpU => hpUI ⟨hpU, hp.2⟩
    refine MemLp.ae_eq hind.symm ?_
    rw [memLp_indicator_iff_restrict hUIm, Measure.restrict_restrict hUIm,
      Set.inter_eq_left.2 hsub]
    exact hF.memL2 α hα
  · have hα' : (α ++ [j]).length ≤ n := by
      simp only [List.length_append, List.length_singleton]; omega
    let φ' : Vec3 × ℝ → ℝ := fun p => κ p.1 * φ p
    have hκ' : ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => κ p.1) := hκ.comp contDiff_fst
    have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ' := hκ'.mul hφ
    have hφ'c : HasCompactSupport φ' := hφc.mul_left
    have hφ'V : tsupport φ' ⊆ U ×ˢ I :=
      tsupport_mul_subset_of_compl hκc.isCompact hκU
        (fun p hp => image_eq_zero_of_notMem_tsupport hp) hφV
    have hdφ (p : Vec3 × ℝ) (hp : p.1 ∈ N) : spatialPartial φ' j p = spatialPartial φ j p := by
      have hev : (fun x : Vec3 => κ x * φ (x, p.2)) =ᶠ[𝓝 p.1] fun x => φ (x, p.2) := by
        filter_upwards [hN.mem_nhds hp] with x hx
        rw [hκN x hx, one_mul]
      change (fderiv ℝ (fun x : Vec3 => κ x * φ (x, p.2)) p.1) (basisVec j) =
        (fderiv ℝ (fun x : Vec3 => φ (x, p.2)) p.1) (basisVec j)
      rw [hev.fderiv_eq]
    have hkey := hF.weak α j hα φ' hφ' hφ'c hφ'V
    have hL : ∫ p in (univ : Set Vec3) ×ˢ I, F α p * spatialPartial φ j p =
        ∫ p in U ×ˢ I, F α p * spatialPartial φ' j p := by
      rw [setIntegral_univ_prod_eq (U := U) hIm fun p hp => by rw [hFU α hα.le p hp, zero_mul]]
      refine setIntegral_congr_fun hUIm fun p _ => ?_
      by_cases hpK : p.1 ∈ K
      · rw [hdφ p (hKN hpK)]
      · rw [hFK α hα.le p hpK, zero_mul, zero_mul]
    have hR : ∫ p in (univ : Set Vec3) ×ˢ I, F (α ++ [j]) p * φ p =
        ∫ p in U ×ˢ I, F (α ++ [j]) p * φ' p := by
      rw [setIntegral_univ_prod_eq (U := U) hIm fun p hp => by rw [hFU _ hα' p hp, zero_mul]]
      refine setIntegral_congr_fun hUIm fun p _ => ?_
      by_cases hpK : p.1 ∈ K
      · simp only [φ', hκN p.1 (hKN hpK), one_mul]
      · rw [hFK _ hα' p hpK, zero_mul, zero_mul]
    rw [hL, hR]
    exact hkey

end ESS
