/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessEnergyLower
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeakLocal
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientWeakLocal

/-!
# Compactness Limit Bounds

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The all-time local slice energy bound passes to the selected limit. -/
theorem compactness_limit_slice_bound
    {U : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (huMeas : ∀ n, Measurable (u n))
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧
      K j ⊆ K (j + 1) ∧ K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hχ : ∀ j x, x ∈ K j → χ j x = 1)
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ J →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ j t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
      (nhds (inner ℝ (V j t) x)))
    (C : Set Vec3) (hC : IsCompact C) (hCU : C ⊆ U)
    (T : Set ℝ) (hTI : T ⊆ I)
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hMb : ∀ n t, t ∈ T →
      (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
        (2 : ℝ) ∂volume) ≤ M) :
    ∀ t ∈ T, (∫⁻ x in C,
      ENNReal.ofReal (vec3EuclideanNorm
        (compactnessMollifiedLimit u σ (x,t))) ^ (2 : ℝ) ∂volume) ≤ M := by
  intro t ht
  let f (k : ℕ) (x : Vec3) : L2Vec3 := WithLp.toLp 2 (u (σ k) (x,t))
  let v (x : Vec3) : L2Vec3 :=
    WithLp.toLp 2 (compactnessMollifiedLimit u σ (x,t))
  obtain ⟨hs, hl, hw⟩ :=
    weak_slices_to_compactnessMollifiedLimit_on_compact hI
      u σ huMeas K χ hK hKcover hχ hbound hmem V hweak
      C hC hCU ⟨t, hTI ht⟩
  have hsource (k : ℕ) :
      (∫⁻ x, ‖f k x‖ₑ ^ (2 : ℝ) ∂(volume.restrict C)) ≤ M := by
    simpa only [f, ← ofReal_norm, ← vec3EuclideanNorm_eq_l2] using
      hMb (σ k) t ht
  have hlimit := lintegral_enorm_sq_le_of_weak_l2_bounded
    f (hl.toLp v) hs hw M hM hsource
  have heq : (fun x => hl.toLp v x) =ᵐ[volume.restrict C] v :=
    hl.coeFn_toLp
  calc
    (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm
        (compactnessMollifiedLimit u σ (x,t))) ^ (2 : ℝ) ∂volume) =
      ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂(volume.restrict C) := by
        apply lintegral_congr
        intro x
        simp only [v, ← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
    _ = ∫⁻ x, ‖hl.toLp v x‖ₑ ^ (2 : ℝ) ∂(volume.restrict C) := by
        exact (lintegral_congr_ae (heq.mono fun x hx => by
          exact congrArg (fun y : L2Vec3 => ‖y‖ₑ ^ (2 : ℝ)) hx)).symm
    _ ≤ M := hlimit

/-- The local matrix energy bound passes to the measurable weak limit. -/
theorem compactness_limit_gradient_bound
    {U : Set Vec3} {I : Set ℝ}
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (hDuMeas : ∀ n, Measurable (Du n))
    (σ : ℕ → ℕ)
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧
      K j ⊆ K (j + 1) ∧ K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hJ : ∀ j, IsCompact (J j) ∧ J j ⊆ I ∧
      J j ⊆ J (j + 1) ∧ J j ⊆ interior (J (j + 1)))
    (hJcover : ⋃ j, J j = I)
    (D : ∀ j, Lp CompactnessGradientFiber 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))))
    (hDweak : ∀ j,
      ∃ hgrad : ∀ k, MemLp
        (fun z : Vec3 × ℝ => toCompactnessGradientFiber (Du (σ k) z)) 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))),
        ∀ w, Tendsto
          (fun k => inner ℝ ((hgrad k).toLp
            (fun z => toCompactnessGradientFiber (Du (σ k) z))) w) atTop
          (nhds (inner ℝ (D j) w)))
    (g : Vec3 × ℝ → CompactnessGradientFiber) (hg : Measurable g)
    (hgEq : ∀ j, g =ᵐ[
      (volume.restrict (interior (K j))).prod (volume.restrict (J j))]
      compactnessGradientLocalRepresentative K J D j)
    (C : Set Vec3) (hC : IsCompact C) (hCU : C ⊆ U)
    (T : Set ℝ) (hT : IsCompact T) (hTI : T ⊆ I)
    (G : ℝ≥0∞) (hG : G < ⊤)
    (hGb : ∀ n,
      (∫⁻ t in T, ∫⁻ x in C,
        ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
          ∂volume) ≤ G) :
    (∫⁻ t in T, ∫⁻ x in C,
      ENNReal.ofReal (CKN.spatialGradientSq
        (fun _ => (0 : Vec3))
        (fun z i m => g z i m) (x,t)) ∂volume) ≤ G := by
  let Q : Set (Vec3 × ℝ) := C ×ˢ T
  have hQ : IsCompact Q := hC.prod hT
  have hQI : Q ⊆ U ×ˢ I := by
    intro z hz
    exact ⟨hCU hz.1, hTI hz.2⟩
  obtain ⟨hs, hl, hw⟩ := weak_gradient_to_measurable_limit_on_compact
    Du σ K J hK hKcover hJ hJcover D hDweak g hgEq Q hQ hQI
  let f (k : ℕ) (z : Vec3 × ℝ) : CompactnessGradientFiber :=
    toCompactnessGradientFiber (Du (σ k) z)
  let F : Vec3 × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (CKN.spatialGradientSq
      (fun _ => (0 : Vec3)) (fun z i m => g z i m) z)
  have hF : Measurable F := by
    unfold F CKN.spatialGradientSq
    fun_prop
  have hsource (k : ℕ) :
      (∫⁻ z, ‖f k z‖ₑ ^ (2 : ℝ) ∂(volume.restrict Q)) ≤ G := by
    have henergy : (∫⁻ z in Q,
        ENNReal.ofReal (CKN.spatialGradientSq (u (σ k))
          (Du (σ k)) z) ∂volume) ≤ G := by
      change (∫⁻ z in C ×ˢ T,
        ENNReal.ofReal (CKN.spatialGradientSq (u (σ k))
          (Du (σ k)) z) ∂(volume : Measure ParabolicPoint)) ≤ G
      rw [lintegral_parabolic_rectangle_eq_iterated]
      · exact hGb (σ k)
      · unfold CKN.spatialGradientSq
        have hm := hDuMeas (σ k)
        fun_prop
    calc
      (∫⁻ z, ‖f k z‖ₑ ^ (2 : ℝ) ∂(volume.restrict Q)) =
          ∫⁻ z in Q, ENNReal.ofReal (CKN.spatialGradientSq
            (u (σ k)) (Du (σ k)) z) ∂volume := by
            apply lintegral_congr
            intro z
            calc
              ‖f k z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖f k z‖ ^ 2) := by
                norm_num [← ofReal_norm, ENNReal.rpow_natCast,
                  ENNReal.ofReal_pow (norm_nonneg (f k z))]
              _ = _ := by
                exact congrArg ENNReal.ofReal
                  (norm_toCompactnessGradientFiber_sq
                    (u (σ k)) (Du (σ k)) z)
      _ ≤ G := henergy
  have hlimit := lintegral_enorm_sq_le_of_weak_l2_bounded
    f (hl.toLp g) hs hw G hG hsource
  have heq : (fun z => hl.toLp g z) =ᵐ[volume.restrict Q] g :=
    hl.coeFn_toLp
  have hnorm (z : Vec3 × ℝ) :
      ‖g z‖ ^ 2 = CKN.spatialGradientSq
        (fun _ => (0 : Vec3)) (fun z i m => g z i m) z := by
    rw [PiLp.norm_sq_eq_of_L2]
    unfold CKN.spatialGradientSq
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro m _
    simp [Real.norm_eq_abs, sq_abs]
  have hpoint (z : Vec3 × ℝ) : ‖g z‖ₑ ^ (2 : ℝ) = F z := by
    calc
      ‖g z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖g z‖ ^ 2) := by
        norm_num [← ofReal_norm, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow (norm_nonneg (g z))]
      _ = F z := by rw [hnorm]
  have hboundQ : (∫⁻ z, F z ∂(volume.restrict Q)) ≤ G := by
    calc
      (∫⁻ z, F z ∂(volume.restrict Q)) =
          ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂(volume.restrict Q) := by
            exact lintegral_congr fun z => (hpoint z).symm
      _ = ∫⁻ z, ‖hl.toLp g z‖ₑ ^ (2 : ℝ)
          ∂(volume.restrict Q) := by
            exact (lintegral_congr_ae (heq.mono fun z hz =>
              congrArg (fun y : CompactnessGradientFiber =>
                ‖y‖ₑ ^ (2 : ℝ)) hz)).symm
      _ ≤ G := hlimit
  change (∫⁻ t in T, ∫⁻ x in C, F (x,t) ∂volume) ≤ G
  rw [← lintegral_parabolic_rectangle_eq_iterated F hF]
  exact hboundQ

end CKN.Leray
