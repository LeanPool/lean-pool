/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityBase
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityCurlAlgebra

/-!
# Weak divergence and curl identities along the bootstrap

Restriction of weak identities to smaller sets, and the propagation of the weak divergence-free
condition and of the weak antisymmetric-derivative identity to weak derivatives. These supply the
inputs of the div–curl recovery at each level of `thm:vorticity-regularity`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A weak identity between integrands supported where the test is supported restricts to every
smaller set. -/
theorem vorticity_restrict_identity {W W' : Set (Vec3 × ℝ)} (hW' : W' ⊆ W)
    {Φ Ψ : (Vec3 × ℝ → ℝ) → Vec3 × ℝ → ℝ}
    (hΦ : ∀ ψ : Vec3 × ℝ → ℝ, ∀ z, z ∉ tsupport ψ → Φ ψ z = 0)
    (hΨ : ∀ ψ : Vec3 × ℝ → ℝ, ∀ z, z ∉ tsupport ψ → Ψ ψ z = 0)
    (h : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ z in W, Φ ψ z = ∫ z in W, Ψ ψ z) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W' → ∫ z in W', Φ ψ z = ∫ z in W', Ψ ψ z := by
  intro ψ hψ hψc hψW'
  have hΦ' : ∀ z, z ∉ W' → Φ ψ z = 0 := fun z hz => hΦ ψ z fun h' => hz (hψW' h')
  have hΨ' : ∀ z, z ∉ W' → Ψ ψ z = 0 := fun z hz => hΨ ψ z fun h' => hz (hψW' h')
  rw [vorticity_setIntegral_congr_of_vanish hW' hΦ', vorticity_setIntegral_congr_of_vanish hW' hΨ']
  exact h ψ hψ hψc (hψW'.trans hW')

/-- A spatial derivative of a test vanishes off its support. -/
theorem vorticity_spatialPartial_off {ψ : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ)
    (j : Fin 3) : spatialPartial ψ j z = 0 := by
  have hz' : z ∉ tsupport (fun z : Vec3 × ℝ => spatialPartial ψ j z) := fun h' =>
    hz (CKN.tsupport_spatialPartial_subset j h')
  exact image_eq_zero_of_notMem_tsupport hz'

/-- A weak derivative identity restricts to smaller sets. -/
theorem vorticity_weakPartial_restrict {W W' : Set (Vec3 × ℝ)} (hW' : W' ⊆ W)
    {f g : Vec3 × ℝ → ℝ} {j : Fin 3}
    (h : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * spatialPartial ψ j y = -∫ y in W, g y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W' → ∫ y in W', f y * spatialPartial ψ j y = -∫ y in W', g y * ψ y := by
  intro ψ hψ hψc hψW'
  have h' := vorticity_restrict_identity (Φ := fun ψ y => f y * spatialPartial ψ j y)
    (Ψ := fun ψ y => -(g y * ψ y)) hW'
    (fun ψ z hz => by simp [vorticity_spatialPartial_off hz])
    (fun ψ z hz => by simp [image_eq_zero_of_notMem_tsupport hz])
    (fun ψ hψ hψc hψW => by rw [integral_neg]; exact h ψ hψ hψc hψW) ψ hψ hψc hψW'
  rw [← integral_neg]
  exact h'

/-- A weak heat equation restricts to smaller sets. -/
theorem vorticityHeat_restrict {W W' : Set (Vec3 × ℝ)} (hW' : W' ⊆ W)
    {w : Vec3 × ℝ → ℝ} {F : Fin 3 → Vec3 × ℝ → ℝ}
    (h : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in W, ∑ j : Fin 3, F j y * spatialPartial ψ j y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W' →
      ∫ y in W', w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in W', ∑ j : Fin 3, F j y * spatialPartial ψ j y := by
  intro ψ hψ hψc hψW'
  have h' := vorticity_restrict_identity
    (Φ := fun ψ y => w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y))
    (Ψ := fun ψ y => -∑ j : Fin 3, F j y * spatialPartial ψ j y) hW'
    (fun ψ z hz => by
      have ht : timePartial ψ z = 0 := by
        by_contra hne
        exact hz (CKN.tsupport_timePartial_subset ψ (subset_tsupport _ hne))
      simp [ht, CKN.spatialSecondPartial_eq_zero_off_tsupport hz])
    (fun ψ z hz => by simp [vorticity_spatialPartial_off hz])
    (fun ψ hψ hψc hψW => by rw [integral_neg]; exact h ψ hψ hψc hψW) ψ hψ hψc hψW'
  rw [← integral_neg]
  exact h'

/-- A weak divergence-free condition restricts to smaller sets. -/
theorem vorticityDiv_restrict {W W' : Set (Vec3 × ℝ)} (hW' : W' ⊆ W)
    {Y : Fin 3 → Vec3 × ℝ → ℝ}
    (h : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, Y i y * spatialPartial ψ i y = 0) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W' → ∫ y in W', ∑ i : Fin 3, Y i y * spatialPartial ψ i y = 0 := by
  intro ψ hψ hψc hψW'
  have h' := vorticity_restrict_identity
    (Φ := fun ψ y => ∑ i : Fin 3, Y i y * spatialPartial ψ i y) (Ψ := fun _ _ => 0) hW'
    (fun ψ z hz => by simp [vorticity_spatialPartial_off hz])
    (fun _ _ _ => rfl)
    (fun ψ hψ hψc hψW => by rw [integral_zero]; exact h ψ hψ hψc hψW) ψ hψ hψc hψW'
  rw [h', integral_zero]

/-- The velocity satisfies the weak antisymmetric-derivative identity with the vorticity of its
weak gradient. -/
theorem vorticityAnti_base {W : Set (Vec3 × ℝ)} {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} (hG : ∀ i j, IntegrableOn (G i j) W)
    (hU : ∀ i, IntegrableOn (U i) W)
    (hdU : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, U i y * spatialPartial ψ j y = -∫ y in W, G i j y * ψ y) :
    ∀ i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, (U k y * spatialPartial ψ i y - U i y * spatialPartial ψ k y) =
        -∫ y in W, vorticityAntisym (fun l => vorticityCurl G l y) i k * ψ y := by
  intro i k ψ hψ hψc hψW
  have h1 := hdU k i ψ hψ hψc hψW
  have h2 := hdU i k ψ hψ hψc hψW
  have hi1 : IntegrableOn (fun y => U k y * spatialPartial ψ i y) W :=
    vorticity_integrableOn_mul_smooth (hU k) (CKN.spatialPartial_contDiff hψ i).continuous
      (CKN.hasCompactSupport_spatialPartial hψc i)
  have hi2 : IntegrableOn (fun y => U i y * spatialPartial ψ k y) W :=
    vorticity_integrableOn_mul_smooth (hU i) (CKN.spatialPartial_contDiff hψ k).continuous
      (CKN.hasCompactSupport_spatialPartial hψc k)
  have hi3 : IntegrableOn (fun y => G k i y * ψ y) W :=
    vorticity_integrableOn_mul_smooth (hG k i) hψ.continuous hψc
  have hi4 : IntegrableOn (fun y => G i k y * ψ y) W :=
    vorticity_integrableOn_mul_smooth (hG i k) hψ.continuous hψc
  have hr : ∫ y in W, vorticityAntisym (fun l => vorticityCurl G l y) i k * ψ y =
      (∫ y in W, G k i y * ψ y) - ∫ y in W, G i k y * ψ y := by
    rw [← integral_sub hi3 hi4]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      simp only [vorticityAntisym_curl G y i k]
      ring)
  rw [integral_sub hi1 hi2, hr, h1, h2]
  ring

/-- Moving a weak derivative onto a derivative of the test: `∫ Y' ∂ₐψ = -∫ Y ∂ₐ(∂ₘψ)`. -/
theorem vorticity_weakPartial_testDeriv {W : Set (Vec3 × ℝ)} {Y Y' : Vec3 × ℝ → ℝ} {m : Fin 3}
    (hdY : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, Y y * spatialPartial ψ m y = -∫ y in W, Y' y * ψ y)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψW : tsupport ψ ⊆ W) (a : Fin 3) :
    ∫ y in W, Y' y * spatialPartial ψ a y =
      -∫ y in W, Y y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) a y := by
  have h := hdY (fun y : Vec3 × ℝ => spatialPartial ψ a y) (CKN.spatialPartial_contDiff hψ a)
    (CKN.hasCompactSupport_spatialPartial hψc a)
    ((CKN.tsupport_spatialPartial_subset a).trans hψW)
  have hcomm : ∀ y : Vec3 × ℝ, spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ a y) m y =
      spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) a y := fun y =>
    spatialSecondPartial_comm hψ y a m
  have h' : ∫ y in W, Y y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) a y =
      -∫ y in W, Y' y * spatialPartial ψ a y := by
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun y =>
      congrArg (fun t => Y y * t) (hcomm y).symm)
  linarith only [h']

/-- Weak derivatives of a weakly divergence-free field are weakly divergence free. -/
theorem vorticityDiv_deriv {W : Set (Vec3 × ℝ)} {Y Y' : Fin 3 → Vec3 × ℝ → ℝ} {m : Fin 3}
    (hY : ∀ i, IntegrableOn (Y i) W) (hY' : ∀ i, IntegrableOn (Y' i) W)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, Y i y * spatialPartial ψ i y = 0)
    (hdY : ∀ i, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, Y i y * spatialPartial ψ m y = -∫ y in W, Y' i y * ψ y) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, Y' i y * spatialPartial ψ i y = 0 := by
  intro ψ hψ hψc hψW
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => spatialPartial ψ m y) :=
    CKN.spatialPartial_contDiff hψ m
  have hχc : HasCompactSupport (fun y : Vec3 × ℝ => spatialPartial ψ m y) :=
    CKN.hasCompactSupport_spatialPartial hψc m
  have hχW : tsupport (fun y : Vec3 × ℝ => spatialPartial ψ m y) ⊆ W :=
    (CKN.tsupport_spatialPartial_subset m).trans hψW
  have h0 := hdiv _ hχ hχc hχW
  rw [integral_finsetSum _ fun i _ => vorticity_integrableOn_mul_smooth (hY' i)
    (CKN.spatialPartial_contDiff hψ i).continuous (CKN.hasCompactSupport_spatialPartial hψc i)]
  rw [integral_finsetSum _ fun i _ => vorticity_integrableOn_mul_smooth (hY i)
    (CKN.spatialPartial_contDiff hχ i).continuous (CKN.hasCompactSupport_spatialPartial hχc i)]
    at h0
  have hterm : ∀ i : Fin 3, ∫ y in W, Y' i y * spatialPartial ψ i y =
      -∫ y in W, Y i y * spatialPartial (fun y : Vec3 × ℝ => spatialPartial ψ m y) i y :=
    fun i => vorticity_weakPartial_testDeriv (hdY i) hψ hψc hψW i
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_neg_distrib, h0, neg_zero]

/-- Weak derivatives of a field satisfying the weak antisymmetric-derivative identity satisfy it
with the derivative of the antisymmetric data. -/
theorem vorticityAnti_deriv {W : Set (Vec3 × ℝ)} {Y Y' v v' : Fin 3 → Vec3 × ℝ → ℝ}
    {m : Fin 3} (hY : ∀ i, IntegrableOn (Y i) W) (hv : ∀ l, IntegrableOn (v l) W)
    (hv' : ∀ l, IntegrableOn (v' l) W)
    (hanti : ∀ i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, (Y k y * spatialPartial ψ i y - Y i y * spatialPartial ψ k y) =
        -∫ y in W, vorticityAntisym (fun l => v l y) i k * ψ y)
    (hdY : ∀ i, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, Y i y * spatialPartial ψ m y = -∫ y in W, Y' i y * ψ y)
    (hdv : ∀ l, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, v l y * spatialPartial ψ m y = -∫ y in W, v' l y * ψ y)
    (hY' : ∀ i, IntegrableOn (Y' i) W) :
    ∀ i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, (Y' k y * spatialPartial ψ i y - Y' i y * spatialPartial ψ k y) =
        -∫ y in W, vorticityAntisym (fun l => v' l y) i k * ψ y := by
  intro i k ψ hψ hψc hψW
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => spatialPartial ψ m y) :=
    CKN.spatialPartial_contDiff hψ m
  have hχc : HasCompactSupport (fun y : Vec3 × ℝ => spatialPartial ψ m y) :=
    CKN.hasCompactSupport_spatialPartial hψc m
  have hχW : tsupport (fun y : Vec3 × ℝ => spatialPartial ψ m y) ⊆ W :=
    (CKN.tsupport_spatialPartial_subset m).trans hψW
  have hmul : ∀ (f : Vec3 × ℝ → ℝ), IntegrableOn f W → ∀ (φ : Vec3 × ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → IntegrableOn (fun y => f y * φ y) W :=
    fun f hf φ hφ hφc => vorticity_integrableOn_mul_smooth hf hφ.continuous hφc
  have e1 := vorticity_weakPartial_testDeriv (hdY k) hψ hψc hψW i
  have e2 := vorticity_weakPartial_testDeriv (hdY i) hψ hψc hψW k
  have ea := hanti i k _ hχ hχc hχW
  rw [integral_sub (hmul _ (hY k) _ (CKN.spatialPartial_contDiff hχ i)
      (CKN.hasCompactSupport_spatialPartial hχc i))
    (hmul _ (hY i) _ (CKN.spatialPartial_contDiff hχ k)
      (CKN.hasCompactSupport_spatialPartial hχc k))] at ea
  rw [integral_sub (hmul _ (hY' k) _ (CKN.spatialPartial_contDiff hψ i)
      (CKN.hasCompactSupport_spatialPartial hψc i))
    (hmul _ (hY' i) _ (CKN.spatialPartial_contDiff hψ k)
      (CKN.hasCompactSupport_spatialPartial hψc k)), e1, e2]
  -- expand the antisymmetric matrices linearly
  have hexp : ∀ (u : Fin 3 → Vec3 × ℝ → ℝ) (φ : Vec3 × ℝ → ℝ), (∀ l, IntegrableOn (u l) W) →
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ y in W, vorticityAntisym (fun l => u l y) i k * φ y =
        ∑ l : Fin 3, vorticityEps i k l * ∫ y in W, u l y * φ y := by
    intro u φ hu hφ hφc
    have hpt : ∀ y, vorticityAntisym (fun l => u l y) i k * φ y =
        ∑ l : Fin 3, vorticityEps i k l * (u l y * φ y) := by
      intro y
      rw [vorticityAntisym_eq_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finsetSum _ fun l _ => (hmul _ (hu l) φ hφ hφc).const_mul _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  rw [hexp v _ hv hχ hχc] at ea
  rw [hexp v' ψ hv' hψ hψc]
  have hl : ∀ l : Fin 3, ∫ y in W, v l y * spatialPartial ψ m y = -∫ y in W, v' l y * ψ y :=
    fun l => hdv l ψ hψ hψc hψW
  simp only [hl] at ea
  have hsum : ∑ l : Fin 3, vorticityEps i k l * -∫ y in W, v' l y * ψ y =
      -∑ l : Fin 3, vorticityEps i k l * ∫ y in W, v' l y * ψ y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hsum] at ea
  linarith only [ea]

end ESS
