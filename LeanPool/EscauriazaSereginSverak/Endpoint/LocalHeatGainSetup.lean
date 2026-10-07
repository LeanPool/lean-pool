/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainShape
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Auxiliary facts for the cutoff argument of `lem:local-heat-gain`

Leibniz families vanish where the multiplier and its spatial derivatives
vanish, reduce to the second family where the multiplier is one near the
point, and are strongly measurable. Space-time derivative families restrict
to smaller orders, shifted words and smaller sets, and the distributional heat
equation is insensitive to almost everywhere modification.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

theorem stLeibniz_eq_zero_of_forall (α : List (Fin 3)) {A B : List (Fin 3) → Vec3 × ℝ → ℝ}
    {p : Vec3 × ℝ} (hA : ∀ γ, A γ p = 0) : stLeibniz α A B p = 0 := by
  induction α generalizing A B with
  | nil => simp [stLeibniz, hA []]
  | cons j α ih =>
      simp only [stLeibniz]
      rw [ih (A := fun γ => A (j :: γ)) (fun γ => hA (j :: γ)), ih hA, add_zero]

theorem stLeibniz_eq_of_unit (α : List (Fin 3)) {A B : List (Fin 3) → Vec3 × ℝ → ℝ}
    {p : Vec3 × ℝ} (h1 : A [] p = 1) (h0 : ∀ γ, γ ≠ [] → A γ p = 0) :
    stLeibniz α A B p = B α p := by
  induction α generalizing B with
  | nil => simp [stLeibniz, h1]
  | cons j α ih =>
      simp only [stLeibniz]
      rw [stLeibniz_eq_zero_of_forall α (A := fun γ => A (j :: γ))
        (fun γ => h0 (j :: γ) (List.cons_ne_nil _ _)), zero_add, ih]

theorem stLeibniz_stronglyMeasurable (α : List (Fin 3)) {A B : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hA : ∀ γ, StronglyMeasurable (A γ)) (hB : ∀ γ, StronglyMeasurable (B γ)) :
    StronglyMeasurable (stLeibniz α A B) := by
  induction α generalizing A B with
  | nil => exact (hA []).mul (hB [])
  | cons j α ih =>
      exact (ih (fun γ => hA (j :: γ)) hB).add (ih hA fun γ => hB (j :: γ))

theorem IsSpaceTimeFamily.mono_order {n n' : ℕ} {V : Set (Vec3 × ℝ)}
    {B : List (Fin 3) → Vec3 × ℝ → ℝ} (h : IsSpaceTimeFamily n V B) (hn : n' ≤ n) :
    IsSpaceTimeFamily n' V B :=
  ⟨fun α hα => h.memL2 α (hα.trans hn), fun α j hα => h.weak α j (lt_of_lt_of_le hα hn)⟩

theorem IsSpaceTimeFamily.shift {n : ℕ} {V : Set (Vec3 × ℝ)}
    {B : List (Fin 3) → Vec3 × ℝ → ℝ} (h : IsSpaceTimeFamily n V B) (hn : 1 ≤ n) (j : Fin 3) :
    IsSpaceTimeFamily (n - 1) V (fun γ => B (j :: γ)) :=
  ⟨fun γ hγ => h.memL2 (j :: γ) (by simp only [List.length_cons]; omega),
    fun γ l hγ => h.weak (j :: γ) l (by simp only [List.length_cons]; omega)⟩

/-- Distributional spatial derivatives restrict to smaller measurable sets. -/
theorem IsSpaceTimeWeakPartial.mono {V W : Set (Vec3 × ℝ)} {j : Fin 3} {f g : Vec3 × ℝ → ℝ}
    (h : IsSpaceTimeWeakPartial V j f g) (hV : MeasurableSet V)
    (hWV : W ⊆ V) : IsSpaceTimeWeakPartial W j f g := by
  intro φ hφ hφc hφW
  have hkey := h φ hφ hφc (hφW.trans hWV)
  have hdφ0 : ∀ p, p ∉ W → f p * spatialPartial φ j p = 0 := fun p hp => by
    rw [CKN.spatialPartial_eq_zero_off_tsupport (fun h => hp (hφW h)) j, mul_zero]
  have hφ0 : ∀ p, p ∉ W → g p * φ p = 0 := fun p hp => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hφW h)), mul_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hWV fun p hp => hdφ0 p hp.2,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hWV fun p hp => hφ0 p hp.2] at hkey
  exact hkey

/-- The distributional heat equation is insensitive to almost everywhere
modification. -/
theorem _root_.CKN.IsHeatSolutionOn.congr_ae {U : Set Vec3} {I : Set ℝ} {z z' G G' : Vec3 × ℝ → ℝ}
    (h : IsHeatSolutionOn U I z G) (hz : z =ᵐ[volume.restrict (U ×ˢ I)] z')
    (hG : G =ᵐ[volume.restrict (U ×ˢ I)] G') : IsHeatSolutionOn U I z' G' := by
  intro φ hφ hφc hφV
  have h1 := h φ hφ hφc hφV
  have e1 : ∫ y in U ×ˢ I, z y * (-timePartial φ y - ∑ j : Fin 3, spatialSecondPartial φ j j y) =
      ∫ y in U ×ˢ I, z' y * (-timePartial φ y - ∑ j : Fin 3, spatialSecondPartial φ j j y) :=
    integral_congr_ae (hz.mono fun p hp => by simp only [hp])
  have e2 : ∫ y in U ×ˢ I, G y * φ y = ∫ y in U ×ˢ I, G' y * φ y :=
    integral_congr_ae (hG.mono fun p hp => by simp only [hp])
  rw [e1, e2] at h1
  exact h1

/-- The time derivative of a separated field. -/
theorem timePartial_separated {c : ℝ → ℝ} (hc : Differentiable ℝ c) (g : Vec3 → ℝ)
    (x₀ : Vec3) (p : Vec3 × ℝ) :
    timePartial (fun q : Vec3 × ℝ => c q.2 * g (q.1 - x₀)) p =
      deriv c p.2 * g (p.1 - x₀) := by
  change (fderiv ℝ (fun s : ℝ => c s * g (p.1 - x₀)) p.2) 1 = _
  rw [fderiv_mul_const (hc p.2)]
  simp [mul_comm]

end ESS
