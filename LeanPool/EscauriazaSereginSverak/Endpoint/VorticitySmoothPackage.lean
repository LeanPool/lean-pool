/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityHeatSup

/-!
# The weak and smooth relations among the bootstrap fields

The velocity, its first and second derivatives, the vorticity and its first and second
derivatives satisfy weak divergence and antisymmetric-derivative identities at each order; their
backward mollifications satisfy the corresponding identities pointwise wherever the kernel ball
lies in the box (the inputs of the div–curl steps of `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The weak divergence and antisymmetric-derivative identities of the first and second
derivatives of the velocity. -/
theorem vorticityWeakRelations {W : Set (Vec3 × ℝ)} (hWb : Bornology.IsBounded W)
    {U : Fin 3 → Vec3 × ℝ → ℝ} {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hU : ∀ i, MemLp (U i) 2 (volume.restrict W)) (hG : ∀ i j, MemLp (G i j) 2 (volume.restrict W))
    (hD2 : ∀ i j k, MemLp (D2 i j k) 2 (volume.restrict W))
    (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 (volume.restrict W))
    (hΩ2 : ∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict W))
    (hdU : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, U i y * spatialPartial ψ j y = -∫ y in W, G i j y * ψ y)
    (hdG : ∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, G i j y * spatialPartial ψ k y = -∫ y in W, D2 i j k y * ψ y)
    (hdw : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, vorticityCurl G i y * spatialPartial ψ j y = -∫ y in W, Ω1 i j y * ψ y)
    (hdΩ1 : ∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, Ω1 i j y * spatialPartial ψ k y = -∫ y in W, Ω2 i j k y * ψ y)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, U i y * spatialPartial ψ i y = 0) :
    (∀ i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, (U k y * spatialPartial ψ i y - U i y * spatialPartial ψ k y) =
        -∫ y in W, vorticityAntisym (fun l => vorticityCurl G l y) i k * ψ y) ∧
    (∀ m : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, G i m y * spatialPartial ψ i y = 0) ∧
    (∀ m i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, (G k m y * spatialPartial ψ i y - G i m y * spatialPartial ψ k y) =
        -∫ y in W, vorticityAntisym (fun l => Ω1 l m y) i k * ψ y) ∧
    (∀ j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, D2 i j k y * spatialPartial ψ i y = 0) ∧
    (∀ j k i c : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, (D2 c j k y * spatialPartial ψ i y - D2 i j k y * spatialPartial ψ c y) =
        -∫ y in W, vorticityAntisym (fun l => Ω2 l j k y) i c * ψ y) := by
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hint : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → IntegrableOn f W :=
    fun f hf => hf.integrable (by norm_num)
  have hanti0 := vorticityAnti_base (fun i j => hint _ (hG i j)) (fun i => hint _ (hU i)) hdU
  have hdiv1 : ∀ m : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, G i m y * spatialPartial ψ i y = 0 := fun m =>
    vorticityDiv_deriv (fun i => hint _ (hU i)) (fun i => hint _ (hG i m)) hdiv
      (fun i => hdU i m)
  have hanti1 : ∀ m i k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, (G k m y * spatialPartial ψ i y - G i m y * spatialPartial ψ k y) =
        -∫ y in W, vorticityAntisym (fun l => Ω1 l m y) i k * ψ y := fun m =>
    vorticityAnti_deriv (fun i => hint _ (hU i))
      (fun l => hint _ (vorticityCurl_memLp hG l)) (fun l => hint _ (hΩ1 l m)) hanti0
      (fun i => hdU i m) (fun l => hdw l m) (fun i => hint _ (hG i m))
  refine ⟨hanti0, hdiv1, hanti1, ?_, ?_⟩
  · intro j k
    exact vorticityDiv_deriv (fun i => hint _ (hG i j)) (fun i => hint _ (hD2 i j k))
      (hdiv1 j) (fun i => hdG i j k)
  · intro j k
    exact vorticityAnti_deriv (fun i => hint _ (hG i j)) (fun l => hint _ (hΩ1 l j))
      (fun l => hint _ (hΩ2 l j k)) (hanti1 j) (fun i => hdG i j k) (fun l => hdΩ1 l j k)
      (fun i => hint _ (hD2 i j k))

/-- The pointwise relations of the backward mollifications of the bootstrap fields. -/
theorem vorticitySmoothRelations {W : Set (Vec3 × ℝ)} (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W)
    {U : Fin 3 → Vec3 × ℝ → ℝ} {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hU : ∀ i, MemLp (U i) 2 (volume.restrict W)) (hG : ∀ i j, MemLp (G i j) 2 (volume.restrict W))
    (hD2 : ∀ i j k, MemLp (D2 i j k) 2 (volume.restrict W))
    (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 (volume.restrict W))
    (hΩ2 : ∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict W))
    (hdU : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, U i y * spatialPartial ψ j y = -∫ y in W, G i j y * ψ y)
    (hdG : ∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, G i j y * spatialPartial ψ k y = -∫ y in W, D2 i j k y * ψ y)
    (hdw : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, vorticityCurl G i y * spatialPartial ψ j y = -∫ y in W, Ω1 i j y * ψ y)
    (hdΩ1 : ∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, Ω1 i j y * spatialPartial ψ k y = -∫ y in W, Ω2 i j k y * ψ y)
    (hdiv : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, U i y * spatialPartial ψ i y = 0)
    {ε : ℝ} (hε : 0 < ε) {z : Vec3 × ℝ}
    (hz : Metric.closedBall (z - vorticityBackShift ε) ε ⊆ W) :
    (∑ i : Fin 3, spatialPartial (vorticityBackMollify W (U i) ε hε) i z = 0) ∧
    (∀ i k : Fin 3, spatialPartial (vorticityBackMollify W (U k) ε hε) i z -
        spatialPartial (vorticityBackMollify W (U i) ε hε) k z =
      vorticityAntisym (fun l => vorticityBackMollify W (vorticityCurl G l) ε hε z) i k) ∧
    (∀ i j : Fin 3, spatialPartial (vorticityBackMollify W (U i) ε hε) j z =
      vorticityBackMollify W (G i j) ε hε z) ∧
    (∀ m : Fin 3, ∑ i : Fin 3, spatialPartial (vorticityBackMollify W (G i m) ε hε) i z = 0) ∧
    (∀ m i k : Fin 3, spatialPartial (vorticityBackMollify W (G k m) ε hε) i z -
        spatialPartial (vorticityBackMollify W (G i m) ε hε) k z =
      vorticityAntisym (fun l => vorticityBackMollify W (Ω1 l m) ε hε z) i k) ∧
    (∀ i j k : Fin 3, spatialPartial (vorticityBackMollify W (G i j) ε hε) k z =
      vorticityBackMollify W (D2 i j k) ε hε z) ∧
    (∀ j k : Fin 3,
      ∑ i : Fin 3, spatialPartial (vorticityBackMollify W (D2 i j k) ε hε) i z = 0) ∧
    (∀ j k i c : Fin 3, spatialPartial (vorticityBackMollify W (D2 c j k) ε hε) i z -
        spatialPartial (vorticityBackMollify W (D2 i j k) ε hε) c z =
      vorticityAntisym (fun l => vorticityBackMollify W (Ω2 l j k) ε hε z) i c) ∧
    (∀ i j : Fin 3, spatialPartial (vorticityBackMollify W (vorticityCurl G i) ε hε) j z =
      vorticityBackMollify W (Ω1 i j) ε hε z) ∧
    (∀ i j k : Fin 3, spatialPartial (vorticityBackMollify W (Ω1 i j) ε hε) k z =
      vorticityBackMollify W (Ω2 i j k) ε hε z) := by
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hint : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W) → IntegrableOn f W :=
    fun f hf => hf.integrable (by norm_num)
  have hWm : MeasurableSet W := hWo.measurableSet
  obtain ⟨hanti0, hdiv1, hanti1, hdiv2, hanti2⟩ :=
    vorticityWeakRelations hWb hU hG hD2 hΩ1 hΩ2 hdU hdG hdw hdΩ1 hdiv
  have hw := vorticityCurl_memLp hG
  refine ⟨vorticityBackMollify_div_of_weak hWo (fun i => hint _ (hU i)) hdiv hε hz, ?_,
    fun i j => vorticityBackMollify_spatialPartial_of_weak hWo (hint _ (hU i)) (hdU i j) hε hz,
    fun m => vorticityBackMollify_div_of_weak hWo (fun i => hint _ (hG i m)) (hdiv1 m) hε hz,
    ?_,
    fun i j k => vorticityBackMollify_spatialPartial_of_weak hWo (hint _ (hG i j)) (hdG i j k)
      hε hz,
    fun j k => vorticityBackMollify_div_of_weak hWo (fun i => hint _ (hD2 i j k)) (hdiv2 j k)
      hε hz,
    ?_,
    fun i j => vorticityBackMollify_spatialPartial_of_weak hWo (hint _ (hw i)) (hdw i j) hε hz,
    fun i j k => vorticityBackMollify_spatialPartial_of_weak hWo (hint _ (hΩ1 i j))
      (hdΩ1 i j k) hε hz⟩
  · intro i k
    rw [vorticityBackMollify_curl_of_weak hWo (hint _ (hU i)) (hint _ (hU k)) (hanti0 i k) hε hz,
      vorticityBackMollify_antisym hWm (fun l => hint _ (hw l)) hε i k z]
  · intro m i k
    rw [vorticityBackMollify_curl_of_weak hWo (hint _ (hG i m)) (hint _ (hG k m)) (hanti1 m i k)
      hε hz, vorticityBackMollify_antisym hWm (fun l => hint _ (hΩ1 l m)) hε i k z]
  · intro j k i c
    rw [vorticityBackMollify_curl_of_weak hWo (hint _ (hD2 i j k)) (hint _ (hD2 c j k))
      (hanti2 j k i c) hε hz, vorticityBackMollify_antisym hWm (fun l => hint _ (hΩ2 l j k))
      hε i c z]

end ESS
