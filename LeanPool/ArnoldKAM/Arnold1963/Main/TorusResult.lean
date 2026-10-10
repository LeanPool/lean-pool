/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Main.GlobalCover

/-!
The direct specification of one analytic invariant torus: center, frequency, lift, quotient
embedding, inverse angle map, and all-time trajectories, realized by the same local limit.
-/

@[expose] public section
noncomputable section
open Set Function Topology
open scoped NNReal
namespace KamProject.Arnold1963

/-- An analytic nonresonant torus with small displacement and original Hamiltonian trajectories. -/
structure KAMTorus (n : ℕ) (H₀ : ComplexSpace n → ℂ)
    (H₁ : ComplexPhaseSpace n → ℂ) (ambient : Set (ComplexSpace n))
    (r : ℝ≥0) (κ : ℝ) (T : Set (RealPhaseSpace n)) where
  /-- The real action center whose original frequency labels this torus. -/
  center : RealSpace n
  /-- The nonresonant real frequency of the torus's uniform rotation. -/
  frequency : RealSpace n
  /-- The analytic lift from complex angles to complex phase space. -/
  lift : ComplexSpace n → ComplexPhaseSpace n
  /-- The closed embedding of the real angle torus into real phase space. -/
  embedding : RealTorus n → RealPhaseSpace n
  /-- The analytic inverse for the angle component of the torus lift at real points. -/
  angleInverse : ComplexSpace n → ComplexSpace n
  center_mem : center ∈ realSlice ambient
  frequency_eq : actionFrequency H₀ (complexify center) = complexify frequency
  nonresonance : ∀ k : FourierIndex n, k ≠ 0 → indexPairing k (complexify frequency) ≠ 0
  analytic : AnalyticOnNhd ℂ lift (angleStrip n r)
  periodic : ∀ q ∈ angleStrip n r, ∀ k : FourierIndex n,
    lift (q + angleShift k) = phaseShift k (lift q)
  real_value : ∀ q : RealSpace n,
    complexifyPhase (realPartPhase (lift (complexify q))) = lift (complexify q)
  embedding_lift : ∀ q : RealSpace n,
    embedding (fun j => (q j : AddCircle (2 * Real.pi))) =
      torusProjection (realPartPhase (lift (complexify q)))
  embedding_range : range embedding = T
  closedEmbedding : IsClosedEmbedding embedding
  immersion : ∀ q ∈ angleStrip n r, Injective (fderiv ℂ lift q)
  angle_homeomorph : ∃ e : RealTorus n ≃ₜ RealTorus n, ∀ Q, e Q = (embedding Q).2
  inverse_analytic : ∀ Q : RealSpace n, AnalyticAt ℂ angleInverse (complexify Q)
  inverse_left : ∀ q : RealSpace n, angleInverse (lift (complexify q)).2 = complexify q
  inverse_right : ∀ Q : RealSpace n, (lift (angleInverse (complexify Q))).2 = complexify Q
  displacement : ∀ q ∈ angleStrip n r,
    ‖(lift q).1 - complexify center‖ < κ ∧ ‖(lift q).2 - q‖ < κ
  orbit_equation : ∀ q : RealSpace n, ∀ t : ℝ,
    HasDerivAt (fun u : ℝ => lift (complexify (q + u • frequency)))
      (hamiltonianVectorField (fun z => H₀ z.1 + H₁ z)
        (lift (complexify (q + t • frequency)))) t
  orbit_mem : ∀ q : RealSpace n, ∀ t : ℝ,
    torusProjection (realPartPhase (lift (complexify (q + t • frequency)))) ∈ T

namespace FiniteLocalization
variable {n : ℕ} {H₀ : ComplexSpace n → ℂ} {ambient : Set (ComplexSpace n)}
  {ρ : ℝ≥0} {κ : ℝ} (L : FiniteLocalization n H₀ ambient ρ κ)
  (f : AnalyticPhaseFunction n ambient ρ) (hf : f.uniformNorm ≤ L.threshold)

/-- A realized invariant torus extracted from one local patch's limiting construction. -/
def torusResult (c : L.patches) {p : RealSpace n}
    (hp : p ∈ realSlice ((L.data f hf c).limitDomain (L.parameters c))) :
    KAMTorus n H₀ f.toFun ambient (L.width / 6) κ
      ((L.data f hf c).invariantTorus (L.parameters c) p) := by
  let h := L.data f hf c
  let b := L.parameters c
  let ω := h.limitFrequency b (complexify p)
  let pc := h.unperturbedCenter ω
  have hstrip : angleStrip n (L.width / 6) ⊆
      Iteration.InitialData.commonAngleStrip n L.width :=
    Iteration.InitialData.thinAngleStrip_subset b
  have hpc : complexify (realPart pc) = pc := h.unperturbedCenter_real b hp
  have hω : complexify (realPart ω) = ω := h.limitFrequency_real_value b hp
  have ho (q : RealSpace n) : h.orbit b p q =
      fun t : ℝ => h.limitMap b (complexify p, complexify (q + t • realPart ω)) :=
    funext (h.orbit_eq_real_angle b hp q)
  refine {
    center := realPart pc
    frequency := realPart ω
    lift := fun q => h.limitMap b (complexify p, q)
    embedding := h.torusEmbedding b p
    angleInverse := h.complexAngleInverse b (complexify p)
    center_mem := ?_
    frequency_eq := ?_
    nonresonance := ?_
    analytic := (h.limitMap_angle_analytic b hp).mono hstrip
    periodic := ?_
    real_value := fun q => h.limitMap_real_value b (x := (p, q)) hp
    embedding_lift := h.torusEmbedding_lift b hp
    embedding_range := h.torusEmbedding_range b p
    closedEmbedding := h.torusEmbedding_isClosedEmbedding b hp
    immersion := fun _ hq => h.torusLift_derivative_injective b hp hq
    angle_homeomorph := ⟨h.torusAngleHomeomorph b hp, fun _ => rfl⟩
    inverse_analytic := h.complexAngleInverse_analytic_at_real b hp
    inverse_left := fun q => (h.complexAngleInverse_analytic b hp q).2.1
    inverse_right := ?_
    displacement := ?_
    orbit_equation := ?_
    orbit_mem := ?_ }
  · change complexify (realPart pc) ∈ ambient
    rw [hpc]
    have hlocal : pc ∈ c.val.domain := h.unperturbedCenter_mem b hp
    exact c.val.subset hlocal
  · rw [hpc, hω]
    exact h.chart.right (by simpa using h.limitFrequency_mem b hp 0)
  · intro k hk
    rw [hω]
    exact h.limitFrequency_no_integer_relation b hp k hk
  · intro q hq k
    exact h.limitMap_periodic b
      (h.angle_mem_limitPhase b hp (hstrip hq)) k
  · intro Q
    rw [h.complexAngleInverse_real_value b hp]
    change h.angleMap b (complexify p) (complexify (h.realAngleInverse b p Q)) = complexify Q
    rw [← h.angleMap_real_value b hp, h.realAngleInverse_right b hp]
  · intro q hq
    rw [hpc]
    exact L.corrections_small f hf c hp (hstrip hq)
  · intro q t
    have hh := L.orbit_original f hf c hp q t
    change HasDerivAt (h.orbit b p q)
      (hamiltonianVectorField (fun z => H₀ z.1 + f.toFun z) (h.orbit b p q t)) t at hh
    simpa only [ho q] using hh
  · intro q t
    have hh := h.orbit_mem_torus_image b hp q t
    simpa only [ho q, Iteration.InitialData.invariantTorus] using hh

end FiniteLocalization
end KamProject.Arnold1963
