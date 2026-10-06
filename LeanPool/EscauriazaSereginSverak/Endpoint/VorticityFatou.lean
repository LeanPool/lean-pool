/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakCalculus

/-!
# Lower semicontinuity of nonlinear integrals along `L²` approximations

If finitely many sequences converge in `L²` and a continuous nonnegative function of their values
has integrals eventually bounded by `K`, then the same function of the limits has integral at most
`K`. This transfers the smooth nonlinear estimates of the bootstrap of `thm:vorticity-regularity`
to the weak fields.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Fatou's lemma for a continuous nonnegative function of finitely many `L²`-convergent
sequences. -/
theorem vorticity_integral_le_of_L2_tendsto {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] {a : ι → ℕ → α → ℝ} {A : ι → α → ℝ}
    (ha : ∀ i n, MemLp (a i n) 2 μ) (hA : ∀ i, MemLp (A i) 2 μ)
    (hconv : ∀ i, Tendsto (fun n => eLpNorm (a i n - A i) 2 μ) atTop (𝓝 0))
    {H : (ι → ℝ) → ℝ} (hH : Continuous H) (hH0 : ∀ v, 0 ≤ H v)
    (hint : ∀ n, Integrable (fun x => H (fun i => a i n x)) μ)
    {K : ℝ} (hK : ∀ᶠ n in atTop, ∫ x, H (fun i => a i n x) ∂μ ≤ K) :
    Integrable (fun x => H (fun i => A i x)) μ ∧ ∫ x, H (fun i => A i x) ∂μ ≤ K := by
  obtain ⟨φ, hφ, hae⟩ := vorticity_exists_subseq_ae ha hA hconv
  obtain ⟨N, hN⟩ := eventually_atTop.1 hK
  have hmeas : AEStronglyMeasurable (fun x => H (fun i => A i x)) μ :=
    hH.comp_aestronglyMeasurable
      (AEMeasurable.of_eval fun i => (hA i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  refine vorticity_integral_le_of_ae_tendsto (g := fun n x => H (fun i => a i (φ (n + N)) x))
    (fun n x => hH0 _) (fun n => hint _) hmeas ?_ (fun n => hN _ ?_)
  · filter_upwards [hae] with x hx
    have hvec : Tendsto (fun n => fun i => a i (φ (n + N)) x) atTop (𝓝 fun i => A i x) := by
      rw [tendsto_pi_nhds]
      intro i
      exact (hx i).comp ((tendsto_add_atTop_iff_nat N).2 tendsto_id)
    exact (hH.tendsto _).comp hvec
  · exact le_trans (Nat.le_add_left N n) (hφ.id_le (n + N))

end ESS
