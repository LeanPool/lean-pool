/-
Copyright (c) 2026 Jacob Parish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish
-/

module

public import LeanPool.Erdos111.Basic
public import LeanPool.Erdos111.Probability.Minimax

/-!
# Mixtures of couplings

Let `Λ` be a law, `A` a set of coordinates to keep, and `W` a finite set of coordinates
outside `A` to choose. A coupling chooses the signs on `W` as a function of the signs on
a finite set `U ⊆ A`. If every nonnegative combination of finitely many costs, each a
function of the coordinates in `U ∪ W`, has expected optimal value at most the same
combination of the bounds `c i`, then the finite minimax lemma gives a mixture of
couplings meeting every bound at once. The mixture keeps the marginals of `Λ` on `A`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos111

variable {V : Type*}

open Classical in
/-- A mixture of couplings that choose the signs on `W` meets finitely many expected-cost
bounds at once, if every nonnegative combination of them is met by optimal choices. -/
theorem exists_mixture {r : ℕ} (Λ : Measure (V → Bool)) [IsProbabilityMeasure Λ]
    (A : Set V) (U W : Finset V) (hW : ∀ w ∈ W, w ∉ A)
    (f : Fin r → (V → Bool) → ℕ) (hf : ∀ i, DependsOn (f i) (↑U ∪ ↑W))
    (c : Fin r → ℝ≥0)
    (hkey : ∀ ρ : Fin r → ℝ≥0,
      ∫⁻ τ, ⨅ η : V → Bool, ∑ i, (ρ i : ℝ≥0∞) * f i (W.piecewise η τ) ∂Λ ≤
        ∑ i, (ρ i : ℝ≥0∞) * c i) :
    ∃ μ : Measure (V → Bool), IsProbabilityMeasure μ ∧ SameOn A Λ μ ∧
      ∀ i, ∫⁻ τ, (f i τ : ℝ≥0∞) ∂μ ≤ c i := by
  -- a pure coupling `ψ` chooses the signs on `W` from the signs on `U`
  let ext : (W → Bool) → V → Bool := fun ζ v => if hv : v ∈ W then ζ ⟨v, hv⟩ else true
  let extU : (U → Bool) → V → Bool := fun σ v => if hv : v ∈ U then σ ⟨v, hv⟩ else true
  let Ψ : ((U → Bool) → (W → Bool)) → (V → Bool) → V → Bool :=
    fun ψ τ => W.piecewise (ext (ψ (U.restrict τ))) τ
  -- the costs see only the signs on `U` and the choices on `W`
  have hfeq : ∀ i (τ τ' η η' : V → Bool), (∀ u ∈ U, τ u = τ' u) →
      (∀ w ∈ W, η w = η' w) → f i (W.piecewise η τ) = f i (W.piecewise η' τ') := by
    intro i τ τ' η η' hτ hη
    refine hf i fun v hv => ?_
    by_cases hw : v ∈ W
    · simp only [Finset.piecewise_eq_of_mem _ _ _ hw, hη v hw]
    · have hu : v ∈ U := by
        rcases hv with hu | hw'
        · exact hu
        · exact absurd hw' hw
      simp only [Finset.piecewise_eq_of_notMem _ _ _ hw, hτ v hu]
  have hmf : ∀ i, Measurable fun τ => (f i τ : ℝ≥0∞) := fun i =>
    measurable_from_nat.comp (measurable_of_dependsOn (J := U ∪ W) (by simpa using hf i))
  have hΨ : ∀ ψ, Measurable (Ψ ψ) := by
    intro ψ
    refine Measurable.of_eval fun v => ?_
    by_cases hw : v ∈ W
    · simp only [Ψ, Finset.piecewise_eq_of_mem _ _ _ hw, ext, dite_eq_left hw]
      refine measurable_of_dependsOn (J := U) fun τ τ' h => ?_
      rw [show U.restrict τ = U.restrict τ' from funext fun u => h u u.2]
    · simp only [Ψ, Finset.piecewise_eq_of_notMem _ _ _ hw]
      exact measurable_pi_apply v
  -- the expected cost of a pure coupling is finite
  let pay : Fin r → ((U → Bool) → (W → Bool)) → ℝ≥0∞ :=
    fun i ψ => ∫⁻ τ, (f i (Ψ ψ τ) : ℝ≥0∞) ∂Λ
  have hpay : ∀ i ψ, pay i ψ ≠ ∞ := by
    intro i ψ
    let e : (↥(U ∪ W) → Bool) → V → Bool :=
      fun σ v => if hv : v ∈ U ∪ W then σ ⟨v, hv⟩ else true
    have hB : ∀ τ, f i τ ≤ Finset.univ.sup fun σ => f i (e σ) := by
      intro τ
      have : f i τ = f i (e ((U ∪ W).restrict τ)) := hf i fun v hv => by
        have hv' : v ∈ U ∪ W := by simpa using hv
        rw [show e ((U ∪ W).restrict τ) v = τ v from dite_eq_left hv']
      rw [this]
      exact Finset.le_sup (f := fun σ => f i (e σ)) (Finset.mem_univ _)
    refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top (Finset.univ.sup fun σ => f i (e σ))) ?_
    calc pay i ψ ≤ ∫⁻ _, ((Finset.univ.sup fun σ => f i (e σ) : ℕ) : ℝ≥0∞) ∂Λ :=
          lintegral_mono fun τ => Nat.cast_le.2 (hB _)
      _ = _ := by simp
  -- every nonnegative combination of the bounds is met by a pure coupling
  obtain ⟨p, hp0, hp1, hpc⟩ := exists_mixed_le (fun i ψ => (pay i ψ).toReal) (fun i => c i) (by
    intro ρ hρ
    let ρ' : Fin r → ℝ≥0 := fun i => (ρ i).toNNReal
    let G : (U → Bool) → (W → Bool) → ℝ≥0∞ :=
      fun σ ζ => ∑ i, (ρ' i : ℝ≥0∞) * f i (W.piecewise (ext ζ) (extU σ))
    let ψ : (U → Bool) → (W → Bool) := fun σ => (Finite.exists_min (G σ)).choose
    have hτU : ∀ τ : V → Bool, ∀ u ∈ U, τ u = extU (U.restrict τ) u := by
      intro τ u hu
      simp [extU, hu]
    have hopt : ∀ τ, ∑ i, (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ) ≤
        ⨅ η : V → Bool, ∑ i, (ρ' i : ℝ≥0∞) * f i (W.piecewise η τ) := by
      intro τ
      refine le_iInf fun η => ?_
      calc ∑ i, (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ) = G (U.restrict τ) (ψ (U.restrict τ)) :=
            Finset.sum_congr rfl fun i _ => by
              rw [hfeq i τ (extU (U.restrict τ)) _ _ (hτU τ) fun _ _ => rfl]
        _ ≤ G (U.restrict τ) (W.restrict η) := (Finite.exists_min _).choose_spec _
        _ = _ := Finset.sum_congr rfl fun i _ => by
              rw [hfeq i (extU (U.restrict τ)) τ (ext (W.restrict η)) η
                (fun u hu => (hτU τ u hu).symm) fun w hw => by simp [ext, hw]]
    have hsum : ∑ i, (ρ' i : ℝ≥0∞) * pay i ψ ≤ ∑ i, (ρ' i : ℝ≥0∞) * c i :=
      calc ∑ i, (ρ' i : ℝ≥0∞) * pay i ψ =
            ∫⁻ τ, ∑ i, (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ) ∂Λ := by
            rw [lintegral_finsetSum (f := fun i τ => (ρ' i : ℝ≥0∞) * f i (Ψ ψ τ)) _
              fun i _ => ((hmf i).comp (hΨ ψ)).const_mul _]
            exact Finset.sum_congr rfl fun i _ =>
              (lintegral_const_mul _ ((hmf i).comp (hΨ ψ))).symm
        _ ≤ ∫⁻ τ, ⨅ η : V → Bool, ∑ i, (ρ' i : ℝ≥0∞) * f i (W.piecewise η τ) ∂Λ :=
            lintegral_mono hopt
        _ ≤ _ := hkey ρ'
    refine ⟨ψ, ?_⟩
    have hρ' : ∀ i, ρ i = ρ' i := fun i => (Real.coe_toNNReal _ (hρ i)).symm
    have h1 : ∑ i, ρ i * (pay i ψ).toReal = (∑ i, (ρ' i : ℝ≥0∞) * pay i ψ).toReal := by
      rw [ENNReal.toReal_sum fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top (hpay i ψ)]
      simp [ENNReal.toReal_mul, hρ']
    have h2 : ∑ i, ρ i * (c i : ℝ) = (∑ i, (ρ' i : ℝ≥0∞) * c i).toReal := by
      rw [ENNReal.toReal_sum fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]
      simp [ENNReal.toReal_mul, hρ']
    rw [h1, h2]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hsum)
  -- the mixture of the pure couplings
  let μ : Measure (V → Bool) := ∑ ψ, ENNReal.ofReal (p ψ) • Λ.map (Ψ ψ)
  have hμ : ∀ s, MeasurableSet s → μ s = ∑ ψ, ENNReal.ofReal (p ψ) * Λ (Ψ ψ ⁻¹' s) := by
    intro s hs
    simp [μ, Measure.finsetSum_apply, Measure.map_apply (hΨ _) hs]
  have hp : ∑ ψ, ENNReal.ofReal (p ψ) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ψ _ => hp0 ψ, hp1, ENNReal.ofReal_one]
  refine ⟨μ, ⟨by simp [hμ _ MeasurableSet.univ, hp]⟩, fun J hJ => ?_, fun i => ?_⟩
  · -- each pure coupling keeps the signs on `A`
    ext s hs
    have hJ' : Measurable (J.restrict (π := fun _ => Bool)) := Finset.measurable_restrict J
    rw [Measure.map_apply hJ' hs, Measure.map_apply hJ' hs, hμ _ (hJ' hs)]
    have : ∀ ψ, Ψ ψ ⁻¹' (J.restrict ⁻¹' s) = J.restrict ⁻¹' s := by
      intro ψ
      ext τ
      have : J.restrict (Ψ ψ τ) = J.restrict τ := by
        funext j
        exact Finset.piecewise_eq_of_notMem _ _ _ fun hw => hW _ hw (hJ j.2)
      simp only [Set.mem_preimage, this]
    simp only [this, ← Finset.sum_mul, hp, one_mul]
  · calc ∫⁻ τ, (f i τ : ℝ≥0∞) ∂μ = ∑ ψ, ENNReal.ofReal (p ψ) * pay i ψ := by
          simp only [μ, lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul]
          exact Finset.sum_congr rfl fun ψ _ => by rw [lintegral_map (hmf i) (hΨ ψ)]
      _ = ENNReal.ofReal (∑ ψ, p ψ * (pay i ψ).toReal) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun ψ _ => mul_nonneg (hp0 ψ) ENNReal.toReal_nonneg]
          refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [ENNReal.ofReal_mul (hp0 ψ), ENNReal.ofReal_toReal (hpay i ψ)]
      _ ≤ ENNReal.ofReal (c i) := ENNReal.ofReal_le_ofReal (hpc i)
      _ = c i := ENNReal.ofReal_coe_nnreal

end Erdos111
