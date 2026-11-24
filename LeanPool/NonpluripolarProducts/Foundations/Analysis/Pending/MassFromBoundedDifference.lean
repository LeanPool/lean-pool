/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalSlotComparison
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.Envelopes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

/-!
# Mass monotonicity from the bounded-difference case

Suppose the total mass of the global mixed measure does not increase from `b` to
`a` whenever `a ≤ b ≤ a + t` slotwise (nondegenerate potentials). Then it is
monotone in the singularity order: if every `u i` is more singular than `v i`,
the mass of `u` is at most that of `v`.

Proof. Shift `v` so that `u ≤ v`. For `t ∈ ℕ`, `φₜ = max(u, v - t)` satisfies
`v - t ≤ φₜ ≤ v`, so `mass φₜ ≤ mass v`. On `Sₜ = {∀ i, v i - t < u i}` the
measures of `φₜ` and `u` agree (locality of maxima). The sets `Sₜ` increase and
exhaust `M` up to the pole sets of `u`, which are null. Hence
`mass u = sup μ_u(Sₜ) = sup μ_{φₜ}(Sₜ) ≤ mass v`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.MassFromBoundedDifference

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open GlobalNonPluripolar BoundedGlobalProduct GlobalMaxLocality GlobalSlotComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- **Monotonicity in the singularity order from the bounded-difference case.** -/
theorem globalMixedMeasure_univ_le_of_moreSingular {θ : Fin n → ClosedRealOneOneForm n M}
    {u v : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (huv : ∀ i, MoreSingularOn (u i) (v i) univ)
    (hH : ∀ (a b : Fin n → M → EReal) (ha : ∀ i, IsThetaPshPotential (θ i).val (a i))
      (hb : ∀ i, IsThetaPshPotential (θ i).val (b i)) (t : ℝ), 0 ≤ t →
      (∀ i p, a i p ≤ b i p) → (∀ i p, b i p ≤ a i p + (t : EReal)) →
      globalMixedMeasure θ a (fun i => (ha i).1) univ ≤
        globalMixedMeasure θ b (fun i => (hb i).1) univ) :
    globalMixedMeasure θ u (fun i => (hu i).1) univ ≤
      globalMixedMeasure θ v (fun i => (hv i).1) univ := by
  classical
  choose C hC using huv
  -- shift `v` above `u`
  set v' : Fin n → M → EReal := fun i x => v i x - ((-C i : ℝ) : EReal) with hv'def
  have hv' : ∀ i, IsThetaPshPotential (θ i).val (v' i) := fun i => (hv i).sub_const (-C i)
  have hmass_v' : globalMixedMeasure θ v' (fun i => (hv' i).1) univ =
      globalMixedMeasure θ v (fun i => (hv i).1) univ :=
    congrArg (fun μ : Measure M => μ univ)
      (GlobalMeasureInvariance.globalMixedMeasure_sub_const (fun i => (hv i).1) (fun i => -C i))
  have huv' : ∀ i p, u i p ≤ v' i p := by
    intro i p
    have h := hC i p (mem_univ p)
    simpa [hv'def, sub_eq_add_neg, EReal.coe_neg] using h
  -- the competitors `φₜ = max(u, v' - t)`
  let w (t : ℕ) : Fin n → M → EReal := fun i x => v' i x - ((t : ℝ) : EReal)
  have hw (t : ℕ) : ∀ i, IsThetaPshPotential (θ i).val (w t i) :=
    fun i => (hv' i).sub_const (t : ℝ)
  let φ (t : ℕ) : Fin n → M → EReal := fun i x => max (u i x) (w t i x)
  have hφ (t : ℕ) : ∀ i, IsThetaPshPotential (θ i).val (φ t i) := fun i =>
    ⟨BoundedGlobalProduct.ThetaPlurisubharmonic.max (hu i).1 (hw t i).1,
      (hu i).2.mono fun x => le_max_left _ _⟩
  have hwle (t : ℕ) (i : Fin n) (p : M) : w t i p ≤ v' i p := by
    change v' i p - ((t : ℝ) : EReal) ≤ v' i p
    exact EReal.sub_le_of_le_add (le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le t))
  have hmass_φ (t : ℕ) : globalMixedMeasure θ (φ t) (fun i => (hφ t i).1) univ ≤
      globalMixedMeasure θ v' (fun i => (hv' i).1) univ :=
    hH (φ t) v' (hφ t) hv' t (Nat.cast_nonneg t)
      (fun i p => max_le (huv' i p) (hwle t i p))
      (fun i p => by
        calc v' i p = w t i p + ((t : ℝ) : EReal) := by
              change v' i p = v' i p - ((t : ℝ) : EReal) + ((t : ℝ) : EReal)
              rw [EReal.sub_add_cancel]
          _ ≤ φ t i p + ((t : ℝ) : EReal) := by gcongr; exact le_max_right _ _)
  -- locality on `Sₜ`
  set μu := globalMixedMeasure θ u (fun i => (hu i).1)
  let S (t : ℕ) : Set M := {x | ∀ i, w t i x < u i x}
  have hloc (t : ℕ) : μu (S t) ≤ globalMixedMeasure θ v (fun i => (hv i).1) univ := by
    have h := globalMixedMeasure_restrict_max_eq (fun i => (hu i).1) (fun i => (hw t i).1)
      (fun i => (hφ t i).1)
    have h2 := congrArg (fun ν : Measure M => ν univ) h
    simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter] at h2
    calc μu (S t) = globalMixedMeasure θ (φ t) (fun i => (hφ t i).1) (S t) := h2.symm
      _ ≤ globalMixedMeasure θ (φ t) (fun i => (hφ t i).1) univ := measure_mono (subset_univ _)
      _ ≤ _ := (hmass_φ t).trans hmass_v'.le
  have hmono : Monotone S := by
    intro s t hst x hx i
    refine lt_of_le_of_lt ?_ (hx i)
    exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hst))
  have hcover : univ ⊆ (⋃ t, S t) ∪ ⋃ i, {x | u i x = ⊥} := by
    intro x _
    by_cases hx : ∃ i, u i x = ⊥
    · obtain ⟨i, hi⟩ := hx
      exact Or.inr (mem_iUnion.mpr ⟨i, hi⟩)
    · push Not at hx
      refine Or.inl (mem_iUnion.mpr ?_)
      have hlt (i : Fin n) : ∃ t : ℕ, w t i x < u i x := by
        have htop : v' i x ≠ ⊤ :=
          ((hv' i).1.quasiPlurisubharmonic.ne_top x)
        induction hvx : v' i x using EReal.rec with
        | bot => exact ⟨0, by simp [w, hvx, bot_lt_iff_ne_bot.mpr (hx i)]⟩
        | top => exact absurd hvx htop
        | coe r =>
          induction hux : u i x using EReal.rec with
          | bot => exact absurd hux (hx i)
          | top => exact ⟨0, by simp [w, hvx]⟩
          | coe s =>
            obtain ⟨t, ht⟩ := exists_nat_gt (r - s)
            refine ⟨t, ?_⟩
            simp only [w, hvx]
            rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
            linarith
      choose T hT using hlt
      refine ⟨∑ i, T i, fun i => lt_of_le_of_lt ?_ (hT i)⟩
      have hTi : T i ≤ ∑ j, T j :=
        Finset.single_le_sum (f := T) (fun j _ => Nat.zero_le (T j)) (Finset.mem_univ i)
      exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hTi))
  calc μu univ ≤ μu ((⋃ t, S t) ∪ ⋃ i, {x | u i x = ⊥}) := measure_mono hcover
    _ ≤ μu (⋃ t, S t) + μu (⋃ i, {x | u i x = ⊥}) := measure_union_le _ _
    _ = μu (⋃ t, S t) := by
      rw [measure_iUnion_null fun i => globalMixedMeasure_pole_null _ i, add_zero]
    _ = ⨆ t, μu (S t) := hmono.measure_iUnion
    _ ≤ _ := iSup_le hloc

end

end SGPT.Foundations.Analysis.Pending.MassFromBoundedDifference
