/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Probability.Independence.Basic

/-!
# Grouping and concatenating independent families

An independent family of σ-algebras (or random variables) indexed by pairs `(i, j)` stays
independent after grouping along the second coordinate: the σ-algebras `⨆ i, m (i, j)` are
independent in `j`, and the random vectors `(Y (i, j))ᵢ` are independent in `j`.

Two independent families also concatenate. If each of two families of σ-algebras is independent
and their suprema are independent of each other, the family indexed by the sum of the two index
types is independent; for two families of real random variables indexed by `Fin d` and `Fin p`
this gives the family indexed by `Fin (d + p)` obtained by concatenation.

## Main statements

* `LevyStochCalc.Probability.iIndep_iSup_fiber` — grouping an independent family indexed by
  pairs along the second coordinate.
* `LevyStochCalc.Probability.iIndepFun_fiber` — the same for random variables.
* `LevyStochCalc.Probability.iIndep_sumElim` — concatenating two independent families of
  σ-algebras.
* `LevyStochCalc.Probability.iIndepFun_addCases` — concatenating two independent families of
  real random variables.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An independent family of σ-algebras indexed by pairs, grouped along the second
coordinate. -/
theorem iIndep_iSup_fiber {m : ι × κ → MeasurableSpace Ω} (h_le : ∀ q, m q ≤ mΩ)
    (h : iIndep m μ) : iIndep (fun j => ⨆ i, m (i, j)) μ := by
  classical
  rw [iIndep_iff]
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | @insert j₀ s hj₀ ih =>
    intro f hf
    have hind := indep_iSup_of_disjoint h_le h (S := {q : ι × κ | q.2 = j₀})
      (T := {q : ι × κ | q.2 ∈ s}) (by
        rw [Set.disjoint_left]
        rintro ⟨i, j⟩ (hj : j = j₀) (hj' : j ∈ s)
        exact hj₀ (hj ▸ hj'))
    rw [Indep_iff] at hind
    have h1 : MeasurableSet[⨆ q ∈ {q : ι × κ | q.2 = j₀}, m q] (f j₀) := by
      refine MeasurableSpace.le_def.mp (iSup_le fun i => ?_) _ (hf j₀ (Finset.mem_insert_self _ _))
      exact le_iSup₂_of_le (i, j₀) rfl le_rfl
    have h2 : MeasurableSet[⨆ q ∈ {q : ι × κ | q.2 ∈ s}, m q] (⋂ j ∈ s, f j) := by
      refine MeasurableSet.biInter s.countable_toSet fun j hj => ?_
      refine MeasurableSpace.le_def.mp (iSup_le fun i => ?_) _ (hf j (Finset.mem_insert_of_mem hj))
      exact le_iSup₂_of_le (i, j) hj le_rfl
    rw [Finset.set_biInter_insert, hind _ _ h1 h2, Finset.prod_insert hj₀,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- Independent random variables indexed by pairs, grouped into random vectors along the
second coordinate. -/
theorem iIndepFun_fiber {𝓧 : ι × κ → Type*} [∀ q, MeasurableSpace (𝓧 q)] {Y : ∀ q, Ω → 𝓧 q}
    (mY : ∀ q, Measurable (Y q)) (h : iIndepFun Y μ) :
    iIndepFun (fun j ω (i : ι) => Y (i, j) ω) μ := by
  rw [iIndepFun_iff_iIndep] at h ⊢
  convert iIndep_iSup_fiber (fun q => (mY q).comap_le) h using 1
  funext j
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  congr
  funext i
  rw [MeasurableSpace.comap_comp]
  rfl

/-! ### Concatenating two independent families -/

section Concatenation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Two independent families of σ-algebras whose suprema are independent form an independent
family indexed by the sum of the two index types. -/
theorem iIndep_sumElim {ι κ : Type*} {m₁ : ι → MeasurableSpace Ω}
    {m₂ : κ → MeasurableSpace Ω} (h₁ : iIndep m₁ P) (h₂ : iIndep m₂ P)
    (h : Indep (⨆ i, m₁ i) (⨆ j, m₂ j) P) : iIndep (Sum.elim m₁ m₂) P := by
  rw [iIndep_iff]
  intro s f hf
  have hl : ∀ i ∈ s.toLeft, MeasurableSet[m₁ i] (f (Sum.inl i)) := fun i hi =>
    hf _ (Finset.mem_toLeft.mp hi)
  have hr : ∀ j ∈ s.toRight, MeasurableSet[m₂ j] (f (Sum.inr j)) := fun j hj =>
    hf _ (Finset.mem_toRight.mp hj)
  have hsplit : (⋂ x ∈ s, f x)
      = (⋂ i ∈ s.toLeft, f (Sum.inl i)) ∩ ⋂ j ∈ s.toRight, f (Sum.inr j) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_toLeft, Finset.mem_toRight]
    refine ⟨fun hx => ⟨fun i hi => hx _ hi, fun j hj => hx _ hj⟩, ?_⟩
    rintro ⟨ha, hb⟩ (i | j) hx
    · exact ha i hx
    · exact hb j hx
  have hA : MeasurableSet[⨆ i, m₁ i] (⋂ i ∈ s.toLeft, f (Sum.inl i)) :=
    Finset.measurableSet_biInter _ fun i hi => (le_iSup m₁ i) _ (hl i hi)
  have hB : MeasurableSet[⨆ j, m₂ j] (⋂ j ∈ s.toRight, f (Sum.inr j)) :=
    Finset.measurableSet_biInter _ fun j hj => (le_iSup m₂ j) _ (hr j hj)
  rw [hsplit, (Indep_iff _ _ _).mp h _ _ hA hB, h₁.meas_biInter hl, h₂.meas_biInter hr,
    Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

/-- Two independent families of real random variables indexed by `Fin d` and `Fin p`, whose
generated σ-algebras are independent, form an independent family indexed by `Fin (d + p)`. -/
theorem iIndepFun_addCases {d p : ℕ} {X : Fin d → Ω → ℝ} {Y : Fin p → Ω → ℝ}
    (hX : iIndepFun X P) (hY : iIndepFun Y P)
    (h : Indep (⨆ j, MeasurableSpace.comap (X j) inferInstance)
      (⨆ k, MeasurableSpace.comap (Y k) inferInstance) P) :
    iIndepFun (Fin.addCases (motive := fun _ => Ω → ℝ) X Y) P := by
  rw [iIndepFun_iff_iIndep] at hX hY ⊢
  have h2 := (iIndep_sumElim hX hY h).precomp
    (finSumFinEquiv (m := d) (n := p)).symm.injective
  refine (?_ : (fun x => MeasurableSpace.comap
      (Fin.addCases (motive := fun _ => Ω → ℝ) X Y x) inferInstance)
    = Sum.elim (fun j => MeasurableSpace.comap (X j) inferInstance)
      (fun k => MeasurableSpace.comap (Y k) inferInstance) ∘ finSumFinEquiv.symm) ▸ h2
  funext x
  refine Fin.addCases (fun j => ?_) (fun k => ?_) x <;> simp

end Concatenation

end LevyStochCalc.Probability
