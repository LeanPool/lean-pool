/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Probability.Independence.Basic

/-!
# LayerIndependence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Mutual independence of joins of row-wise independent sigma-fields

This file is carrier-neutral: it works over an abstract probability space and
uses nothing but Mathlib's independence A.  It supplies the one purely
measure-theoretic brick that the varying-truncation-level independence producer
of Section 4.1 needs and that Mathlib does not have.

The situation is the following.  A doubly indexed family of sub-sigma-fields
`A : ι → L → MeasurableSpace Ω` is given, together with a mutually independent
family `κ : L → MeasurableSpace Ω` dominating it row by row (`A i l ≤ κ l`).
Each *row* — the family `(A i l)_i` at a fixed `l` — is mutually independent.
The conclusion needed downstream is that the *joins* `(⨆ l, A i l)_i` are
mutually independent: one index `i` may read every `l`, and the reads at
different `i` must still decouple.

Mathlib's `ProbabilityTheory.indep_iSup_of_disjoint` splits a mutually
independent family into two disjoint blocks; iterating it over a `Finset` of
indices is exactly what turns the refined `ι × L`-family into the `ι`-indexed
join statement.

## Main results

* `iIndep_prod_of_iIndep_rows`: the `ι × L`-refinement of a doubly indexed
  family with independent rows is mutually independent.
* `iIndep_iSup_of_iIndep_rows`: the `ι`-indexed joins of row-wise independent
  families over an independent `L`-family are mutually independent.
* `iIndep_of_le`: mutual independence passes to smaller sigma-fields.
* `iIndepFun_of_iIndep_sigma`: real observables measurable for a mutually
  independent family of sigma-fields are mutually independent.
-/

namespace Algsuperdiff.Section4.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Omega : Type*} [mOmega : MeasurableSpace Omega] {mu : Measure Omega}

/-- **The `ι × L`-refinement of a doubly indexed family is mutually
independent.**  If `kappa : L → MeasurableSpace Omega` is mutually independent,
every `A i l` is contained in `kappa l`, and each row `(A i l)_i` at a fixed
`l` is mutually independent, then the whole family `(A p.1 p.2)_{p : ι × L}` is
mutually independent.

A finite intersection is regrouped by the *second* (layer) coordinate: the
independence of `kappa` multiplies across distinct layers, and the row
independence multiplies inside a single layer. -/
theorem iIndep_prod_of_iIndep_rows [IsProbabilityMeasure mu] {iota L : Type*}
    {kappa : L → MeasurableSpace Omega} {A : iota → L → MeasurableSpace Omega}
    (hkappa : iIndep kappa mu) (hle : ∀ i l, A i l ≤ kappa l)
    (hrow : ∀ l, iIndep (fun i => A i l) mu) :
    iIndep (fun p : iota × L => A p.1 p.2) mu := by
  classical
  rw [iIndep_iff]
  intro S g hg
  set Ls := S.image Prod.snd with hLs
  set fib : L → Finset (iota × L) := fun l => S.filter (fun q => q.2 = l) with hfib
  have hInter : (⋂ p ∈ S, g p) = ⋂ l ∈ Ls, ⋂ p ∈ fib l, g p := by
    ext x
    simp only [Set.mem_iInter, hfib, Finset.mem_filter, hLs, Finset.mem_image]
    constructor
    · intro h l _ p hp
      exact h p hp.1
    · intro h p hp
      exact h p.2 ⟨p, hp, rfl⟩ p ⟨hp, rfl⟩
  have hGmeas : ∀ l ∈ Ls, MeasurableSet[kappa l] (⋂ p ∈ fib l, g p) := by
    intro l _
    refine @Finset.measurableSet_biInter _ _ (kappa l) _ _ (fun p hp => ?_)
    have hpl : p.2 = l := (Finset.mem_filter.1 hp).2
    have hmem := (hle p.1 p.2) _ (hg p (Finset.mem_filter.1 hp).1)
    rwa [hpl] at hmem
  have hfiber : ∀ l ∈ Ls, mu (⋂ p ∈ fib l, g p) = ∏ p ∈ fib l, mu (g p) := by
    intro l _
    have hinj : ∀ p ∈ fib l, ∀ q ∈ fib l, p.1 = q.1 → p = q := by
      intro p hp q hq hpq
      have hp2 : p.2 = l := (Finset.mem_filter.1 hp).2
      have hq2 : q.2 = l := (Finset.mem_filter.1 hq).2
      exact Prod.ext hpq (by rw [hp2, hq2])
    have heta : ∀ p ∈ fib l, ((p.1, l) : iota × L) = p := by
      intro p hp
      have hp2 : p.2 = l := (Finset.mem_filter.1 hp).2
      rw [← hp2]
    have hmeas : ∀ i ∈ (fib l).image Prod.fst, MeasurableSet[A i l] (g (i, l)) := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
      have hp2 : p.2 = l := (Finset.mem_filter.1 hp).2
      have hmp := hg p (Finset.mem_filter.1 hp).1
      rw [hp2] at hmp
      rw [heta p hp]
      exact hmp
    have hset : (⋂ p ∈ fib l, g p) = ⋂ i ∈ (fib l).image Prod.fst, g (i, l) := by
      ext x
      simp only [Set.mem_iInter]
      constructor
      · intro hx i hi
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
        rw [heta p hp]
        exact hx p hp
      · intro hx p hp
        rw [← heta p hp]
        exact hx p.1 (Finset.mem_image_of_mem _ hp)
    rw [hset, (hrow l).meas_biInter hmeas, Finset.prod_image hinj]
    exact Finset.prod_congr rfl fun p hp => by rw [heta p hp]
  rw [hInter, hkappa.meas_biInter hGmeas, Finset.prod_congr rfl hfiber]
  exact Finset.prod_fiberwise_of_maps_to
    (fun p hp => hLs ▸ Finset.mem_image_of_mem Prod.snd hp) (fun p => mu (g p))

/-- **The `ι`-indexed join of row-wise independent families is mutually
independent.**  Let `kappa : L → MeasurableSpace Omega` be mutually independent
with every `kappa l` a sub-sigma-field of the ambient one, and let
`A : ι → L → MeasurableSpace Omega` satisfy `A i l ≤ kappa l` with every row
mutually independent.  Then the joins `(⨆ l, A i l)_i` are mutually
independent.

Proof: `iIndep_prod_of_iIndep_rows` gives mutual independence of the refined
`ι × L`-family; the `ι`-blocks `{p | p.1 = i}` are pairwise disjoint, so
Mathlib's `indep_iSup_of_disjoint` splits off one block at a time along a
`Finset` induction. -/
theorem iIndep_iSup_of_iIndep_rows [IsProbabilityMeasure mu] {iota L : Type*}
    {kappa : L → MeasurableSpace Omega} {A : iota → L → MeasurableSpace Omega}
    (hkappa : iIndep kappa mu) (hkappale : ∀ l, kappa l ≤ mOmega)
    (hle : ∀ i l, A i l ≤ kappa l) (hrow : ∀ l, iIndep (fun i => A i l) mu) :
    iIndep (fun i => ⨆ l, A i l) mu := by
  classical
  have hprod : iIndep (fun p : iota × L => A p.1 p.2) mu :=
    iIndep_prod_of_iIndep_rows hkappa hle hrow
  have hnle : ∀ p : iota × L, A p.1 p.2 ≤ mOmega := fun p => (hle p.1 p.2).trans (hkappale p.2)
  have hblock : ∀ i : iota, (⨆ p ∈ ({p : iota × L | p.1 = i}), A p.1 p.2) = ⨆ l, A i l := by
    intro i
    apply le_antisymm
    · refine iSup₂_le ?_
      rintro ⟨j, l⟩ (hj : j = i)
      subst hj
      exact le_iSup (A j) l
    · exact iSup_le fun l => le_iSup₂_of_le (i, l) rfl le_rfl
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hdisj :
          Disjoint ({p : iota × L | p.1 = i}) ({p : iota × L | p.1 ∈ (s : Set iota)}) := by
        rw [Set.disjoint_left]
        rintro ⟨j, l⟩ (hj : j = i) (hj' : j ∈ (s : Set iota))
        subst hj
        exact hi (by simpa only [Finset.mem_coe] using hj')
      have hmain := indep_iSup_of_disjoint hnle hprod hdisj
      rw [hblock i] at hmain
      have hTle : ∀ j ∈ s, (⨆ l, A j l)
          ≤ ⨆ p ∈ ({p : iota × L | p.1 ∈ (s : Set iota)}), A p.1 p.2 := by
        intro j hj
        exact iSup_le fun l =>
          le_iSup₂_of_le (j, l) (by simpa only [Finset.mem_coe] using! hj) le_rfl
      have hs_meas : @MeasurableSet Omega
          (⨆ p ∈ ({p : iota × L | p.1 ∈ (s : Set iota)}), A p.1 p.2) (⋂ j ∈ s, f j) := by
        refine @Finset.measurableSet_biInter _ _
          (⨆ p ∈ ({p : iota × L | p.1 ∈ (s : Set iota)}), A p.1 p.2) _ _ (fun j hj => ?_)
        exact hTle j hj _ (hf j (by simp [hj]))
      have h_inter : mu (f i ∩ ⋂ j ∈ s, f j) = mu (f i) * mu (⋂ j ∈ s, f j) :=
        (Indep_iff (⨆ l, A i l)
            (⨆ p ∈ ({p : iota × L | p.1 ∈ (s : Set iota)}), A p.1 p.2) mu).1
          hmain (f i) (⋂ j ∈ s, f j) (hf i (by simp)) hs_meas
      calc
        mu (⋂ j ∈ insert i s, f j) = mu (f i ∩ ⋂ j ∈ s, f j) := by simp
        _ = mu (f i) * mu (⋂ j ∈ s, f j) := h_inter
        _ = mu (f i) * ∏ j ∈ s, mu (f j) := by rw [ih (fun j hj => hf j (by simp [hj]))]
        _ = ∏ j ∈ insert i s, mu (f j) := by rw [Finset.prod_insert hi]

/-- Mutual independence is inherited by any pointwise smaller family of
sigma-fields. -/
theorem iIndep_of_le {iota : Type*} {m m' : iota → MeasurableSpace Omega}
    (h : iIndep m mu) (hle : ∀ i, m' i ≤ m i) : iIndep m' mu := by
  rw [iIndep_iff] at h ⊢
  intro s f hf
  exact h s fun i hi => hle i _ (hf i hi)

/-- **Real observables measurable for a mutually independent family of
sigma-fields are mutually independent.**  The comap sigma-field of `f i` is
contained in `m i`, so the mutual independence of the `m i` passes to the
functions. -/
theorem iIndepFun_of_iIndep_sigma {iota : Type*} {m : iota → MeasurableSpace Omega}
    (h : iIndep m mu) {f : iota → Omega → ℝ} (hf : ∀ i, Measurable[m i] (f i)) :
    iIndepFun f mu :=
  (iIndepFun_iff_iIndep (fun _ : iota => (inferInstance : MeasurableSpace ℝ)) f mu).mpr
    (iIndep_of_le h fun i => (hf i).comap_le)

end Algsuperdiff.Section4.Probability
