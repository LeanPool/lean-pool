/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Jacobson.Ideal

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nakayama

/-!
# Nakayama's lemma for ideals in finite algebras

Two consequences of Nakayama's lemma that are missing from Mathlib:

* `Ideal.eq_top_of_sup_map_eq_top`: an ideal of a *finite* `R`-algebra that becomes the unit
  ideal modulo (the extension of) an ideal `I ≤ jacobson ⊥` of `R` is the unit ideal.
* `Polynomial.span_eq_top_of_sup_map_C_eq_top`: the same conclusion for the span of a set of
  polynomials over `R` **containing a monic polynomial** — `R[X]` itself is not finite over
  `R`, but the quotient by the monic member is, which is exactly what makes the statement
  true (it fails without the monicity hypothesis: `1 - rX` with `r ∈ jacobson ⊥` generates
  the unit ideal modulo `I.map C` but not over `R`).
-/

@[expose] public section

namespace Ideal

/-- **Nakayama's lemma for ideals in a finite algebra**: an ideal of a finite `R`-algebra `S`
that becomes the unit ideal modulo (the extension of) an ideal `I` contained in the Jacobson
radical of `R` is the unit ideal. -/
theorem eq_top_of_sup_map_eq_top {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥) {J : Ideal S}
    (h : J ⊔ I.map (algebraMap R S) = ⊤) : J = ⊤ := by
  have hle : (⊤ : Submodule R S) ≤ J.restrictScalars R ⊔ I • ⊤ := by
    intro x _
    have hx : x ∈ J ⊔ I.map (algebraMap R S) := h.ge trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    refine Submodule.add_mem_sup ha ?_
    rwa [Ideal.smul_top_eq_map]
  have := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hle
  exact eq_top_iff.mpr fun x _ ↦ this Submodule.mem_top

end Ideal

namespace Polynomial

open Ideal

/-- A set of polynomials over `R` that contains a monic polynomial and generates the unit
ideal modulo (constants from) an ideal `I` contained in the Jacobson radical of `R`
generates the unit ideal. Monicity is essential: `{1 - rX}` with `r ∈ jacobson ⊥` satisfies
the other hypotheses but does not generate the unit ideal. -/
theorem span_eq_top_of_sup_map_C_eq_top {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {s : Set R[X]} (hs : ∃ p ∈ s, p.Monic)
    (h : Ideal.span s ⊔ I.map (C : R →+* R[X]) = ⊤) : Ideal.span s = ⊤ := by
  obtain ⟨u, hus, hu⟩ := hs
  have : Module.Finite R (R[X] ⧸ Ideal.span {u}) := hu.finite_quotient
  have hmap : algebraMap R (R[X] ⧸ Ideal.span {u})
      = (Ideal.Quotient.mk (Ideal.span {u})).comp (C : R →+* R[X]) := by
    rw [IsScalarTower.algebraMap_eq R R[X] (R[X] ⧸ Ideal.span {u}), Ideal.Quotient.algebraMap_eq,
      Polynomial.algebraMap_eq]
  have htop : (Ideal.span s).map (Ideal.Quotient.mk (Ideal.span {u}))
      ⊔ I.map (algebraMap R (R[X] ⧸ Ideal.span {u})) = ⊤ := by
    have := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span {u}))) h
    rwa [Ideal.map_sup, Ideal.map_top (Ideal.Quotient.mk (Ideal.span {u})), Ideal.map_map,
      ← hmap] at this
  have hker : Ideal.comap (Ideal.Quotient.mk (Ideal.span {u})) ⊥ = Ideal.span {u} := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hcm := Ideal.comap_map_of_surjective (Ideal.Quotient.mk (Ideal.span {u}))
    Ideal.Quotient.mk_surjective (Ideal.span s)
  rw [Ideal.eq_top_of_sup_map_eq_top hI htop, hker,
    sup_eq_left.mpr (Ideal.span_mono (Set.singleton_subset_iff.mpr hus))] at hcm
  rw [eq_top_iff, ← hcm]
  exact fun x _ ↦ Ideal.mem_comap.mpr trivial

/-- A set of polynomials over `R` that contains a monic polynomial and whose image under a
surjective ring homomorphism with kernel contained in the Jacobson radical generates the
unit ideal generates the unit ideal itself. -/
theorem span_eq_top_of_span_image_map_eq_top {R S : Type*} [CommRing R] [CommRing S]
    {φ : R →+* S} (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≤ Ideal.jacobson ⊥)
    {s : Set R[X]} (hs : ∃ p ∈ s, p.Monic) (h : Ideal.span (map φ '' s) = ⊤) :
    Ideal.span s = ⊤ := by
  refine span_eq_top_of_sup_map_C_eq_top hker hs ?_
  have hsurj : Function.Surjective (mapRingHom φ) := map_surjective _ hφ
  have hcm := Ideal.comap_map_of_surjective (mapRingHom φ) hsurj (Ideal.span s)
  rw [Ideal.map_span, ← RingHom.ker_eq_comap_bot, ker_mapRingHom] at hcm
  simp only [coe_mapRingHom] at hcm
  rw [h] at hcm
  rw [eq_top_iff, ← hcm]
  exact fun x _ ↦ Ideal.mem_comap.mpr trivial

end Polynomial

end
