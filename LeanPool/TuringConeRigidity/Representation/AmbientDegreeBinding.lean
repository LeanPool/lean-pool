/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/AmbientDegreeBinding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.AmbientDegreeSyntax
public import LeanPool.TuringConeRigidity.SetModels.ModelDegreeOrder

/-!
# Ambient Degree Binding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

/-- A full formula defining the model's collection of natural-number binary relation graphs. -/
noncomputable def ownGraphBound (o Q : ℕ) : SentenceForm :=
  definedSet Q (.allMem 0 (productMember (o+2) (o+2) 0))

theorem ownGraphBound_spec (M : ZFSet.{u}) (hM : Transitive M)
    (o Q : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (ownGraphBound o Q).Sat (M : Set ZFSet) e ↔
      ∀ x, x ∈ e Q ↔ x ∈ M ∧ x ⊆ ZFSet.prod (e o) (e o) := by
  rw [ownGraphBound,definedSet_spec M hM Q _ e he]
  simp only [Formula.eval_allMem,productMember_spec,cons_zero,cons_succ]
  constructor
  · intro h x
    exact ⟨fun hx => ⟨hM _ (he Q) _ hx,(h x (hM _ (he Q) _ hx)).mp hx⟩,
      fun hx => (h x hx.1).mpr hx.2⟩
  · intro h x hx
    exact (h x).trans (and_iff_right hx)

theorem graphBound_certificates (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {Q : ZFSet.{u}} (hQ : ∀ x, x ∈ Q ↔ x ∈ M ∧ x ⊆ ZFSet.prod ZFSet.omega ZFSet.omega) :
    ∀ f : ℕ → ℕ, ∀ n, finiteNaturalGraph f n ∈ Q := by
  intro f n
  refine (hQ _).mpr ⟨finiteNaturalGraph_mem M hM hT.pairing hT.union
    (sourceT_omega_mem M hM hT) f n,?_⟩
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteNaturalGraph f n z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,(mem_omega _).mpr ⟨f i,rfl⟩,rfl⟩

/-- A full formula defining the model's real set, graph bound, degree universe, and degree
order. -/
noncomputable def degreeSetup (eqf lef : Formula) : SentenceForm :=
  .conj (ownPower 6 3) (.conj (ownGraphBound 6 2)
    (.conj (definedSet 1 (Formula.degreeUniverseMember eqf 7 3 8 4 0))
      (definedSet 0 (Formula.degreeOrderMember lef 7 3 8 2 0))))

theorem degreeSetup_spec {eqf lef : Formula} (heq : DegreeEqualityFormula.{u} eqf)
    (hle : DegreeOrderFormula.{u} lef)
    (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (ho : e 6 = ZFSet.omega) (hz : e 7 = natSet 0) :
    (degreeSetup eqf lef).Sat (M : Set ZFSet) e ↔
      (∀ x, x ∈ e 3 ↔ x ∈ M ∧ x ⊆ ZFSet.omega) ∧
      (∀ x, x ∈ e 2 ↔ x ∈ M ∧ x ⊆ ZFSet.prod ZFSet.omega ZFSet.omega) ∧
      e 1 = degreeUniverse (e 3) ∧ e 0 = degreeOrder (e 3) := by
  simp only [degreeSetup,Sat,ownPower_spec M hM 6 3 e he,
    ownGraphBound_spec M hM 6 2 e he,ho]
  apply and_congr_right; intro hR
  apply and_congr_right; intro hQ
  have hr : ∀ w ∈ e 3, ∃ A : Oracle, realCode A = w := by
    intro w hw
    exact ⟨decodeReal w,realCode_decodeReal ((hR w).mp hw).2⟩
  have hq := graphBound_certificates M hM hT hQ
  have hd := definedSet_unique M hM 1 (Formula.degreeUniverseMember eqf 7 3 8 4 0) e he
    (degreeUniverse (e 3)) (internal_degreeUniverse M hM hT _ (he 3) hr)
    (fun x _ => Formula.degreeUniverseMember_spec heq 7 3 8 4 0 (cons x e) ho hq hz hr)
  rw [hd]
  apply and_congr_right; intro hD
  exact definedSet_unique M hM 0 (Formula.degreeOrderMember lef 7 3 8 2 0) e he
    (degreeOrder (e 3)) (internal_degreeOrder M hM hT _ (he 3) hr)
    (fun x _ => Formula.degreeOrderMember_spec hle 7 3 8 2 0 (cons x e) ho hq hz (e 3) hD hr)

end TuringRigidity.FullSetForcing

end OAI
