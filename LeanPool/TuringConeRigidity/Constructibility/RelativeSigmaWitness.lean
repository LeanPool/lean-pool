/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeSigmaWitness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelBounds
public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction

/-!
# Relative Sigma Witness
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
open ElementaryModel SentenceForm
universe u

theorem relative_level_subset (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) {o : Ordinal.{u}} (ho : o.toZFSet ∈ M) :
    level R o ⊆ relativeModel M R :=
  fun x hx => (mem_relativeModel M R x hM hT hR).mpr ⟨o,ho,hx⟩

theorem relative_sigma_level_witness (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (i : Ordinal.{u}) (hi : i.toZFSet ∈ M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ n, e n ∈ level R i)
    (hφ : φ.Realize (relativeModel M R) e) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ level R i ⊆ level R o ∧
      φ.Realize (level R o) e := by
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix _ e).mp hφ
  have hsM := FiniteTuple.elements_mem M hM hT.pairing hT.union
    (by simpa only [Ordinal.toZFSet_zero] using internal_ordinal_zero M hM hT) xs
    (fun x hx => relativeModel_subset M R (hxs x hx))
  obtain ⟨j,hj,hjs⟩ := relative_level_bound M R (FiniteTuple.elements xs) hM hT hR hsM
    (fun x hx => (mem_relativeModel M R x hM hT hR).mp
      (hxs x ((FiniteTuple.mem_elements x xs).mp hx)))
  have hlist : ∀ x ∈ xs, x ∈ level R (max i j) := fun x hx =>
    level_mono R (le_max_right i j) (hjs ((FiniteTuple.mem_elements x xs).mpr hx))
  have heL : ∀ n, e n ∈ level R (max i j) := fun n => level_mono R (le_max_left i j) (he n)
  have heN := fun n => relative_level_subset M R hM hT hR hi (he n)
  refine ⟨max i j,internal_ordinal_max M hi hj,level_mono R (le_max_left i j),
    (φ.realize_iff_prefix _ e).mpr ⟨xs,hlen,hlist,?_⟩⟩
  exact (φ.matrix.absolute _ (level_transitive R _) _ (SigmaFormula.feed_mem xs e _ hlist heL)).mpr
    ((φ.matrix.absolute _ (relativeModel_transitive M R hM) _
      (SigmaFormula.feed_mem xs e _ hxs heN)).mp hmat)

theorem sigmaDefinable_request_bound {M : ZFSet.{u}}
    {P : (ℕ → ZFSet.{u}) → Prop} (h : SigmaDefinable M P)
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ W ∈ M, ∀ x ∈ a, (∃ y ∈ M, P (cons y (cons x e))) →
      ∃ y ∈ W, P (cons y (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  let q := (p.rename bindSlots).rename (liftMap bindSlots)
  have hm : ∀ i, mix e d i ∈ M := by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _
  have hq (x y : ZFSet.{u}) (hx : x ∈ M) (hy : y ∈ M) :
      q.Realize M (cons y (cons x (mix e d))) ↔ P (cons y (cons x e)) := by
    dsimp only [q]
    rw [SigmaFormula.realize_rename]
    have eq : (fun n => cons y (cons x (mix e d)) (liftMap bindSlots n)) =
        cons y (mix (cons x e) d) := by
      funext n; cases n with
      | zero => rfl
      | succ n => exact congrFun (bind_mix x e d) n
    rw [eq,SigmaFormula.realize_rename]
    change p.Realize M (cons y (mix (cons x e) d) ∘ bindSlots) ↔ _
    rw [bind_mix]
    exact hp _ (by
      intro i
      rcases i with _ | i
      · exact hy
      rcases i with _ | i
      · exact hx
      exact he i)
  obtain ⟨W,hW,hw⟩ := internal_sigma_request_bound M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice q (mix e d) hm ha
  refine ⟨W,hW,?_⟩
  intro x hx hxy
  have hxM := hM a ha x hx
  obtain ⟨y,hy,hqxy⟩ := hw x hx (by
    obtain ⟨y,hy,hxy⟩ := hxy
    exact ⟨y,hy,(hq x y hxM hy).mpr hxy⟩)
  exact ⟨y,hy,(hq x y hxM (hM W hW y hy)).mp hqxy⟩

theorem relative_sigma_request_definable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (φ : SigmaFormula) :
    SigmaDefinable M (fun e => (e 0).IsOrdinal ∧ e 2 ⊆ stage R (e 0) ∧
      φ.Realize (stage R (e 0)) (cons (e 1) (fun i => e (i+3)))) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  let v : ℕ → ℕ := fun n => match n with | 0 => 4 | k+1 => 2*(k+4)
  have hs : Definable M (fun e => φ.Realize (e 0) (cons (e 2) (fun i => e (i+4)))) := by
    refine ⟨setBounded (fromSigma φ) 0 v,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e
    rw [setBounded_eval,show mix e (fun _ => ZFSet.omega) 0 = e 0 from rfl,sigma_sat]
    have eq : (fun i => mix e (fun _ => ZFSet.omega) (v i)) =
        cons (e 2) (fun i => e (i+4)) := by
      funext i; cases i with
      | zero => exact mix_even e (fun _ => ZFSet.omega) 2
      | succ i => simp [v]
    rw [eq]
  have h := (stage_sigmaDefinable M R hM hT hR).and
    (((ordinal_definable C 1).toSigma hM).and
      (((SentenceCoding.defSubset C 3 0).toSigma hM).and (hs.toSigma hM)))
  apply h.existsSet.congr
  intro e he
  change (∃ A ∈ M, A = stage R (e 0) ∧ (e 0).IsOrdinal ∧ e 2 ⊆ A ∧
    φ.Realize A (cons (e 1) (fun i => e (i+3)))) ↔ _
  constructor
  · rintro ⟨A,_,rfl,ho,ht,hφ⟩; exact ⟨ho,ht,hφ⟩
  · rintro ⟨ho,ht,hφ⟩
    exact ⟨_,stage_mem M R (e 0) hM hT hR (he 0),rfl,ho,ht,hφ⟩

end TuringRigidity.RelativeConstructible

end OAI
