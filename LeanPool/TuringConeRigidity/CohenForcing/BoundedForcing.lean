/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/BoundedForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.AtomicTruth
public import LeanPool.TuringConeRigidity.Syntax.BoundedRelations

/-!
# Bounded Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames CountableForcing AtomicForcing
open BoundedSetTheory (Formula)
universe u
variable {P : Type u} [Preorder P]

def push {α : Sort*} (x : α) (e : ℕ → α) : ℕ → α
  | 0 => x
  | n+1 => e n

@[simp] theorem push_zero {α : Sort*} (x : α) (e : ℕ → α) : push x e 0 = x := rfl
@[simp] theorem push_succ {α : Sort*} (x : α) (e : ℕ → α) (n : ℕ) : push x e (n+1) = e n := rfl

omit [Preorder P] in
theorem child_relation (a : Name P) (i : a.arity) : Name.Child (a.child i) a := by
  cases a
  exact ⟨i,rfl⟩

def Forces (e : ℕ → Name P) : Formula → P → Prop
  | .equal i j, p => EqForces (e i) (e j) p
  | .member i j, p => MemForces (e i) (e j) p
  | .conj φ ψ, p => Forces e φ p ∧ Forces e ψ p
  | .neg φ, p => ∀ q, q ≤ p → ¬ Forces e φ q
  | .existsMem i φ, p => ∃ j, p ≤ (e i).tag j ∧ Forces (push ((e i).child j) e) φ p

theorem forces_mono (φ : Formula) (e : ℕ → Name P) {p q : P} (hqp : q ≤ p)
    (h : Forces e φ p) : Forces e φ q := by
  induction φ generalizing e with
  | equal i j => exact eq_mono _ _ hqp h
  | member i j => exact mem_mono _ _ hqp h
  | conj φ ψ ihφ ihψ => exact ⟨ihφ e h.1,ihψ e h.2⟩
  | neg φ ih => exact fun r hr => h r (hr.trans hqp)
  | existsMem i φ ih =>
    obtain ⟨j,hj,hf⟩ := h
    exact ⟨j,hqp.trans hj,ih _ hf⟩

def Decision (e : ℕ → Name P) (φ : Formula) : Set P := {p | Forces e φ p ∨ Forces e (.neg φ) p}

theorem decision_dense (e : ℕ → Name P) (φ : Formula) : Dense (Decision e φ) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ Forces e φ q
  · obtain ⟨q,hq,hf⟩ := h
    exact ⟨q,hq,Or.inl hf⟩
  · exact ⟨p,le_rfl,Or.inr (fun q hq hf => h ⟨q,hq,hf⟩)⟩

def Generic (N : Set (Name P)) (G : GenericFilter P) : Prop :=
  ∀ φ e, (∀ i, e i ∈ N) → ∃ p ∈ G.carrier, p ∈ Decision e φ

theorem truth {N : Set (Name P)} (hN : ChildClosed N) (G : GenericFilter P)
    (hA : AtomicForcing.Generic N G) (hG : Generic N G) (φ : Formula)
    (e : ℕ → Name P) (he : ∀ i, e i ∈ N) :
    φ.Eval (fun i => (e i).val G.carrier) ↔ ∃ p ∈ G.carrier, Forces e φ p := by
  induction φ generalizing e with
  | equal i j => exact eq_truth hN G hA _ _ (he i) (he j)
  | member i j => exact mem_truth hN G hA _ _ (he i) (he j)
  | conj φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hφ,hψ⟩
      obtain ⟨p,hp,hfp⟩ := (ihφ e he).mp hφ
      obtain ⟨q,hq,hfq⟩ := (ihψ e he).mp hψ
      obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact ⟨r,hr,forces_mono φ e hrp hfp,forces_mono ψ e hrq hfq⟩
    · rintro ⟨p,hp,hφ,hψ⟩
      exact ⟨(ihφ e he).mpr ⟨p,hp,hφ⟩,(ihψ e he).mpr ⟨p,hp,hψ⟩⟩
  | neg φ ih =>
    constructor
    · intro hn
      obtain ⟨p,hp,hf | hf⟩ := hG φ e he
      · exact False.elim (hn ((ih e he).mpr ⟨p,hp,hf⟩))
      · exact ⟨p,hp,hf⟩
    · rintro ⟨p,hp,hn⟩ hv
      obtain ⟨q,hq,hf⟩ := (ih e he).mp hv
      obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact hn r hrp (forces_mono φ e hrq hf)
  | existsMem i φ ih =>
    have hej (j) : ∀ n, push ((e i).child j) e n ∈ N := by
      intro n
      cases n with
      | zero =>
        exact hN (e i) (he i) _ (child_relation (e i) j)
      | succ n => exact he n
    have env (j) : (fun n => (push ((e i).child j) e n).val G.carrier) =
        BoundedSetTheory.cons ((e i).child j |>.val G.carrier) (fun n => (e n).val G.carrier) := by
      funext n
      cases n <;> rfl
    constructor
    · rintro ⟨x,hx,hφ⟩
      obtain ⟨j,hj,hxj⟩ := ((e i).mem_val_children G.carrier x).mp hx
      subst x
      rw [←env j] at hφ
      obtain ⟨p,hp,hf⟩ := (ih _ (hej j)).mp hφ
      obtain ⟨q,hq,hqp,hqj⟩ := G.directed hp hj
      exact ⟨q,hq,j,hqj,forces_mono φ _ hqp hf⟩
    · rintro ⟨p,hp,j,hj,hf⟩
      refine ⟨_,((e i).mem_val_children G.carrier _).mpr ⟨j,G.upper hj hp,rfl⟩,?_⟩
      rw [←env j]
      exact (ih _ (hej j)).mpr ⟨p,hp,hf⟩

end TuringRigidity.BoundedForcing

end OAI
