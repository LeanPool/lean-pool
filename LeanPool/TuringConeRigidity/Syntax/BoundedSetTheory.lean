/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedSetTheory.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.TransitiveNameModel

/-!
# Bounded Set Theory
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open Set
open TransitiveNameModel (Transitive)
universe u

inductive Formula where
  | equal (i j : ℕ)
  | member (i j : ℕ)
  | conj (φ ψ : Formula)
  | neg (φ : Formula)
  | existsMem (i : ℕ) (φ : Formula)

def cons (x : ZFSet.{u}) (env : ℕ → ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => x
  | n+1 => env n

@[simp] theorem cons_zero (x : ZFSet.{u}) (env : ℕ → ZFSet.{u}) : cons x env 0 = x := rfl
@[simp] theorem cons_succ (x : ZFSet.{u}) (env : ℕ → ZFSet.{u}) (n : ℕ) :
    cons x env (n+1) = env n := rfl

def Formula.Eval (env : ℕ → ZFSet.{u}) : Formula → Prop
  | .equal i j => env i = env j
  | .member i j => env i ∈ env j
  | .conj φ ψ => Eval env φ ∧ Eval env ψ
  | .neg φ => ¬ Eval env φ
  | .existsMem i φ => ∃ x ∈ env i, Eval (cons x env) φ

def Formula.Realize (M : ZFSet.{u}) (env : ℕ → ZFSet.{u}) : Formula → Prop
  | .equal i j => env i = env j
  | .member i j => env i ∈ env j
  | .conj φ ψ => Realize M env φ ∧ Realize M env ψ
  | .neg φ => ¬ Realize M env φ
  | .existsMem i φ => ∃ x ∈ M, x ∈ env i ∧ Realize M (cons x env) φ

theorem Formula.absolute (φ : Formula) (M : ZFSet.{u}) (hM : Transitive M)
    (env : ℕ → ZFSet.{u}) (he : ∀ i, env i ∈ M) :
    φ.Realize M env ↔ φ.Eval env := by
  induction φ generalizing env with
  | equal => rfl
  | member => rfl
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env he) (ihψ env he)
  | neg φ ih => exact not_congr (ih env he)
  | existsMem i φ ih =>
    constructor
    · rintro ⟨x,hx,hi,hφ⟩
      exact ⟨x,hi,(ih (cons x env) (fun n => by cases n <;> simp [cons,he,hx])).mp hφ⟩
    · rintro ⟨x,hi,hφ⟩
      have hx := hM _ (he i) _ hi
      exact ⟨x,hx,hi,(ih (cons x env) (fun n => by cases n <;> simp [cons,he,hx])).mpr hφ⟩

def Pairing (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∀ b ∈ M, ∃ c ∈ M, ∀ x ∈ M, x ∈ c ↔ x = a ∨ x = b

def Union (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ ∃ y ∈ M, y ∈ a ∧ x ∈ y

def PowerSet (M : ZFSet.{u}) : Prop :=
  ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ ∀ y ∈ M, y ∈ x → y ∈ a

def Separation (M : ZFSet.{u}) : Prop :=
  ∀ (φ : Formula) (env : ℕ → ZFSet.{u}), (∀ i, env i ∈ M) →
    ∀ a ∈ M, ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ φ.Realize M (cons x env)

theorem pair_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ({a,b} : ZFSet.{u}) ∈ M := by
  obtain ⟨c,hc,hcdef⟩ := hP a ha b hb
  have hc' : c = ({a,b} : ZFSet.{u}) := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      exact ZFSet.mem_pair.mpr ((hcdef x (hM c hc x hx)).mp hx)
    · intro hx
      have hx' := ZFSet.mem_pair.mp hx
      have hxM : x ∈ M := hx'.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
      exact (hcdef x hxM).mpr hx'
  exact hc' ▸ hc

theorem singleton_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {a : ZFSet.{u}} (ha : a ∈ M) : ({a} : ZFSet.{u}) ∈ M := by
  simpa using pair_mem M hM hP ha ha

theorem orderedPair_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) : ZFSet.pair a b ∈ M := by
  exact pair_mem M hM hP (singleton_mem M hM hP ha) (pair_mem M hM hP ha hb)

theorem union_mem (M : ZFSet.{u}) (hM : Transitive M) (hU : Union M)
    {a : ZFSet.{u}} (ha : a ∈ M) : ZFSet.sUnion a ∈ M := by
  obtain ⟨b,hb,hbdef⟩ := hU a ha
  have he : b = ZFSet.sUnion a := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨y,_,hy,hxy⟩ := (hbdef x (hM b hb x hx)).mp hx
      exact ZFSet.mem_sUnion.mpr ⟨y,hy,hxy⟩
    · intro hx
      obtain ⟨y,hy,hxy⟩ := ZFSet.mem_sUnion.mp hx
      have hyM := hM a ha y hy
      exact (hbdef x (hM y hyM x hxy)).mpr ⟨y,hyM,hy,hxy⟩
  exact he ▸ hb

theorem internal_power (M : ZFSet.{u}) (hM : Transitive M) (hP : PowerSet M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ b ∈ M, ∀ x, x ∈ b ↔ x ∈ M ∧ x ⊆ a := by
  obtain ⟨b,hb,hbdef⟩ := hP a ha
  refine ⟨b,hb,fun x => ?_⟩
  constructor
  · intro hx
    have hxM := hM b hb x hx
    exact ⟨hxM,fun y hy => (hbdef x hxM).mp hx y (hM x hxM y hy) hy⟩
  · rintro ⟨hxM,hsub⟩
    exact (hbdef x hxM).mpr (fun y _ hy => hsub hy)

theorem sep_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    (φ : Formula) (env : ℕ → ZFSet.{u}) (he : ∀ i, env i ∈ M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => φ.Eval (cons x env)) a ∈ M := by
  obtain ⟨b,hb,hbdef⟩ := hS φ env he a ha
  have heq : b = ZFSet.sep (fun x => φ.Eval (cons x env)) a := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      have hxM := hM b hb x hx
      obtain ⟨hxa,hφ⟩ := (hbdef x hxM).mp hx
      refine ZFSet.mem_sep.mpr ⟨hxa,?_⟩
      exact (φ.absolute M hM _ (fun n => by cases n <;> simp [cons,he,hxM])).mp hφ
    · intro hx
      obtain ⟨hxa,hφ⟩ := ZFSet.mem_sep.mp hx
      have hxM := hM a ha x hxa
      apply (hbdef x hxM).mpr
      exact ⟨hxa,(φ.absolute M hM _ (fun n => by cases n <;> simp [cons,he,hxM])).mpr hφ⟩
  exact heq ▸ hb

namespace Formula

def disj (φ ψ : Formula) : Formula := .neg (.conj (.neg φ) (.neg ψ))
def allMem (i : ℕ) (φ : Formula) : Formula := .neg (.existsMem i (.neg φ))

@[simp] theorem eval_disj (φ ψ : Formula) (env : ℕ → ZFSet.{u}) :
    (disj φ ψ).Eval env ↔ φ.Eval env ∨ ψ.Eval env := by
  classical
  simp only [disj,Eval]
  constructor
  · intro h
    by_cases hφ : φ.Eval env
    · exact Or.inl hφ
    · exact Or.inr (Classical.byContradiction (fun hψ => h ⟨hφ,hψ⟩))
  · intro h hn
    exact h.elim hn.1 hn.2

@[simp] theorem eval_allMem (i : ℕ) (φ : Formula) (env : ℕ → ZFSet.{u}) :
    (allMem i φ).Eval env ↔ ∀ x ∈ env i, φ.Eval (cons x env) := by
  classical
  simp [allMem,Eval]

def singleton (s a : ℕ) : Formula :=
  .conj (.member a s) (allMem s (.equal 0 (a+1)))

def unorderedPair (s a b : ℕ) : Formula :=
  .conj (.member a s) (.conj (.member b s)
    (allMem s (disj (.equal 0 (a+1)) (.equal 0 (b+1)))))

@[simp] theorem eval_singleton (s a : ℕ) (env : ℕ → ZFSet.{u}) :
    (singleton s a).Eval env ↔ env s = ({env a} : ZFSet.{u}) := by
  simp only [singleton,Eval,eval_allMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨ha,hall⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_singleton]
    exact ⟨hall x,fun hx => hx ▸ ha⟩
  · intro h
    simp [h]

@[simp] theorem eval_unorderedPair (s a b : ℕ) (env : ℕ → ZFSet.{u}) :
    (unorderedPair s a b).Eval env ↔ env s = ({env a,env b} : ZFSet.{u}) := by
  simp only [unorderedPair,Eval,eval_allMem,eval_disj,cons_zero,cons_succ]
  constructor
  · rintro ⟨ha,hb,hall⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_pair]
    exact ⟨hall x,fun hx => hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb)⟩
  · intro h
    simp [h]

def orderedPair (s a b : ℕ) : Formula :=
  .conj (allMem s (disj (singleton 0 (a+1)) (unorderedPair 0 (a+1) (b+1))))
    (.conj (.existsMem s (singleton 0 (a+1)))
      (.existsMem s (unorderedPair 0 (a+1) (b+1))))

@[simp] theorem eval_orderedPair (s a b : ℕ) (env : ℕ → ZFSet.{u}) :
    (orderedPair s a b).Eval env ↔ env s = ZFSet.pair (env a) (env b) := by
  simp only [orderedPair,Eval,eval_allMem,eval_disj,eval_singleton,
    eval_unorderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨hall,⟨x,hx,hxa⟩,y,hy,hyab⟩
    apply ZFSet.ext
    intro z
    change z ∈ env s ↔ z ∈ ({({env a} : ZFSet.{u}),({env a,env b} : ZFSet.{u})} : ZFSet.{u})
    rw [ZFSet.mem_pair]
    exact ⟨hall z,fun hz => hz.elim (fun h => h ▸ hxa ▸ hx) (fun h => h ▸ hyab ▸ hy)⟩
  · intro h
    rw [h]
    simp [ZFSet.pair]

def pairMem (a b s : ℕ) : Formula := .existsMem s (orderedPair 0 (a+1) (b+1))

@[simp] theorem eval_pairMem (a b s : ℕ) (env : ℕ → ZFSet.{u}) :
    (pairMem a b s).Eval env ↔ ZFSet.pair (env a) (env b) ∈ env s := by
  simp [pairMem,Eval]
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
