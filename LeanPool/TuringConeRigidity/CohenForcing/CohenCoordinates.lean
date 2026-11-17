/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenCoordinates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenSymmetry

/-!
# Cohen Coordinates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenCoordinates
open Set CohenSymmetry
universe u v
variable {ι : Type u} {κ : Type v}

def restrict (f : κ ↪ ι) (p : Condition ι) : Condition κ where
  val i := p.val (f i)
  finite := p.finite.preimage_embedding f

theorem restrict_mono (f : κ ↪ ι) {p q : Condition ι} (h : p ≤ q) :
    restrict f p ≤ restrict f q := fun i b hb => h (f i) b hb

def reindex (e : ι ≃ κ) : Condition ι ≃o Condition κ where
  toFun := restrict e.symm.toEmbedding
  invFun := restrict e.toEmbedding
  left_inv p := by ext i; simp [restrict]
  right_inv p := by ext i; simp [restrict]
  map_rel_iff' := by
    intro p q
    constructor
    · intro h i b hb
      simpa [restrict] using h (e i) b (by simpa [restrict] using hb)
    · exact restrict_mono _

def combine (p : Condition ι) (q : Condition κ) : Condition (ι ⊕ κ) where
  val := Sum.elim p.val q.val
  finite := (p.finite.image Sum.inl |>.union (q.finite.image Sum.inr)).subset (by
    intro i hi
    cases i with
    | inl i => exact Or.inl ⟨i,hi,rfl⟩
    | inr i => exact Or.inr ⟨i,hi,rfl⟩)

def sumIso : Condition (ι ⊕ κ) ≃o (Condition ι × Condition κ) where
  toFun p := (restrict ⟨Sum.inl,Sum.inl_injective⟩ p,
    restrict ⟨Sum.inr,Sum.inr_injective⟩ p)
  invFun p := combine p.1 p.2
  left_inv p := by ext i; cases i <;> rfl
  right_inv p := by apply Prod.ext <;> ext i <;> rfl
  map_rel_iff' := by
    intro p q
    constructor
    · rintro ⟨hl,hr⟩ i b hb
      cases i with
      | inl i => exact hl i b hb
      | inr i => exact hr i b hb
    · intro h
      exact ⟨restrict_mono _ h,restrict_mono _ h⟩

noncomputable def partitionIso (S : Set ι) :
    Condition ι ≃o (Condition S × Condition (Sᶜ : Set ι)) := by
  classical
  exact (reindex (Equiv.Set.sumCompl S).symm).trans sumIso

noncomputable def support (p : Condition ι) : Finset ι := p.finite.toFinset

theorem mem_support (p : Condition ι) (i : ι) : i ∈ support p ↔ p.val i ≠ none :=
  p.finite.mem_toFinset

noncomputable def erase (i : ι) (p : Condition ι) : Condition ι := by
  classical
  exact ⟨fun j => if j = i then none else p.val j,
    p.finite.subset (by intro j hj; by_cases h : j = i <;> simp_all)⟩

theorem support_erase [DecidableEq ι] (p : Condition ι) (i : ι) :
    support (erase i p) = (support p).erase i := by
  classical
  ext j
  by_cases h : j = i <;> simp [mem_support,erase,h]

theorem erase_injective_on (i : ι) (b : Bool) :
    Set.InjOn (erase i) {p : Condition ι | p.val i = some b} := by
  intro p hp q hq he
  apply Condition.ext
  funext j
  by_cases h : j = i
  · subst j
    exact hp.trans hq.symm
  · have := congrArg (fun r : Condition ι => r.val j) he
    simpa [erase,h] using this

theorem compatible_of_erase (i : ι) (b : Bool) {p q : Condition ι}
    (hp : p.val i = some b) (hq : q.val i = some b)
    (h : Compatible (erase i p) (erase i q)) : Compatible p q := by
  intro j a c ha hc
  by_cases hj : j = i
  · have hab : a = b := Option.some.inj (ha.symm.trans (hj ▸ hp))
    have hcb : c = b := Option.some.inj (hc.symm.trans (hj ▸ hq))
    exact hab.trans hcb.symm
  · exact h j a c (by simpa [erase,hj] using ha) (by simpa [erase,hj] using hc)

end TuringRigidity.CohenCoordinates

end OAI
