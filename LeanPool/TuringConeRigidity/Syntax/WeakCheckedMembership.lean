/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/WeakCheckedMembership.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedMembershipSeparation
public import LeanPool.TuringConeRigidity.Syntax.WeakCheckedValue
public import LeanPool.TuringConeRigidity.CohenForcing.WeakForcingCode

/-!
# Weak Checked Membership
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem checkedMembership_spec_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
  (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {o : ZFSet.{u}} (ho : ∀ r s : Conditions c,
      ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (p : Conditions c) (x : ZFSet.{u})
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (h0 : e 0 = x) (h1 : e 1 = c) (h2 : e 2 = o) (h3 : e 3 = label c p)
    (h4 : e 4 = t.encode (label c)) (h5 : e 5 = label c ⊤) :
    checkedMembershipFormula.Sat (M : Set ZFSet) e ↔ MemForces (Name.check x) t p := by
  let v : ℕ → ℕ := fun i => match i with | 0 => 0 | _ => 5
  let k : ℕ → ℕ := fun i => match i with | 0 => 0 | 1 => 1 | _ => 6
  let names : ℕ → Name (Conditions c) := fun i => match i with | 0 => Name.check x | _ => t
  have hc : c ∈ M := h1 ▸ he 1
  have hx : x ∈ M := h0 ▸ he 0
  have hcheck : (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hP hU hPow
      hS.bounded hR hI hc hx
  have henv (z : ZFSet.{u}) (hz : z ∈ M) : ∀ i, cons z e i ∈ M := by
    intro i
    cases i
    · exact hz
    · exact he _
  have checked (z : ZFSet.{u}) (hz : z ∈ M) :
      (checkedValueFormula.rename k).Sat (M : Set ZFSet) (cons z e) ↔
        z = (Name.check x : Name (Conditions c)).encode (label c) := by
    rw [sat_rename,checkedValue_spec_without_choice M hM hP hU hPow hS hR hI _ (fun i => henv z hz
      (k i))]
    simp only [k,cons_zero,cons_succ,h0,h5,encode_check]
  have forcing (z : ZFSet.{u}) (hz : z ∈ M)
      (hzv : z = (Name.check x : Name (Conditions c)).encode (label c)) :
      (code (.member 0 1) 2 3 4 v).Sat (M : Set ZFSet) (cons z e) ↔
        MemForces (Name.check x) t p := by
    exact realize_code_without_choice M hM hP hU hPow hS hR hI ho (.member 0 1) names p (cons z e)
      (henv z hz)
      2 3 4 v h1 h2 h3 (by
        intro i
        cases i
        · exact hzv
        · exact h4)
  change (∃ z ∈ M, (checkedValueFormula.rename k).Sat _ (cons z e) ∧ _) ↔ _
  constructor
  · rintro ⟨z,hz,hzv,hf⟩
    exact (forcing z hz ((checked z hz).mp hzv)).mp hf
  · intro hf
    exact ⟨_,hcheck,(checked _ hcheck).mpr rfl,(forcing _ hcheck rfl).mpr hf⟩

theorem internal_forced_members_without_choice (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing
  M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (hc : c ∈ M) {o a : ZFSet.{u}}
    (hoM : o ∈ M) (ha : a ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (t : Name (Conditions c)) (ht : t.encode (label c) ∈ M) (p : Conditions c) :
    ∃ b ∈ M, ∀ x, x ∈ b ↔ x ∈ a ∧ MemForces (Name.check x) t p := by
  let e := cons c (cons o (cons (label c p) (cons (t.encode (label c)) (fun _ => label c ⊤))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact hc
    · exact hoM
    · exact hM c hc _ (label_mem c p)
    · exact ht
    · exact hM c hc _ (label_mem c ⊤)
  obtain ⟨b,hb,hdef⟩ := hS checkedMembershipSigma e he a ha
  have spec (x : ZFSet.{u}) (hx : x ∈ M) := checkedMembership_spec_without_choice M hM hP hU hPow
    hS hR hI ho t p x
    (cons x e) (by
      intro i
      cases i
      · exact hx
      · exact he _) rfl rfl rfl rfl rfl rfl
  refine ⟨b,hb,fun x => ?_⟩
  constructor
  · intro hx
    have hxM := hM b hb x hx
    obtain ⟨hxa,hf⟩ := (hdef x hxM).mp hx
    exact ⟨hxa,(spec x hxM).mp ((checkedMembershipSigma_spec M _).mp hf)⟩
  · rintro ⟨hxa,hf⟩
    have hxM := hM a ha x hxa
    exact (hdef x hxM).mpr ⟨hxa,(checkedMembershipSigma_spec M _).mpr ((spec x hxM).mpr hf)⟩

end TuringRigidity.FullSetForcing

end OAI
