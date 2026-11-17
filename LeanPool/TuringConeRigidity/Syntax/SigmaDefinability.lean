/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/SigmaDefinability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedCertificate
public import LeanPool.TuringConeRigidity.SetModels.InternalNameValidity
public import LeanPool.TuringConeRigidity.Syntax.SigmaSyntax
public import LeanPool.TuringConeRigidity.CohenForcing.SigmaForcing

/-!
# Sigma Definability
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u

namespace SigmaCode

/-- A sigma formula encoding forcing through bounded certificates and valid existential name
witnesses. -/
def forcing : SigmaFormula → ℕ → ℕ → ℕ → (ℕ → ℕ) → SigmaFormula
  | .bounded φ, ci,oi,pi,v => CertificateCode.certificate φ ci oi pi v
  | .existsSet φ, ci,oi,pi,v => .existsSet
      (SigmaFormula.conj (NameValidity.Code.valid (ci+1) 0)
        (forcing φ (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1))))
end SigmaCode

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem realize_sigmaForcing (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {o : ZFSet.{u}}
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (henv : ∀ i, env i ∈ M)
    (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (SigmaCode.forcing φ ci oi pi v).Realize M env ↔ SigmaForces M e φ p := by
  induction φ generalizing e env ci oi pi v with
  | bounded φ =>
    exact realize_boundedCertificate M hM hP hU hPow hS hR hI ho φ e p env henv ci oi pi v hc ho'
      hp hv
  | existsSet φ ih =>
    have henv' (x : ZFSet.{u}) (hx : x ∈ M) : ∀ i, cons x env i ∈ M := by
      intro i
      cases i with
      | zero => simpa only [cons_zero] using hx
      | succ i => simpa only [cons_succ] using henv i
    have valid (x : ZFSet.{u}) (hx : x ∈ M) :
        (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
          ∃ a : Name (Conditions c), a.encode (label c) = x := by
      have h := NameValidity.realize_valid M hM hP hU hPow hS hR hI
        (cons x env) (henv' x hx) (ci+1) 0
      change (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
        (∃ a : Name (Conditions (env ci)), a.encode (label (env ci)) = x) at h
      rw [hc] at h
      exact h
    have sub (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :=
      ih (push a e) (cons (a.encode (label c)) env) (henv' _ ha)
        (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1)) hc ho' hp
        (by intro i; cases i <;> simp only [push_zero,push_succ,cons_zero,cons_succ,hv])
    simp only [SigmaCode.forcing,SigmaFormula.Realize,SigmaFormula.realize_conj]
    constructor
    · rintro ⟨x,hx,hvalid,hforce⟩
      obtain ⟨a,rfl⟩ := (valid x hx).mp hvalid
      exact ⟨a,hx,(sub a hx).mp hforce⟩
    · rintro ⟨a,ha,hforce⟩
      exact ⟨_,ha,(valid _ ha).mpr ⟨a,rfl⟩,(sub a ha).mpr hforce⟩

end TuringRigidity.BoundedForcing

end OAI
