/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalNameValidity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.NameValidity
public import LeanPool.TuringConeRigidity.SetModels.InternalContainer

/-!
# Internal Name Validity
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.NameValidity
open RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

namespace Code

/-- A sigma formula requesting a transitive domain and a certificate that `x` is a valid name
code. -/
def valid (c x : ℕ) : SigmaFormula := .existsSet (.existsSet (.bounded
  (.conj (.transitive 1) (.conj (.member (x+2) 1)
    (.conj (certificate 1 (c+2) 0) (.member (x+2) 0))))))
end Code

theorem realize_valid (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (c x : ℕ) :
    (Code.valid c x).Realize M e ↔
      ∃ a : Name (Conditions (e c)), a.encode (label (e c)) = e x := by
  have matrix (d h : ZFSet.{u}) (hd : d ∈ M) (hh : h ∈ M) :
      (Formula.conj (.transitive 1) (.conj (.member (x+2) 1)
        (.conj (Code.certificate 1 (c+2) 0) (.member (x+2) 0)))).Realize M
          (cons h (cons d e)) ↔
        Transitive d ∧ e x ∈ d ∧ Certificate d (e c) h ∧ e x ∈ h := by
    rw [Formula.absolute _ M hM _ (by
      intro i
      rcases i with _ | i
      · exact hh
      rcases i with _ | i
      · exact hd
      exact he i)]
    simp only [Formula.Eval,Formula.eval_transitive,Code.eval_certificate,cons_zero,cons_succ]
  change (∃ d ∈ M, ∃ h ∈ M, _) ↔ _
  constructor
  · rintro ⟨d,hd,h,hh,hφ⟩
    obtain ⟨_,_,hcert,hx⟩ := (matrix d h hd hh).mp hφ
    exact hcert.decode _ hx
  · rintro ⟨a,ha⟩
    obtain ⟨d,hd,hdT,hxd⟩ := internal_transitive_container M hM hP hU hS hR hI (he x)
    obtain ⟨h,hh,hcert⟩ := internal_certificate M hM hU hPow hS hd (he c)
    exact ⟨d,hd,h,hh,(matrix d h hd hh).mpr
      ⟨hdT,hxd,hcert,(hcert.correct hdT hxd).mpr ⟨a,ha⟩⟩⟩

end TuringRigidity.NameValidity

end OAI
