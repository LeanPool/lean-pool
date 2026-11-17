/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/FullSetForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory
public import LeanPool.TuringConeRigidity.SetModels.ElementarySatisfaction

/-!
# Full Set Forcing
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FullSetForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
open ElementaryModel SentenceForm BoundedForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

/-- Forcing for full set-theoretic sentences, with quantified names restricted to codes in
`M`. -/
def Forces (M : ZFSet.{u}) (e : ℕ → Name (Conditions c)) : SentenceForm → Conditions c → Prop
  | .equal i j, p => EqForces (e i) (e j) p
  | .member i j, p => MemForces (e i) (e j) p
  | .conj φ ψ, p => Forces M e φ p ∧ Forces M e ψ p
  | .neg φ, p => ∀ q, q ≤ p → ¬ Forces M e φ q
  | .ex φ, p => ∃ a : Name (Conditions c), a.encode (label c) ∈ M ∧ Forces M (push a e) φ p

theorem forces_mono (M : ZFSet.{u}) (φ : SentenceForm) (e : ℕ → Name (Conditions c))
    {p q : Conditions c} (hqp : q ≤ p) (h : Forces M e φ p) : Forces M e φ q := by
  induction φ generalizing e with
  | equal i j => exact eq_mono _ _ hqp h
  | member i j => exact mem_mono _ _ hqp h
  | conj φ ψ ihφ ihψ => exact ⟨ihφ _ h.1,ihψ _ h.2⟩
  | neg φ ih => exact fun r hr => h r (hr.trans hqp)
  | ex φ ih => obtain ⟨a,ha,hf⟩ := h; exact ⟨a,ha,ih _ hf⟩

/-- Full set-theoretic formula encoding the forcing relation for a sentence. -/
noncomputable def code : SentenceForm → ℕ → ℕ → ℕ → (ℕ → ℕ) → SentenceForm
  | .equal i j, ci,oi,pi,v => fromSigma (SigmaCode.forcing (.bounded (.equal i j)) ci oi pi v)
  | .member i j, ci,oi,pi,v => fromSigma (SigmaCode.forcing (.bounded (.member i j)) ci oi pi v)
  | .conj φ ψ, ci,oi,pi,v => .conj (code φ ci oi pi v) (code ψ ci oi pi v)
  | .neg φ, ci,oi,pi,v => all (imp (.member 0 (ci+1))
      (imp (fromBounded (Formula.pairMem 0 (pi+1) (oi+1)))
        (.neg (code φ (ci+1) (oi+1) 0 (fun i => v i+1)))))
  | .ex φ, ci,oi,pi,v => .ex (.conj (fromSigma (NameValidity.Code.valid (ci+1) 0))
      (code φ (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1))))

theorem realize_code (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {o : ZFSet.{u}}
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SentenceForm) (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (henv : ∀ i, env i ∈ M)
    (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (code φ ci oi pi v).Sat (M : Set ZFSet) env ↔ Forces M e φ p := by
  have hS := hT.separation.finitePrefix.bounded
  have hR := hT.replacement.finitePrefix
  induction φ generalizing e p env ci oi pi v with
  | equal i j =>
    exact (sigma_sat _ M env).trans (realize_sigmaForcing M hM hT.pairing hT.union hT.powerSet hS hR
      hT.infinity ho (.bounded (.equal i j)) e p env henv ci oi pi v hc ho' hp hv)
  | member i j =>
    exact (sigma_sat _ M env).trans (realize_sigmaForcing M hM hT.pairing hT.union hT.powerSet hS hR
      hT.infinity ho (.bounded (.member i j)) e p env henv ci oi pi v hc ho' hp hv)
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e p env henv ci oi pi v hc ho' hp hv)
      (ihψ e p env henv ci oi pi v hc ho' hp hv)
  | neg φ ih =>
    have hcM : c ∈ M := hc ▸ henv ci
    have pair (q : Conditions c) :
        (fromBounded (Formula.pairMem 0 (pi+1) (oi+1))).Sat
          (M : Set ZFSet) (cons (label c q) env) ↔ q ≤ p := by
      rw [bounded_sat,Formula.absolute _ M hM _ (by
        intro i
        cases i
        · exact hM c hcM _ (label_mem c q)
        · exact henv _)]
      simp only [Formula.eval_pairMem,cons_zero,cons_succ,hp,ho']
      exact ho q p
    have sub (q : Conditions c) := ih e q (cons (label c q) env)
      (by
        intro i
        cases i
        · exact hM c hcM _ (label_mem c q)
        · exact henv _)
      (ci+1) (oi+1) 0 (fun i => v i+1) hc ho' rfl hv
    simp only [code,sat_all,sat_imp,Sat,cons_zero,cons_succ,hc]
    constructor
    · intro h q hq hf
      exact h _ (hM c hcM _ (label_mem c q)) (label_mem c q) ((pair q).mpr hq) ((sub q).mpr hf)
    · intro h x _ hx hxp hf
      obtain ⟨q,rfl⟩ := label_surjective c hx
      exact h q ((pair q).mp hxp) ((sub q).mp hf)
  | ex φ ih =>
    have henv' (x : ZFSet.{u}) (hx : x ∈ M) : ∀ i, cons x env i ∈ M := by
      intro i
      cases i
      · exact hx
      · exact henv _
    have valid (x : ZFSet.{u}) (hx : x ∈ M) :
        (fromSigma (NameValidity.Code.valid (ci+1) 0)).Sat (M : Set ZFSet) (cons x env) ↔
          ∃ a : Name (Conditions c), a.encode (label c) = x := by
      rw [sigma_sat]
      have h := NameValidity.realize_valid M hM hT.pairing hT.union hT.powerSet hS hR hT.infinity
        (cons x env) (henv' x hx) (ci+1) 0
      change (NameValidity.Code.valid (ci+1) 0).Realize M (cons x env) ↔
        (∃ a : Name (Conditions (env ci)), a.encode (label (env ci)) = x) at h
      rw [hc] at h
      exact h
    have sub (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :=
      ih (push a e) p (cons (a.encode (label c)) env) (henv' _ ha)
        (ci+1) (oi+1) (pi+1) (push 0 (fun i => v i+1)) hc ho' hp
        (by intro i; cases i <;> simp only [push_zero,push_succ,cons_zero,cons_succ,hv])
    simp only [code,Sat]
    constructor
    · rintro ⟨x,hx,hvalid,hforce⟩
      obtain ⟨a,rfl⟩ := (valid x hx).mp hvalid
      exact ⟨a,hx,(sub a hx).mp hforce⟩
    · rintro ⟨a,ha,hforce⟩
      exact ⟨_,ha,(valid _ ha).mpr ⟨a,rfl⟩,(sub a ha).mpr hforce⟩

end TuringRigidity.FullSetForcing

end OAI
