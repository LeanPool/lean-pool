/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/BoundedForcingCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.BoundedForcing
public import LeanPool.TuringConeRigidity.Syntax.AtomicCertificate

/-!
# Bounded Forcing Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u

def code : BoundedSetTheory.Formula → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → BoundedSetTheory.Formula
  | .equal i j, _d,_c,k,_o,f,v,p => AtomicFormula.triple k f (v i) (v j) p
  | .member i j, d,c,k,o,f,v,p => AtomicFormula.membership d c k o f (v i) (v j) p
  | .conj φ ψ, d,c,k,o,f,v,p => .conj (code φ d c k o f v p) (code ψ d c k o f v p)
  | .neg φ, d,c,k,o,f,v,p => Formula.allMem c
      (Formula.imp (Formula.pairMem 0 (p+1) (o+1))
        (.neg (code φ (d+1) (c+1) (k+1) (o+1) (f+1) (fun i => v i+1) 0)))
  | .existsMem i φ, d,c,k,o,f,v,p => .existsMem d (.existsMem (c+1)
      (.conj (Formula.pairMem 1 0 (v i+2)) (.conj (Formula.pairMem (p+2) 0 (o+2))
        (code φ (d+2) (c+2) (k+2) (o+2) (f+2) (push 1 (fun i => v i+2)) (p+2)))))

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem eval_code (φ : BoundedSetTheory.Formula) {d o f : ZFSet.{u}} (hd : Transitive d)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hf : Graph d c o f) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ d) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (di ci ki oi fi : ℕ) (v : ℕ → ℕ) (pi : ℕ)
    (slots : env di = d ∧ env ci = c ∧ env ki = ZFSet.prod d d ∧ env oi = o ∧ env fi = f ∧ env pi
      = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (code φ di ci ki oi fi v pi).Eval env ↔ Forces e φ p := by
  induction φ generalizing e p env di ci ki oi fi v pi with
  | equal i j =>
    simp only [code,AtomicFormula.eval_triple,slots.2.2.1,slots.2.2.2.2.1,slots.2.2.2.2.2,hv,Forces]
    exact (triple_pair (he i) (he j)).trans (hf.correct hd ho _ _ (he i) (he j) p)
  | member i j =>
    exact eval_membership hd ho hf _ _ (he i) (he j) p env di ci ki oi fi (v i) (v j) pi
      ⟨slots.1,slots.2.1,slots.2.2.1,slots.2.2.2.1,slots.2.2.2.2.1,hv i,hv j,slots.2.2.2.2.2⟩
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e he p env di ci ki oi fi v pi slots hv)
      (ihψ e he p env di ci ki oi fi v pi slots hv)
  | neg φ ih =>
    simp only [code,Formula.eval_allMem,Formula.eval_imp,Formula.eval_pairMem,Formula.Eval,
      cons_zero,cons_succ,slots.2.1,slots.2.2.2.1,slots.2.2.2.2.2]
    have sub (q : Conditions c) := ih e he q (cons (label c q) env)
      (di+1) (ci+1) (ki+1) (oi+1) (fi+1) (fun i => v i+1) 0
      ⟨slots.1,slots.2.1,slots.2.2.1,slots.2.2.2.1,slots.2.2.2.2.1,rfl⟩ hv
    constructor
    · intro h q hq hforce
      exact h _ (label_mem c q) ((ho q p).mpr hq) ((sub q).mpr hforce)
    · intro h q hq hqp hforce
      obtain ⟨r,rfl⟩ := label_surjective c hq
      exact h r ((ho r p).mp hqp) ((sub r).mp hforce)
  | existsMem i φ ih =>
    simp only [code,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,
      slots.1,slots.2.1,slots.2.2.2.1,slots.2.2.2.2.2,hv]
    have hej (j) : ∀ n, (push ((e i).child j) e n).encode (label c) ∈ d := by
      intro n
      cases n with
      | zero =>
        exact names_childClosed d c hd (e i) (he i) _ (child_relation (e i) j)
      | succ n => exact he n
    have sub (j) (s : Conditions c) := ih (push ((e i).child j) e) (hej j) p
      (cons (label c s) (cons (((e i).child j).encode (label c)) env))
      (di+2) (ci+2) (ki+2) (oi+2) (fi+2) (push 1 (fun n => v n+2)) (pi+2)
      ⟨slots.1,slots.2.1,slots.2.2.1,slots.2.2.2.1,slots.2.2.2.2.1,slots.2.2.2.2.2⟩
      (by intro n; cases n <;> simp only [push_zero,push_succ,cons_zero,cons_succ,hv])
    constructor
    · rintro ⟨x,hx,s,hs,hxs,hps,hφ⟩
      obtain ⟨j,hj,hjs⟩ := (pair_mem_encode _ _ _ _).mp hxs
      subst x
      subst s
      exact ⟨j,(ho p ((e i).tag j)).mp hps,(sub j ((e i).tag j)).mp hφ⟩
    · rintro ⟨j,hj,hφ⟩
      exact ⟨_,hej j 0,_,label_mem c ((e i).tag j),
        (pair_mem_encode _ _ _ _).mpr ⟨j,rfl,rfl⟩,(ho p ((e i).tag j)).mpr hj,
        (sub j ((e i).tag j)).mpr hφ⟩

end TuringRigidity.BoundedForcing

end OAI
