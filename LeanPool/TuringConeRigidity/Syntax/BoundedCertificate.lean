/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedSupport

/-!
# Bounded Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing
universe u

namespace CertificateCode

def slots : ℕ → ℕ → (ℕ → ℕ) → Formula
  | 0, d, _v => .equal d d
  | n+1, d, v => .conj (slots n d v) (.member (v n) d)

theorem eval_slots (n d : ℕ) (v : ℕ → ℕ) (env : ℕ → ZFSet.{u}) :
    (slots n d v).Eval env ↔ ∀ i, i < n → env (v i) ∈ env d := by
  induction n with
  | zero => simp [slots,Formula.Eval]
  | succ n ih =>
    simp only [slots,Formula.Eval,ih]
    constructor
    · rintro ⟨h,hlast⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
      · exact h i hi
      · exact hlast
    · intro h; exact ⟨fun i hi => h i (by omega),h n (by omega)⟩

def matrix (φ : Formula) (ci oi pi : ℕ) (v : ℕ → ℕ) : Formula :=
  .conj (.transitive 2) (.conj (AtomicFormula.product 2 1)
    (.conj (AtomicFormula.graph 2 (ci+3) 1 (oi+3) 0)
      (.conj (slots (bound φ+1) 2 (fun i => v i+3))
        (code φ 2 (ci+3) 1 (oi+3) 0
          (fun i => truncate (bound φ+1) v i+3) (pi+3)))))

def certificate (φ : Formula) (ci oi pi : ℕ) (v : ℕ → ℕ) : SigmaFormula :=
  .existsSet (.existsSet (.existsSet (.bounded (matrix φ ci oi pi v))))
end CertificateCode

variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem eval_certificate_matrix (φ : Formula) (d k f o : ZFSet.{u})
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (CertificateCode.matrix φ ci oi pi v).Eval (cons f (cons k (cons d env))) ↔
      Transitive d ∧ k = ZFSet.prod d d ∧ Graph d c o f ∧
        (∀ i, i < bound φ+1 → (e i).encode (label c) ∈ d) ∧ Forces e φ p := by
  have query (hd : Transitive d) (hk : k = ZFSet.prod d d) (hf : Graph d c o f)
      (hs : ∀ i, i < bound φ+1 → (e i).encode (label c) ∈ d) :
      (code φ 2 (ci+3) 1 (oi+3) 0
        (fun i => truncate (bound φ+1) v i+3) (pi+3)).Eval
          (cons f (cons k (cons d env))) ↔ Forces e φ p := by
    let e' := truncate (bound φ+1) e
    have he' (i) : (e' i).encode (label c) ∈ d := by
      dsimp only [e',truncate]
      split
      · exact hs i (by assumption)
      · exact hs 0 (by omega)
    have ht (i) : env (truncate (bound φ+1) v i) = (e' i).encode (label c) := by
      dsimp only [e',truncate]
      split <;> exact hv _
    exact (eval_code φ hd ho hf e' he' p (cons f (cons k (cons d env)))
      2 (ci+3) 1 (oi+3) 0 (fun i => truncate (bound φ+1) v i+3) (pi+3)
      ⟨rfl,hc,hk,ho',rfl,hp⟩ ht).trans
      (forces_congr φ e' e (fun i hi => ite_eq_left (by omega)) p)
  simp only [CertificateCode.matrix,Formula.Eval,Formula.eval_transitive,
    AtomicFormula.eval_product,CertificateCode.eval_slots,cons_zero,cons_succ,hv]
  constructor
  · rintro ⟨hd,hk,hgraph,hs,hquery⟩
    have hf : Graph d c o f := by
      have h := (AtomicFormula.eval_graph 2 (ci+3) 1 (oi+3) 0 _ hk).mp hgraph
      simpa only [cons_zero,cons_succ,hc,ho'] using h
    exact ⟨hd,hk,hf,hs,(query hd hk hf hs).mp hquery⟩
  · rintro ⟨hd,hk,hf,hs,hq⟩
    refine ⟨hd,hk,?_,hs,(query hd hk hf hs).mpr hq⟩
    apply (AtomicFormula.eval_graph 2 (ci+3) 1 (oi+3) 0 _ hk).mpr
    simpa only [cons_zero,cons_succ,hc,ho'] using hf

theorem realize_boundedCertificate (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M)
    {o : ZFSet.{u}}
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : Formula) (e : ℕ → Name (Conditions c)) (p : Conditions c)
    (env : ℕ → ZFSet.{u}) (henv : ∀ i, env i ∈ M)
    (ci oi pi : ℕ) (v : ℕ → ℕ)
    (hc : env ci = c) (ho' : env oi = o) (hp : env pi = label c p)
    (hv : ∀ i, env (v i) = (e i).encode (label c)) :
    (CertificateCode.certificate φ ci oi pi v).Realize M env ↔ Forces e φ p := by
  have matrix (d k f : ZFSet.{u}) (hd : d ∈ M) (hk : k ∈ M) (hf : f ∈ M) :=
    (Formula.absolute (CertificateCode.matrix φ ci oi pi v) M hM
      (cons f (cons k (cons d env))) (by
        intro i
        rcases i with _ | i
        · exact hf
        rcases i with _ | i
        · exact hk
        rcases i with _ | i
        · exact hd
        exact henv i)).trans (eval_certificate_matrix φ d k f o ho e p env ci oi pi v hc ho' hp hv)
  change (∃ d ∈ M, ∃ k ∈ M, ∃ f ∈ M, _) ↔ _
  constructor
  · rintro ⟨d,hd,k,hk,f,hf,hm⟩
    exact ((matrix d k f hd hk hf).mp hm).2.2.2.2
  · intro hforce
    have he (i) : (e i).encode (label c) ∈ M := hv i ▸ henv (v i)
    obtain ⟨d,hd,hdT,_,hs⟩ := finite_container M hM hP hU hS hR hI
      (fun i => (e i).encode (label c)) he (bound φ+1)
    have hk := product_mem M hM hP hU hPow hS hd hd
    obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd
      (hc ▸ henv ci) (ho' ▸ henv oi)
    exact ⟨d,hd,_,hk,f,hf,(matrix d _ f hd hk hf).mpr ⟨hdT,rfl,hfG,hs,hforce⟩⟩

end TuringRigidity.BoundedForcing

end OAI
