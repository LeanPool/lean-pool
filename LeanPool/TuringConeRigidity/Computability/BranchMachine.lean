/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/BranchMachine.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.PartialComputability
public import LeanPool.TuringConeRigidity.SetModels.ParametricEval
public import LeanPool.TuringConeRigidity.Effective.FiniteApproximation

/-!
# Branch Machine
-/


@[expose] public section

namespace OAI

namespace TuringRigidity
open Computable

/-- Interleave two partial functions, using the first at even and the second at odd inputs. -/
def partialJoin (f g : ℕ →. ℕ) (k : ℕ) : Part ℕ :=
  if k.bodd then g (k/2) else f (k/2)

namespace BranchMachine

/-- Read the initial-state channel of a partial oracle. -/
def initial (g : ℕ →. ℕ) (k : ℕ) : Part ℕ := g (8*k)
/-- Read the anchor channel of a partial oracle. -/
def anchor (g : ℕ →. ℕ) (k : ℕ) : Part ℕ := g (8*k+4)
/-- Read the branch-dependent increment channel of a partial oracle. -/
def increment (g : ℕ →. ℕ) (h b k : ℕ) : Part ℕ :=
  g (if b = h then 2*k+1 else 4*k+2)

/-- One branch-machine step, composing the two programs with the selected increment and anchor
channels. -/
def step (p q : OracleCode) (j h : ℕ) (g old : ℕ →. ℕ) (k : ℕ) : Part ℕ :=
  old j >>= fun b =>
    OracleCode.eval
      (partialJoin (OracleCode.eval (partialJoin old (increment g h b)) p) (anchor g)) q k

/-- Iterate the branch-machine transition from the initial partial state. -/
def stage (p q : OracleCode) (j h : ℕ) (g : ℕ →. ℕ) : ℕ → ℕ →. ℕ
  | 0 => initial g
  | n+1 => step p q j h g (stage p q j h g n)

theorem partialJoin_approximates {f g : ℕ →. ℕ} {fs gs : ℕ → ℕ →. ℕ}
    (hf : ∀ k, Approximates (f k) (fun m => fs m k))
    (hg : ∀ k, Approximates (g k) (fun m => gs m k)) (k : ℕ) :
    Approximates (partialJoin f g k) (fun m => partialJoin (fs m) (gs m) k) := by
  simp only [partialJoin]
  split
  · exact hg _
  · exact hf _

theorem stage_approximates (p q : OracleCode) (j h : ℕ)
    {g : ℕ →. ℕ} {gs : ℕ → ℕ →. ℕ}
    (hg : ∀ k, Approximates (g k) (fun m => gs m k)) :
    ∀ n k, Approximates (stage p q j h g n k)
      (fun m => stage p q j h (gs m) n k) := by
  intro n
  induction n with
  | zero => intro k; exact hg _
  | succ n ih =>
    intro k
    apply (ih j).bind
    intro b
    apply OracleCode.eval_approximates _ q k
    intro x
    apply partialJoin_approximates
    · exact OracleCode.eval_approximates
        (fun x => partialJoin_approximates ih (fun k => hg _) x) p
    · intro x; exact hg _

variable {α : Type*} [Primcodable α]

theorem partialJoin_partrec {f g : α → ℕ →. ℕ} (hf : Partrec₂ f) (hg : Partrec₂ g) :
    Partrec₂ (fun a k => partialJoin (f a) (g a) k) := by
  apply partrec_cond (Computable.nat_bodd.comp snd)
  · exact hg.comp fst ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.comp snd)
  · exact hf.comp fst ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp.comp snd)

theorem increment_index_computable (h : ℕ) :
    Computable₂ (fun b k : ℕ => if b = h then 2*k+1 else 4*k+2) := by
  apply (Computable.cond ((Primrec.beq.comp Primrec.fst (Primrec.const h)).to_comp)
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 1)).to_comp)
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd)
      (Primrec.const 2)).to_comp)).of_eq
  intro z
  by_cases hh : z.1 = h
  · simp [hh]
  · have he : (z.1 == h) = false := Bool.eq_false_iff.mpr (fun he => hh (beq_iff_eq.mp he))
    simp [hh,he]

theorem step_partrec (p q : OracleCode) (j h : ℕ)
    {g old : α → ℕ →. ℕ} (hg : Partrec₂ g) (ho : Partrec₂ old) :
    Partrec₂ (fun a k => step p q j h (g a) (old a) k) := by
  change Partrec (fun z : α × ℕ => (old z.1 j).bind _)
  apply Partrec.bind (ho.comp fst (Computable.const j))
  let β := (α × ℕ) × ℕ
  have hleft : Partrec₂ (fun z : β => old z.1.1) :=
    ho.comp (fst.comp (fst.comp fst)) snd
  have hinc : Partrec₂ (fun z : β => increment (g z.1.1) h z.2) :=
    hg.comp (fst.comp (fst.comp fst))
      ((increment_index_computable h).comp (snd.comp fst) snd)
  have hforward := OracleCode.eval_partrec (partialJoin_partrec hleft hinc) p
  have hanchor : Partrec₂ (fun z : β => anchor (g z.1.1)) :=
    hg.comp (fst.comp (fst.comp fst))
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.snd)
        (Primrec.const 4)).to_comp)
  exact (OracleCode.eval_partrec (partialJoin_partrec hforward hanchor) q).comp
    Computable.id (snd.comp fst)

/-- Partial lookup of an entry in a finite natural-number list. -/
def lookup (L : List ℕ) (k : ℕ) : Part ℕ := (L[k]? : Part ℕ)

theorem lookup_partrec : Partrec₂ lookup :=
  Computable.ofOption Primrec.list_getElem?.to_comp

theorem stage_finite_partrec (p q : OracleCode) (j h : ℕ) :
    Partrec (fun z : List ℕ × ℕ × ℕ => stage p q j h (lookup z.1) z.2.1 z.2.2) := by
  let α := List ℕ × ℕ × ℕ
  let body (c : Nat.Partrec.Code) (z : α) : Part ℕ :=
    if z.2.1 == 0 then initial (lookup z.1) z.2.2 else
      step p q j h (lookup z.1)
        (fun k => c.eval (Encodable.encode (z.1, z.2.1-1, k))) z.2.2
  have hb : Partrec₂ body := by
    apply partrec_cond ((Primrec.beq.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)).to_comp)
    · exact lookup_partrec.comp (fst.comp snd)
        ((Primrec.nat_mul.comp (Primrec.const 8)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp)
    · have hg : Partrec₂ (fun z : Nat.Partrec.Code × α => lookup z.2.1) :=
        lookup_partrec.comp (fst.comp (snd.comp fst)) snd
      have ho : Partrec₂ (fun z : Nat.Partrec.Code × α =>
          fun k => z.1.eval (Encodable.encode (z.2.1,z.2.2.1-1,k))) :=
        Nat.Partrec.Code.eval_part.comp (fst.comp fst)
          ((Computable.encode (α := List ℕ × ℕ × ℕ)).comp ((fst.comp (snd.comp fst)).pair
            ((Computable.pred.comp (fst.comp (snd.comp (snd.comp fst)))).pair snd)))
      exact (step_partrec p q j h hg ho).comp Computable.id (snd.comp (snd.comp snd))
  obtain ⟨c,hc⟩ := partrec_fixed_point hb
  have heq : ∀ n L k, c.eval (Encodable.encode (L,n,k)) = stage p q j h (lookup L) n k := by
    intro n
    induction n with
    | zero => intro L k; rw [hc]; rfl
    | succ n ih =>
      intro L k
      rw [hc]
      have hn0 : (n+1 == 0) = false := rfl
      simp only [body, hn0,
        Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel, stage]
      congr 1
      funext i
      exact ih L i
  exact (Nat.Partrec.Code.eval_part.comp (Computable.const c) Computable.encode).of_eq
    (fun z => heq z.2.1 z.1 z.2.2)

end BranchMachine
end TuringRigidity

end OAI
