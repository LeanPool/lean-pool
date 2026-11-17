/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformPrograms.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracle

/-!
# Uniform Programs
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformPrograms
open Encodable

/-- One oracle program uniformly computes the family of partial functions from the given
oracle family. -/
def Runs {X : Type*} (O : X → ℕ →. ℕ) (f : X → ℕ →. ℕ) : Prop :=
  ∃ p : OracleCode, ∀ x, OracleCode.eval (O x) p = f x

variable {X : Type*} {O : X → ℕ →. ℕ}

theorem oracle_free {f : ℕ →. ℕ} (hf : Nat.RecursiveIn ∅ f) :
    ∃ p : OracleCode, ∀ g, OracleCode.eval g p = f := by
  induction hf with
  | zero => exact ⟨.zero,fun _ => rfl⟩
  | succ => exact ⟨.succ,fun _ => rfl⟩
  | left => exact ⟨.left,fun _ => rfl⟩
  | right => exact ⟨.right,fun _ => rfl⟩
  | oracle f hf => simp at hf
  | pair _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.pair c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | comp _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.comp c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | prec _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.prec c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | rfind _ hc =>
    obtain ⟨c,hc⟩ := hc
    exact ⟨.find c,fun g => by simp only [OracleCode.eval,hc g]; rfl⟩

theorem primrec {f : ℕ → ℕ} (hf : Primrec f) : Runs O (fun _ n => Part.some (f n)) := by
  obtain ⟨p,hp⟩ := oracle_free (RecursiveIn.iff_nat.mp (hf.computableIn (O := ∅)))
  exact ⟨p,fun x => hp (O x)⟩

theorem query : Runs O O := ⟨.query,fun _ => rfl⟩

theorem Runs.of_eq {f g : X → ℕ →. ℕ} (hf : Runs O f) (h : ∀ x n, f x n = g x n) : Runs O g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun x => (hp x).trans (funext (h x))⟩

theorem Runs.pair {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x n => Nat.pair <$> f x n <*> g x n) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.pair p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.comp {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x n => g x n >>= f x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.comp p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.prec {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x p => ((Nat.unpair p).2).rec (f x (Nat.unpair p).1)
      (fun y ih => ih.bind (fun i => g x (Nat.pair (Nat.unpair p).1 (Nat.pair y i))))) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.prec p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.find {f : X → ℕ →. ℕ} (hf : Runs O f) :
    Runs O (fun x a => Nat.rfind (fun n => (fun m => decide (m=0)) <$> f x (Nat.pair a n))) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨.find p,fun x => by simp only [OracleCode.eval,hp x]; rfl⟩

theorem total_comp {f g : X → ℕ → ℕ}
    (hf : Runs O (fun x n => Part.some (f x n)))
    (hg : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x n => Part.some (f x (g x n))) := by
  simpa using hf.comp hg

theorem total_pair {f g : X → ℕ → ℕ}
    (hf : Runs O (fun x n => Part.some (f x n)))
    (hg : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x n => Part.some (Nat.pair (f x n) (g x n))) := by
  simpa [Seq.seq] using hf.pair hg

theorem initial_program (g : X → ℕ → ℕ)
    (hquery : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x m => Part.some (encode (UniformOracle.oraclePrefix (g x) m))) := by
  have hy := (primrec (O := O)) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (primrec (O := O)) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp ((primrec (O := O)) (UniformOracle.appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hquery hy))
  have hp := Runs.prec ((primrec (O := O)) (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Runs.comp hp (total_pair ((primrec (O := O)) (Primrec.const 0))
    ((primrec (O := O)) Primrec.id))
  apply hh.of_eq
  intro x n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [UniformOracle.appendEncoded,
      PrefixComputability.appendEncoded,UniformOracle.oraclePrefix,
      PrefixComputability.oraclePrefix,List.range_succ]

private def flag (e : ℕ) : ℕ :=
  if ((decode (α := Option ℕ) e).getD none).isSome then 0 else 1
private def answer (e : ℕ) : ℕ := ((decode (α := Option ℕ) e).getD none).getD 0

private theorem flag_primrec : Primrec flag := by
  apply (Primrec.cond (Primrec.option_isSome.comp (Primrec.option_getD_default.comp
    (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases hh : ((decode (α := Option ℕ) n).getD none).isSome <;> simp only [flag,hh] <;> rfl
private theorem answer_primrec : Primrec answer :=
  Primrec.option_getD_default.comp (Primrec.option_getD_default.comp Primrec.decode)

theorem total_search {E : X → ℕ → ℕ → Option ℕ}
    (hE : Runs O (fun x z => Part.some (encode (E x (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : X → ℕ → ℕ) (hsound : ∀ x n m a, a ∈ E x n m → a = f x n)
    (hcomplete : ∀ x n, ∃ m a, a ∈ E x n m) :
    Runs O (fun x n => Part.some (f x n)) := by
  have hflag := total_comp (primrec flag_primrec) hE
  have hfind := Runs.find hflag
  have hpair := Runs.pair (primrec Primrec.id) hfind
  have hrun := Runs.comp (primrec answer_primrec) (Runs.comp hE hpair)
  apply hrun.of_eq
  intro x n
  apply Part.eq_some_iff.mpr
  have hex : ∃ m, (E x n m).isSome = true := by
    obtain ⟨m,a,ha⟩ := hcomplete x n
    exact ⟨m,Option.isSome_iff_exists.mpr ⟨a,ha⟩⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hm
  have hval : a = f x n := hsound x n m a ha
  have hmem : m ∈ Nat.rfind (fun k =>
      (fun v : ℕ => decide (v=0)) <$> Part.some (flag (encode (E x n k)))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · simp [flag,m,hm]
    · intro k hk
      have hk' : (E x n k).isSome = false := Bool.eq_false_iff.mpr (Nat.find_min hex hk)
      simp [flag,hk']
  apply Part.mem_bind_iff.mpr
  refine ⟨encode (E x n m),?_,?_⟩
  · apply Part.mem_bind_iff.mpr
    refine ⟨Nat.pair n m,?_,?_⟩
    · simp only [Seq.seq]
      apply Part.mem_bind_iff.mpr
      refine ⟨Nat.pair n,(Part.mem_map_iff _).mpr ⟨n,Part.mem_some _,rfl⟩,?_⟩
      exact (Part.mem_map_iff _).mpr ⟨m,by simpa only [Nat.unpair_pair] using hmem,rfl⟩
    · simp
  · have hea : E x n m = some a := Option.mem_def.mp ha
    apply Part.mem_some_iff.mpr
    rw [hea]
    simpa only [answer,Encodable.encodek,Option.getD_some] using hval.symm

end TuringRigidity.UniformPrograms

end OAI
