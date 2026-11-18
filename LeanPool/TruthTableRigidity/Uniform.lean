/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import LeanPool.TruthTableRigidity.Defs
public import LeanPool.TuringConeRigidity.Effective.UniformPrograms

/-!
# Uniform oracle programs

Tools for building a *single* oracle program that works for every oracle, and the
criterion `isTTFunctional_of_approx`: a functional which can be computed from finite
prefixes of the oracle by a computable function is a tt-functional.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity Encodable

/-- The value `0`/`1` of a bit. -/
def bv (b : Bool) : ℕ := if b then 1 else 0

theorem oracleFunction_eq (X : Oracle) : oracleFunction X = fun n => Part.some (bv (X n)) := rfl

/-- The finite prefix `X ↾ m` of an oracle. -/
def pre (X : Oracle) (m : ℕ) : List Bool := (List.range m).map X

theorem pre_succ (X : Oracle) (l : ℕ) : pre X (l + 1) = pre X l ++ [X l] := by
  simp [pre, List.range_succ]

/-- A family of partial functions computed uniformly in the oracle by one program. -/
def URec (F : Oracle → ℕ →. ℕ) : Prop :=
  ∃ c : OracleCode, ∀ X, OracleCode.eval (oracleFunction X) c = F X

/-- A family of total functions computed uniformly in the oracle by one program. -/
def UTot (F : Oracle → ℕ → ℕ) : Prop := URec fun X n => Part.some (F X n)

theorem nat_partrec_oracleCode {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    ∃ c : OracleCode, ∀ g, OracleCode.eval g c = f :=
  UniformPrograms.oracle_free hf.recursiveIn

namespace UTot

theorem const {f : ℕ → ℕ} (hf : Computable f) : UTot fun _ n => f n := by
  obtain ⟨c, hc⟩ := nat_partrec_oracleCode (Partrec.nat_iff.mp hf)
  exact ⟨c, fun X => hc _⟩

theorem query : UTot fun X n => bv (X n) := ⟨.query, fun _ => rfl⟩

theorem comp {F G : Oracle → ℕ → ℕ} (hF : UTot F) (hG : UTot G) :
    UTot fun X n => F X (G X n) := by
  obtain ⟨c, hc⟩ := hF
  obtain ⟨d, hd⟩ := hG
  refine ⟨.comp c d, fun X => ?_⟩
  funext n
  simp only [OracleCode.eval, hc, hd]
  simp

theorem pair {F G : Oracle → ℕ → ℕ} (hF : UTot F) (hG : UTot G) :
    UTot fun X n => Nat.pair (F X n) (G X n) := by
  obtain ⟨c, hc⟩ := hF
  obtain ⟨d, hd⟩ := hG
  refine ⟨.pair c d, fun X => ?_⟩
  funext n
  simp only [OracleCode.eval, hc, hd]
  simp [Seq.seq]

theorem precomp {F : Oracle → ℕ → ℕ} {f : ℕ → ℕ} (hF : UTot F) (hf : Computable f) :
    UTot fun X n => F X (f n) :=
  comp hF (const hf)

theorem map {F : Oracle → ℕ → ℕ} {h : ℕ → ℕ} (hh : Computable h) (hF : UTot F) :
    UTot fun X n => h (F X n) :=
  comp (const hh) hF

theorem map₂ {F G : Oracle → ℕ → ℕ} {h : ℕ → ℕ → ℕ} (hh : Computable₂ h) (hF : UTot F)
    (hG : UTot G) : UTot fun X n => h (F X n) (G X n) := by
  have hh' : Computable fun p : ℕ => h p.unpair.1 p.unpair.2 :=
    hh.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  simpa using comp (const hh') (pair hF hG)

theorem id : UTot fun _ n => n := const Computable.id

/-- A single program computes the numerical prefix of every Boolean oracle. -/
theorem numericalPrefixes : UTot fun X m =>
    encode (UniformOracle.oraclePrefix (fun k => bv (X k)) m) :=
  UniformPrograms.initial_program (O := oracleFunction) (fun X k => bv (X k)) query

/-- The bit prefixes are uniformly computable by decoding the numerical prefixes. -/
theorem prefixes : UTot fun X m => encode (pre X m) := by
  let bits : ℕ → ℕ := fun e =>
    encode (((decode (α := List ℕ) e).getD []).map fun k => k == 1)
  have hbits : Primrec bits :=
    Primrec.encode.comp (Primrec.list_map (Primrec.option_getD_default.comp Primrec.decode)
      (Primrec.beq.comp Primrec.snd (Primrec.const 1)))
  have he (X : Oracle) (m : ℕ) :
      bits (encode (UniformOracle.oraclePrefix (fun k => bv (X k)) m)) = encode (pre X m) := by
    simp only [bits, encodek, Option.getD_some, UniformOracle.oraclePrefix,
      PrefixComputability.oraclePrefix, pre, List.map_map]
    congr 1
    apply congrArg (fun f : ℕ → Bool => (List.range m).map f)
    funext k
    cases hx : X k <;> simp [Function.comp_apply, bv, hx]
  simpa only [he] using map hbits.to_comp numericalPrefixes

theorem rfind_some {p : ℕ → Bool} (h : ∃ k, p k = true) :
    Nat.rfind (fun k => Part.some (p k)) = Part.some (Nat.find h) := by
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  refine ⟨by simpa using Nat.find_spec h, fun {k} hk => ?_⟩
  have := Nat.find_min h hk
  simpa using this

/-- Unbounded search, when it always succeeds. -/
theorem search {G : Oracle → ℕ → ℕ} (hG : UTot G)
    (h : ∀ X n, ∃ m, G X (Nat.pair n m) = 0) :
    UTot fun X n => Nat.find (h X n) := by
  obtain ⟨c, hc⟩ := hG
  refine ⟨.find c, fun X => ?_⟩
  funext n
  simp only [OracleCode.eval, hc]
  have h' : ∃ k, decide (G X (Nat.pair n k) = 0) = true := by simpa using h X n
  have := rfind_some h'
  have e : (fun k => (fun m => decide (m = 0)) <$> Part.some (G X (Nat.pair n k))) =
      fun k => Part.some (decide (G X (Nat.pair n k) = 0)) := by funext k; rfl
  rw [e, this]
  congr 1
  apply le_antisymm
  · exact Nat.find_mono (fun k hk => by simpa using hk)
  · exact Nat.find_mono (fun k hk => by simpa using hk)

end UTot

theorem isTTFunctional_of_utot {Φ : Oracle → Oracle} (h : UTot fun X n => bv (Φ X n)) :
    IsTTFunctional Φ := h

/-- **Finite approximation criterion.**  If `H` is computable, every answer it gives on a
prefix of `X` is correct, and on every input it eventually answers on long enough prefixes,
then the functional is a tt-functional. -/
theorem isTTFunctional_of_approx {Φ : Oracle → Oracle}
    {H : List (Option Bool) → ℕ → Option Bool} (hH : Computable₂ H)
    (hsound : ∀ X m n b, H ((pre X m).map some) n = some b → Φ X n = b)
    (hcomplete : ∀ X n, ∃ m, (H ((pre X m).map some) n).isSome) : IsTTFunctional Φ := by
  let dec : ℕ → List (Option Bool) := fun e => ((decode (α := List Bool) e).getD []).map some
  have hdec : Computable dec :=
    (Primrec.list_map (Primrec.option_getD_default.comp Primrec.decode)
      (Primrec.option_some.comp Primrec.snd).to₂).to_comp
  let g₁ : ℕ → ℕ → ℕ := fun e n => cond (H (dec e) n).isSome 0 1
  have hg₁ : Computable₂ g₁ :=
    Computable.cond (Primrec.option_isSome.to_comp.comp (hH.comp (hdec.comp Computable.fst)
      Computable.snd)) (Computable.const 0) (Computable.const 1)
  let g₂ : ℕ → ℕ → ℕ := fun e n => bv ((H (dec e) n).getD false)
  have hg₂ : Computable₂ g₂ := by
    have : Computable₂ fun e n => cond ((H (dec e) n).getD false) 1 0 :=
      Computable.cond (Computable.option_getD (hH.comp (hdec.comp Computable.fst)
        Computable.snd) (Computable.const false)) (Computable.const 1) (Computable.const 0)
    refine this.of_eq fun p => ?_
    simp only [g₂, bv]
    cases (H (dec p.1) p.2).getD false <;> rfl
  have hdecpre : ∀ X m, dec (encode (pre X m)) = (pre X m).map some := by
    intro X m; simp [dec]
  have hG : UTot fun X z => g₁ (encode (pre X (Nat.unpair z).2)) (Nat.unpair z).1 :=
    UTot.map₂ hg₁ (UTot.precomp UTot.prefixes (Computable.snd.comp Computable.unpair))
      (UTot.const (Computable.fst.comp Computable.unpair))
  have hex : ∀ X n, ∃ m, (fun X z => g₁ (encode (pre X (Nat.unpair z).2)) (Nat.unpair z).1)
      X (Nat.pair n m) = 0 := by
    intro X n
    obtain ⟨m, hm⟩ := hcomplete X n
    exact ⟨m, by simp [g₁, hdecpre, hm]⟩
  have hM := UTot.search hG hex
  have hV : UTot fun X n => g₂ (encode (pre X (Nat.find (hex X n)))) n :=
    UTot.map₂ hg₂ (UTot.comp UTot.prefixes hM) UTot.id
  apply isTTFunctional_of_utot
  refine (show (fun X n => g₂ (encode (pre X (Nat.find (hex X n)))) n) =
      (fun X n => bv (Φ X n)) from ?_) ▸ hV
  funext X n
  have hs := Nat.find_spec (hex X n)
  generalize Nat.find (hex X n) = m at hs ⊢
  simp only [g₁, hdecpre, Nat.unpair_pair] at hs
  have hsome : (H ((pre X m).map some) n).isSome := by
    revert hs
    cases (H ((pre X m).map some) n).isSome <;> simp
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  simp only [g₂, hdecpre, hb, Option.getD_some]
  rw [hsound X _ n b hb]

end TT
