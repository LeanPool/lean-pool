/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageSyndromeObjective
public import LeanPool.KLRandomness.StageRankProbability
public import LeanPool.KLRandomness.SparseListConstruction
public import LeanPool.KLRandomness.PoolSearch
public import LeanPool.KLRandomness.AffineProgramLength

/-!
# One fixed reconstruction program for a whole stage

All earlier affine codes, protected strategies, rational parameters, and the
pool program form a fixed header. The variable input is only the trial rank,
the candidate-list index, and bounded integer horizon advice. Pool and sparse
list construction, horizon search, syndrome minimization, and certified code
reconstruction are composed as actual partial recursive computations.
-/

@[expose] public section

noncomputable section

namespace Klr.StageReconstruction

open SparseListSearch

/-- Trial rank, list position, and bounded integer horizon advice. -/
abbrev Input := ℕ × (ℕ × ℕ)

/-- Decode a natural number as a list of positions, using the empty list on failure. -/
def decodePool (n : ℕ) : List ℕ :=
  (@Encodable.decode (List ℕ) (inferInstance : Primcodable (List ℕ)).toEncodable n).getD []

theorem computable_decodePool : Computable decodePool :=
  Primrec.option_getD_default.to_comp.comp Computable.decode

@[simp] theorem decodePool_encodePool (G : List ℕ) :
    decodePool (PoolAdvice.encodePool G) = G := by
  simp [decodePool, PoolAdvice.encodePool]

/-- Execute the fixed pool program at the trial size `r⁸`. -/
def readPool (poolProgram : Nat.Partrec.Code) (r : ℕ) : Part (List ℕ) :=
  (poolProgram.eval (r ^ 8)).map decodePool

theorem partrec_readPool (poolProgram : Nat.Partrec.Code) : Partrec (readPool poolProgram) :=
  (Nat.Partrec.Code.eval_part.comp (Computable.const poolProgram)
    (SparseListConstruction.computable_pow_const 8)).map
      (computable_decodePool.comp Computable.snd)

theorem mem_readPool {poolProgram : Nat.Partrec.Code} {r : ℕ} {G : List ℕ}
    (hG : PoolAdvice.encodePool G ∈ poolProgram.eval (r ^ 8)) : G ∈ readPool poolProgram r := by
  simpa only [readPool, decodePool_encodePool] using Part.mem_map decodePool hG

/-- Search the horizon and recover the syndrome and certified output from
an already selected concrete candidate. -/
def atCandidate (rules : List BettingStrategy) (cs : List AffineCode.Data) (error : ℚ)
    (p : (List ℕ × Entry) × ℕ) : Part AffineCode.Data :=
  (StageHorizon.search error
    (StageRankProbability.u (rules.map (fun s => s.normalize.scan)))
    (StageRankProbability.v (rules.map (fun s => s.normalize.scan)))
    (((cs, p.1.1), p.1.2.2), p.2)).bind fun V =>
      StageSyndromeObjective.finish rules cs (p.1, V)

theorem partrec_atCandidate (rules : List BettingStrategy)
    (cs : List AffineCode.Data) (error : ℚ) : Partrec (atCandidate rules cs error) := by
  have hG : Computable (fun p : (List ℕ × Entry) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hc : Computable (fun p : (List ℕ × Entry) × ℕ => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hi := (((Computable.const cs).pair hG).pair hc).pair Computable.snd
  have hs := (StageHorizon.partrec_search error
    (StageRankProbability.computable_u (rules.map (fun s => s.normalize.scan)))
    (StageRankProbability.computable_v (rules.map (fun s => s.normalize.scan)))).comp hi
  have hf : Partrec (fun p : ((List ℕ × Entry) × ℕ) × ℕ =>
      StageSyndromeObjective.finish rules cs (p.1.1, p.2)) :=
    (StageSyndromeObjective.partrec_finish rules cs).comp
    ((Computable.fst.comp Computable.fst).pair Computable.snd)
  exact hs.bind hf.to₂

/-- Generate the same complete sparse list as in candidate selection and
retrieve its supplied list position. -/
def afterPool (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (error τ θ : ℚ) (p : Input × List ℕ) : Part AffineCode.Data :=
  (SparseListConstruction.construct τ θ p.1.1).bind fun L =>
    atCandidate rules cs error ((p.2, L.getD p.1.2.1 default), p.1.2.2)

theorem partrec_afterPool (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (error τ θ : ℚ) : Partrec (afterPool rules cs error τ θ) := by
  have hs : Partrec (fun p : Input × List ℕ => SparseListConstruction.construct τ θ p.1.1) :=
    (SparseListConstruction.partrec_construct τ θ).comp
    (Computable.fst.comp Computable.fst)
  have hG : Computable (fun p : (Input × List ℕ) × CodeList => p.1.2) :=
    Computable.snd.comp Computable.fst
  have hq : Computable (fun p : (Input × List ℕ) × CodeList => p.1.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have hb : Computable (fun p : (Input × List ℕ) × CodeList => p.1.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
  have ha := (Primrec.list_getD (default : Entry)).to_comp.comp Computable.snd hq
  have hf := (partrec_atCandidate rules cs error).comp ((hG.pair ha).pair hb)
  exact hs.bind hf.to₂

/-- The actual complete fixed-stage reconstruction computation. -/
def run (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (poolProgram : Nat.Partrec.Code) (error τ θ : ℚ) (input : Input) : Part AffineCode.Data :=
  (readPool poolProgram input.1).bind fun G => afterPool rules cs error τ θ (input, G)

theorem partrec_run (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (poolProgram : Nat.Partrec.Code) (error τ θ : ℚ) :
    Partrec (run rules cs poolProgram error τ θ) :=
  ((partrec_readPool poolProgram).comp Computable.fst).bind
    (partrec_afterPool rules cs error τ θ).to₂

/-- Decode the explicit nested natural-number pairing used in the length bound. -/
def inputOfNat (n : ℕ) : Input :=
  (n.unpair.1, (n.unpair.2.unpair.1, n.unpair.2.unpair.2))

theorem computable_inputOfNat : Computable inputOfNat :=
  (Computable.fst.comp Primrec.unpair.to_comp).pair
    (Primrec.unpair.to_comp.comp (Computable.snd.comp Primrec.unpair.to_comp))

@[simp] theorem inputOfNat_pair (r q b : ℕ) :
    inputOfNat (Nat.pair r (Nat.pair q b)) = (r, (q, b)) := by simp [inputOfNat]

/-- A single actual code, chosen before the rank and both advice values,
implements every successful stage reconstruction. -/
theorem exists_fixed_program (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (poolProgram : Nat.Partrec.Code) (error τ θ : ℚ) :
    ∃ e : Nat.Partrec.Code, ∀ r q b,
      AffineDescription.run (AffineDescription.programFor e (Nat.pair r (Nat.pair q b))) =
        run rules cs poolProgram error τ θ (r, (q, b)) := by
  have hp := (partrec_run rules cs poolProgram error τ θ).comp computable_inputOfNat
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp hp
  refine ⟨e, fun r q b => ?_⟩
  rw [AffineDescription.run_programFor, he]
  simp only [Encodable.decode_nat, Part.coe_some, Part.bind_some, inputOfNat_pair, Part.map_map]
  exact Part.map_id' (fun _ => AffineDescription.decodeOutput_encode _) _

/-- Executing the composite program agrees with independently established
pool, list, horizon, and final-output witnesses. -/
theorem mem_run_of_witnesses (rules : List BettingStrategy) (cs : List AffineCode.Data)
    (poolProgram : Nat.Partrec.Code) (error τ θ : ℚ)
    {r q b : ℕ} {G : List ℕ} {L : CodeList} {V : ℕ} {c : AffineCode.Data}
    (hG : PoolAdvice.encodePool G ∈ poolProgram.eval (r ^ 8))
    (hL : L ∈ SparseListConstruction.construct τ θ r)
    (hV : V ∈ StageHorizon.search error
      (StageRankProbability.u (rules.map (fun s => s.normalize.scan)))
      (StageRankProbability.v (rules.map (fun s => s.normalize.scan)))
      (((cs, G), (L.getD q default).2), b))
    (hc : c ∈ StageSyndromeObjective.finish rules cs ((G, L.getD q default), V)) :
    c ∈ run rules cs poolProgram error τ θ (r, (q, b)) := by
  exact Part.mem_bind (mem_readPool hG)
    (Part.mem_bind hL (Part.mem_bind hV hc))

end Klr.StageReconstruction
