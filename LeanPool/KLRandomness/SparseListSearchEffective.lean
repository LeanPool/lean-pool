/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseListSearchComputable

/-!
# Effective exhaustive search for sparse candidate lists

The search enumerates ordinary natural-number encodings of finite lists and
runs the proved finite checker. It is partial recursive on all parameter
tuples, and it halts exactly when a list satisfying the mathematical sparse
contract exists. Thus a separate finite existence theorem supplies halting;
no classical choice of finite objects is assumed computable.
-/

@[expose] public section

namespace Klr.SparseListSearch

/-- Decode and check one possible finite list. -/
def trial (p : Parameters) (n : ℕ) : Option CodeList :=
  (Encodable.decode n).bind fun L => if check p L then some L else none

theorem computable_trial : Computable₂ trial := by
  have hf : Computable₂ (fun p L => if check p L then some L else none) := by
    have h := Computable.cond computable_check
      (Computable.option_some.comp Computable.snd) (Computable.const none)
    exact h.of_eq fun _ => by simp [Bool.cond_eq_ite]
  exact Computable.bind_decode_iff.mpr hf

/-- Actual partial-recursive exhaustive search through code-list encodings. -/
def search (p : Parameters) : Part CodeList := Nat.rfindOpt (trial p)

theorem partrec_search : Partrec search := Partrec.rfindOpt computable_trial

theorem search_check {p : Parameters} {L : CodeList} (hL : L ∈ search p) :
    check p L = true := by
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hL
  simp only [trial, Option.mem_bind_iff] at hn
  obtain ⟨K, _, hK⟩ := hn
  split_ifs at hK with hv
  · have he : K = L := Option.mem_some_iff.mp hK
    simpa only [he] using hv
  · simp at hK

/-- Every returned list meets the full sparse-list contract. -/
theorem search_spec {p : Parameters} {L : CodeList} (hL : L ∈ search p) :
    Good (universeSize p) (supportSize p) (rowRank p) (listLength p)
      (density p) (badFraction p) L :=
  (check_eq_true p L).mp (search_check hL)

/-- Existence of a good finite code is precisely the halting condition of the actual search. -/
theorem search_dom_iff (p : Parameters) : (search p).Dom ↔
    ∃ L : CodeList, Good (universeSize p) (supportSize p) (rowRank p) (listLength p)
      (density p) (badFraction p) L := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := Part.dom_iff_mem.mp h
    exact ⟨L, search_spec hL⟩
  · rintro ⟨L, hL⟩
    apply Nat.rfindOpt_dom.mpr
    refine ⟨Encodable.encode L, L, ?_⟩
    simp [trial, (check_eq_true p L).mpr hL]

theorem exists_search_output_iff (p : Parameters) :
    (∃ L : CodeList, L ∈ search p) ↔
      ∃ L : CodeList, Good (universeSize p) (supportSize p) (rowRank p) (listLength p)
        (density p) (badFraction p) L :=
  Part.dom_iff_mem.symm.trans (search_dom_iff p)

/-- Encode parameters with the canonical computability presentation of the rationals.
The unrelated default `Encodable ℚ` instance need not use this presentation. -/
def encodeParameters (p : Parameters) : ℕ :=
  @Encodable.encode Parameters (inferInstance : Primcodable Parameters).toEncodable p

theorem computable_encodeParameters : Computable encodeParameters := Computable.encode

/-- One fixed Mathlib partial-recursive program implements the parameterized search. -/
theorem exists_search_program : ∃ e : Nat.Partrec.Code, ∀ p : Parameters,
    e.eval (encodeParameters p) = (search p).map Encodable.encode := by
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp partrec_search
  refine ⟨e, fun p => ?_⟩
  rw [he]
  dsimp only [encodeParameters]
  rw [@Encodable.encodek Parameters (inferInstance : Primcodable Parameters).toEncodable p]
  simp only [Part.coe_some, Part.bind_some]

/-- Fix an actual program for the search, without making a program-size claim. -/
noncomputable def searchProgram : Nat.Partrec.Code := Classical.choose exists_search_program

theorem searchProgram_eval (p : Parameters) :
    searchProgram.eval (encodeParameters p) = (search p).map Encodable.encode :=
  Classical.choose_spec exists_search_program p

theorem searchProgram_dom_iff (p : Parameters) :
    (searchProgram.eval (encodeParameters p)).Dom ↔
      ∃ L : CodeList, Good (universeSize p) (supportSize p) (rowRank p) (listLength p)
        (density p) (badFraction p) L := by
  rw [searchProgram_eval]
  exact search_dom_iff p

end Klr.SparseListSearch
