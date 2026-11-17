/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/CutTranscript.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteTranscript
public import LeanPool.TuringConeRigidity.Computability.Cuts
public import LeanPool.TuringConeRigidity.Computability.Joins

/-!
# Cut Transcript
-/


@[expose] public section

namespace OAI

open Set
namespace TuringRigidity

theorem cut_prefix_left (x : ℝ) (m : ℕ) :
    ∃ l : ℝ, l < x ∧ ∀ y, l < y → y ≤ x → ∀ k, k < m → cut y k = cut x k := by
  induction m with
  | zero => exact ⟨x-1, by linarith, by simp⟩
  | succ m ih =>
    obtain ⟨l,hl,he⟩ := ih
    by_cases hq : (rationalEnumeration m : ℝ) < x
    · refine ⟨max l (rationalEnumeration m), max_lt hl hq, ?_⟩
      intro y hy hyx k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact he y ((le_max_left _ _).trans_lt hy) hyx k hk
      · subst k
        have hqy := (le_max_right l (rationalEnumeration m : ℝ)).trans_lt hy
        simp [cut, hq, hqy]
    · refine ⟨l,hl,?_⟩
      intro y hy hyx k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact he y hy hyx k hk
      · subst k
        have hqy : ¬ (rationalEnumeration m : ℝ) < y :=
          not_lt.mpr (hyx.trans (not_lt.mp hq))
        simp [cut,hq,hqy]

namespace CategorySearch

/-- Join the fixed oracle with the cut oracles of the two real coordinates. -/
noncomputable def pairOracle (A : Oracle) (p : ℝ × ℝ) : Oracle := join (join A (cut p.1)) (cut p.2)
/-- Read one bit of the joined category-search oracle as a natural number. -/
noncomputable def value (A : Oracle) (p : ℝ × ℝ) (k : ℕ) : ℕ := if pairOracle A p k then 1 else 0

theorem value_prefix (A : Oracle) (p q : ℝ × ℝ) (m : ℕ)
    (h1 : ∀ k, k < m → cut q.1 k = cut p.1 k)
    (h2 : ∀ k, k < m → cut q.2 k = cut p.2 k) :
    ∀ k, k < m → value A q k = value A p k := by
  intro k hk
  apply congrArg (fun b : Bool => if b then (1 : ℕ) else 0)
  have hk2 : k/2 < m := by omega
  have hk4 : k/2/2 < m := by omega
  simp only [pairOracle,join,h1 _ hk4,h2 _ hk2]

theorem halting_left (A : Oracle) (c : OracleCode) (p : ℝ × ℝ) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (pairOracle A p)) c n) :
    ∃ l : ℝ × ℝ, l.1 < p.1 ∧ l.2 < p.2 ∧
      ∀ q : ℝ × ℝ, l.1 < q.1 → q.1 ≤ p.1 → l.2 < q.2 → q.2 ≤ p.2 →
        a ∈ OracleCode.eval (oracleFunction (pairOracle A q)) c n := by
  obtain ⟨m,hm⟩ := OracleCode.eval_total_stable (value A p) c n a ha
  obtain ⟨l1,h1,he1⟩ := cut_prefix_left p.1 m
  obtain ⟨l2,h2,he2⟩ := cut_prefix_left p.2 m
  refine ⟨(l1,l2),h1,h2,?_⟩
  intro q hq1 hq1' hq2 hq2'
  exact hm (value A q) (value_prefix A p q m (he1 _ hq1 hq1') (he2 _ hq2 hq2'))

/-- The open rectangle determined by rational lower and upper coordinate bounds. -/
def rectangle (l r : ℚ × ℚ) : Set (ℝ × ℝ) :=
  Ioo (l.1 : ℝ) (r.1 : ℝ) ×ˢ Ioo (l.2 : ℝ) (r.2 : ℝ)

/-- Real pairs at which the program computes exactly the target oracle. -/
def success (A Y : Oracle) (c : OracleCode) : Set (ℝ × ℝ) :=
  {p | OracleCode.eval (oracleFunction (pairOracle A p)) c = oracleFunction Y}

theorem dense_sound (A Y : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (hd : rectangle l r ⊆ closure (success A Y c)) (p : ℝ × ℝ)
    (hp : p ∈ rectangle l r) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (pairOracle A p)) c n) :
    a = if Y n then 1 else 0 := by
  obtain ⟨b,hb1,hb2,he⟩ := halting_left A c p n a ha
  let U : Set (ℝ × ℝ) := Ioo (max b.1 (l.1 : ℝ)) p.1 ×ˢ Ioo (max b.2 (l.2 : ℝ)) p.2
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hne : U.Nonempty :=
    (nonempty_Ioo.mpr (max_lt hb1 hp.1.1)).prod (nonempty_Ioo.mpr (max_lt hb2 hp.2.1))
  have hsub : U ⊆ rectangle l r := by
    intro q hq
    exact ⟨⟨(le_max_right _ _).trans_lt hq.1.1,hq.1.2.trans hp.1.2⟩,
      ⟨(le_max_right _ _).trans_lt hq.2.1,hq.2.2.trans hp.2.2⟩⟩
  obtain ⟨q,hq⟩ := hne
  obtain ⟨z,hzU,hzS⟩ := mem_closure_iff.mp (hd (hsub hq)) U hU hq
  have hz := he z ((le_max_left _ _).trans_lt hzU.1.1) hzU.1.2.le
    ((le_max_left _ _).trans_lt hzU.2.1) hzU.2.2.le
  rw [hzS] at hz
  exact Part.mem_some_iff.mp hz

theorem rational_halting (A : Oracle) (c : OracleCode) (l r : ℚ × ℚ)
    (p : ℝ × ℝ) (hp : p ∈ rectangle l r) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (pairOracle A p)) c n) :
    ∃ q : ℚ × ℚ, ((q.1 : ℝ),(q.2 : ℝ)) ∈ rectangle l r ∧
      a ∈ OracleCode.eval (oracleFunction (pairOracle A ((q.1 : ℝ),(q.2 : ℝ)))) c n := by
  obtain ⟨b,hb1,hb2,he⟩ := halting_left A c p n a ha
  obtain ⟨u,hu1,hu2⟩ := exists_rat_btwn (max_lt hb1 hp.1.1)
  obtain ⟨v,hv1,hv2⟩ := exists_rat_btwn (max_lt hb2 hp.2.1)
  exact ⟨(u,v),⟨⟨(le_max_right _ _).trans_lt hu1,hu2.trans hp.1.2⟩,
    ⟨(le_max_right _ _).trans_lt hv1,hv2.trans hp.2.2⟩⟩,
    he _ ((le_max_left _ _).trans_lt hu1) hu2.le ((le_max_left _ _).trans_lt hv1) hv2.le⟩

end CategorySearch
end TuringRigidity

end OAI
