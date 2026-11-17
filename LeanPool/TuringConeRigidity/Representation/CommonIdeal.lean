/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CommonIdeal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteTranscript
public import LeanPool.TuringConeRigidity.Representation.BorelGeneric
public import LeanPool.TuringConeRigidity.Computability.Joins

/-!
# Common Ideal
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CommonIdeal
open Set Encodable

def bit (b : Bool) : ℕ := if b then 1 else 0

def table (s : List Bool) : ℕ →. ℕ := BranchMachine.lookup (s.map bit)

def run (A : Oracle) (p : OracleCode) (s : List Bool) : ℕ →. ℕ :=
  OracleCode.eval (partialJoin (oracleFunction A) (table s)) p

def Extends (G : Oracle) (s : List Bool) : Prop :=
  ∀ i, i < s.length → G i = s.getD i false

theorem table_mono {s t : List Bool} (h : s <+: t) :
    ∀ k a, a ∈ table s k → a ∈ table t k := by
  obtain ⟨u,rfl⟩ := h
  intro k a ha
  change a ∈ (((s ++ u).map bit)[k]? : Part ℕ)
  change a ∈ ((s.map bit)[k]? : Part ℕ) at ha
  have hk : k < s.length := by
    by_contra hn
    simp [List.getElem?_eq_none (show (s.map bit).length ≤ k by simp; omega)] at ha
  simpa [List.map_append, List.getElem?_append, hk] using ha

theorem table_total {G : Oracle} {s : List Bool} (h : Extends G s) :
    ∀ k a, a ∈ table s k → a ∈ oracleFunction G k := by
  intro k a ha
  change a ∈ ((s.map bit)[k]? : Part ℕ) at ha
  have hk : k < s.length := by
    by_contra hn
    simp [List.getElem?_eq_none (show (s.map bit).length ≤ k by simp; omega)] at ha
  have he : (s.map bit)[k]? = some (bit (s.getD k false)) := by
    simp [List.getD, hk]
  rw [he] at ha
  have hv : a = bit (s.getD k false) := by simpa using ha
  change a ∈ Part.some (bit (G k))
  rw [h k hk]
  exact Part.mem_some_iff.mpr hv

theorem run_mono {A : Oracle} {p : OracleCode} {s t : List Bool}
    (h : s <+: t) (n a : ℕ) (ha : a ∈ run A p s n) : a ∈ run A p t n := by
  apply OracleCode.eval_mono (c := p) (n := n) (a := a) ?_ ha
  intro k b hb
  cases hk : k.bodd with
  | false => simpa [partialJoin,hk] using hb
  | true =>
    exact table_mono h _ _ (by simpa [partialJoin,hk] using hb) |>
      (fun hh => by simpa [partialJoin,hk] using hh)

theorem run_total {A G : Oracle} {p : OracleCode} {s : List Bool}
    (h : Extends G s) (n a : ℕ) (ha : a ∈ run A p s n) :
    a ∈ OracleCode.eval (oracleFunction (join A G)) p n := by
  apply OracleCode.eval_mono (c := p) (n := n) (a := a) ?_ ha
  intro k b hb
  cases hk : k.bodd with
  | false => simpa [partialJoin, oracleFunction, join, hk] using hb
  | true =>
    have ht : b ∈ table s (k/2) := by simpa [partialJoin,hk] using hb
    simpa [oracleFunction,join,hk] using table_total h _ _ ht

def initialWord (G : Oracle) (m : ℕ) : List Bool := (List.range m).map G

@[simp] theorem prefix_length (G : Oracle) (m : ℕ) : (initialWord G m).length = m := by
  simp [initialWord]

@[simp] theorem prefix_getD (G : Oracle) (m i : ℕ) (hi : i < m) :
    (initialWord G m).getD i false = G i := by
  simp [initialWord,List.getD,List.getElem?_range hi]

theorem extends_prefix (G : Oracle) (m : ℕ) : Extends G (initialWord G m) := by
  intro i hi
  exact (prefix_getD G m i (by simpa using hi)).symm

theorem prefix_mono (G : Oracle) {m n : ℕ} (h : m ≤ n) : initialWord G m <+: initialWord G n := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using h, ?_⟩
  intro i hi
  simp [initialWord]

theorem table_prefix (G : Oracle) (m : ℕ) :
    table (initialWord G m) = BranchMachine.lookup (UniformOracle.oraclePrefix (fun k => bit (G
      k)) m) := by
  simp only [table,initialWord,UniformOracle.oraclePrefix,List.map_map,Function.comp_def]
  rfl

theorem run_approximates (A G : Oracle) (p : OracleCode) (n : ℕ) :
    Approximates (OracleCode.eval (oracleFunction (join A G)) p n)
      (fun m => run A p (initialWord G m) n) := by
  have he : partialJoin (oracleFunction A) (oracleFunction G) = oracleFunction (join A G) := by
    funext k
    cases hk : k.bodd <;> simp [partialJoin,oracleFunction,join,hk]
  rw [←he]
  apply OracleCode.eval_approximates
  intro k
  apply BranchMachine.partialJoin_approximates
  · intro k; exact Approximates.const _
  · intro k
    simpa only [table_prefix,oracleFunction,bit] using UniformOracle.prefix_approximates (fun k =>
      bit (G k)) k

theorem prefix_of_extends {G : Oracle} {s : List Bool} (h : Extends G s)
    {m : ℕ} (hm : s.length ≤ m) : s <+: initialWord G m := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using hm, ?_⟩
  intro i hi
  have hh := h i hi
  simpa [List.getD,List.getElem?_eq_getElem hi,initialWord,List.getElem_map,List.getElem_range]
    using hh.symm

theorem run_finite_extension {A G : Oracle} {p : OracleCode} {s : List Bool}
    (h : Extends G s) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (join A G)) p n) :
    ∃ t, s <+: t ∧ a ∈ run A p t n := by
  obtain ⟨m,hm⟩ := (run_approximates A G p n).2 a ha
  exact ⟨initialWord G (max m s.length),prefix_of_extends h (le_max_right _ _),
    hm _ (le_max_left _ _)⟩

def Disagree (A : Oracle) (p q : OracleCode) (s t : List Bool) : Prop :=
  ∃ n a b, a ≠ b ∧ a ∈ run A p s n ∧ b ∈ run A q t n

def Agree (A : Oracle) (p q : OracleCode) (s t : List Bool) : Prop :=
  ∀ u v n a b, s <+: u → t <+: v →
    a ∈ run A p u n → b ∈ run A q v n → a = b

def Requirement (A : Oracle) (p q : OracleCode) (s t : List Bool) : Prop :=
  Disagree A p q s t ∨ Agree A p q s t

theorem requirement_dense (A : Oracle) (p q : OracleCode) (s t : List Bool) :
    ∃ u v, s <+: u ∧ t <+: v ∧ Requirement A p q u v := by
  classical
  by_cases h : ∃ u v, s <+: u ∧ t <+: v ∧ Disagree A p q u v
  · obtain ⟨u,v,hu,hv,hh⟩ := h
    exact ⟨u,v,hu,hv,Or.inl hh⟩
  · refine ⟨s,t,List.prefix_rfl,List.prefix_rfl,Or.inr ?_⟩
    intro u v n a b hu hv ha hb
    by_contra hab
    exact h ⟨u,v,hu,hv,n,a,b,hab,ha,hb⟩

theorem requirement_mono {A : Oracle} {p q : OracleCode} {s t u v : List Bool}
    (hs : s <+: u) (ht : t <+: v) (h : Requirement A p q s t) :
    Requirement A p q u v := by
  rcases h with ⟨n,a,b,hab,ha,hb⟩ | h
  · exact Or.inl ⟨n,a,b,hab,run_mono hs n a ha,run_mono ht n b hb⟩
  · exact Or.inr (fun x y n a b hx hy => h x y n a b (hs.trans hx) (ht.trans hy))

theorem agree_of_common_output {A G H Y : Oracle} {p q : OracleCode} {s t : List Bool}
    (hs : Extends G s) (ht : Extends H t) (hR : Requirement A p q s t)
    (hp : OracleCode.eval (oracleFunction (join A G)) p = oracleFunction Y)
    (hq : OracleCode.eval (oracleFunction (join A H)) q = oracleFunction Y) :
    Agree A p q s t := by
  rcases hR with ⟨n,a,b,hab,ha,hb⟩ | hR
  · have ha' := run_total hs n a ha
    have hb' := run_total ht n b hb
    rw [hp] at ha'
    rw [hq] at hb'
    exact False.elim (hab (Part.mem_unique ha' hb'))
  · exact hR

theorem agreeing_search_sound {A H Y : Oracle} {p q : OracleCode} {s t : List Bool}
    (ht : Extends H t) (h : Agree A p q s t)
    (hq : OracleCode.eval (oracleFunction (join A H)) q = oracleFunction Y)
    (w : List Bool) (n a : ℕ) (ha : a ∈ run A p (s ++ w) n) : a = bit (Y n) := by
  have hb : bit (Y n) ∈ OracleCode.eval (oracleFunction (join A H)) q n := by
    rw [hq]; exact Part.mem_some _
  obtain ⟨v,hv,hb'⟩ := run_finite_extension ht n (bit (Y n)) hb
  exact h (s ++ w) v n a (bit (Y n)) (List.prefix_append s w) hv ha hb'

theorem agreeing_search_complete {A G Y : Oracle} {p : OracleCode} {s : List Bool}
    (hs : Extends G s)
    (hp : OracleCode.eval (oracleFunction (join A G)) p = oracleFunction Y) (n : ℕ) :
    ∃ w a, a ∈ run A p (s ++ w) n := by
  have ha : bit (Y n) ∈ OracleCode.eval (oracleFunction (join A G)) p n := by
    rw [hp]; exact Part.mem_some _
  obtain ⟨u,⟨w,rfl⟩,hu⟩ := run_finite_extension hs n (bit (Y n)) ha
  exact ⟨w,bit (Y n),hu⟩

end TuringRigidity.CommonIdeal

end OAI
