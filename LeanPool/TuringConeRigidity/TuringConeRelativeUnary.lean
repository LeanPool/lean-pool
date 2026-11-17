/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeRelativeUnary.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeRelativeRelations
public import LeanPool.TuringConeRigidity.SetModels.FixedArithmetic

/-!
# Localized unary coding in a principal cone

For arbitrary oracles A and X, the predicate X has a coded copy in the cone
above deg A whose parameters lie between deg A and deg(X join A'). The bound
uses X join A', not the jump of X. This is the relative coding input needed
for forward locality of partial cone isomorphisms.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeRelativeCoding

open EncodedForcing OracleJump ArithmeticHierarchy UniformOracle
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Regard a set code as a unary relation code. -/
def unaryCode (p : SetCode) : RelationCode 1 := ⟨fun _ => p, p.tags⟩

theorem unaryCode_holds (a : Degree) (p : SetCode) (x : Degree) :
    ConeCoding.Holds a (unaryCode p) (one x) ↔ ∃ c, ConeCoding.Graph a p x c := by
  constructor
  · rintro ⟨c, hc, _⟩
    exact ⟨c 0, hc 0⟩
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => c, ?_, ?_⟩
    · intro i
      fin_cases i
      exact hc
    · have he : Finset.univ.sup (fun _ : Fin 1 => c) = c :=
        le_antisymm (Finset.sup_le fun _ _ => le_rfl)
          (Finset.le_sup (f := fun _ : Fin 1 => c) (Finset.mem_univ 0))
      change ConeCoding.Antichain a p.tags (a ⊔ Finset.univ.sup (fun _ : Fin 1 => c))
      rw [he, sup_eq_right.mpr hc.2.2.1.1]
      exact hc.2.2.1

theorem unaryCode_above {p : SetCode} {a : Degree} (h : SetAbove p a) :
    RelationAbove (unaryCode p) a := ⟨fun _ => h, h.2.1⟩

theorem unaryCode_below {p : SetCode} {b : Degree} (h : SetBelow p b) :
    RelationBelow (unaryCode p) b := ⟨fun _ => h, h.2.1⟩

/-- The empty antichain code with all three parameters equal to the cone base. -/
def emptyAntichain (a : Degree) : AntichainCode := ⟨a, a, a⟩

theorem emptyAntichain_holds (a x : Degree) :
    ¬ ConeCoding.Antichain a (emptyAntichain a) x := by
  rintro ⟨hax, ⟨_, z, hz, _, hn⟩, _⟩
  apply hn
  simpa only [emptyAntichain, sup_eq_right.mpr hax] using hz

/-- The empty relation code of the specified arity with all parameters at the cone base. -/
def emptyRelation (a : Degree) (n : ℕ) : RelationCode n :=
  ⟨fun _ => ⟨a, emptyAntichain a, emptyAntichain a⟩, emptyAntichain a⟩

theorem emptyRelation_above (a : Degree) (n : ℕ) : RelationAbove (emptyRelation a n) a :=
  ⟨fun _ => ⟨le_rfl, ⟨le_rfl, le_rfl, le_rfl⟩, ⟨le_rfl, le_rfl, le_rfl⟩⟩,
    ⟨le_rfl, le_rfl, le_rfl⟩⟩

theorem emptyRelation_below (a b : Degree) (h : a ≤ b) (n : ℕ) :
    RelationBelow (emptyRelation a n) b :=
  ⟨fun _ => ⟨h, ⟨h, h, h⟩, ⟨h, h, h⟩⟩, ⟨h, h, h⟩⟩

theorem emptyRelation_holds (a : Degree) (n : ℕ) (v : Fin n → Degree) :
    ¬ ConeCoding.Holds a (emptyRelation a n) v := by
  rintro ⟨c, _, hc⟩
  exact emptyAntichain_holds a _ hc

/-- Code an arbitrary unary predicate on a fixed low relative frame. -/
theorem predicate_code (A C G : Oracle) (hAC : Reduces A C)
    (hind : Independent C G) (hbase : ∀ k, degree A ≤ degree (columns C k))
    (hlow : Reduces (jump (join C G)) (jump A)) (X : Oracle) :
    ∃ p : RelationCode 1, RelationAbove p (degree A) ∧
      RelationBelow p (degree (join X (jump A))) ∧
      ∀ x, ConeCoding.Holds (degree A) p (one x) ↔
        ∃ k, X k = true ∧ x = degree (columns C k) := by
  by_cases hne : ∃ k, X k = true
  · obtain ⟨k₀, hk₀⟩ := hne
    let P := fun k => X k = true
    let select := EffectivePresentation.pick P k₀
    have hP : RecursivePred X P := by
      have hq : Nat.RecursiveIn {oracleFunction X} (oracleFunction X) := .oracle _
        (Set.mem_singleton _)
      exact hq.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction, P, hx])
    have hs := EffectivePresentation.pick_recursive hP k₀
    have hsel (k : ℕ) : X (select k) = true := by
      by_cases hk : X k = true
      · simpa only [select, EffectivePresentation.pick, P, ite_eq_left hk] using hk
      · simpa only [select, EffectivePresentation.pick, P, ite_eq_right hk] using hk₀
    have hfix (k : ℕ) (hk : X k = true) : select k = k := by
      simp only [select, EffectivePresentation.pick, P, ite_eq_left hk]
    let B := join C G
    let T := pad A G
    let F := EffectiveFamilies.mix C T
    have hT : Reduces T B := reduces_trans (pad_reduces A G) (join_mono hAC (reduces_refl G))
    have hF : Reduces F B := reduces_trans (EffectiveFamilies.mix_reduces C T)
      (join_reduces (reduces_join_left C G) hT)
    have hcol (k : ℕ) : degree (columns C k) ≤ degree C :=
      CodingExtraction.column_projection_reduces C k
    have htag (x y : Degree) (hx : x ≤ degree C) (hy : y ≤ degree C)
        (hax : degree A ≤ x) (hay : degree A ≤ y) (i j : ℕ) :
        x ⊔ degree (columns T i) ≤ y ⊔ degree (columns T j) ↔ x ≤ y ∧ i = j :=
      padded_tag_order hind x y hx hy hax hay i j
    have hAntiT : ∀ i j, degree (columns T i) ≤ degree (columns T j) →
        degree (columns T i) = degree (columns T j) := by
      intro i j hij
      have h := (htag (degree A) (degree A) hAC hAC le_rfl le_rfl i j).mp
        (sup_le_sup_left hij (degree A))
      rw [h.2]
    have hAntiF : ∀ i j, degree (columns F (select i)) ≤ degree (columns F (select j)) →
        degree (columns F (select i)) = degree (columns F (select j)) := by
      intro i j hij
      have h := (htag _ _ (hcol _) (hcol _) (hbase _) (hbase _) _ _).mp (by
        simpa only [F, EffectiveFamilies.mix_column, join_degree] using hij)
      exact congrArg (fun k => degree (columns F k)) h.2
    have haB : degree A ≤ degree B := hAC.trans (reduces_join_left C G)
    obtain ⟨pc, hac, hpc, hpcspec⟩ := antichain_code (degree A) hT haB
      (base_le_pad_column A G) hAntiT
    obtain ⟨pt, hat, hpt, hptspec⟩ := selected_antichain_code (degree A) hF haB select hs
      (fun k => by
        rw [show F = EffectiveFamilies.mix C T from rfl, EffectiveFamilies.mix_column]
        exact (hbase _).trans (reduces_join_left _ _)) hAntiF
    let ps : SetCode := ⟨degree C, pc, pt⟩
    have hB : degree B ≤ degree (join X (jump A)) :=
      (reduces_jump B).trans (hlow.trans (reduces_join_right _ _))
    have hps : SetBelow ps (degree (join X (jump A))) :=
      ⟨(reduces_join_left C G).trans hB,
        hpc.mono (hlow.trans (reduces_join_right _ _)),
        hpt.mono (join_mono (reduces_refl X) hlow)⟩
    refine ⟨unaryCode ps, unaryCode_above ⟨hAC, hac, hat⟩, unaryCode_below hps, ?_⟩
    intro x
    rw [unaryCode_holds]
    constructor
    · rintro ⟨c, hax, hx, hc, hd⟩
      obtain ⟨i, rfl⟩ := (hpcspec c).mp hc
      obtain ⟨j, hj⟩ := (hptspec (x ⊔ degree (columns T i))).mp hd
      have he : degree (columns C (select j)) ⊔ degree (columns T (select j)) =
          x ⊔ degree (columns T i) := by
        simpa only [F, EffectiveFamilies.mix_column, join_degree] using hj
      have h₀ := (htag _ x (hcol _) hx (hbase _) hax _ _).mp he.le
      have h₁ := (htag x _ hx (hcol _) hax (hbase _) _ _).mp he.ge
      exact ⟨select j, hsel j, le_antisymm h₁.1 h₀.1⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨degree (columns T k), hbase k, hcol k, (hpcspec _).mpr ⟨k, rfl⟩, ?_⟩
      apply (hptspec _).mpr
      refine ⟨k, ?_⟩
      rw [hfix k hk, show F = EffectiveFamilies.mix C T from rfl, EffectiveFamilies.mix_column]
      rfl
  · have ha : degree A ≤ degree (join X (jump A)) :=
      (reduces_jump A).trans (reduces_join_right _ _)
    refine ⟨emptyRelation (degree A) 1, emptyRelation_above _ _,
      emptyRelation_below _ _ ha _, ?_⟩
    intro x
    exact ⟨fun h => False.elim (emptyRelation_holds _ _ _ h),
      fun ⟨k, hk, _⟩ => False.elim (hne ⟨k, hk⟩)⟩

/-- Relative localized unary coding, with all parameters in the cone. -/
theorem localized_copy (A X : Oracle) :
    ∃ c : ConeCoding.Copy (degree A) (fun n => X n = true),
      RelationAbove c.successor (degree A) ∧ RelationAbove c.predicate (degree A) ∧
      RelationBelow c.successor (degree (join X (jump A))) ∧
      RelationBelow c.predicate (degree (join X (jump A))) := by
  obtain ⟨C, _, hlow, hind⟩ := CohenColumns.uniform_low_independent A
  let N := pad A C
  let B := join A C
  have hNB : Reduces N B := pad_reduces A C
  have hAN : Reduces A N :=
    reduces_trans (base_le_pad_column A C 0) (CodingExtraction.column_projection_reduces N 0)
  have hNlow : Reduces (jump N) (jump A) := by
    change degree (jump N) ≤ degree (jump A)
    rw [← hlow]
    exact jump_mono hNB
  have hinj : Function.Injective (fun k => degree (columns N k)) := by
    intro i j he
    have hh := (hind (degree A) (degree A) le_rfl le_rfl i {j}).mp (by
      simpa only [N, pad_column, join_degree, Finset.sup_singleton] using he.le)
    simpa only [Finset.mem_singleton] using hh.2
  have hrows : Reduces (FixedArithmetic.rows N) B :=
    reduces_trans (FixedArithmetic.rows_reduces N) hNB
  have hbase : ∀ i : Fin 2, ∀ j,
      degree A ≤ degree (columns (FixedArithmetic.rows N) (Nat.pair i.val j)) := by
    intro i j
    fin_cases i
    · simpa only [FixedArithmetic.row_zero] using base_le_pad_column A C j
    · simpa only [FixedArithmetic.row_one] using base_le_pad_column A C (j + 1)
  obtain ⟨S, haS, hS, hs⟩ := relation_sequence A (FixedArithmetic.rows N) B
    (reduces_join_left A C) hrows 2 hbase
  have hS' : RelationBelow S (degree (jump A)) := hlow ▸ hS
  have hspec (x y : Degree) : ConeCoding.Holds (degree A) S (two x y) ↔
      ∃ k, x = degree (columns N k) ∧ y = degree (columns N (k + 1)) := by
    rw [hs]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [two] using (hk 0).symm, by simpa [two] using (hk 1).symm⟩
    · rintro ⟨k, rfl, rfl⟩
      refine ⟨k, fun i => ?_⟩
      fin_cases i <;> simp [two]
  obtain ⟨G, _, hglow, hg⟩ := CohenColumns.uniform_low_independent N
  have hglow' : Reduces (jump (join N G)) (jump A) := by
    change degree (jump (join N G)) ≤ degree (jump A)
    rw [hglow]
    exact hNlow
  obtain ⟨P, haP, hP, hp⟩ := predicate_code A N G hAN hg
    (base_le_pad_column A C) hglow' X
  let node (n : ℕ) : Set.Ici (degree A) :=
    ⟨degree (columns N n), Set.mem_Ici.mpr (base_le_pad_column A C n)⟩
  have hnode (x : Set.Ici (degree A)) (k : ℕ) :
      x.val = degree (columns N k) ↔ x = node k :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let c : ConeCoding.Copy (degree A) (fun n => X n = true) :=
    { node := node
      injective := fun i j h => hinj (congrArg Subtype.val h)
      successor := S
      predicate := P
      successor_spec := by
        intro x y
        rw [hspec]
        exact exists_congr (fun k => and_congr (hnode x k) (hnode y (k + 1)))
      predicate_spec := by
        intro x
        rw [hp]
        exact exists_congr (fun k => and_congr_right (fun _ => hnode x k)) }
  exact ⟨c, haS, haP, hS'.mono (reduces_join_right _ _), hP⟩

end
end OAI.TuringRigidity.ConeRelativeCoding
