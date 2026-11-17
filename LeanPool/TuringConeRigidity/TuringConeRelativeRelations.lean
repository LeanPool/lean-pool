/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeRelativeRelations.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeRelativeAntichain
public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumns

/-!
# Uniform relation codes inside a principal cone

Tags carry the base oracle. Independence is used only for degrees above that
base, and the empty tuple has join equal to the base, not the ambient bottom.
All coding parameters lie above the base and below one jump of the data bound.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeRelativeCoding

open EncodedForcing OracleJump ArithmeticHierarchy
open SetCoding RelationCoding BoundedDecoding EffectiveFamilies

noncomputable section

theorem join_degree (A B : Oracle) : degree (join A B) = degree A ⊔ degree B := rfl

/-- The independence conclusion of the existing relative Cohen construction. -/
def Independent (B G : Oracle) : Prop :=
  ∀ x y : Degree, x ≤ degree B → y ≤ degree B → ∀ i (F : Finset ℕ),
    x ⊔ degree (columns G i) ≤ y ⊔ F.sup (fun j => degree (columns G j)) ↔
      x ≤ y ∧ i ∈ F

theorem absorb_base {a x : Degree} (h : a ≤ x) (z : Degree) :
    x ⊔ (a ⊔ z) = x ⊔ z := by
  rw [← sup_assoc, sup_eq_left.mpr h]

theorem padded_tag_order {A B G : Oracle} (hind : Independent B G)
    (x y : Degree) (hx : x ≤ degree B) (hy : y ≤ degree B)
    (hax : degree A ≤ x) (hay : degree A ≤ y) (i j : ℕ) :
    x ⊔ degree (columns (pad A G) i) ≤ y ⊔ degree (columns (pad A G) j) ↔
      x ≤ y ∧ i = j := by
  rw [pad_column, pad_column]
  change x ⊔ (degree A ⊔ degree (columns G i)) ≤
    y ⊔ (degree A ⊔ degree (columns G j)) ↔ _
  rw [absorb_base hax, absorb_base hay]
  simpa only [Finset.sup_singleton, Finset.mem_singleton] using hind x y hx hy i {j}

theorem coordinate_code {A R B G : Oracle} (hAB : Reduces A B) (hRB : Reduces R B)
    (hind : Independent B G) (i : ℕ)
    (hbase : ∀ j, degree A ≤ degree (columns R (Nat.pair i j))) :
    ∃ p : SetCode, SetAbove p (degree A) ∧
      SetBelow p (degree (jump (join B G))) ∧
      ∀ x c, ConeCoding.Graph (degree A) p x c ↔
        ∃ j, degree (columns R (Nat.pair i j)) = x ∧
          degree (columns (pad A G) (Nat.pair i j)) = c := by
  let T := pad A G
  have hdata (j : ℕ) : degree (columns R (Nat.pair i j)) ≤ degree B :=
    reduces_trans (CodingExtraction.column_projection_reduces R _) hRB
  have htag (x y : Degree) (hx : x ≤ degree B) (hy : y ≤ degree B)
      (hax : degree A ≤ x) (hay : degree A ≤ y) (j k : ℕ) :
      x ⊔ degree (columns T (Nat.pair i j)) ≤ y ⊔ degree (columns T (Nat.pair i k)) ↔
        x ≤ y ∧ j = k := by
    simpa [T] using padded_tag_order hind x y hx hy hax hay (Nat.pair i j) (Nat.pair i k)
  have hanti : ∀ j k, degree (columns (slice T i) j) ≤ degree (columns (slice T i) k) →
      degree (columns (slice T i) j) = degree (columns (slice T i) k) := by
    intro j k hjk
    have h := (htag (degree A) (degree A) hAB hAB le_rfl le_rfl j k).mp (by
      simpa only [slice_column, T, pad_column, join_degree, ← sup_assoc, sup_idem] using hjk)
    rw [h.2]
  have had : ∀ j k, degree (columns (mix (slice R i) (slice T i)) j) ≤
      degree (columns (mix (slice R i) (slice T i)) k) →
      degree (columns (mix (slice R i) (slice T i)) j) =
        degree (columns (mix (slice R i) (slice T i)) k) := by
    intro j k hjk
    have h := (htag _ _ (hdata j) (hdata k) (hbase j) (hbase k) j k).mp (by
      simp only [mix_column, slice_column] at hjk
      exact hjk)
    rw [h.2]
  have hT : Reduces T (join B G) :=
    reduces_trans (pad_reduces A G) (join_mono hAB (reduces_refl G))
  have htBound : Reduces (slice T i) (join B G) :=
    reduces_trans (slice_reduces T i) hT
  have hdBound : Reduces (mix (slice R i) (slice T i)) (join B G) :=
    reduces_trans (mix_reduces _ _) (join_reduces
      (reduces_trans (slice_reduces R i) (reduces_trans hRB (reduces_join_left B G))) htBound)
  have haBound : degree A ≤ degree (join B G) := hAB.trans (reduces_join_left B G)
  obtain ⟨pc, hac, hpc, hc⟩ := antichain_code (degree A) htBound haBound
    (fun j => by simpa only [slice_column] using base_le_pad_column A G (Nat.pair i j)) hanti
  obtain ⟨pd, had', hpd, hd⟩ := antichain_code (degree A) hdBound haBound
    (fun j => by
      rw [mix_column, slice_column]
      exact (hbase j).trans (reduces_join_left _ _)) had
  refine ⟨⟨degree B, pc, pd⟩, ⟨hAB, hac, had'⟩,
    ⟨(reduces_join_left B G).trans (reduces_jump _), hpc, hpd⟩, ?_⟩
  intro x c
  change (degree A ≤ x ∧ x ≤ degree B ∧ ConeCoding.Antichain (degree A) pc c ∧
    ConeCoding.Antichain (degree A) pd (x ⊔ c)) ↔ _
  rw [hc, hd]
  simp only [slice_column, mix_column]
  constructor
  · rintro ⟨hax, hx, ⟨j, rfl⟩, ⟨k, hk⟩⟩
    have hl := (htag _ x (hdata k) hx (hbase k) hax k j).mp hk.le
    have hr := (htag x _ hx (hdata k) hax (hbase k) j k).mp hk.ge
    have hkj := hl.2
    subst k
    exact ⟨j, le_antisymm hl.1 hr.1, rfl⟩
  · rintro ⟨j, rfl, rfl⟩
    exact ⟨hbase j, hdata j, ⟨j, rfl⟩, ⟨j, rfl⟩⟩

theorem tag_below_tuple {A B G : Oracle} (hAB : Reduces A B) (hind : Independent B G)
    {n i j k : ℕ}
    (h : degree (columns (pad A G) (Nat.pair i j)) ≤
      degree (columns (pad A (tuples G n)) k)) : j = k := by
  classical
  let F := (Finset.range n).image (fun l => Nat.pair l k)
  have hh : degree A ⊔ degree (columns G (Nat.pair i j)) ≤
      degree A ⊔ F.sup (fun l => degree (columns G l)) := by
    simpa only [pad_column, join_degree, tuples_degree, F, Finset.sup_image, Function.comp_def]
      using h
  have hm := (hind (degree A) (degree A) hAB hAB (Nat.pair i j) F).mp hh
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hm.2
  simpa only [Nat.unpair_pair] using (congrArg (fun m => (Nat.unpair m).2) hl).symm

theorem padded_tuples_antichain {A B G : Oracle} (hAB : Reduces A B)
    (hind : Independent B G) (n : ℕ) :
    ∀ j k, degree (columns (pad A (tuples G n)) j) ≤
      degree (columns (pad A (tuples G n)) k) →
      degree (columns (pad A (tuples G n)) j) = degree (columns (pad A (tuples G n)) k) := by
  intro j k hjk
  cases n with
  | zero => simp only [pad_column, join_degree, tuples_degree, Finset.range_zero, Finset.sup_empty]
  | succ n =>
    have htag : degree (columns (pad A G) (Nat.pair 0 j)) ≤
        degree (columns (pad A (tuples G (n + 1))) j) := by
      simp only [pad_column, join_degree, tuples_degree]
      exact sup_le_sup_left (Finset.le_sup (f := fun i => degree (columns G (Nat.pair i j)))
        (by simp)) _
    have he := tag_below_tuple hAB hind (htag.trans hjk)
    rw [he]

theorem fin_sup (n : ℕ) (f : ℕ → Degree) :
    Finset.univ.sup (fun i : Fin n => f i.val) = (Finset.range n).sup f := by
  classical
  have he : (Finset.univ : Finset (Fin n)).image Fin.val = Finset.range n := by
    ext m
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ha ▸ a.isLt, fun hm => ⟨⟨m, hm⟩, rfl⟩⟩
  simpa only [Finset.sup_image, Function.comp_def] using congrArg (fun F : Finset ℕ => F.sup f) he

theorem sup_padded {ι : Type*} (a : Degree) (s : Finset ι) (f : ι → Degree) :
    a ⊔ s.sup (fun i => a ⊔ f i) = a ⊔ s.sup f := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Finset.sup_le
    intro i hi
    exact sup_le le_sup_left ((Finset.le_sup (f := f) hi).trans le_sup_right)
  · apply sup_le le_sup_left
    apply Finset.sup_le
    intro i hi
    exact (le_sup_right : f i ≤ a ⊔ f i).trans
      ((Finset.le_sup (f := fun i => a ⊔ f i) hi).trans le_sup_right)

theorem relation_code {A R B G : Oracle} (hAB : Reduces A B) (hRB : Reduces R B)
    (hind : Independent B G) (n : ℕ)
    (hbase : ∀ i : Fin n, ∀ j, degree A ≤ degree (columns R (Nat.pair i.val j))) :
    ∃ p : RelationCode n, RelationAbove p (degree A) ∧
      RelationBelow p (degree (jump (join B G))) ∧
      ∀ v, ConeCoding.Holds (degree A) p v ↔
        ∃ j, ∀ i : Fin n, degree (columns R (Nat.pair i.val j)) = v i := by
  classical
  choose pc hac hpc hc using fun i : Fin n => coordinate_code hAB hRB hind i.val (hbase i)
  obtain ⟨pt, hat, hpt, ht⟩ := antichain_code (degree A)
    (reduces_trans (pad_reduces A (tuples G n)) (join_mono hAB (tuples_reduces G n)))
    (hAB.trans (reduces_join_left B G)) (base_le_pad_column A (tuples G n))
    (padded_tuples_antichain hAB hind n)
  refine ⟨⟨pc, pt⟩, ⟨hac, hat⟩, ⟨hpc, hpt⟩, ?_⟩
  intro v
  constructor
  · rintro ⟨c, hgraph, hT⟩
    obtain ⟨j, hj⟩ := (ht _).mp hT
    refine ⟨j, fun i => ?_⟩
    obtain ⟨k, hkv, hkc⟩ := (hc i _ _).mp (hgraph i)
    have hle : degree (columns (pad A G) (Nat.pair i.val k)) ≤
        degree (columns (pad A (tuples G n)) j) := by
      rw [hkc, hj]
      exact (Finset.le_sup (f := c) (Finset.mem_univ i)).trans le_sup_right
    have he := tag_below_tuple hAB hind hle
    simpa only [he] using hkv
  · rintro ⟨j, hj⟩
    let c := fun i : Fin n => degree (columns (pad A G) (Nat.pair i.val j))
    refine ⟨c, fun i => (hc i _ _).mpr ⟨j, hj i, rfl⟩, (ht _).mpr ⟨j, ?_⟩⟩
    simp only [pad_column, join_degree, tuples_degree, c]
    rw [sup_padded]
    exact congrArg (fun z : Degree => degree A ⊔ z)
      (fin_sup n (fun i => degree (columns G (Nat.pair i j)))).symm

/-- Relativized effective coding, with a bound fixed before choosing tags. -/
theorem relation_sequence (A R B : Oracle) (hAB : Reduces A B) (hRB : Reduces R B)
    (n : ℕ) (hbase : ∀ i : Fin n, ∀ j, degree A ≤ degree (columns R (Nat.pair i.val j))) :
    ∃ p : RelationCode n, RelationAbove p (degree A) ∧
      RelationBelow p (degree (jump B)) ∧
      ∀ v, ConeCoding.Holds (degree A) p v ↔
        ∃ j, ∀ i : Fin n, degree (columns R (Nat.pair i.val j)) = v i := by
  obtain ⟨G, _, hg, hlow⟩ := CohenLowness.relative_low_generic B
  obtain ⟨p, ha, hp, hs⟩ := relation_code hAB hRB (CohenColumns.independence hg) n hbase
  exact ⟨p, ha, hlow ▸ hp, hs⟩

end
end OAI.TuringRigidity.ConeRelativeCoding
