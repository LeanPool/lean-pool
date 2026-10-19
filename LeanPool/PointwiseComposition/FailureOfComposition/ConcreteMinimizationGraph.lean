/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteEvaluatorGraph

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
PA graph laws for concrete minimization programs.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Encodable

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace ConcreteEvaluator

noncomputable section

private theorem rfind_tag (c : Nat.Partrec.Code) :
    partrecCodeTag (encode (Nat.Partrec.Code.rfind' c)) = 7 :=
  by
  have hb (n : ℕ) : n.bodd.toNat = n % 2 := by rw [Nat.mod_two_of_bodd]
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode]
  have h : ¬2 * (2 * Nat.Partrec.Code.encodeCode c + 1) + 1 + 4 < 4 := by omega
  simp only [partrecCodeTag, h, ite_false, hb, Nat.div2_val]
  omega

private theorem rfind_payload (c : Nat.Partrec.Code) :
    partrecCodePayload (encode (Nat.Partrec.Code.rfind' c)) = encode c :=
  by
  simp only [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode, partrecCodePayload,
    Nat.div2_val]
  omega

private def pairedStageFormula (q : ℕ) : ArithmeticSemisentence 4 :=
  “s a m y. ∃ u, !pairDef u a m ∧ !evalnCertificateFormula.val s !!(q)u y”

private def pairedEventualFormula (q : ℕ) : ArithmeticSemisentence 3 :=
  “a m y. ∃ u, !pairDef u a m ∧ !(eventualGraph q).val u y”

variable {M : Type*} [ORingStructure M]

section

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private abbrev sc (q : ℕ) (s a m y : M) : Prop :=
  Semiformula.Evalb ![s, (q : M), FFL.FirstOrder.Arithmetic.pair a m, y]
    (evalnCertificateFormula : ArithmeticSemisentence 4)

private abbrev egp (q : ℕ) (a m y : M) : Prop :=
  (eventualGraph q).val.Evalb ![FFL.FirstOrder.Arithmetic.pair a m, y]

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private theorem pairedStageFormula_eval (q : ℕ) (s a m y : M) :
    (pairedStageFormula q).Evalb ![s, a, m, y] ↔ sc q s a m y := by
  simp [pairedStageFormula, sc, numeral_eq_natCast]

private theorem pairedEventualFormula_eval (q : ℕ) (a m y : M) :
    (pairedEventualFormula q).Evalb ![a, m, y] ↔ egp q a m y := by
  simp [pairedEventualFormula, egp]

private theorem egp_iff (q : ℕ) (a m y : M) : egp q a m y ↔ ∃ s : M, sc q s a m y := by
  simpa only [sc, egp, numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
    eventualGraph_eval q ![FFL.FirstOrder.Arithmetic.pair a m, y]

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private theorem sc_rfind (f : Nat.Partrec.Code) (s a m y : M) (hs : 0 < s) :
    sc (encode (Nat.Partrec.Code.rfind' f)) s a m y ↔
      FFL.FirstOrder.Arithmetic.pair a m < s ∧
        ∃ v : M,
          sc (encode f) s a m v ∧
            ((0 < v ∧ sc (encode (Nat.Partrec.Code.rfind' f)) (s - 1) a (m + 1) y) ∨
              (v = 0 ∧ y = m)) :=
  by
  simpa only [sc, rfind_payload, FFL.FirstOrder.Arithmetic.pi₁_pair,
    FFL.FirstOrder.Arithmetic.pi₂_pair] using
    evalnCertificateFormula_tag_seven_iff (encode (Nat.Partrec.Code.rfind' f)) (rfind_tag f) s
      (FFL.FirstOrder.Arithmetic.pair a m) y hs

end

private def forwardFormula (q p : ℕ) : ArithmeticSemisentence 1 :=
  “s.
    ∀ a m y,
      !(pairedStageFormula q)s a m y →
        (m ≤ y ∧
            !(pairedEventualFormula p)a y 0 ∧
              ∀ k, m ≤ k → k < y → ∃ v, v ≠ 0 ∧ !(pairedEventualFormula p)a k v)”

section

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private theorem forwardFormula_eval (q p : ℕ) (s : M) :
    (forwardFormula q p).Evalb ![s] ↔
      ∀ a m y : M,
        sc q s a m y →
          m ≤ y ∧ egp p a y 0 ∧ ∀ k : M, m ≤ k → k < y → ∃ v : M, v ≠ 0 ∧ egp p a k v :=
  by simp [forwardFormula, pairedStageFormula_eval, pairedEventualFormula_eval]

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private theorem rfind_forward (f : Nat.Partrec.Code) :
    ∀ s a m y : M,
      sc (encode (Nat.Partrec.Code.rfind' f)) s a m y →
        m ≤ y ∧
          egp (encode f) a y 0 ∧
            ∀ k : M, m ≤ k → k < y → ∃ v : M, v ≠ 0 ∧ egp (encode f) a k v :=
  by
  have := models_inductionScheme_univ (M := M)
  have : Inhabited M := ⟨0⟩
  intro s
  apply
    InductionScheme.succ_induction (C := Set.univ) (P := fun s : M =>
      ∀ a m y : M,
        sc (encode (Nat.Partrec.Code.rfind' f)) s a m y →
          m ≤ y ∧
            egp (encode f) a y 0 ∧
              ∀ k : M, m ≤ k → k < y → ∃ v : M, v ≠ 0 ∧ egp (encode f) a k v)
      ⟨fun _ => default,
        Rew.emb ▹ forwardFormula (encode (Nat.Partrec.Code.rfind' f)) (encode f), trivial, ?_⟩
      ?_ ?_ s
  · intro x
    rw [← forwardFormula_eval]
    simp [Semiformula.eval_emb]
  · intro a m y h
    have hh := (evalnCertificateFormula_eval_history_iff (0 : M) _ _ _).mp h
    have hlt := ((eval_codeHistoryEvaluator_succ_iff_cell (0 : M) _ _ _).mp hh).1
    exact False.elim ((not_lt_of_ge (FFL.FirstOrder.Arithmetic.zero_le _)) hlt)
  · intro s ih a m y h
    have hs : (0 : M) < s + 1 :=
      lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le s) (lt_add_one s)
    obtain ⟨_, v, hv, hcase⟩ := (sc_rfind f (s + 1) a m y hs).mp h
    rcases hcase with ⟨hvp, hr⟩ | ⟨hv0, rfl⟩
    · have hr' : sc (encode (Nat.Partrec.Code.rfind' f)) s a (m + 1) y := by
        simpa only [add_sub_self] using hr
      obtain ⟨hmy, hy, hp⟩ := ih a (m + 1) y hr'
      refine ⟨le_trans (le_self_add : m ≤ m + 1) hmy, hy, ?_⟩
      intro k hmk hky
      rcases eq_or_lt_of_le hmk with rfl | hmk'
      · exact ⟨v, ne_of_gt hvp, (egp_iff _ _ _ _).mpr ⟨s + 1, hv⟩⟩
      · exact hp k (FFL.FirstOrder.Arithmetic.succ_le_iff_lt.mpr hmk') hky
    · refine ⟨le_refl _, ?_, ?_⟩
      · exact (egp_iff _ _ _ _).mpr ⟨s + 1, by simpa only [hv0] using hv⟩
      · intro k hmk hkm
        exact False.elim ((not_lt_of_ge hmk) hkm)

private theorem rfind_stop (f : Nat.Partrec.Code) (a m : M) (h : egp (encode f) a m 0) :
    egp (encode (Nat.Partrec.Code.rfind' f)) a m m :=
  by
  obtain ⟨s, hs⟩ := (egp_iff _ _ _ _).mp h
  let u := FFL.FirstOrder.Arithmetic.pair a m
  have hu : u < s + u + 1 := lt_of_le_of_lt le_add_self (lt_add_one _)
  have hp : (0 : M) < s + u + 1 :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) (lt_add_one _)
  apply (egp_iff _ _ _ _).mpr
  refine ⟨s + u + 1, (sc_rfind f _ a m m hp).mpr ⟨hu, 0, ?_, Or.inr ⟨rfl, rfl⟩⟩⟩
  exact
    evalnCertificateFormula_natCode_persist (encode f) s (s + u + 1) u 0
      (le_trans le_self_add le_self_add) hs

private theorem rfind_next (f : Nat.Partrec.Code) (a m y : M)
    (h : ∃ v : M, v ≠ 0 ∧ egp (encode f) a m v)
    (hr : egp (encode (Nat.Partrec.Code.rfind' f)) a (m + 1) y) :
    egp (encode (Nat.Partrec.Code.rfind' f)) a m y :=
  by
  obtain ⟨v, hv, hvg⟩ := h
  obtain ⟨sv, hvs⟩ := (egp_iff _ _ _ _).mp hvg
  obtain ⟨sr, hrs⟩ := (egp_iff _ _ _ _).mp hr
  let u := FFL.FirstOrder.Arithmetic.pair a m
  let t := sv + sr + u
  have hu : u < t + 1 := lt_of_le_of_lt le_add_self (lt_add_one _)
  have ht : (0 : M) < t + 1 :=
    lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le _) (lt_add_one _)
  have hvp : 0 < v := lt_of_le_of_ne (FFL.FirstOrder.Arithmetic.zero_le v) (Ne.symm hv)
  apply (egp_iff _ _ _ _).mpr
  refine ⟨t + 1, (sc_rfind f _ a m y ht).mpr ⟨hu, v, ?_, Or.inl ⟨hvp, ?_⟩⟩⟩
  · exact
      evalnCertificateFormula_natCode_persist (encode f) sv (t + 1) u v
        (le_trans (le_trans le_self_add le_self_add) le_self_add) hvs
  · have hle : sr ≤ t := le_trans le_add_self le_self_add
    have hc :=
      evalnCertificateFormula_natCode_persist (encode (Nat.Partrec.Code.rfind' f)) sr t
        (FFL.FirstOrder.Arithmetic.pair a (m + 1)) y hle hrs
    simpa only [add_sub_self] using hc

end

private def reverseFormula (q p : ℕ) : ArithmeticSemisentence 1 :=
  “l.
    ∀ a m,
      (!(pairedEventualFormula p)a(m + l)0 ∧
            ∀ k, m ≤ k → k < m + l → ∃ v, v ≠ 0 ∧ !(pairedEventualFormula p)a k v) →
        !(pairedEventualFormula q)a m(m + l)”

section

variable [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private theorem reverseFormula_eval (q p : ℕ) (l : M) :
    (reverseFormula q p).Evalb ![l] ↔
      ∀ a m : M,
        (egp p a (m + l) 0 ∧ ∀ k : M, m ≤ k → k < m + l → ∃ v : M, v ≠ 0 ∧ egp p a k v) →
          egp q a m (m + l) :=
  by simp [reverseFormula, pairedEventualFormula_eval]

end

section

variable [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private theorem rfind_reverse (f : Nat.Partrec.Code) :
    ∀ l a m : M,
      (egp (encode f) a (m + l) 0 ∧
          ∀ k : M, m ≤ k → k < m + l → ∃ v : M, v ≠ 0 ∧ egp (encode f) a k v) →
        egp (encode (Nat.Partrec.Code.rfind' f)) a m (m + l) :=
  by
  have := models_inductionScheme_univ (M := M)
  have : Inhabited M := ⟨0⟩
  intro l
  apply
    InductionScheme.succ_induction (C := Set.univ) (P := fun l : M =>
      ∀ a m : M,
        (egp (encode f) a (m + l) 0 ∧
            ∀ k : M, m ≤ k → k < m + l → ∃ v : M, v ≠ 0 ∧ egp (encode f) a k v) →
          egp (encode (Nat.Partrec.Code.rfind' f)) a m (m + l))
      ⟨fun _ => default,
        Rew.emb ▹ reverseFormula (encode (Nat.Partrec.Code.rfind' f)) (encode f), trivial, ?_⟩
      ?_ ?_ l
  · intro x
    rw [← reverseFormula_eval]
    simp [Semiformula.eval_emb]
  · intro a m h
    simp only [add_zero] at h ⊢
    exact rfind_stop f a m h.1
  · intro l ih a m h
    have he : m + 1 + l = m + (l + 1) := by rw [add_assoc, add_comm (1 : M) l]
    have hml : m < m + (l + 1) :=
      by
      have h0 : (0 : M) < l + 1 :=
        lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le l) (lt_add_one l)
      simpa only [zero_add, add_zero, add_comm] using add_lt_add_left h0 m
    have hp := h.2 m (le_refl m) hml
    have hr : egp (encode (Nat.Partrec.Code.rfind' f)) a (m + 1) (m + 1 + l) :=
      by
      apply ih a (m + 1)
      refine ⟨by simpa only [he] using h.1, ?_⟩
      intro k hmk hky
      exact h.2 k (le_trans le_self_add hmk) (by simpa only [he] using hky)
    exact rfind_next f a m (m + (l + 1)) hp (by simpa only [he] using hr)

/-- The complete existential-stage graph of minimization from candidate zero.
The candidate bound and every computation stage range over the PA model. -/
theorem eventualGraph_rfind_code_eval (f : Nat.Partrec.Code) (a y : M) :
    (eventualGraph (encode (Nat.Partrec.Code.rfind' f))).val.Evalb
        ![FFL.FirstOrder.Arithmetic.pair a 0, y] ↔
      (eventualGraph (encode f)).val.Evalb ![FFL.FirstOrder.Arithmetic.pair a y, 0] ∧
        ∀ k : M,
          k < y →
            ∃ z : M,
              z ≠ 0 ∧
                (eventualGraph (encode f)).val.Evalb ![FFL.FirstOrder.Arithmetic.pair a k, z] :=
  by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (egp_iff _ _ _ _).mp h
    obtain ⟨_, hy, hp⟩ := rfind_forward f s a 0 y hs
    exact ⟨hy, fun k hk => hp k (FFL.FirstOrder.Arithmetic.zero_le k) hk⟩
  · intro h
    have hh :
      egp (encode f) a (0 + y) 0 ∧
        ∀ k : M, 0 ≤ k → k < 0 + y → ∃ z : M, z ≠ 0 ∧ egp (encode f) a k z :=
      by simpa only [zero_add] using And.intro h.1 (fun k _ hk => h.2 k hk)
    simpa only [zero_add] using rfind_reverse f y a 0 hh

end

end

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
