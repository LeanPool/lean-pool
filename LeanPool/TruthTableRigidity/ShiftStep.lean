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

public import LeanPool.TruthTableRigidity.Cantor
public import Mathlib.Tactic.Abel

/-!
# Step 3 of Proposition 3.1: the shift functional

From the three uniform relations on a box `N_α × N_β` and a splitting bit at `τ ⊇ α`,
we build a tt-functional `Θ` with `Θ (F (τ⌢W)) = F (τ⌢S(W))`.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

/-! ### Bits of some explicit oracles -/

theorem prep_rep_lt {m i : ℕ} (X : Oracle) (h : i < m) :
    prep (List.replicate m false) X i = false := by
  rw [prep_lt _ _ (by simpa using h)]; simp

theorem prep_rep_ge {m i : ℕ} (X : Oracle) (h : m ≤ i) :
    prep (List.replicate m false) X i = X (i - m) := by
  rw [prep_ge _ _ (by simpa using h)]; simp

theorem lowZero_prep_rep (m : ℕ) (X : Oracle) : LowZero m (prep (List.replicate m false) X) :=
  fun _ hi => prep_rep_lt X hi

/-- The 2-adic integer `2^l = 0^l⌢1⌢0^ω`. -/
def zpow2 (l : ℕ) : Z2 := prep (List.replicate l false) (cons true zzero)

theorem lowZero_zpow2 (l : ℕ) : LowZero l (zpow2 l) := lowZero_prep_rep l _

theorem ttComputable_zpow2 (l : ℕ) : TTComputable (zpow2 l) :=
  (ttComputable_const_false.apply (isTTFunctional_cons true)).apply (isTTFunctional_prep _)

theorem zpow2_apply (l k : ℕ) : zpow2 l k = decide (k = l) := by
  simp only [zpow2]
  by_cases h : k < l
  · rw [prep_rep_lt _ h]; simp; omega
  · rw [prep_rep_ge _ (by omega)]
    by_cases h' : k = l
    · subst h'; simp [cons]
    · simp [cons, show k - l ≠ 0 by omega, h', zzero]

/-! ### Shifting the translations -/

theorem prep_rep_apply_self (l : ℕ) (W : Oracle) : prep (List.replicate l false) W l = W 0 := by
  rw [prep_rep_ge _ le_rfl, Nat.sub_self]

theorem shift_prep_rep_succ (l : ℕ) (W : Oracle) :
    shift (prep (List.replicate (l + 1) false) W) = prep (List.replicate l false) W := by
  funext i
  simp only [shift]
  by_cases h : i < l
  · rw [prep_rep_lt _ h, prep_rep_lt _ (by omega)]
  · rw [prep_rep_ge _ (by omega), prep_rep_ge _ (by omega)]
    congr 1; omega

theorem prep_rep_succ_shift_of_false (l : ℕ) {W : Oracle} (hW : W 0 = false) :
    prep (List.replicate (l + 1) false) (shift W) = prep (List.replicate l false) W := by
  funext i
  by_cases h : i < l
  · rw [prep_rep_lt _ (by omega : i < l + 1), prep_rep_lt _ h]
  · by_cases h' : i = l
    · subst h'; rw [prep_rep_lt _ (by omega), prep_rep_ge _ le_rfl, Nat.sub_self, hW]
    · rw [prep_rep_ge _ (by omega), prep_rep_ge _ (by omega)]
      simp only [shift]; congr 1; omega

theorem prep_rep_eq_add_of_true (l : ℕ) {W : Oracle} (hW : W 0 = true) :
    Z2.of (prep (List.replicate l false) W) =
      Z2.of (prep (List.replicate (l + 1) false) (shift W)) + zpow2 l := by
  symm
  rw [Z2.add_of_disjoint]
  · funext i
    simp only [zpow2, Z2.of_apply]
    by_cases h : i < l
    · rw [prep_rep_lt _ (by omega : i < l + 1), prep_rep_lt _ h, prep_rep_lt _ h]; rfl
    · by_cases h' : i = l
      · subst h'
        rw [prep_rep_lt _ (by omega), prep_rep_ge _ le_rfl, prep_rep_ge _ le_rfl,
          Nat.sub_self, hW]; rfl
      · rw [prep_rep_ge _ (by omega), prep_rep_ge _ (by omega), prep_rep_ge _ (by omega)]
        simp only [shift, cons, show i - l ≠ 0 by omega, ite_false, zzero, Bool.or_false]
        congr 1; omega
  · intro i
    simp only [Z2.of_apply]
    by_cases h' : i = l
    · subst h'; exact Or.inl (lowZero_prep_rep (i + 1) _ i (by omega))
    · right
      rw [zpow2_apply]
      simp [h']

theorem prep_zzero_ge {τ : List Bool} {i : ℕ} (h : τ.length ≤ i) : prep τ zzero i = false := by
  rw [prep_ge _ _ h]; rfl

/-- `τ⌢0^ω + 0^{|τ|}⌢W = τ⌢W` (no carries). -/
theorem prep_add_prep (τ : List Bool) (W : Oracle) :
    (Z2.of (prep τ zzero) + Z2.of (prep (List.replicate τ.length false) W) : Z2) = prep τ W := by
  rw [Z2.add_of_disjoint]
  · funext i
    simp only [Z2.of_apply]
    by_cases h : i < τ.length
    · rw [prep_rep_lt W h, Bool.or_false, prep_lt _ _ h, prep_lt _ _ h]
    · rw [prep_zzero_ge (by omega), prep_rep_ge W (by omega), Bool.false_or, prep_ge _ _ (by omega)]
  · intro i
    simp only [Z2.of_apply]
    by_cases h : i < τ.length
    · exact Or.inr (prep_rep_lt W h)
    · exact Or.inl (prep_zzero_ge (by omega))

theorem mem_Ncyl_add {α : List Bool} {G T : Z2} (hG : G ∈ Ncyl α) (hT : LowZero α.length T) :
    (G + T : Z2) ∈ Ncyl α := by
  rw [mem_Ncyl] at hG ⊢
  intro i hi
  rw [Z2.add_low hT G hi, hG i hi]

theorem ttComputable_prep (τ : List Bool) : TTComputable (prep τ zzero) :=
  ttComputable_const_false.apply (isTTFunctional_prep τ)

theorem TTComputable.add {A B : Z2} (hA : TTComputable A) (hB : TTComputable B) :
    TTComputable (A + B : Z2) :=
  ttComputable_const_false.apply ((isTTFunctional_const hA).add (isTTFunctional_const hB))

theorem TTComputable.neg {A : Z2} (hA : TTComputable A) : TTComputable (-A : Z2) :=
  ttComputable_const_false.apply (isTTFunctional_const hA).neg

theorem TTComputable.sub {A B : Z2} (hA : TTComputable A) (hB : TTComputable B) :
    TTComputable (A - B : Z2) := by
  rw [sub_eq_add_neg]; exact hA.add hB.neg

/-- The three relations `(R+)`, `(R−)`, `(R1/2)` of the paper for a pair `(G, H)`. -/
def Relations (F Φp Φm Φh : Oracle → Oracle) (G H : Z2) : Prop :=
  F (G + H) = Φp (ojoin (F G) (F H)) ∧
  F G = Φm (ojoin (F (G + H)) (F (-H))) ∧
  F (G + H) = Φh (ojoin (F G) (F (G + (H + H))))

/-- The addition and subtraction relations give translation by `κ` (equation (9)). -/
theorem Relations.translate {F Φp Φm Φh : Oracle → Oracle} {G H T κ : Z2}
    (hadd : Relations F Φp Φm Φh (G + T) (H + κ))
    (hsub : Relations F Φp Φm Φh (G + (T + κ)) H) :
    F (G + (T + κ)) = Φm (ojoin (Φp (ojoin (F (G + T)) (F (H + κ)))) (F (-H))) := by
  rw [hsub.2.1, show G + (T + κ) + H = G + T + (H + κ) by abel, hadd.1]

/-- The halving and subtraction relations recover the half-translation (equation (10)). -/
theorem Relations.halve {F Φp Φm Φh : Oracle → Oracle} {G H T half : Z2}
    (hdouble : half + half = T)
    (hhalf : Relations F Φp Φm Φh (G + T) (H - half))
    (hsub : Relations F Φp Φm Φh (G + half) H) :
    F (G + half) = Φm (ojoin (Φh (ojoin (F (G + T)) (F (G + (H + H))))) (F (-H))) := by
  have htranslated : G + half + H = G + T + (H - half) := by rw [← hdouble]; abel
  have hdoubled : G + T + (H - half + (H - half)) = G + (H + H) := by rw [← hdouble]; abel
  rw [hsub.2.1, htranslated, hhalf.2.2, hdoubled]

theorem shift_functional {F : Oracle → Oracle}
    (hC : ∀ A, TTComputable A → TTComputable (F A))
    {α β τ : List Bool} (hlen : α.length = β.length) (hατ : α <+: τ)
    {Φp Φm Φh : Oracle → Oracle} (hp : IsTTFunctional Φp) (hm : IsTTFunctional Φm)
    (hh : IsTTFunctional Φh)
    (hR : ∀ G H : Z2, G ∈ Ncyl α → H ∈ Ncyl β → Relations F Φp Φm Φh G H)
    {j : ℕ} {b : Bool} (hsplit : ∀ W, F (prep τ W) j = xor b (W 0)) :
    ∃ Θ, IsTTFunctional Θ ∧ ∀ W, Θ (F (prep τ W)) = F (prep τ (shift W)) := by
  set k := α.length with hk
  set l := τ.length with hl
  have hkl : k ≤ l := hατ.length_le
  -- the computable parameters
  let G : Z2 := prep τ zzero
  let H : Z2 := prep β zzero
  let Y := zpow2 l
  have hG : TTComputable G := ttComputable_prep τ
  have hH : TTComputable H := ttComputable_prep β
  have hY : TTComputable Y := ttComputable_zpow2 l
  have hP1 : TTComputable (F (H - Y)) := hC _ (hH.sub hY)
  have hP2 : TTComputable (F (-H)) := hC _ hH.neg
  have hP3 : TTComputable (F (G + (H + H))) := hC _ (hG.add (hH.add hH))
  set P1 := F (H - Y)
  set P2 := F (-H)
  set P3 := F (G + (H + H))
  -- the functional
  let Ψ₁ : Oracle → Oracle := fun A => Φm (ojoin (Φp (ojoin A P1)) P2)
  have hΨ₁ : IsTTFunctional Ψ₁ :=
    hm.comp ((hp.comp (isTTFunctional_id.join (isTTFunctional_const hP1))).join
      (isTTFunctional_const hP2))
  let A' : Oracle → Oracle := fun A n => if A j = b then A n else Ψ₁ A n
  have hA' : IsTTFunctional A' :=
    isTTFunctional_id.ite_eq isTTFunctional_id hΨ₁ j b
  let Θ : Oracle → Oracle := fun A => Φm (ojoin (Φh (ojoin (A' A) P3)) P2)
  have hΘ : IsTTFunctional Θ :=
    hm.comp ((hh.comp (hA'.join (isTTFunctional_const hP3))).join (isTTFunctional_const hP2))
  refine ⟨Θ, hΘ, fun W => ?_⟩
  -- the translations
  let T : Z2 := prep (List.replicate l false) W
  let T' : Z2 := prep (List.replicate (l + 1) false) (shift W)
  let Th : Z2 := Z2.of (shift T')
  have hTl : LowZero l T := lowZero_prep_rep l W
  have hT'l : LowZero (l + 1) T' := lowZero_prep_rep (l + 1) _
  have hYl : LowZero l Y := lowZero_zpow2 l
  have hThl : LowZero l Th := lowZero_shift hT'l
  have hThTh : Th + Th = T' := Z2.shift_add_shift (hT'l 0 (by omega))
  have hGT : G + T = prep τ W := prep_add_prep τ W
  have hGTh : G + Th = prep τ (shift W) := by
    change (Z2.of (prep τ zzero) + Z2.of (shift T') : Z2) = _
    rw [show shift T' = prep (List.replicate l false) (shift W) from shift_prep_rep_succ l _]
    exact prep_add_prep τ (shift W)
  -- membership in the box
  have hGα : G ∈ Ncyl α := Ncyl_antitone hατ (prep_mem τ zzero)
  have hHβ : H ∈ Ncyl β := prep_mem β zzero
  have mα : ∀ {S : Z2}, LowZero k S → (G + S : Z2) ∈ Ncyl α := fun hS => mem_Ncyl_add hGα hS
  have mβ : ∀ {S : Z2}, LowZero k S → (H + S : Z2) ∈ Ncyl β := fun hS =>
    mem_Ncyl_add hHβ (by rw [← hlen]; exact hS)
  have lowk : ∀ {S : Oracle}, LowZero l S → LowZero k S := fun hS => hS.mono hkl
  -- `A' (F (τ⌢W)) = F (G + T')`
  have step1 : A' (F (prep τ W)) = F (G + T') := by
    cases hW : W 0 with
    | false =>
      have hTT' : T' = T := prep_rep_succ_shift_of_false l hW
      funext n
      simp only [A', hsplit, hW, Bool.xor_false, ite_true]
      rw [hTT', hGT]
    | true =>
      have hTY : T = T' + Y := prep_rep_eq_add_of_true l hW
      have hT' : T' = T - Y := by rw [hTY]; abel
      have hne : ¬ (F (prep τ W) j = b) := by rw [hsplit, hW]; simp
      have e1 : A' (F (prep τ W)) = Ψ₁ (F (prep τ W)) := by
        funext n; simp only [A', hne, ite_false]
      rw [e1]
      have hplus := hR (G + T) (H - Y) (mα (lowk hTl))
        (by rw [sub_eq_add_neg]; exact mβ (lowk (Z2.lowZero_neg hYl)))
      have hminus := hR (G + (T - Y)) H (mα (lowk (Z2.lowZero_sub hTl hYl))) hHβ
      have htranslate := Relations.translate (κ := -Y)
        (by simpa only [sub_eq_add_neg] using hplus)
        (by simpa only [sub_eq_add_neg] using hminus)
      rw [hT', sub_eq_add_neg, htranslate, hGT]
      simp only [Ψ₁, P1, P2, sub_eq_add_neg]
  -- `Θ (F (τ⌢W)) = F (G + T/2)`
  have hhalf := hR (G + T') (H - Th) (mα (lowk (hT'l.mono (by omega))))
    (by rw [sub_eq_add_neg]; exact mβ (lowk (Z2.lowZero_neg hThl)))
  have hminus := hR (G + Th) H (mα (lowk hThl)) hHβ
  change Φm (ojoin (Φh (ojoin (A' (F (prep τ W))) P3)) P2) = _
  rw [step1, ← hGTh, Relations.halve hThTh hhalf hminus]

end TT
