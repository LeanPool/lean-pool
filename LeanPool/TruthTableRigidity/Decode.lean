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

public import LeanPool.TruthTableRigidity.DecodeTools

/-!
# The decoding step of the coding lemma (Proposition 4.3)

For a fixed "good" pair `(G, H)` (all translates by the countable group `C_X` satisfy the
three relations and land in `D`), we decode `X` from `F(G + 0^l⌢X)` and finitely many
parameters `F(H + 2^{l+1})`, `F(H - 2^l)`, `F(-H)`, `F(G + 2H)`.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity

theorem ojoin_evens_odds (B : Oracle) : ojoin (evens B) (odds B) = B := by
  funext n
  simp only [ojoin, evens, odds]
  split_ifs with h
  · congr 1; omega
  · congr 1; omega

/-! ### The decoding lemma -/

/-- **Decoding (Proposition 4.3, for a fixed good pair).** -/
theorem decode_of_good {F Φp Φm Φh : Oracle → Oracle} (hp : IsTTFunctional Φp)
    (hm : IsTTFunctional Φm) (hh : IsTTFunctional Φh) {D : Set Oracle} {j : ℕ} {b i : Bool}
    {σ q₁ : List Bool} (hq : σ ++ [!i] <+: q₁)
    (hb0 : ∀ Z ∈ D, Z ∈ Ncyl (σ ++ [i]) → F Z j = b)
    (hb1 : ∀ Z ∈ D, Z ∈ Ncyl q₁ → F Z j = !b)
    (C : AddSubgroup Z2) (hCl : ∀ T ∈ C, LowZero σ.length T) (hY : zpow2 σ.length ∈ C)
    (X : Oracle) (hXm : ∀ m, zseq σ.length X m ∈ C) {G H : Z2} (hG : G ∈ Ncyl (σ ++ [i]))
    (hgood : ∀ c₁ ∈ C, ∀ c₂ ∈ C,
      Relations F Φp Φm Φh (G + c₁) (H + c₂) ∧ ((G + c₁ : Z2) : Oracle) ∈ D) :
    TTReducible X (ojoin (F (G + zseq σ.length X 0))
      (ojoin (ojoin (F (H + (zpow2 σ.length + zpow2 σ.length))) (F (H - zpow2 σ.length)))
        (ojoin (F (-H)) (F (G + (H + H)))))) := by
  set l := σ.length with hl
  set Y := zpow2 l with hYdef
  set N := 2 ^ (q₁.length - (l + 1)) with hN
  set P1 := F (H + (Y + Y))
  set P1' := F (H - Y)
  set P2 := F (-H)
  set P3 := F (G + (H + H))
  set P := ojoin (ojoin P1 P1') (ojoin P2 P3) with hP
  let a : Z2 → Oracle := fun T => F (G + T)
  have hYY : Y + Y ∈ C := C.add_mem hY hY
  -- (9) translation
  have tr : ∀ T ∈ C, ∀ κ ∈ C, a (T + κ) = Φm (ojoin (Φp (ojoin (a T) (F (H + κ)))) P2) := by
    intro T hT κ hκ
    have Rp := (hgood T hT κ hκ).1.1
    have Rm := (hgood (T + κ) (C.add_mem hT hκ) 0 C.zero_mem).1.2.1
    simp only [add_zero] at Rm
    change F (G + (T + κ)) = _
    rw [Rm, show G + (T + κ) + H = G + T + (H + κ) by abel, Rp]
  -- iterating the translation by `2^{l+1}`
  let Ξ : Oracle → Oracle := fun A => Φm (ojoin (Φp (ojoin A P1)) P2)
  have it : ∀ T ∈ C, ∀ c : ℕ, Ξ^[c] (a T) = a (T + c • (Y + Y)) := by
    intro T hT c
    induction c with
    | zero => simp
    | succ c ih =>
      rw [Function.iterate_succ_apply', ih, succ_nsmul, ← add_assoc]
      exact (tr _ (C.add_mem hT (C.nsmul_mem hYY c)) _ hYY).symm
  -- (11) reading a bit
  have rd : ∀ T ∈ C, decide (∃ c < N, (Ξ^[c] (a T)) j ≠ b) = T l := by
    intro T hT
    cases hTl : T l with
    | true =>
      obtain ⟨c, hc, hmem⟩ := exists_hit hG (hCl T hT) hTl hq
      have hD := (hgood _ (C.add_mem hT (C.nsmul_mem hYY c)) 0 C.zero_mem).2
      refine decide_eq_true ⟨c, hc, ?_⟩
      rw [it T hT c]
      change F (G + (T + c • (Y + Y))) j ≠ b
      rw [hb1 _ hD hmem]
      cases b <;> simp
    | false =>
      refine decide_eq_false ?_
      rintro ⟨c, -, hc⟩
      apply hc
      rw [it T hT c]
      have hD := (hgood _ (C.add_mem hT (C.nsmul_mem hYY c)) 0 C.zero_mem).2
      have hlow : LowZero (σ ++ [i]).length (T + c • (Y + Y)) := by
        have hT1 : LowZero (l + 1) T := by
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact hCl T hT k hk
          · exact hTl
        simpa [hl] using Z2.lowZero_add hT1 (lowZero_nsmul (lowZero_zpow2_two l) c)
      exact hb0 _ hD (mem_Ncyl_add hG hlow)
  -- (10) halving
  have hv : ∀ T ∈ C, LowZero (l + 1) T → Z2.of (shift T) ∈ C →
      Φm (ojoin (Φh (ojoin (a T) P3)) P2) = a (Z2.of (shift T)) := by
    intro T hT hT1 hsh
    have hThTh : Z2.of (shift T) + Z2.of (shift T) = T := Z2.shift_add_shift (hT1 0 (by omega))
    generalize Z2.of (shift T) = Th at hsh hThTh ⊢
    have Rh := (hgood T hT (-Th) (C.neg_mem hsh)).1.2.2
    have Rm := (hgood Th hsh 0 C.zero_mem).1.2.1
    simp only [add_zero] at Rm
    have e1 : G + T + (H + -Th + (H + -Th)) = G + (H + H) := by rw [← hThTh]; abel
    have e2 : G + Th + H = G + T + (H + -Th) := by rw [← hThTh]; abel
    change _ = F (G + Th)
    rw [Rm, e2, Rh, e1]
  -- the tt-functionals, acting on `A ⊕ P`
  let Ξh : Oracle → Oracle := fun B =>
    ojoin (Φm (ojoin (Φp (ojoin (evens B) (evens (evens (odds B))))) (evens (odds (odds B)))))
      (odds B)
  have hΞh : IsTTFunctional Ξh :=
    (hm.comp ((hp.comp (isTTFunctional_evens.join (isTTFunctional_evens.comp
      (isTTFunctional_evens.comp isTTFunctional_odds)))).join
      (isTTFunctional_evens.comp (isTTFunctional_odds.comp isTTFunctional_odds)))).join
      isTTFunctional_odds
  let Ih : Oracle → Oracle := fun B m => (Ξh^[m] B) (2 * j)
  have hIh : IsTTFunctional Ih := hΞh.iterate (2 * j)
  let εh : Oracle → Oracle := fun B _ => decide (∃ c < N, Ih B c ≠ b)
  have hεh : IsTTFunctional εh := (isTTFunctional_someNe N b).comp hIh
  let Ξ'core : Oracle → Oracle := fun B =>
    Φm (ojoin (Φp (ojoin (evens B) (odds (evens (odds B))))) (evens (odds (odds B))))
  have hΞ'core : IsTTFunctional Ξ'core :=
    hm.comp ((hp.comp (isTTFunctional_evens.join (isTTFunctional_odds.comp
      (isTTFunctional_evens.comp isTTFunctional_odds)))).join
      (isTTFunctional_evens.comp (isTTFunctional_odds.comp isTTFunctional_odds)))
  let A'h : Oracle → Oracle := fun B n => if εh B 0 = true then Ξ'core B n else evens B n
  have hA'h : IsTTFunctional A'h := hεh.ite hΞ'core isTTFunctional_evens 0
  let Θh : Oracle → Oracle := fun B =>
    ojoin (Φm (ojoin (Φh (ojoin (A'h B) (odds (odds (odds B))))) (evens (odds (odds B)))))
      (odds B)
  have hΘh : IsTTFunctional Θh :=
    (hm.comp ((hh.comp (hA'h.join (isTTFunctional_odds.comp
      (isTTFunctional_odds.comp isTTFunctional_odds)))).join
      (isTTFunctional_evens.comp (isTTFunctional_odds.comp isTTFunctional_odds)))).join
      isTTFunctional_odds
  let Γ : Oracle → Oracle := fun B m => εh (Θh^[m] B) 0
  have hΓ : IsTTFunctional Γ := hΘh.iterate_read hεh 0
  -- semantics of the functionals on `A ⊕ P`
  have sΞh : ∀ A, Ξh (ojoin A P) = ojoin (Ξ A) P := by
    intro A; simp only [Ξh, Ξ, P, evens_ojoin, odds_ojoin]
  have sΞh' : ∀ c A, Ξh^[c] (ojoin A P) = ojoin (Ξ^[c] A) P := by
    intro c
    induction c with
    | zero => intro A; rfl
    | succ c ih =>
      intro A
      rw [Function.iterate_succ_apply', ih, sΞh, Function.iterate_succ_apply']
  have sεh : ∀ A, εh (ojoin A P) 0 = decide (∃ c < N, (Ξ^[c] A) j ≠ b) := by
    intro A
    simp only [εh, Ih, sΞh', ojoin_even]
  have sΘh : ∀ m, Θh (ojoin (a (zseq l X m)) P) = ojoin (a (zseq l X (m + 1))) P ∧
      εh (ojoin (a (zseq l X m)) P) 0 = X m := by
    intro m
    set W := shift^[m] X with hW
    have hTW : zseq l X m = prep (List.replicate l false) W := rfl
    have hT1 : zseq l X (m + 1) = prep (List.replicate l false) (shift W) := by
      simp only [zseq, hW, Function.iterate_succ_apply']
    have hTl : (zseq l X m) l = X m := by
      rw [hTW, prep_rep_apply_self, hW, iterate_shift_zero]
    have hε : εh (ojoin (a (zseq l X m)) P) 0 = X m := by
      rw [sεh, rd _ (hXm m), hTl]
    refine ⟨?_, hε⟩
    set T' : Z2 := prep (List.replicate (l + 1) false) (shift W) with hT'
    have hT'low : LowZero (l + 1) T' := lowZero_prep_rep _ _
    have hshT' : Z2.of (shift T') = zseq l X (m + 1) := by
      rw [hT1]; exact shift_prep_rep_succ l (shift W)
    have hA' : A'h (ojoin (a (zseq l X m)) P) = a T' ∧ T' ∈ C := by
      cases hXmv : X m with
      | false =>
        have hW0 : W 0 = false := by rw [hW, iterate_shift_zero, hXmv]
        have e : T' = zseq l X m := by
          rw [hT', hTW]; exact prep_rep_succ_shift_of_false l hW0
        refine ⟨?_, e ▸ hXm m⟩
        funext n
        simp only [A'h, hε, hXmv, Bool.false_eq_true, ite_false, evens_ojoin, e]
      | true =>
        have hW0 : W 0 = true := by rw [hW, iterate_shift_zero, hXmv]
        have e : zseq l X m = T' + Y := by rw [hTW]; exact prep_rep_eq_add_of_true l hW0
        have e' : T' = zseq l X m + -Y := by rw [e]; abel
        have hT'C : T' ∈ C := e' ▸ C.add_mem (hXm m) (C.neg_mem hY)
        refine ⟨?_, hT'C⟩
        funext n
        simp only [A'h, hε, hXmv, ite_true]
        have := tr _ (hXm m) _ (C.neg_mem hY)
        rw [← e', ← sub_eq_add_neg] at this
        rw [this]
        simp only [Ξ'core, evens_ojoin, odds_ojoin, P]
        rfl
    obtain ⟨hA'1, hT'C⟩ := hA'
    have := hv T' hT'C hT'low (hshT' ▸ hXm (m + 1))
    rw [hshT'] at this
    simp only [Θh, hA'1, odds_ojoin, P, evens_ojoin]
    rw [← this]
  have hit : ∀ m, Θh^[m] (ojoin (a (zseq l X 0)) P) = ojoin (a (zseq l X m)) P := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, (sΘh m).1]
  refine ⟨Γ, hΓ, ?_⟩
  funext m
  change εh (Θh^[m] (ojoin (a (zseq l X 0)) P)) 0 = X m
  rw [hit, (sΘh m).2]

end TT
