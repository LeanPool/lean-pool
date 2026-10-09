/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import LeanPool.RunsOfMultiples.Alt.Compression
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring

/-!
# The two compressions of Lemma 2, and the closure theorem

* `pChain p`: chains `b, b p, b p², …` with `p ∤ b`;
* `pqChain p q` (`p < q`): chains `b p^D, b p^(D-1) q, …, b q^D` with `p, q ∤ b`.

Both satisfy the window condition `Cons`, so compression keeps every `|A S t|` from decreasing.
Taking a compression-stable set of minimal element sum gives `exists_closed`, the content of
Lemma 2 of the second proof.
-/

open Finset

@[expose] public section

namespace RunsOfMultiples

section pChain

variable {p : ℕ} (hp : p.Prime)

/-- Chains along a single prime `p`. -/
noncomputable def pChain : ChainSys ℕ where
  key n := n / p ^ n.factorization p
  pos n := n.factorization p
  elt b u := b * p ^ u
  vld b _ := 0 < b ∧ ¬ p ∣ b
  elt_key_pos n hn := Nat.div_mul_cancel (Nat.ordProj_dvd n p)
  vld_key_pos n hn := ⟨Nat.ordCompl_pos p hn.ne', Nat.not_dvd_ordCompl hp hn.ne'⟩
  key_elt b u h := by
    have hfac : (b * p ^ u).factorization p = u := by
      rw [Nat.factorization_mul h.1.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow,
        Finsupp.add_apply, Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd h.2,
        hp.factorization_self]
      simp
    change b * p ^ u / p ^ (b * p ^ u).factorization p = b
    rw [hfac, Nat.mul_div_cancel _ (pow_pos hp.pos u)]
  pos_elt b u h := by
    rw [Nat.factorization_mul h.1.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd h.2,
      hp.factorization_self]
    simp
  elt_pos b u h := Nat.mul_pos h.1 (pow_pos hp.pos u)
  vld_mono _ _ _ h _ := h
  elt_lt b u v h huv := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.one_lt huv) h.1

lemma pChain_cons (t : ℕ) (b : ℕ) : (pChain hp).Cons t b := by
  classical
  by_cases hb : 0 < b ∧ ¬ p ∣ b
  swap
  · exact ⟨PUnit, ∅, fun _ => b, fun _ => 0, fun e he => absurd he hb,
      fun S _ e he => absurd he hb⟩
  refine ⟨ℕ, (Icc 1 t).filter (fun c => ¬ p ∣ c), fun c => b * c, fun c => Nat.log p (t / c),
    ?_, ?_⟩
  · intro e _ c hc h _
    rw [mem_filter, mem_Icc] at hc
    exact ⟨Nat.mul_pos hb.1 (by omega), fun hdvd =>
      ((Nat.Prime.dvd_mul hp).1 hdvd).elim hb.2 hc.2⟩
  · intro S hS e he
    change b * p ^ e ∈ A S t ↔ b * p ^ e ∈ S ∧ ∀ c ∈ (Icc 1 t).filter (fun c => ¬ p ∣ c),
      ∀ h ≤ Nat.log p (t / c), b * c * p ^ (e + h) ∈ S
    rw [A, mem_filter]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hall c hc h hh
      rw [mem_filter, mem_Icc] at hc
      have hct : c * p ^ h ≤ t := by
        have h1 : p ^ h ≤ t / c := by
          have hpos : t / c ≠ 0 := (Nat.div_pos hc.1.2 hc.1.1).ne'
          exact le_trans (Nat.pow_le_pow_right hp.pos hh) (Nat.pow_log_le_self p hpos)
        calc c * p ^ h ≤ c * (t / c) := Nat.mul_le_mul_left c h1
          _ ≤ t := Nat.mul_div_le t c
      have := hall (c * p ^ h) (mem_Icc.2 ⟨Nat.mul_pos hc.1.1 (pow_pos hp.pos h) , hct⟩)
      rw [show c * p ^ h * (b * p ^ e) = b * c * p ^ (e + h) by ring] at this
      exact this
    · intro hcons j hj
      rw [mem_Icc] at hj
      have hj0 : 0 < j := by omega
      set c := (pChain hp).key j with hc
      set h := (pChain hp).pos j with hh
      have hvj := (pChain hp).vld_key_pos j hj0
      have hjeq : c * p ^ h = j := (pChain hp).elt_key_pos j hj0
      have hcle : c ≤ j := by
        calc c = c * 1 := (mul_one c).symm
          _ ≤ c * p ^ h := Nat.mul_le_mul_left c (Nat.one_le_pow _ _ hp.pos)
          _ = j := hjeq
      have hcI : c ∈ (Icc 1 t).filter (fun c => ¬ p ∣ c) :=
        mem_filter.2 ⟨mem_Icc.2 ⟨hvj.1, hcle.trans hj.2⟩, hvj.2⟩
      have hhle : h ≤ Nat.log p (t / c) := by
        apply Nat.le_log_of_pow_le hp.one_lt
        rw [Nat.le_div_iff_mul_le hvj.1, mul_comm, hjeq]
        exact hj.2
      have := hcons c hcI h hhle
      rw [show b * c * p ^ (e + h) = c * p ^ h * (b * p ^ e) by ring, hjeq] at this
      exact this

/-- `x / p` sits one position below `x` on the `p`-chain of `x`. -/
lemma pChain_div {x : ℕ} (hx : 0 < x) (hpx : p ∣ x) :
    (pChain hp).vld ((pChain hp).key x) ((pChain hp).pos x - 1) ∧
      (pChain hp).pos x - 1 < (pChain hp).pos x ∧
      (pChain hp).elt ((pChain hp).key x) ((pChain hp).pos x - 1) = x / p := by
  have hv := (pChain hp).vld_key_pos x hx
  have hx' := (pChain hp).elt_key_pos x hx
  have hpos : 0 < (pChain hp).pos x := by
    change 0 < x.factorization p
    exact hp.factorization_pos_of_dvd hx.ne' hpx
  refine ⟨hv, by omega, ?_⟩
  change (pChain hp).key x * p ^ ((pChain hp).pos x - 1) = x / p
  conv_rhs => rw [← hx']
  change _ = (pChain hp).key x * p ^ (pChain hp).pos x / p
  rw [show (pChain hp).pos x = (pChain hp).pos x - 1 + 1 by omega, pow_succ, ← mul_assoc,
    Nat.mul_div_cancel _ hp.pos]
  simp

end pChain

section pqChain

variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)

lemma pow_mul_pow_mono {a b : ℕ} (hab : a ≤ b) {d u v : ℕ} (huv : u ≤ v) (hvd : v ≤ d) :
    a ^ (d - u) * b ^ u ≤ a ^ (d - v) * b ^ v := by
  have e1 : d - u = (d - v) + (v - u) := by omega
  have e2 : v = u + (v - u) := by omega
  rw [e1, pow_add, show b ^ v = b ^ u * b ^ (v - u) by rw [← pow_add, Nat.add_sub_cancel' huv]]
  have : a ^ (v - u) ≤ b ^ (v - u) := Nat.pow_le_pow_left hab _
  calc a ^ (d - v) * a ^ (v - u) * b ^ u = a ^ (d - v) * b ^ u * a ^ (v - u) := by ring
    _ ≤ a ^ (d - v) * b ^ u * b ^ (v - u) := Nat.mul_le_mul_left _ this
    _ = a ^ (d - v) * (b ^ u * b ^ (v - u)) := by ring

include hp hq hpq in
lemma pq_factorization {b D u : ℕ} (hb : 0 < b) (hbp : ¬ p ∣ b) (hbq : ¬ q ∣ b) :
    (b * p ^ (D - u) * q ^ u).factorization p = D - u ∧
      (b * p ^ (D - u) * q ^ u).factorization q = u := by
  have hpq' : p ≠ q := hpq.ne
  have h1 : b * p ^ (D - u) ≠ 0 := Nat.mul_ne_zero hb.ne' (pow_ne_zero _ hp.ne_zero)
  rw [Nat.factorization_mul h1 (pow_ne_zero _ hq.ne_zero),
    Nat.factorization_mul hb.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow,
    Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd hbp, Nat.factorization_eq_zero_of_not_dvd hbq,
    hp.factorization, hq.factorization, Finsupp.single_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · simp [hpq'.symm]
  · simp [hpq']

/-- Chains along a pair of primes `p < q` (fixed total exponent). -/
noncomputable def pqChain : ChainSys (ℕ × ℕ) where
  key n := (n / (p ^ n.factorization p * q ^ n.factorization q),
    n.factorization p + n.factorization q)
  pos n := n.factorization q
  elt k u := k.1 * p ^ (k.2 - u) * q ^ u
  vld k u := 0 < k.1 ∧ ¬ p ∣ k.1 ∧ ¬ q ∣ k.1 ∧ u ≤ k.2
  elt_key_pos n hn := by
    have hcop : Nat.Coprime (p ^ n.factorization p) (q ^ n.factorization q) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hpq.ne)
    have hdvd : p ^ n.factorization p * q ^ n.factorization q ∣ n :=
      hcop.mul_dvd_of_dvd_of_dvd (Nat.ordProj_dvd n p) (Nat.ordProj_dvd n q)
    simp only [Nat.add_sub_cancel]
    rw [mul_assoc, Nat.div_mul_cancel hdvd]
  vld_key_pos n hn := by
    have hcop : Nat.Coprime (p ^ n.factorization p) (q ^ n.factorization q) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hpq.ne)
    have hdvd : p ^ n.factorization p * q ^ n.factorization q ∣ n :=
      hcop.mul_dvd_of_dvd_of_dvd (Nat.ordProj_dvd n p) (Nat.ordProj_dvd n q)
    set b := n / (p ^ n.factorization p * q ^ n.factorization q) with hbdef
    have hbn : b * (p ^ n.factorization p * q ^ n.factorization q) = n := Nat.div_mul_cancel hdvd
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · rw [h, zero_mul] at hbn; omega
      · exact h
    have hfac : b.factorization p = 0 ∧ b.factorization q = 0 := by
      have := congrArg (fun m => m.factorization) hbn
      rw [Nat.factorization_mul hb0.ne' (Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero)
          (pow_ne_zero _ hq.ne_zero)),
        Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
        Nat.factorization_pow, Nat.factorization_pow] at this
      have hpv := DFunLike.congr_fun this p
      have hqv := DFunLike.congr_fun this q
      simp only [Finsupp.add_apply, Finsupp.smul_apply, hp.factorization, hq.factorization,
        Finsupp.single_apply, smul_eq_mul] at hpv hqv
      simp only [hpq.ne, hpq.ne.symm, ite_true, ite_false] at hpv hqv
      constructor <;> omega
    refine ⟨hb0, fun h => ?_, fun h => ?_, by omega⟩
    · have := hp.factorization_pos_of_dvd hb0.ne' h; omega
    · have := hq.factorization_pos_of_dvd hb0.ne' h; omega
  key_elt k u h := by
    obtain ⟨hb, hbp, hbq, hu⟩ := h
    obtain ⟨h1, h2⟩ := pq_factorization (D := k.2) (u := u) hp hq hpq hb hbp hbq
    simp only [h1, h2]
    ext
    · simp only
      rw [mul_assoc, Nat.mul_div_cancel _ (Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _))]
    · simp only
      omega
  pos_elt k u h := (pq_factorization hp hq hpq h.1 h.2.1 h.2.2.1).2
  elt_pos k u h := Nat.mul_pos (Nat.mul_pos h.1 (pow_pos hp.pos _)) (pow_pos hq.pos _)
  vld_mono k u v h hvu := ⟨h.1, h.2.1, h.2.2.1, le_trans hvu h.2.2.2⟩
  elt_lt k u v h huv := by
    obtain ⟨hb, -, -, hv⟩ := h
    have e1 : k.2 - u = (k.2 - v) + (v - u) := by omega
    have e2 : v = u + (v - u) := by omega
    have hlt : p ^ (v - u) < q ^ (v - u) := Nat.pow_lt_pow_left hpq (by omega)
    change k.1 * p ^ (k.2 - u) * q ^ u < k.1 * p ^ (k.2 - v) * q ^ v
    rw [e1, pow_add, show q ^ v = q ^ u * q ^ (v - u) by rw [← pow_add, Nat.add_sub_cancel' huv.le]]
    have hpos : 0 < k.1 * p ^ (k.2 - v) * q ^ u :=
      Nat.mul_pos (Nat.mul_pos hb (pow_pos hp.pos _)) (pow_pos hq.pos _)
    calc k.1 * (p ^ (k.2 - v) * p ^ (v - u)) * q ^ u
        = k.1 * p ^ (k.2 - v) * q ^ u * p ^ (v - u) := by ring
      _ < k.1 * p ^ (k.2 - v) * q ^ u * q ^ (v - u) := Nat.mul_lt_mul_of_pos_left hlt hpos
      _ = k.1 * p ^ (k.2 - v) * (q ^ u * q ^ (v - u)) := by ring

lemma pqChain_cons (t : ℕ) (k : ℕ × ℕ) : (pqChain hp hq hpq).Cons t k := by
  classical
  by_cases hk : 0 < k.1 ∧ ¬ p ∣ k.1 ∧ ¬ q ∣ k.1
  swap
  · exact ⟨PUnit, ∅, fun _ => k, fun _ => 0, fun e he => absurd ⟨he.1, he.2.1, he.2.2.1⟩ hk,
      fun S _ e he => absurd ⟨he.1, he.2.1, he.2.2.1⟩ hk⟩
  obtain ⟨b, D⟩ := k
  obtain ⟨hb, hbp, hbq⟩ := hk
  set P : ℕ → ℕ → ℕ → Prop := fun c d h => c * p ^ (d - h) * q ^ h ≤ t with hP
  set I : Finset (ℕ × ℕ) :=
    (((Icc 1 t).filter (fun c => ¬ p ∣ c ∧ ¬ q ∣ c)) ×ˢ range (t + 1)).filter
    (fun cd => cd.1 * p ^ cd.2 ≤ t) with hI
  refine ⟨ℕ × ℕ, I, fun cd => (b * cd.1, D + cd.2),
    fun cd => Nat.findGreatest (P cd.1 cd.2) cd.2, ?_, ?_⟩
  · intro e he cd hcd h hh
    simp only [hI, mem_filter, mem_product, mem_Icc] at hcd
    have hle : Nat.findGreatest (P cd.1 cd.2) cd.2 ≤ cd.2 := Nat.findGreatest_le _
    refine ⟨Nat.mul_pos hb (by omega), fun hdvd => ?_, fun hdvd => ?_, ?_⟩
    · exact ((Nat.Prime.dvd_mul hp).1 hdvd).elim hbp hcd.1.1.2.1
    · exact ((Nat.Prime.dvd_mul hq).1 hdvd).elim hbq hcd.1.1.2.2
    · change e + h ≤ D + cd.2
      have heD : e ≤ D := he.2.2.2
      have hh' : h ≤ Nat.findGreatest (P cd.1 cd.2) cd.2 := hh
      omega
  · intro S hS e he
    have heD : e ≤ D := he.2.2.2
    change b * p ^ (D - e) * q ^ e ∈ A S t ↔ b * p ^ (D - e) * q ^ e ∈ S ∧ ∀ cd ∈ I,
      ∀ h ≤ Nat.findGreatest (P cd.1 cd.2) cd.2,
        b * cd.1 * p ^ (D + cd.2 - (e + h)) * q ^ (e + h) ∈ S
    rw [A, mem_filter]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hall cd hcd h hh
      simp only [hI, mem_filter, mem_product, mem_Icc, mem_range] at hcd
      obtain ⟨⟨⟨⟨hc1, hct⟩, -⟩, -⟩, hcpd⟩ := hcd
      have hd : Nat.findGreatest (P cd.1 cd.2) cd.2 ≤ cd.2 := Nat.findGreatest_le _
      -- `P cd.1 cd.2 h` holds since `P` holds at the greatest index and is antitone
      have hPG : P cd.1 cd.2 (Nat.findGreatest (P cd.1 cd.2) cd.2) :=
        Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (by simpa [hP] using hcpd)
      have hPh : P cd.1 cd.2 h := by
        simp only [hP] at hPG ⊢
        calc cd.1 * p ^ (cd.2 - h) * q ^ h
            = cd.1 * (p ^ (cd.2 - h) * q ^ h) := by ring
          _ ≤ cd.1 * (p ^ (cd.2 - Nat.findGreatest (P cd.1 cd.2) cd.2) *
                q ^ Nat.findGreatest (P cd.1 cd.2) cd.2) :=
              Nat.mul_le_mul_left _ (pow_mul_pow_mono hpq.le hh hd)
          _ = _ := by ring
          _ ≤ t := hPG
      have hj := hall (cd.1 * p ^ (cd.2 - h) * q ^ h)
        (mem_Icc.2 ⟨Nat.mul_pos (Nat.mul_pos hc1 (pow_pos hp.pos _)) (pow_pos hq.pos _), hPh⟩)
      have hexp : D + cd.2 - (e + h) = (D - e) + (cd.2 - h) := by omega
      rw [hexp, pow_add, pow_add]
      rw [show cd.1 * p ^ (cd.2 - h) * q ^ h * (b * p ^ (D - e) * q ^ e) =
        b * cd.1 * (p ^ (D - e) * p ^ (cd.2 - h)) * (q ^ e * q ^ h) by ring] at hj
      exact hj
    · intro hcons j hj
      rw [mem_Icc] at hj
      have hj0 : 0 < j := by omega
      set C := pqChain hp hq hpq
      have hvj := C.vld_key_pos j hj0
      have hjeq := C.elt_key_pos j hj0
      set c := (C.key j).1
      set d := (C.key j).2
      set h := C.pos j
      have hhd : h ≤ d := hvj.2.2.2
      change c * p ^ (d - h) * q ^ h = j at hjeq
      have hcpd : c * p ^ d ≤ j := by
        have := Nat.mul_le_mul_left c (pow_mul_pow_mono hpq.le (Nat.zero_le h) hhd)
        simp only [Nat.sub_zero, pow_zero, mul_one] at this
        calc c * p ^ d ≤ c * (p ^ (d - h) * q ^ h) := this
          _ = j := by rw [← hjeq]; ring
      have hc1 : 1 ≤ c := hvj.1
      have hdt : d < t + 1 := by
        have : d < p ^ d := Nat.lt_pow_self hp.one_lt
        have : p ^ d ≤ c * p ^ d := Nat.le_mul_of_pos_left _ hc1
        omega
      have hcI : (c, d) ∈ I := by
        simp only [hI, mem_filter, mem_product, mem_Icc, mem_range]
        refine ⟨⟨⟨⟨hc1, ?_⟩, hvj.2.1, hvj.2.2.1⟩, hdt⟩, by omega⟩
        have : c ≤ c * p ^ d := Nat.le_mul_of_pos_right _ (pow_pos hp.pos _)
        omega
      have hhG : h ≤ Nat.findGreatest (P c d) d :=
        Nat.le_findGreatest hhd (by simp only [hP]; omega)
      have := hcons (c, d) hcI h hhG
      have hexp : D + d - (e + h) = (D - e) + (d - h) := by omega
      simp only at this
      rw [hexp, pow_add, pow_add] at this
      rw [show j * (b * p ^ (D - e) * q ^ e) = b * c * (p ^ (D - e) * p ^ (d - h)) *
        (q ^ e * q ^ h) by rw [← hjeq]; ring]
      exact this

/-- `a / q * p` sits one position below `a` on the `(p, q)`-chain of `a`. -/
lemma pqChain_shift {a : ℕ} (ha : 0 < a) (hqa : q ∣ a) :
    (pqChain hp hq hpq).vld ((pqChain hp hq hpq).key a) ((pqChain hp hq hpq).pos a - 1) ∧
      (pqChain hp hq hpq).pos a - 1 < (pqChain hp hq hpq).pos a ∧
      (pqChain hp hq hpq).elt ((pqChain hp hq hpq).key a) ((pqChain hp hq hpq).pos a - 1) =
        a / q * p := by
  set C := pqChain hp hq hpq
  have hv := C.vld_key_pos a ha
  have ha' := C.elt_key_pos a ha
  have hpos : 0 < C.pos a := by
    change 0 < a.factorization q
    exact hq.factorization_pos_of_dvd ha.ne' hqa
  refine ⟨C.vld_mono _ _ _ hv (by omega), by omega, ?_⟩
  set b := (C.key a).1
  set D := (C.key a).2
  set u := C.pos a
  have huD : u ≤ D := hv.2.2.2
  change b * p ^ (D - u) * q ^ u = a at ha'
  change b * p ^ (D - (u - 1)) * q ^ (u - 1) = a / q * p
  have e1 : D - (u - 1) = (D - u) + 1 := by omega
  have hqu : q ^ u = q ^ (u - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hpos]
  have ha2 : a = b * p ^ (D - u) * q ^ (u - 1) * q := by rw [← ha', hqu]; ring
  have hdiv : a / q = b * p ^ (D - u) * q ^ (u - 1) := by
    rw [ha2, Nat.mul_div_cancel _ hq.pos]
  rw [hdiv, e1, pow_succ]
  ring

end pqChain

/-- If a chain has an occupied position `pos n` and an empty valid position below it, the
chain's occupied set is not an initial segment. -/
lemma ChainSys.gap {κ : Type} [DecidableEq κ] {C : ChainSys κ} {T : Finset ℕ}
    (hT : ∀ n ∈ T, 0 < n) {n u : ℕ} (hn : n ∈ T) (hu : u < C.pos n)
    (hout : C.elt (C.key n) u ∉ T) :
    C.occ T (C.key n) ≠ range (C.occ T (C.key n)).card := by
  intro h
  have hn0 := hT n hn
  have hmem : C.pos n ∈ C.occ T (C.key n) :=
    (ChainSys.mem_occ_iff hT).2 ⟨C.vld_key_pos n hn0, by rw [C.elt_key_pos n hn0]; exact hn⟩
  rw [h, mem_range] at hmem
  have : u ∈ C.occ T (C.key n) := by rw [h, mem_range]; omega
  exact hout ((ChainSys.mem_occ_iff hT).1 this).2

/-- One-step divisor closure implies divisor closure. -/
lemma divClosed_of_step {T : Finset ℕ} (hT : ∀ n ∈ T, 0 < n)
    (hstep : ∀ x ∈ T, ∀ p : ℕ, p.Prime → p ∣ x → x / p ∈ T) : DivClosed T := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha d hd
    by_cases hda : d = a
    · rw [hda]; exact ha
    have ha0 := hT a ha
    obtain ⟨m, rfl⟩ := hd
    have hm1 : m ≠ 1 := by intro h; apply hda; rw [h, mul_one]
    have hm0 : m ≠ 0 := by intro h; rw [h, mul_zero] at ha0; omega
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at ha0)
    obtain ⟨r, hr, m', rfl⟩ : ∃ r, r.Prime ∧ ∃ m', m = r * m' :=
      ⟨m.minFac, Nat.minFac_prime hm1, Nat.minFac_dvd m⟩
    have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    have hmem := hstep (d * (r * m')) ha r hr ⟨d * m', by ring⟩
    have hdiv : d * (r * m') / r = d * m' := by
      rw [show d * (r * m') = r * (d * m') by ring, Nat.mul_div_cancel_left _ hr.pos]
    rw [hdiv] at hmem
    have hlt : d * m' < d * (r * m') := by
      apply Nat.mul_lt_mul_of_pos_left _ hd0
      have := hr.two_le
      calc m' < 2 * m' := by omega
        _ ≤ r * m' := Nat.mul_le_mul_right _ this
    exact ih _ hlt hmem d (Dvd.intro _ rfl)

/-- **Lemma 2**: every finite set of positive integers can be replaced by a set of the same size,
closed under divisors and under replacing a prime factor by a smaller prime, without decreasing
any run count `|A S t|`. -/
theorem exists_closed (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) :
    ∃ T : Finset ℕ, (∀ a ∈ T, 0 < a) ∧ T.card = S.card ∧ DivClosed T ∧ ShiftClosed T ∧
      ∀ t, (A S t).card ≤ (A T t).card := by
  classical
  let good : Finset ℕ → Prop := fun T =>
    (∀ a ∈ T, 0 < a) ∧ T.card = S.card ∧ ∀ t, (A S t).card ≤ (A T t).card
  have hex : ∃ s, ∃ T, good T ∧ ∑ n ∈ T, n = s := ⟨_, S, ⟨hS, rfl, fun _ => le_rfl⟩, rfl⟩
  obtain ⟨T, hT, hTs⟩ := Nat.find_spec hex
  have hmin : ∀ T', good T' → ∑ n ∈ T, n ≤ ∑ n ∈ T', n := fun T' hT' => by
    rw [hTs]; exact Nat.find_min' hex ⟨T', hT', rfl⟩
  -- compressing a good set gives a good set
  have hcomp : ∀ {κ : Type} [DecidableEq κ] (C : ChainSys κ), (∀ t k, C.Cons t k) →
      good (C.comp T) := by
    intro κ _ C hC
    exact ⟨ChainSys.comp_pos hT.1, by rw [ChainSys.card_comp hT.1, hT.2.1],
      fun t => (hT.2.2 t).trans (ChainSys.card_A_le_comp hT.1 t (hC t))⟩
  -- no chain of a minimal good set has a gap
  have hnogap : ∀ {κ : Type} [DecidableEq κ] (C : ChainSys κ), (∀ t k, C.Cons t k) →
      ∀ k, C.occ T k = range (C.occ T k).card := by
    intro κ _ C hC k
    by_contra hk
    have h1 := (ChainSys.sum_comp_le (C := C) hT.1).2 ⟨k, hk⟩
    have h2 := hmin _ (hcomp C hC)
    omega
  refine ⟨T, hT.1, hT.2.1, ?_, ?_, hT.2.2⟩
  · apply divClosed_of_step hT.1
    intro x hx p hp hpx
    by_contra hout
    obtain ⟨hv, hlt, heq⟩ := pChain_div hp (hT.1 x hx) hpx
    exact ChainSys.gap hT.1 hx hlt (by rw [heq]; exact hout)
      (hnogap (pChain hp) (fun t b => pChain_cons hp t b) _)
  · intro a ha p q hp hq hpq hqa
    by_contra hout
    obtain ⟨hv, hlt, heq⟩ := pqChain_shift hp hq hpq (hT.1 a ha) hqa
    exact ChainSys.gap hT.1 ha hlt (by rw [heq]; exact hout)
      (hnogap (pqChain hp hq hpq) (fun t k => pqChain_cons hp hq hpq t k) _)

end RunsOfMultiples
