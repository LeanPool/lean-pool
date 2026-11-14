/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.CM.Unmixedness
public import LeanPool.RoyStrongSix.M2.Deriv
public import LeanPool.RoyStrongSix.M2.Transl

/-!
# Wüstholz's lemma, linear-algebra part (Roy Lemma 8.16, Thm 8.18)

Setting: an ideal `J` of a commutative `K`-algebra `R`, derivations `D₁, …, D_ℓ`, and `Q₁, …, Q_ℓ
∈ J`
with `Dᵢ Qⱼ ≡ δᵢⱼ (mod J)`.

* `DL Dv l`: the derivations along a word `l`, the first letter applied first.
* `qprod Q m = ∏_{i ∈ m} Qᵢ` for a multiset `m` of indices.
* `DL_qprod_off`, `DL_qprod_diag` (**Roy Lemma 8.16**): for `|l| ≤ |m|`,
  `D_l (P · Q^m) ≡ 0 (mod J)` unless `l` is a word for `m`, and `D_l (P · Q^l) ≡ c P` with `c ≠ 0`.
  We iterate along words instead of using `D^α`, so commutativity of the `Dᵢ` is never needed.
* `indep_mod`: products `Pₐ Q^{mₐ}` (distinct `mₐ`, `|mₐ| ≤ S₀`, `Pₐ` in a complement of `J`) are
  linearly independent modulo any ideal `A` whose elements vanish to order `> S₀` (`D_l A ⊆ J`).
* **`wustholz`** (Roy Thm 8.18, filtered form): `(k+1)^ℓ · H(J; t) ≤ H(A; t + S₀ c₀)` when `ℓ k ≤
S₀`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

section Generic

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {ι : Type*}

theorem derivation_pow_succ_mem (D : Derivation K R R) (J : Ideal R) :
    ∀ (n : ℕ) {x : R}, x ∈ J ^ (n + 1) → D x ∈ J ^ n := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hb (ih ha)
    · rw [map_add]; exact Ideal.add_mem _ hx hy

/-- The derivations along the word `l`; the first letter is applied first. -/
noncomputable def DL (Dv : ι → Derivation K R R) (l : List ι) : R →ₗ[K] R :=
  l.foldr (fun i f => f ∘ₗ (Dv i).toLinearMap) LinearMap.id

variable (Dv : ι → Derivation K R R)

@[simp] theorem DL_nil (x : R) : DL Dv [] x = x := rfl

theorem DL_cons (i : ι) (l : List ι) (x : R) : DL Dv (i :: l) x = DL Dv l (Dv i x) := rfl

theorem DL_pow_mem (J : Ideal R) (l : List ι) :
    ∀ (m : ℕ) {x : R}, x ∈ J ^ (m + l.length) → DL Dv l x ∈ J ^ m := by
  induction l with
  | nil => intro m x hx; simpa using hx
  | cons i l ih =>
    intro m x hx
    rw [DL_cons]
    apply ih
    apply derivation_pow_succ_mem
    simpa [List.length_cons, add_assoc] using hx

/-- `Q^m = ∏_{i ∈ m} Qᵢ`. -/
def qprod (Q : ι → R) (m : Multiset ι) : R := (m.map Q).prod

theorem qprod_zero (Q : ι → R) : qprod Q 0 = 1 := by simp [qprod]

theorem qprod_cons (Q : ι → R) (a : ι) (m : Multiset ι) : qprod Q (a ::ₘ m) = Q a * qprod Q m := by
  simp [qprod]

theorem qprod_mem (J : Ideal R) {Q : ι → R} (hQ : ∀ i, Q i ∈ J) (m : Multiset ι) :
    qprod Q m ∈ J ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp [qprod_zero]
  | cons a m ih =>
    rw [qprod_cons, Multiset.card_cons, pow_succ']
    exact Ideal.mul_mem_mul (hQ a) ih

variable [DecidableEq ι] {J : Ideal R} {Q : ι → R}

/-- `Dᵢ Q^m ≡ (mult. of i in m) · Q^{m − i} (mod J^{|m|})`. -/
theorem Dv_qprod (hQ : ∀ i, Q i ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then 1 else 0) ∈ J)
    (i : ι) (m : Multiset ι) :
    Dv i (qprod Q m) - (m.count i : R) * qprod Q (m.erase i) ∈ J ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp [qprod_zero]
  | cons a m ih =>
    have hsplit : Dv i (qprod Q (a ::ₘ m)) - ((a ::ₘ m).count i : R) * qprod Q ((a ::ₘ m).erase i) =
        Q a * (Dv i (qprod Q m) - (m.count i : R) * qprod Q (m.erase i)) +
          qprod Q m * (Dv i (Q a) - if i = a then 1 else 0) := by
      rw [qprod_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      by_cases h : i = a
      · subst h
        rw [Multiset.count_cons_self, Multiset.erase_cons_head, ite_eq_left rfl]
        by_cases hc : m.count i = 0
        · rw [hc]; push_cast; ring
        · have : qprod Q m = Q i * qprod Q (m.erase i) := by
            conv_lhs => rw [← Multiset.cons_erase (Multiset.count_ne_zero.mp hc)]
            exact qprod_cons Q i _
          rw [this]; push_cast; ring
      · rw [Multiset.count_cons_of_ne h, Multiset.erase_cons_tail m (Ne.symm h), qprod_cons,
        ite_eq_right h]
        ring
    rw [hsplit, Multiset.card_cons]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ']; exact Ideal.mul_mem_mul (hQ a) ih
    · rw [pow_succ]; exact Ideal.mul_mem_mul (qprod_mem J hQ m) (hδ i a)

theorem Dv_mul_qprod (hQ : ∀ i, Q i ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then 1 else 0) ∈ J)
    (i : ι) (m : Multiset ι) (P : R) :
    Dv i (P * qprod Q m) - ((m.count i : R) * P) * qprod Q (m.erase i) ∈ J ^ Multiset.card m := by
  have e : Dv i (P * qprod Q m) - ((m.count i : R) * P) * qprod Q (m.erase i) =
      P * (Dv i (qprod Q m) - (m.count i : R) * qprod Q (m.erase i)) + qprod Q m * Dv i P := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Dv_qprod Dv hQ hδ i m))
    (Ideal.mul_mem_right _ _ (qprod_mem J hQ m))

theorem pow_le_of_ne {n : ℕ} (hn : n ≠ 0) {x : R} (hx : x ∈ J ^ n) : x ∈ J :=
  Ideal.pow_le_self hn hx

/-- **Roy Lemma 8.16, off-diagonal.** -/
theorem DL_qprod_off (hQ : ∀ i, Q i ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then 1 else 0) ∈ J)
    (l : List ι) : ∀ (m : Multiset ι) (P : R), l.length ≤ Multiset.card m → (l : Multiset ι) ≠ m →
      DL Dv l (P * qprod Q m) ∈ J := by
  induction l with
  | nil =>
    intro m P _ hne
    have hm : Multiset.card m ≠ 0 := fun h => hne (Multiset.card_eq_zero.mp h ▸ rfl)
    exact Ideal.mul_mem_left _ _ (pow_le_of_ne hm (qprod_mem J hQ m))
  | cons i l ih =>
    intro m P hlen hne
    rw [List.length_cons] at hlen
    rw [DL_cons]
    have hs := Dv_mul_qprod Dv hQ hδ i m P
    have hs' : DL Dv l (Dv i (P * qprod Q m) - ((m.count i : R) * P) * qprod Q (m.erase i)) ∈ J
      := by
      have := DL_pow_mem Dv J l (Multiset.card m - l.length)
        (x := Dv i (P * qprod Q m) - ((m.count i : R) * P) * qprod Q (m.erase i))
        (by rwa [Nat.sub_add_cancel (by omega)])
      exact pow_le_of_ne (by omega) this
    have hmain : DL Dv l (((m.count i : R) * P) * qprod Q (m.erase i)) ∈ J := by
      by_cases hc : m.count i = 0
      · rw [hc]; simp
      · have him : i ∈ m := Multiset.count_ne_zero.mp hc
        refine ih _ _ ?_ ?_
        · rw [Multiset.card_erase_of_mem him, Nat.pred_eq_sub_one]; omega
        · intro h
          apply hne
          rw [← Multiset.cons_coe, h, Multiset.cons_erase him]
    have := Ideal.add_mem _ hmain hs'
    rwa [map_sub, add_sub_cancel] at this

/-- **Roy Lemma 8.16, diagonal.** -/
theorem DL_qprod_diag (hQ : ∀ i, Q i ∈ J) (hδ : ∀ i j, Dv i (Q j) - (if i = j then 1 else 0) ∈ J)
    (l : List ι) : ∃ c : ℕ, c ≠ 0 ∧ ∀ P : R, DL Dv l (P * qprod Q l) - (c : R) * P ∈ J := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, fun P => by simp [qprod_zero]⟩
  | cons i l ih =>
    obtain ⟨c, hc, hcP⟩ := ih
    refine ⟨c * ((l : Multiset ι).count i + 1), Nat.mul_ne_zero hc (Nat.succ_ne_zero _), fun P
      => ?_⟩
    rw [DL_cons]
    have hs := Dv_mul_qprod Dv hQ hδ i (i :: l : Multiset ι) P
    rw [← Multiset.cons_coe, Multiset.count_cons_self, Multiset.erase_cons_head,
      Multiset.card_cons] at hs
    have hs' := DL_pow_mem Dv J l 1 (by rw [add_comm]; exact hs)
    rw [pow_one] at hs'
    have h1 := hcP ((((l : Multiset ι).count i + 1 : ℕ) : R) * P)
    rw [← Multiset.cons_coe]
    have := Ideal.add_mem _ h1 hs'
    rw [map_sub] at this
    convert this using 1
    push_cast
    ring

theorem mem_of_natCast_mul_mem [CharZero K] {c : ℕ} (hc : c ≠ 0) {x : R} (hx : (c : R) * x ∈ J) :
    x ∈ J := by
  have e : x = algebraMap K R (c : K)⁻¹ * ((c : R) * x) := by
    rw [← mul_assoc, ← map_natCast (algebraMap K R) c, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hc), map_one, one_mul]
  rw [e]; exact Ideal.mul_mem_left _ _ hx

/-- **Independence modulo `A`** (the heart of Roy Thm 8.18). -/
theorem indep_mod [CharZero K] (hQ : ∀ i, Q i ∈ J)
    (hδ : ∀ i j, Dv i (Q j) - (if i = j then 1 else 0) ∈ J) {A : Ideal R} {S0 : ℕ}
    (hA : ∀ x ∈ A, ∀ l : List ι, l.length ≤ S0 → DL Dv l x ∈ J)
    {κ : Type*} [Fintype κ] (idx : κ → Multiset ι) (hidx : Function.Injective idx)
    (hcard : ∀ a, Multiset.card (idx a) ≤ S0) (f : κ → R) (hfJ : ∀ a, f a ∈ J → f a = 0)
    (hsum : ∑ a, f a * qprod Q (idx a) ∈ A) : ∀ a, f a = 0 := by
  classical
  let : DecidableEq κ := Classical.decEq κ
  by_contra hne
  push Not at hne
  have hnon : (Finset.univ.filter fun a => f a ≠ 0).Nonempty := by
    obtain ⟨a, ha⟩ := hne; exact ⟨a, by simpa using ha⟩
  obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image _ (fun a => Multiset.card (idx a)) hnon
  have ha0' : f a0 ≠ 0 := (Finset.mem_filter.mp ha0).2
  set l := (idx a0).toList with hl
  have hlc : (l : Multiset ι) = idx a0 := Multiset.coe_toList _
  have hll : l.length = Multiset.card (idx a0) := Multiset.length_toList _
  have htot := hA _ hsum l (hll ▸ hcard a0)
  rw [map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a0)] at htot
  have hrest : ∑ a ∈ Finset.univ.erase a0, DL Dv l (f a * qprod Q (idx a)) ∈ J := by
    refine Ideal.sum_mem _ fun a ha => ?_
    by_cases hfa : f a = 0
    · rw [hfa, zero_mul, map_zero]; exact J.zero_mem
    · refine DL_qprod_off Dv hQ hδ l _ _ ?_ ?_
      · rw [hll]; exact hmin a (by simpa using hfa)
      · rw [hlc]; exact fun h => (Finset.mem_erase.mp ha).1 (hidx h).symm
  have h0 : DL Dv l (f a0 * qprod Q (idx a0)) ∈ J := by
    have := J.sub_mem htot hrest
    rwa [add_sub_cancel_right] at this
  obtain ⟨c, hc, hcP⟩ := DL_qprod_diag Dv hQ hδ l
  have := J.sub_mem h0 (hcP (f a0))
  rw [hlc, sub_sub_cancel] at this
  exact ha0' (hfJ a0 (mem_of_natCast_mul_mem (K := K) hc this))

end Generic

/-! ### The count in `B = K[X, Y, Z]` -/

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K

omit [CharZero K] in
theorem qprod_mem_FLE {ι : Type*} {D : Fin 2 → ℕ} {Q : ι → B} {c0 : ℕ}
    (hQ : ∀ j, Q j ∈ FLE K blk (c0 • D)) (m : Multiset ι) :
    qprod Q m ∈ FLE K blk ((Multiset.card m * c0) • D) := by
  induction m using Multiset.induction_on with
  | empty => rw [qprod_zero]; exact one_mem_FLE _
  | cons a m ih =>
    rw [qprod_cons, Multiset.card_cons, add_mul, one_mul, add_smul, add_comm]
    exact mul_mem_FLE K (hQ a) ih

/-- **Wüstholz's lemma, counting form.** -/
theorem wustholz_count {D : Fin 2 → ℕ} {ι : Type*} [DecidableEq ι] (Dv : ι → Derivation K B B)
    {A J : Ideal B} {Q : ι → B} (hQ : ∀ i, Q i ∈ J)
    (hδ : ∀ i j, Dv i (Q j) - (if i = j then 1 else 0) ∈ J) {c0 : ℕ}
    (hQdeg : ∀ j, Q j ∈ FLE K blk (c0 • D)) {S0 : ℕ}
    (hA : ∀ x ∈ A, ∀ l : List ι, l.length ≤ S0 → DL Dv l x ∈ J)
    {κ : Type*} [Fintype κ] (idx : κ → Multiset ι) (hidx : Function.Injective idx)
    (hcard : ∀ a, Multiset.card (idx a) ≤ S0) (t : ℕ) :
    Fintype.card κ * hfun blk D K J t ≤ hfun blk D K A (t + S0 * c0) := by
  classical
  let : DecidableEq κ := Classical.decEq κ
  set F := FLE K blk (t • D) with hF
  set F' := FLE K blk ((t + S0 * c0) • D) with hF'
  set p := J.restrictScalars K ⊓ F with hp
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  set E := q ⊓ F with hE
  have : FiniteDimensional K p := Submodule.finiteDimensional_of_le inf_le_right
  have : FiniteDimensional K E := Submodule.finiteDimensional_of_le inf_le_right
  -- `finrank E = hfun J t`
  have hpE : p ⊓ E = ⊥ := eq_bot_iff.mpr fun x hx =>
    hq.disjoint.le_bot ⟨hx.1, hx.2.1⟩
  have hpE' : p ⊔ E = F := by
    rw [hE, ← sup_inf_assoc_of_le q (inf_le_right : p ≤ F), hq.sup_eq_top, top_inf_eq]
  have hdimE : finrank K E = hfun blk D K J t := by
    have := Submodule.finrank_sup_add_finrank_inf_eq p E
    rw [hpE, hpE', finrank_bot] at this
    change _ = finrank K F - finrank K p
    omega
  -- the products
  let Ψ : (κ → E) →ₗ[K] B := ∑ a, (LinearMap.mulRight K (qprod Q (idx a))) ∘ₗ E.subtype ∘ₗ
    LinearMap.proj a
  have hΨ : ∀ f, Ψ f = ∑ a, (f a : B) * qprod Q (idx a) := fun f => by
    simp [Ψ, LinearMap.sum_apply]
  have hEJ : ∀ x : E, (x : B) ∈ J → (x : B) = 0 := fun x hx =>
    (Submodule.mem_bot K).mp (hpE ▸ ⟨⟨hx, x.2.2⟩, x.2⟩)
  have hzero : ∀ f, Ψ f ∈ A → f = 0 := fun f hf => by
    have := indep_mod Dv hQ hδ hA idx hidx hcard (fun a => (f a : B)) (fun a => hEJ (f a))
      (hΨ f ▸ hf)
    funext a; exact Subtype.ext (this a)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    exact (Submodule.mem_bot K).mpr (hzero f (by rw [LinearMap.mem_ker.mp hf]; exact A.zero_mem))
  set U := LinearMap.range Ψ
  have hUF' : U ≤ F' := by
    rintro _ ⟨f, rfl⟩
    rw [hΨ]
    refine Submodule.sum_mem _ fun a _ => ?_
    have h1 : (f a : B) ∈ F := (f a).2.2
    have h2 := qprod_mem_FLE hQdeg (idx a)
    have h3 := mul_mem_FLE K h1 h2
    rw [← add_smul] at h3
    exact FLE_mono K blk (fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by have := hcard a; nlinarith)) h3
  have : FiniteDimensional K U := Submodule.finiteDimensional_of_le hUF'
  set X := A.restrictScalars K ⊓ F'
  have : FiniteDimensional K X := Submodule.finiteDimensional_of_le inf_le_right
  have hUX : U ⊓ X = ⊥ := eq_bot_iff.mpr fun x ⟨⟨f, hf⟩, hxA, _⟩ => by
    subst hf; rw [hzero f hxA, map_zero]; exact Submodule.zero_mem _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U X
  rw [hUX, finrank_bot, add_zero] at hsum
  have hle : finrank K ↥(U ⊔ X) ≤ finrank K F' :=
    Submodule.finrank_mono (sup_le hUF' inf_le_right)
  have hU : finrank K U = Fintype.card κ * finrank K E := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have hA' : hfun blk D K A (t + S0 * c0) = finrank K F' - finrank K X := rfl
  rw [hA', ← hdimE]
  omega

/-- **Wüstholz's lemma** (Roy Thm 8.18) with the box of exponents `{0..k}^ℓ`. -/
theorem wustholz {D : Fin 2 → ℕ} {ℓ : ℕ} (Dv : Fin ℓ → Derivation K B B)
    {A J : Ideal B} {Q : Fin ℓ → B} (hQ : ∀ i, Q i ∈ J)
    (hδ : ∀ i j, Dv i (Q j) - (if i = j then 1 else 0) ∈ J) {c0 : ℕ}
    (hQdeg : ∀ j, Q j ∈ FLE K blk (c0 • D)) {S0 k : ℕ} (hk : ℓ * k ≤ S0)
    (hA : ∀ x ∈ A, ∀ l : List (Fin ℓ), l.length ≤ S0 → DL Dv l x ∈ J) (t : ℕ) :
    (k + 1) ^ ℓ * hfun blk D K J t ≤ hfun blk D K A (t + S0 * c0) := by
  classical
  let idx : (Fin ℓ → Fin (k + 1)) → Multiset (Fin ℓ) := fun a => ∑ i, (a i : ℕ) • {i}
  have hcount : ∀ a j, (idx a).count j = a j := by
    intro a j
    simp only [idx, Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]
    simp
  have hidx : Function.Injective idx := fun a b h => funext fun j => Fin.ext (by
    rw [← hcount a j, ← hcount b j, h])
  have hcard : ∀ a, Multiset.card (idx a) ≤ S0 := by
    intro a
    have : Multiset.card (idx a) = ∑ i, (a i : ℕ) := by
      simp only [idx, Multiset.card_sum, Multiset.card_nsmul, Multiset.card_singleton, mul_one]
    rw [this]
    calc ∑ i, (a i : ℕ) ≤ ∑ _i : Fin ℓ, k := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (a i).2
      _ = ℓ * k := by simp
      _ ≤ S0 := hk
  have := wustholz_count Dv hQ hδ hQdeg hA idx hidx hcard t
  simpa using this

end StrongSix.M2

end LeanPool
