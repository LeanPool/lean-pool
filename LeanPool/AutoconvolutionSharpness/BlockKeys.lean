/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

/-!
# Block indices

`a` and `b` record the multiplicities at the high base - D digits; coordinate
zero of these vectors is position one of the exponent. The low digit `h` is
stored separately. Disjoint index sets allow either the alternating placement
of §2 or a contiguous placement of the two sets of positions.
-/

@[expose] public section

namespace Autoconvolutions.Blocks
open Finset

/-- High digits, before multiplying by the base to reserve the units place. -/
def code {m : ℕ} (D : ℕ) (a : Fin m → ℕ) : ℕ :=
  ∑ i, a i * D ^ i.val

def key {m : ℕ} (D : ℕ) (a b : Fin m → ℕ) (h : ℕ) : ℕ :=
  h + D * (code D a + code D b)

abbrev Row (m : ℕ) := ((Fin m → ℕ) × (Fin m → ℕ)) × ℕ

noncomputable def rows {m : ℕ} (I J : Finset (Fin m)) (u v D : ℕ) : Finset (Row m) := by
  classical
  exact ((I.piAntidiag u) ×ˢ (J.piAntidiag v)) ×ˢ range D

def rowKey {m : ℕ} (D : ℕ) (t : Row m) : ℕ := key D t.1.1 t.1.2 t.2

theorem mem_rows {m u v D : ℕ} {I J : Finset (Fin m)} {t : Row m} :
    t ∈ rows I J u v D ↔ t.1.1 ∈ I.piAntidiag u ∧
      t.1.2 ∈ J.piAntidiag v ∧ t.2 < D := by
  classical
  simp [rows, and_assoc]

theorem ofDigits_eq_code {m D : ℕ} (a : Fin m → ℕ) :
    Nat.ofDigits D (List.ofFn a) = code D a := by
  induction m with
  | zero => simp [code]
  | succ m ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, ih]
    conv_rhs => unfold code; rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, code, pow_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem code_add {m D : ℕ} (a b : Fin m → ℕ) :
    code D (fun i => a i + b i) = code D a + code D b := by
  simp [code, add_mul, Finset.sum_add_distrib]

theorem low_and_high {m D h h' : ℕ} (hD : 1 < D) {a b : Fin m → ℕ}
    (ha : ∀ i, a i < D) (hb : ∀ i, b i < D) (hh : h < D) (hh' : h' < D)
    (heq : h + D * code D a = h' + D * code D b) : h = h' ∧ a = b := by
  have he : h :: List.ofFn a = h' :: List.ofFn b := by
    apply Nat.ofDigits_inj_of_len_eq hD (by simp)
    · simpa [List.forall_mem_cons, hh, List.forall_mem_ofFn_iff] using ha
    · simpa [List.forall_mem_cons, hh', List.forall_mem_ofFn_iff] using hb
    · simpa only [Nat.ofDigits_cons, ofDigits_eq_code] using heq
  exact ⟨(List.cons.inj he).1, List.ofFn_injective (List.cons.inj he).2⟩

theorem coord_zero_of_notMem {m k : ℕ} {I : Finset (Fin m)} {a : Fin m → ℕ}
    (ha : a ∈ I.piAntidiag k) {i : Fin m} (hi : i ∉ I) : a i = 0 := by
  by_contra h
  exact hi ((Finset.mem_piAntidiag.mp ha).2 i h)

theorem coord_le {m k : ℕ} {I : Finset (Fin m)} {a : Fin m → ℕ}
    (ha : a ∈ I.piAntidiag k) (i : Fin m) : a i ≤ k := by
  by_cases hi : i ∈ I
  · rw [← (Finset.mem_piAntidiag.mp ha).1]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi
  · rw [coord_zero_of_notMem ha hi]
    exact Nat.zero_le _

/-- Across arbitrary levels, bounded totals and disjoint supports make the
low digit and the two multiplicity vectors individually recoverable. -/
theorem rowKey_injective {m u v u' v' D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (huv : u + v < D) (huv' : u' + v' < D)
    {t t' : Row m} (ht : t ∈ rows I J u v D) (ht' : t' ∈ rows I J u' v' D)
    (he : rowKey D t = rowKey D t') : t = t' := by
  obtain ⟨ha, hb, hh⟩ := mem_rows.mp ht
  obtain ⟨ha', hb', hh'⟩ := mem_rows.mp ht'
  have hi := low_and_high hD
    (a := fun i => t.1.1 i + t.1.2 i) (b := fun i => t'.1.1 i + t'.1.2 i)
    (fun i => lt_of_le_of_lt (Nat.add_le_add (coord_le ha i) (coord_le hb i)) huv)
    (fun i => lt_of_le_of_lt (Nat.add_le_add (coord_le ha' i) (coord_le hb' i)) huv')
    hh hh' (by simpa only [code_add, rowKey, key] using he)
  have hleft : t.1.1 = t'.1.1 := by
    funext i
    by_cases hiI : i ∈ I
    · have hiJ := Finset.disjoint_left.mp hd hiI
      simpa [coord_zero_of_notMem hb hiJ, coord_zero_of_notMem hb' hiJ] using congrFun hi.2 i
    · rw [coord_zero_of_notMem ha hiI, coord_zero_of_notMem ha' hiI]
  have hright : t.1.2 = t'.1.2 := by
    funext i
    have heq := congrFun hi.2 i
    rw [congrFun hleft i] at heq
    omega
  exact Prod.ext (Prod.ext hleft hright) hi.1

/-- After recovering a row, its right - digit sum determines the level. -/
theorem rowKey_determines_level {m n s s' D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (hs : s ≤ 2 * n) (hs' : s' ≤ 2 * n)
    (hnD : 4 * n < D) {t t' : Row m}
    (ht : t ∈ rows I J (2 * n - s) (2 * n + s) D)
    (ht' : t' ∈ rows I J (2 * n - s') (2 * n + s') D)
    (he : rowKey D t = rowKey D t') : s = s' ∧ t = t' := by
  have h := rowKey_injective hD hd (by omega) (by omega) ht ht' he
  subst t'
  have h1 := (Finset.mem_piAntidiag.mp (mem_rows.mp ht).2.1).1
  have h2 := (Finset.mem_piAntidiag.mp (mem_rows.mp ht').2.1).1
  exact ⟨by omega, rfl⟩

end Autoconvolutions.Blocks
