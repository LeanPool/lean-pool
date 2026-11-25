/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Length
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Kazhdan–Polishchuk Theorem A in its original form, part B

Source: `PROOF.md`, Section 3 ("Finite sums of finite intersections").

Setting. `A : ι → Submodule R M` is a family of submodules (any ring, any module; for a vector
space `d` below is the
dimension), `d (A x) (A y) ≤ r` for all `x, y`, where `d A B` is the length of `A / (A ∩ B)`. `W`
is a submodule with
`d W (A x) ≤ r` and `d (A x) W ≤ r (r + 1)` for all `x`, and with the DESCENT property: for every
`x`, every
`L ≤ A x` with `1 ≤ n := d L W ≤ r (r + 1)` has a member `A y` with `(r + 1) d (L ∩ A y) W ≤ r n`.

The two bounds alone do NOT suffice (one member `A = ⟨e₁, e₂, e₃⟩`, `W = ⟨e₂, e₃⟩`, `r = 1`: no
finite intersection of
members lies in `W`). The descent property follows from inequality (1) of Section 2 of the source
at a level
`t ≥ r/(r+1)` with `(r+1)(t·r(r+1) + τ) < r·r(r+1) + 1` (`descent_of_first_order`).

Result. `D = sumInter A W`, the sum of all finite nonempty intersections of members that lie in
`W`, is
* invariant under every lattice automorphism that permutes the members and fixes `W`
  (`sumInter_map_eq`), in particular
  under a group acting linearly (`sumInter_map_eq_of_group`);
* a FINITE sum of finite nonempty intersections of members (`partB`, first part);
* `d D (A x) ≤ r` and `d (A x) D ≤ r * Kr r` for every `x`, where `Kr r = ∑_{j=1}^{r} ⌈(r+1)/j⌉ ≤
  r (r+1)`.
-/

@[expose] public section

open Submodule

namespace KPFull.PartB

open AlmostInvariant (d d_inf d_sup d_add d_eq_zero d_mono_left d_anti_right d_map
  d_self d_triangle)

/-- For vector spaces, `d` is the dimension. -/
theorem d_le_iff_rank {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] (A B :
    Submodule K V) (n : ℕ) :
    d A B ≤ n ↔ Module.rank K (A ⧸ B.submoduleOf A) ≤ n := by
  rw [d, Module.length_eq_rank, Cardinal.toENat_le_natCast]

section Potential

/-- `Kr r = ∑_{j=1}^{r} ⌈(r+1)/j⌉`, written with `j + 1` in place of `j` and `⌈a/b⌉ = (a + b -
1)/b`. -/
def Kr (r : ℕ) : ℕ := ∑ j ∈ Finset.range r, (r + 1 + j) / (j + 1)

/-- The potential of the greedy descent: band `j` (the values `n` with `j (r+1) < n ≤ (j+1)(r+1)`)
contributes
`⌈min(n - j(r+1), r+1) / (j+1)⌉`. -/
def pot (r n : ℕ) : ℕ := ∑ j ∈ Finset.range r, (min (n - j * (r + 1)) (r + 1) + j) / (j + 1)

theorem pot_mono (r : ℕ) : Monotone (pot r) := by
  intro a b hab
  unfold pot
  refine Finset.sum_le_sum fun j _ => ?_
  apply Nat.div_le_div_right
  generalize j * (r + 1) = X
  omega

theorem pot_top (r : ℕ) : pot r (r * (r + 1)) = Kr r := by
  unfold pot Kr
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j < r := Finset.mem_range.mp hj
  have h : r + 1 ≤ r * (r + 1) - j * (r + 1) := by
    have h1 : (j + 1) * (r + 1) ≤ r * (r + 1) := Nat.mul_le_mul_right _ hj
    have e : (j + 1) * (r + 1) = j * (r + 1) + (r + 1) := by ring
    omega
  rw [min_eq_right h]

theorem pot_le_Kr {r n : ℕ} (h : n ≤ r * (r + 1)) : pot r n ≤ Kr r := pot_top r ▸ pot_mono r h

/-- One greedy step lowers the potential by at least one. -/
theorem pot_step {r n m : ℕ} (hn : 1 ≤ n) (hnB : n ≤ r * (r + 1)) (hm : (r + 1) * m ≤ r * n) :
    pot r m + 1 ≤ pot r n := by
  have hr1 : 0 < r + 1 := Nat.succ_pos r
  obtain ⟨j0, hj0⟩ : ∃ j : ℕ, j = (n - 1) / (r + 1) := ⟨_, rfl⟩
  have hdm : (r + 1) * j0 + (n - 1) % (r + 1) = n - 1 := by
    rw [hj0]; exact Nat.div_add_mod (n - 1) (r + 1)
  have hmod : (n - 1) % (r + 1) < r + 1 := Nat.mod_lt (n - 1) hr1
  have e1 : j0 * (r + 1) = (r + 1) * j0 := by ring
  have e2 : (j0 + 1) * (r + 1) = (r + 1) * j0 + (r + 1) := by ring
  have hX1 : j0 * (r + 1) < n := by omega
  have hX2 : n ≤ j0 * (r + 1) + (r + 1) := by omega
  have hj0r : j0 < r := by
    rw [hj0, Nat.div_lt_iff_lt_mul hr1]
    omega
  have hmj : m + j0 + 1 ≤ n := by
    by_contra hcon
    have h3 : n ≤ m + j0 := by omega
    have h4 : (r + 1) * n ≤ (r + 1) * (m + j0) := Nat.mul_le_mul_left _ h3
    have h5 : (r + 1) * (m + j0) = (r + 1) * m + (r + 1) * j0 := by ring
    have h6 : (r + 1) * n = r * n + n := by ring
    omega
  have hmn : m ≤ n := by omega
  have hterm : ∀ j ∈ Finset.range r, (min (m - j * (r + 1)) (r + 1) + j) / (j + 1) ≤
      (min (n - j * (r + 1)) (r + 1) + j) / (j + 1) := by
    intro j _
    apply Nat.div_le_div_right
    generalize j * (r + 1) = X
    omega
  have hstrict : (min (m - j0 * (r + 1)) (r + 1) + j0) / (j0 + 1) <
      (min (n - j0 * (r + 1)) (r + 1) + j0) / (j0 + 1) := by
    generalize hX : j0 * (r + 1) = X at hX1 hX2 ⊢
    have hp : min (n - X) (r + 1) = n - X := min_eq_left (by omega)
    rw [hp]
    by_cases hmX : m ≤ X
    · have h0 : m - X = 0 := Nat.sub_eq_zero_of_le hmX
      rw [h0, min_eq_left (Nat.zero_le _), zero_add, Nat.div_eq_of_lt (Nat.lt_add_one j0)]
      exact Nat.div_pos (by omega) (by omega)
    · have h1 : min (m - X) (r + 1) + j0 + (j0 + 1) ≤ n - X + j0 := by omega
      calc (min (m - X) (r + 1) + j0) / (j0 + 1) < (min (m - X) (r + 1) + j0) / (j0 + 1) + 1 :=
            Nat.lt_add_one _
        _ = (min (m - X) (r + 1) + j0 + (j0 + 1)) / (j0 + 1) := (Nat.add_div_right _ (by
            omega)).symm
        _ ≤ (n - X + j0) / (j0 + 1) := Nat.div_le_div_right h1
  have h := Finset.sum_lt_sum hterm ⟨j0, Finset.mem_range.mpr hj0r, hstrict⟩
  unfold pot
  omega

/-- `⌈(r+1)/(1+j)⌉₊ = (r + 1 + j) / (j + 1)` (natural division). -/
theorem ceil_eq_div (r j : ℕ) : ⌈((r : ℚ) + 1) / ((1 + j : ℕ) : ℚ)⌉₊ = (r + 1 + j) / (j + 1) := by
  have hj : (0 : ℚ) < ((1 + j : ℕ) : ℚ) := by positivity
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = (r + 1 + j) / (j + 1) := ⟨_, rfl⟩
  rw [← hq]
  have hdm : (j + 1) * q + (r + 1 + j) % (j + 1) = r + 1 + j := by
    rw [hq]; exact Nat.div_add_mod _ _
  have hmod : (r + 1 + j) % (j + 1) < j + 1 := Nat.mod_lt _ (Nat.succ_pos j)
  have hq1 : 1 ≤ q := by
    rw [hq]; exact Nat.div_pos (by omega) (Nat.succ_pos j)
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have e : (j + 1) * (p + 1) = p * (1 + j) + (j + 1) := by ring
  have e' : (p + 1) * (1 + j) = p * (1 + j) + (j + 1) := by ring
  rw [Nat.ceil_eq_iff (by omega)]
  constructor
  · rw [lt_div_iff₀ hj, Nat.add_sub_cancel]
    have h : p * (1 + j) < r + 1 := by omega
    exact_mod_cast h
  · rw [div_le_iff₀ hj]
    have h : r + 1 ≤ (p + 1) * (1 + j) := by omega
    exact_mod_cast h

/-- `Kr r = ∑_{j=1}^{r} ⌈(r+1)/j⌉₊`, in the form of the statement S2'. -/
theorem Kr_eq_ceil (r : ℕ) : Kr r = ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ := by
  have hI : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  unfold Kr
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ceil_eq_div]

theorem Kr_le (r : ℕ) : Kr r ≤ r * (r + 1) := by
  unfold Kr
  calc ∑ j ∈ Finset.range r, (r + 1 + j) / (j + 1) ≤ ∑ _j ∈ Finset.range r, (r + 1) :=
        Finset.sum_le_sum fun j _ => Nat.div_le_of_le_mul (by nlinarith)
    _ = r * (r + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end Potential

section Family

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {ι : Type*}

/-- The intersection of the members `A y`, `y ∈ T`. -/
noncomputable def inter (A : ι → Submodule R M) (T : Finset ι) : Submodule R M := ⨅ y ∈ T, A y

theorem inter_le (A : ι → Submodule R M) {T : Finset ι} {y : ι} (hy : y ∈ T) : inter A T ≤ A y :=
  biInf_le _ hy

theorem inter_anti (A : ι → Submodule R M) {T T' : Finset ι} (h : T ⊆ T') : inter A T'
    ≤ inter A T :=
  le_iInf₂ fun _ hy => inter_le A (h hy)

theorem inter_insert [DecidableEq ι] (A : ι → Submodule R M) (y : ι) (T : Finset ι) :
    inter A (insert y T) = A y ⊓ inter A T := by
  simp only [inter, Finset.iInf_insert]

theorem inter_singleton (A : ι → Submodule R M) (x : ι) : inter A {x} = A x := by
  simp only [inter, Finset.iInf_singleton]

/-- `T` is eligible: a nonempty finite set of indices whose intersection lies in `W`. -/
def Eligible (A : ι → Submodule R M) (W : Submodule R M) (T : Finset ι) : Prop :=
  T.Nonempty ∧ inter A T ≤ W

/-- The sum of all finite nonempty intersections of members that lie in `W`. -/
noncomputable def sumInter (A : ι → Submodule R M) (W : Submodule R M) : Submodule R M :=
  ⨆ (T : Finset ι) (_ : Eligible A W T), inter A T

theorem le_sumInter {A : ι → Submodule R M} {W : Submodule R M} {T : Finset ι} (h : Eligible A W
    T) :
    inter A T ≤ sumInter A W :=
  le_iSup₂ (f := fun T (_ : Eligible A W T) => inter A T) T h

theorem sumInter_le (A : ι → Submodule R M) (W : Submodule R M) : sumInter A W ≤ W :=
  iSup₂_le fun _ h => h.2

/-- The supremum of the intersections indexed by a finite set `F` of finite sets. -/
noncomputable def supOf (A : ι → Submodule R M) (F : Finset (Finset ι)) : Submodule R M := ⨆ T ∈
    F, inter A T

theorem inter_le_supOf (A : ι → Submodule R M) {F : Finset (Finset ι)} {T : Finset ι} (h : T ∈ F) :
    inter A T ≤ supOf A F :=
  le_iSup₂ (f := fun T (_ : T ∈ F) => inter A T) T h

/-- The descent property of `W` (Section 3 of the source; it follows from inequality (1) of
Section 2). -/
def Descent (A : ι → Submodule R M) (W : Submodule R M) (r B : ℕ) : Prop :=
  ∀ (L : Submodule R M) (x : ι) (n : ℕ), L ≤ A x → d L W = n → 1 ≤ n → n ≤ B →
    ∃ y, ((r + 1 : ℕ) : ℕ∞) * d (L ⊓ A y) W ≤ ((r * n : ℕ) : ℕ∞)

/-- The greedy descent: from a finite intersection `inter A T` (with `x ∈ T`) at projected
dimension `n`, a larger finite
set `T'` has its intersection in `W`, at cost at most `r * P n`, for every potential `P` that
drops at each step. -/
theorem descent {A : ι → Submodule R M} {W : Submodule R M} {r B : ℕ} {P : ℕ → ℕ}
    (hP : ∀ n m : ℕ, 1 ≤ n → n ≤ B → (r + 1) * m ≤ r * n → P m + 1 ≤ P n)
    (hA : ∀ x y, d (A x) (A y) ≤ r) (hdesc : Descent A W r B) :
    ∀ (n : ℕ) (x : ι) (T : Finset ι), x ∈ T → d (inter A T) W = n → n ≤ B →
      ∃ T' : Finset ι, T ⊆ T' ∧ inter A T' ≤ W ∧ d (inter A T) (inter A T') ≤ ((r * P n : ℕ) : ℕ∞)
          := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x T hxT hn hnB
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      refine ⟨T, Finset.Subset.refl T, d_eq_zero.mp (by simpa using hn), ?_⟩
      rw [d_self]
      exact zero_le
    · obtain ⟨y, hy⟩ := hdesc (inter A T) x n (inter_le A hxT) hn hpos hnB
      have hfin : d (inter A T ⊓ A y) W ≠ ⊤ := by
        intro htop
        rw [htop, ENat.mul_top (by exact_mod_cast Nat.succ_ne_zero r)] at hy
        exact ENat.natCast_ne_top _ (top_le_iff.mp hy)
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← hm] at hy
      have hy' : (r + 1) * m ≤ r * n := by exact_mod_cast hy
      have hmn : m < n := by
        by_contra hcon
        have h1 : (r + 1) * n ≤ (r + 1) * m := Nat.mul_le_mul_left _ (by omega)
        have h2 : (r + 1) * n = r * n + n := by ring
        omega
      have hT1 : inter A (insert y T) = inter A T ⊓ A y := by rw [inter_insert, inf_comm]
      obtain ⟨T', hsub, hT'W, hcost⟩ := ih m hmn x (insert y T) (Finset.mem_insert_of_mem hxT)
        (by rw [hT1, hm]) (hmn.le.trans hnB)
      refine ⟨T', (Finset.subset_insert y T).trans hsub, hT'W, ?_⟩
      have hchain := d_add (inter_anti A hsub) (inter_anti A (Finset.subset_insert y T))
      have hstep : d (inter A T) (inter A (insert y T)) ≤ r := by
        rw [hT1, d_inf]
        exact (d_mono_left (inter_le A hxT)).trans (hA x y)
      have hPmn := hP n m hpos hnB hy'
      rw [hchain]
      calc d (inter A T) (inter A (insert y T)) + d (inter A (insert y T)) (inter A T')
          ≤ (r : ℕ∞) + ((r * P m : ℕ) : ℕ∞) := add_le_add hstep hcost
        _ ≤ ((r * P n : ℕ) : ℕ∞) := by
          have h1 : r * (P m + 1) ≤ r * P n := Nat.mul_le_mul_left r hPmn
          have h2 : r * (P m + 1) = r * P m + r := by ring
          have h3 : r + r * P m ≤ r * P n := by omega
          exact_mod_cast h3

/-- Every member contains a finite intersection that lies in `W`, at cost at most `r * P B`. -/
theorem exists_inter_le {A : ι → Submodule R M} {W : Submodule R M} {r B : ℕ} {P : ℕ → ℕ}
    (hPmono : Monotone P) (hP : ∀ n m : ℕ, 1 ≤ n → n ≤ B → (r + 1) * m ≤ r * n → P m + 1 ≤ P n)
    (hA : ∀ x y, d (A x) (A y) ≤ r) (hAW : ∀ x, d (A x) W ≤ B) (hdesc : Descent A W r B) (x : ι) :
    ∃ T : Finset ι, x ∈ T ∧ inter A T ≤ W ∧ d (A x) (inter A T) ≤ ((r * P B : ℕ) : ℕ∞) := by
  classical
  have hfin : d (A x) W ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top B) (hAW x)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hnB : n ≤ B := by
    have := hAW x
    rw [← hn] at this
    exact_mod_cast this
  obtain ⟨T', hsub, hT'W, hcost⟩ := descent hP hA hdesc n x {x} (Finset.mem_singleton_self x)
    (by rw [inter_singleton]; exact hn.symm) hnB
  refine ⟨T', hsub (Finset.mem_singleton_self x), hT'W, ?_⟩
  rw [inter_singleton] at hcost
  refine hcost.trans ?_
  have : r * P n ≤ r * P B := Nat.mul_le_mul_left r (hPmono hnB)
  exact_mod_cast this

/-- `sumInter A W` is a finite sum, as soon as one eligible intersection has finite colength in
`W`. -/
theorem sumInter_eq_finite {A : ι → Submodule R M} {W : Submodule R M} {T0 : Finset ι}
    (h0 : Eligible A W T0) (hfin : d W (inter A T0) ≠ ⊤) :
    ∃ F : Finset (Finset ι), T0 ∈ F ∧ (∀ T ∈ F, Eligible A W T) ∧ sumInter A W = supOf A F := by
  classical
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hfin
  have hSW : ∀ F : Finset (Finset ι), (∀ T ∈ F, Eligible A W T) → supOf A F ≤ W :=
    fun F hF => iSup₂_le fun T hT => (hF T hT).2
  have hLS : ∀ F : Finset (Finset ι), T0 ∈ F → inter A T0 ≤ supOf A F := fun F hF =>
      inter_le_supOf A hF
  let Q : ℕ → Prop := fun k => ∃ F : Finset (Finset ι), T0 ∈ F ∧ (∀ T ∈ F, Eligible A W T) ∧
    d (supOf A F) (inter A T0) = k
  have hQle : ∀ k, Q k → k ≤ N := by
    rintro k ⟨F, -, hF, hk⟩
    have h1 : d (supOf A F) (inter A T0) ≤ d W (inter A T0) := d_mono_left (hSW F hF)
    rw [hk, ← hN] at h1
    exact_mod_cast h1
  have hQ0 : Q 0 := by
    refine ⟨{T0}, Finset.mem_singleton_self _, ?_, ?_⟩
    · intro T hT
      rw [Finset.mem_singleton.mp hT]
      exact h0
    · have : supOf A {T0} = inter A T0 := by simp only [supOf, Finset.iSup_singleton]
      rw [this, d_self]
      rfl
  obtain ⟨F, hT0F, hF, hFk⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  have hmax : ∀ T, Eligible A W T → inter A T ≤ supOf A F := by
    intro T hT
    have hF' : ∀ T' ∈ insert T F, Eligible A W T' := by
      intro T' hT'
      rcases Finset.mem_insert.mp hT' with h | h
      · rw [h]; exact hT
      · exact hF T' h
    have hSS : supOf A F ≤ supOf A (insert T F) :=
      iSup₂_le fun T' hT' => inter_le_supOf A (Finset.mem_insert_of_mem hT')
    obtain ⟨k', hk'⟩ := ENat.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top hfin (d_mono_left (hSW _ hF')))
    have hQk' : Q k' := ⟨insert T F, Finset.mem_insert_of_mem hT0F, hF', hk'.symm⟩
    have hk'le : k' ≤ Nat.findGreatest Q N := Nat.le_findGreatest (hQle k' hQk') hQk'
    have hchain : d (supOf A (insert T F)) (inter A T0) =
        d (supOf A (insert T F)) (supOf A F) + d (supOf A F) (inter A T0) := d_add (hLS F hT0F) hSS
    have hzero : d (supOf A (insert T F)) (supOf A F) = 0 := by
      rw [← hk', hFk] at hchain
      have hne : d (supOf A (insert T F)) (supOf A F) ≠ ⊤ := by
        intro htop
        rw [htop, top_add] at hchain
        exact ENat.natCast_ne_top _ hchain
      obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hj] at hchain ⊢
      have h1 : k' = j + Nat.findGreatest Q N := by exact_mod_cast hchain
      have h2 : j = 0 := by omega
      rw [h2]
      rfl
    exact (inter_le_supOf A (Finset.mem_insert_self T F)).trans (d_eq_zero.mp hzero)
  exact ⟨F, hT0F, hF,
    le_antisymm (iSup₂_le fun T hT => hmax T hT) (iSup₂_le fun T hT => le_sumInter (hF T hT))⟩

/-- **Invariance.** A lattice automorphism that maps members to members and fixes `W` maps `D`
into `D`. -/
theorem sumInter_map_le (A : ι → Submodule R M) (W : Submodule R M) (φ : Submodule R M ≃o
    Submodule R M)
    (hφA : ∀ x, ∃ y, φ (A x) = A y) (hφW : φ W = W) : φ (sumInter A W) ≤ sumInter A W := by
  classical
  choose σ hσ using hφA
  unfold sumInter
  rw [OrderIso.map_iSup]
  refine iSup_le fun T => ?_
  rw [OrderIso.map_iSup]
  refine iSup_le fun hT => ?_
  have himg : φ (inter A T) = inter A (T.image σ) := by
    simp only [inter, OrderIso.map_iInf, hσ, Finset.iInf_finset_image]
  have hel : Eligible A W (T.image σ) := by
    refine ⟨hT.1.image σ, ?_⟩
    rw [← himg]
    exact (φ.monotone hT.2).trans_eq hφW
  rw [himg]
  exact le_iSup₂ (f := fun T (_ : Eligible A W T) => inter A T) (T.image σ) hel

theorem sumInter_map_eq (A : ι → Submodule R M) (W : Submodule R M) (φ : Submodule R M ≃o
    Submodule R M)
    (hφA : ∀ x, ∃ y, φ (A x) = A y) (hφA' : ∀ x, ∃ y, φ.symm (A x) = A y) (hφW : φ W = W) :
    φ (sumInter A W) = sumInter A W := by
  refine le_antisymm (sumInter_map_le A W φ hφA hφW) ?_
  have h2 := sumInter_map_le A W φ.symm hφA' (φ.symm_apply_eq.mpr hφW.symm)
  exact (OrderIso.symm_apply_le φ).mp h2

theorem map_map_inv {G : Type*} [Group G] (ρ : G →* (M ≃ₗ[R] M)) (g : G) (S : Submodule R M) :
    (S.map (ρ g⁻¹ : M →ₗ[R] M)).map (ρ g : M →ₗ[R] M) = S := by
  have key : ∀ u : M, ρ g (ρ g⁻¹ u) = u := fun u => by
    change (ρ g * ρ g⁻¹) u = u
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rwa [key]
  · intro hv
    exact ⟨ρ g⁻¹ v, ⟨v, hv, rfl⟩, key v⟩

/-- **Invariance under a group acting linearly** that permutes the members and fixes `W`. -/
theorem sumInter_map_eq_of_group {G : Type*} [Group G] (ρ : G →* (M ≃ₗ[R] M)) (A : ι
    → Submodule R M)
    (W : Submodule R M) (hfam : ∀ g x, ∃ y, (A x).map (ρ g : M →ₗ[R] M) = A y)
    (hW : ∀ g, W.map (ρ g : M →ₗ[R] M) = W) (g : G) :
    (sumInter A W).map (ρ g : M →ₗ[R] M) = sumInter A W := by
  have h1 : ∀ h : G, (sumInter A W).map (ρ h : M →ₗ[R] M) ≤ sumInter A W := fun h =>
    sumInter_map_le A W (Submodule.orderIsoMapComap (ρ h)) (fun x => hfam h x) (hW h)
  refine le_antisymm (h1 g) ?_
  calc sumInter A W = ((sumInter A W).map (ρ g⁻¹ : M →ₗ[R] M)).map (ρ g : M →ₗ[R] M) :=
        (map_map_inv ρ g _).symm
    _ ≤ (sumInter A W).map (ρ g : M →ₗ[R] M) := Submodule.map_mono (h1 g⁻¹)

/-- **Part B, module form.** Under the descent property, `D = sumInter A W` is a finite sum of
finite nonempty
intersections of members, `d D (A x) ≤ r` and `d (A x) D ≤ r * Kr r` for every `x`. -/
theorem partB (A : ι → Submodule R M) (W : Submodule R M) (r : ℕ)
    (hA : ∀ x y, d (A x) (A y) ≤ r) (hWA : ∀ x, d W (A x) ≤ r)
    (hAW : ∀ x, d (A x) W ≤ ((r * (r + 1) : ℕ) : ℕ∞)) (hdesc : Descent A W r (r * (r + 1))) :
    (∃ F : Finset (Finset ι), (Nonempty ι → F.Nonempty) ∧ (∀ T ∈ F, T.Nonempty ∧ inter A T ≤ W) ∧
        sumInter A W = ⨆ T ∈ F, inter A T) ∧
      (∀ x, d (sumInter A W) (A x) ≤ r) ∧ (∀ x, d (A x) (sumInter A W) ≤ ((r * Kr r : ℕ) : ℕ∞))
          := by
  classical
  have hcost : ∀ x, ∃ T : Finset ι, x ∈ T ∧ inter A T ≤ W ∧ d (A x) (inter A T) ≤ ((r * Kr r : ℕ)
      : ℕ∞) := by
    intro x
    obtain ⟨T, hxT, hTW, hc⟩ :=
      exists_inter_le (pot_mono r) (fun n m h1 h2 h3 => pot_step h1 h2 h3) hA hAW hdesc x
    refine ⟨T, hxT, hTW, hc.trans (le_of_eq ?_)⟩
    rw [pot_top]
  refine ⟨?_, fun x => (d_mono_left (sumInter_le A W)).trans (hWA x), fun x => ?_⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨x⟩⟩
    · refine ⟨∅, fun h => (not_isEmpty_of_nonempty ι hι).elim, fun T hT => by simp at hT,
        le_antisymm (iSup₂_le fun T hT => ?_) (iSup₂_le fun T hT => ?_)⟩
      · obtain ⟨y, -⟩ := hT.1
        exact isEmptyElim y
      · simp at hT
    · obtain ⟨T, hxT, hTW, hc⟩ := hcost x
      have hel : Eligible A W T := ⟨⟨x, hxT⟩, hTW⟩
      have hb : d W (inter A T) ≤ ((r + r * Kr r : ℕ) : ℕ∞) := by
        calc d W (inter A T) ≤ d W (A x) + d (A x) (inter A T) := d_triangle _ _ _
          _ ≤ (r : ℕ∞) + ((r * Kr r : ℕ) : ℕ∞) := add_le_add (hWA x) hc
          _ = ((r + r * Kr r : ℕ) : ℕ∞) := by push_cast; ring
      obtain ⟨F, hTF, hF, hD⟩ := sumInter_eq_finite hel (ne_top_of_le_ne_top (ENat.natCast_ne_top
          _) hb)
      exact ⟨F, fun _ => ⟨T, hTF⟩, hF, hD⟩
  · obtain ⟨T, hxT, hTW, hc⟩ := hcost x
    exact (d_anti_right (le_sumInter ⟨⟨x, hxT⟩, hTW⟩)).trans hc

/-- **Inequality (1) of Section 2 implies the descent property.** Weights `w` on a finite set `s`
with sum `1`, a level
`t ≥ r/(r+1)` and an error `τ` with `(r+1)(t B + τ) < r B + 1` (condition (3) of the source with
`B = r (r+1)`), and the
first-order inequality `∑_y w_y dim(π A_y ∩ E) ≤ t dim E + τ` for every `E ⊇ W` of finite
dimension over `W`. -/
theorem descent_of_first_order {A : ι → Submodule R M} {W : Submodule R M} {r B : ℕ}
    (s : Finset ι) (w : ι → ℝ) (hw0 : ∀ y ∈ s, 0 ≤ w y) (hw1 : ∑ y ∈ s, w y = 1) (t τ : ℝ)
    (ht : (r : ℝ) ≤ (r + 1) * t) (htτ : (r + 1) * (t * B + τ) < r * B + 1)
    (h1 : ∀ E : Submodule R M, W ≤ E → d E W ≠ ⊤ →
      ∑ y ∈ s, w y * ((d (A y ⊓ E) W).toNat : ℝ) ≤ t * ((d E W).toNat : ℝ) + τ) :
    Descent A W r B := by
  intro L x n _ hn _ hnB
  have hEW : d (L ⊔ W) W = n := by rw [d_sup, hn]
  have hEfin : d (L ⊔ W) W ≠ ⊤ := by rw [hEW]; exact ENat.natCast_ne_top n
  have hsum := h1 (L ⊔ W) le_sup_right hEfin
  rw [hEW, ENat.toNat_natCast] at hsum
  have hs : s.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hw1]; exact one_ne_zero)
  obtain ⟨y, _, hymin⟩ := Finset.exists_min_image s (fun y => (d (A y ⊓ (L ⊔ W)) W).toNat) hs
  have hk : ((d (A y ⊓ (L ⊔ W)) W).toNat : ℝ) ≤ t * n + τ := by
    calc ((d (A y ⊓ (L ⊔ W)) W).toNat : ℝ) = ∑ z ∈ s, w z * ((d (A y ⊓ (L ⊔ W)) W).toNat : ℝ) := by
          rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ ∑ z ∈ s, w z * ((d (A z ⊓ (L ⊔ W)) W).toNat : ℝ) := by
          refine Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_left ?_ (hw0 z hz)
          exact_mod_cast hymin z hz
      _ ≤ t * n + τ := hsum
  have hne : d (A y ⊓ (L ⊔ W)) W ≠ ⊤ := ne_top_of_le_ne_top hEfin (d_mono_left inf_le_right)
  obtain ⟨k, hkd⟩ := ENat.ne_top_iff_exists.mp hne
  have hkn : (d (A y ⊓ (L ⊔ W)) W).toNat = k := by rw [← hkd, ENat.toNat_natCast]
  rw [hkn] at hk
  have hreal : ((r : ℝ) + 1) * k < r * n + 1 := by
    have hnB' : (n : ℝ) ≤ B := by exact_mod_cast hnB
    have hr0 : (0 : ℝ) ≤ r + 1 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hnB'), mul_le_mul_of_nonneg_left hk
        hr0]
  have hnat : (r + 1) * k ≤ r * n := by
    have : (r + 1) * k < r * n + 1 := by exact_mod_cast hreal
    omega
  refine ⟨y, ?_⟩
  calc ((r + 1 : ℕ) : ℕ∞) * d (L ⊓ A y) W ≤ ((r + 1 : ℕ) : ℕ∞) * d (A y ⊓ (L ⊔ W)) W := by
        gcongr
        exact d_mono_left (le_inf inf_le_right (inf_le_left.trans le_sup_left))
    _ = (((r + 1) * k : ℕ) : ℕ∞) := by rw [← hkd]; push_cast; ring
    _ ≤ ((r * n : ℕ) : ℕ∞) := by exact_mod_cast hnat

/-- For `W ≤ E`: `dim(π A ∩ π E) = d((A + W) ∩ E, W) = d(A ∩ E, W)` (modular law). -/
theorem d_sup_inf_eq {A W E : Submodule R M} (hWE : W ≤ E) : d ((A ⊔ W) ⊓ E) W = d (A ⊓ E) W := by
  rw [sup_comm, sup_inf_assoc_of_le A hWE, sup_comm, d_sup]

/-- **The interface with part A** (`KPFamilies.kp_family_export`): inequality (1) of Section 2 in
the
form `∑_y w_y d((A_y ⊔ W) ⊓ E, W) ≤ t d(E, W) + τ`, with `r/(r+1) ≤ t` and `(t - r/(r+1)) r(r+1) +
τ < 1/(r+1)`
(condition (3) of the source), implies the descent property with `B = r (r+1)`. -/
theorem descent_of_export {A : ι → Submodule R M} {W : Submodule R M} {r : ℕ}
    (s : Finset ι) (w : ι → ℝ) (hw0 : ∀ y ∈ s, 0 ≤ w y) (hw1 : ∑ y ∈ s, w y = 1) (t τ : ℝ)
    (ht : (r : ℝ) / (r + 1) ≤ t) (htτ : (t - r / (r + 1)) * (r * (r + 1)) + τ < 1 / (r + 1))
    (h1 : ∀ E : Submodule R M, W ≤ E → d E W ≠ ⊤ →
      ∑ y ∈ s, w y * ((d ((A y ⊔ W) ⊓ E) W).toNat : ℝ) ≤ t * ((d E W).toNat : ℝ) + τ) :
    Descent A W r (r * (r + 1)) := by
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  have hne : (r : ℝ) + 1 ≠ 0 := hr1.ne'
  have e : ((r : ℝ) + 1) * (r / (r + 1)) = r := by field_simp
  have ht' : (r : ℝ) ≤ (r + 1) * t := by
    have h := mul_le_mul_of_nonneg_left ht hr1.le
    rwa [e] at h
  have htτ' : ((r : ℝ) + 1) * (t * ((r * (r + 1) : ℕ) : ℝ) + τ) < r * ((r * (r + 1) : ℕ) : ℝ)
      + 1 := by
    have h2 := mul_lt_mul_of_pos_left htτ hr1
    have e2 : ((r : ℝ) + 1) * (1 / (r + 1)) = 1 := by field_simp
    have e3 : ((r : ℝ) + 1) * ((t - r / (r + 1)) * (r * (r + 1)) + τ) =
        (r + 1) * (t * (r * (r + 1)) + τ) - r * (r * (r + 1)) := by
      field_simp
      ring
    rw [e2, e3] at h2
    push_cast
    linarith
  refine descent_of_first_order s w hw0 hw1 t τ ht' htτ' fun E hWE hfin => ?_
  have h := h1 E hWE hfin
  have hc : ∀ y ∈ s, w y * ((d ((A y ⊔ W) ⊓ E) W).toNat : ℝ) = w y * ((d (A y ⊓ E) W).toNat : ℝ) :=
    fun y _ => by rw [d_sup_inf_eq hWE]
  rwa [Finset.sum_congr rfl hc] at h

/-- **Invariance under a group acting by lattice automorphisms** (linear or semilinear actions),
which permutes the
members and fixes `W`. -/
theorem sumInter_fixed_of_lattice_group {G : Type*} [Group G] (ρ : G →* (Submodule R M ≃o
    Submodule R M))
    (A : ι → Submodule R M) (W : Submodule R M) (hfam : ∀ g x, ∃ y, ρ g (A x) = A y) (hW : ∀ g,
        ρ g W = W)
    (g : G) : ρ g (sumInter A W) = sumInter A W := by
  have h1 : ∀ h : G, ρ h (sumInter A W) ≤ sumInter A W := fun h => sumInter_map_le A W (ρ h)
      (hfam h) (hW h)
  refine le_antisymm (h1 g) ?_
  have e : ρ g (ρ g⁻¹ (sumInter A W)) = sumInter A W := by
    rw [← RelIso.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  calc sumInter A W = ρ g (ρ g⁻¹ (sumInter A W)) := e.symm
    _ ≤ ρ g (sumInter A W) := (ρ g).monotone (h1 g⁻¹)

end Family

section VectorSpace

/-- **KP Theorem A in its original form, from an invariant `W` with the descent property** (vector
spaces of any
dimension over a division ring, any group acting linearly, any family of members permuted by the
group).
Hypotheses on the family: `dim A_x / (A_x ∩ A_y) ≤ r`. Hypotheses on `W`: invariant, `dim W / (W ∩
A_x) ≤ r`,
`dim A_x / (A_x ∩ W) ≤ r (r+1)`, and the descent property. Conclusion: an invariant `D` that is a
finite sum of finite
nonempty intersections of members, with `dim D / (D ∩ A_x) ≤ r` and `dim A_x / (A_x ∩ D) ≤ r * Kr
r ≤ r² (r+1)`. -/
theorem kp_original_form_of_descent {K V G ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K
    V] [Group G]
    (ρ : G →* (V ≃ₗ[K] V)) (A : ι → Submodule K V)
    (hfam : ∀ g x, ∃ y, (A x).map (ρ g : V →ₗ[K] V) = A y) (r : ℕ)
    (hr : ∀ x y, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r)
    (W : Submodule K V) (hWinv : ∀ g, W.map (ρ g : V →ₗ[K] V) = W)
    (hWA : ∀ x, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r)
    (hAW : ∀ x, Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤ ((r * (r + 1) : ℕ) : Cardinal))
    (hdesc : ∀ (L : Submodule K V) (x : ι) (n : ℕ), L ≤ A x →
      Module.rank K (L ⧸ W.submoduleOf L) = n → 1 ≤ n → n ≤ r * (r + 1) →
      ∃ y, (r + 1) * Module.rank K ((L ⊓ A y : Submodule K V) ⧸ W.submoduleOf (L ⊓ A y))
          ≤ ((r * n : ℕ) : Cardinal)) :
    ∃ D : Submodule K V, (∀ g, D.map (ρ g : V →ₗ[K] V) = D) ∧
      (∃ F : Finset (Finset ι), (∀ T ∈ F, T.Nonempty) ∧ D = ⨆ T ∈ F, ⨅ y ∈ T, A y) ∧
      (∀ x, Module.rank K (D ⧸ (A x).submoduleOf D) ≤ r) ∧
      (∀ x, Module.rank K (A x ⧸ D.submoduleOf (A x)) ≤ ((r * Kr r : ℕ) : Cardinal)) := by
  classical
  have hA' : ∀ x y, d (A x) (A y) ≤ r := fun x y => (d_le_iff_rank _ _ r).mpr (hr x y)
  have hWA' : ∀ x, d W (A x) ≤ r := fun x => (d_le_iff_rank _ _ r).mpr (hWA x)
  have hAW' : ∀ x, d (A x) W ≤ ((r * (r + 1) : ℕ) : ℕ∞) := fun x => (d_le_iff_rank _ _ _).mpr (hAW
      x)
  have hdesc' : Descent A W r (r * (r + 1)) := by
    intro L x n hLx hn hn1 hnB
    have hrank : Module.rank K (L ⧸ W.submoduleOf L) = n := by
      have h := hn
      rw [d, Module.length_eq_rank] at h
      exact Cardinal.toENat_eq_natCast.mp h
    obtain ⟨y, hy⟩ := hdesc L x n hLx hrank hn1 hnB
    refine ⟨y, ?_⟩
    have hle : Module.rank K ((L ⊓ A y : Submodule K V) ⧸ W.submoduleOf (L ⊓ A y)) ≤ ((r * n : ℕ)
        : Cardinal) :=
      le_trans (le_mul_of_one_le_left zero_le (by exact_mod_cast Nat.succ_pos r)) hy
    have hfin : d (L ⊓ A y) W ≤ ((r * n : ℕ) : ℕ∞) := (d_le_iff_rank _ _ _).mpr hle
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hfin)
    have hmr : Module.rank K ((L ⊓ A y : Submodule K V) ⧸ W.submoduleOf (L ⊓ A y)) = m := by
      have h := hm.symm
      rw [d, Module.length_eq_rank] at h
      exact Cardinal.toENat_eq_natCast.mp h
    rw [hmr] at hy
    have hnat : (r + 1) * m ≤ r * n := by exact_mod_cast hy
    rw [← hm]
    exact_mod_cast hnat
  obtain ⟨⟨F, -, hF, hD⟩, hb1, hb2⟩ := partB A W r hA' hWA' hAW' hdesc'
  refine ⟨sumInter A W, sumInter_map_eq_of_group ρ A W hfam hWinv, ⟨F, fun T hT => (hF T hT).1, hD⟩,
    fun x => (d_le_iff_rank _ _ r).mp (hb1 x), fun x => (d_le_iff_rank _ _ _).mp (hb2 x)⟩

/-- **The conclusion of S2' (`KPFull.kp_family_finite_form_sharp` of
`Challenge/StatementFull.lean`) from part A's `W`.**
The hypotheses before `W` are those of S2' word for word. The hypotheses on `W` are what part A
exports
(`KPFamilies.kp_family_export`): invariance, the two bounds, and inequality (1) of Section 2 with
condition (3).
The conclusion is the conclusion of S2' word for word. -/
theorem kp_family_finite_form_sharp_of_W {K V G X : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V]
    [Group G] [MulAction G X] [Nonempty X] (ρ : G →* (V ≃ₗ[K] V)) (A : X → Submodule K V)
    (hA : ∀ (g : G) (x : X), A (g • x) = (A x).map (ρ g : V →ₗ[K] V)) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r)
    (W : Submodule K V) (hWinv : ∀ g : G, W.map (ρ g : V →ₗ[K] V) = W)
    (hWb : ∀ x, d W (A x) ≤ r ∧ d (A x) W ≤ ((r * (r + 1) : ℕ) : ℕ∞))
    (s : Finset X) (wt : X → ℝ) (t τ : ℝ) (hwt0 : ∀ y ∈ s, 0 ≤ wt y) (hwt1 : ∑ y ∈ s, wt y = 1)
    (ht : (r : ℝ) / (r + 1) ≤ t) (htτ : (t - r / (r + 1)) * (r * (r + 1)) + τ < 1 / (r + 1))
    (h1 : ∀ E, W ≤ E → d E W ≠ ⊤ →
      ∑ y ∈ s, wt y * ((d ((A y ⊔ W) ⊓ E) W).toNat : ℝ) ≤ t * ((d E W).toNat : ℝ) + τ) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤
          (r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ : ℕ) := by
  classical
  have hfam : ∀ g x, ∃ y, (A x).map (ρ g : V →ₗ[K] V) = A y := fun g x => ⟨g • x, (hA g x).symm⟩
  have hA' : ∀ x y, d (A x) (A y) ≤ r := fun x y => (d_le_iff_rank _ _ r).mpr (hr x y)
  have hdesc := descent_of_export s wt hwt0 hwt1 t τ ht htτ h1
  obtain ⟨⟨F, hFne, hF, hD⟩, hb1, hb2⟩ :=
    partB A W r hA' (fun x => (hWb x).1) (fun x => (hWb x).2) hdesc
  refine ⟨F, sumInter A W, hFne inferInstance, fun T hT => (hF T hT).1, hD,
    sumInter_map_eq_of_group ρ A W hfam hWinv, fun x => ⟨(d_le_iff_rank _ _ r).mp (hb1 x), ?_⟩⟩
  rw [← Kr_eq_ceil]
  exact (d_le_iff_rank _ _ _).mp (hb2 x)

/-- **The conclusion of S4 (`KPFull.kp_family_canonical`, canonical form) from a `W` that is fixed
by every lattice
automorphism permuting the members** (part A applied to the group of all such automorphisms), with
the bounds and
inequality (1) as exported by part A. The conclusion is the conclusion of S4 word for word. -/
theorem kp_family_canonical_of_W {K V X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Nonempty X]
    (A : X → Submodule K V) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r)
    (W : Submodule K V)
    (hWinv : ∀ φ : Submodule K V ≃o Submodule K V,
      (∀ x, ∃ y, φ (A x) = A y) → (∀ y, ∃ x, φ (A x) = A y) → φ W = W)
    (hWb : ∀ x, d W (A x) ≤ r ∧ d (A x) W ≤ ((r * (r + 1) : ℕ) : ℕ∞))
    (s : Finset X) (wt : X → ℝ) (t τ : ℝ) (hwt0 : ∀ y ∈ s, 0 ≤ wt y) (hwt1 : ∑ y ∈ s, wt y = 1)
    (ht : (r : ℝ) / (r + 1) ≤ t) (htτ : (t - r / (r + 1)) * (r * (r + 1)) + τ < 1 / (r + 1))
    (h1 : ∀ E, W ≤ E → d E W ≠ ⊤ →
      ∑ y ∈ s, wt y * ((d ((A y ⊔ W) ⊓ E) W).toNat : ℝ) ≤ t * ((d E W).toNat : ℝ) + τ) :
    ∃ (S : Finset (Finset X)) (W : Submodule K V),
      S.Nonempty ∧ (∀ s ∈ S, s.Nonempty) ∧ W = (⨆ s ∈ S, ⨅ x ∈ s, A x) ∧
      (∀ φ : Submodule K V ≃o Submodule K V,
        (∀ x, ∃ y, φ (A x) = A y) → (∀ y, ∃ x, φ (A x) = A y) → φ W = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤
          (r * ∑ j ∈ Finset.Icc 1 r, ⌈((r : ℚ) + 1) / (j : ℚ)⌉₊ : ℕ) := by
  classical
  have hA' : ∀ x y, d (A x) (A y) ≤ r := fun x y => (d_le_iff_rank _ _ r).mpr (hr x y)
  have hdesc := descent_of_export s wt hwt0 hwt1 t τ ht htτ h1
  obtain ⟨⟨F, hFne, hF, hD⟩, hb1, hb2⟩ :=
    partB A W r hA' (fun x => (hWb x).1) (fun x => (hWb x).2) hdesc
  refine ⟨F, sumInter A W, hFne inferInstance, fun T hT => (hF T hT).1, hD, fun φ hφ1 hφ2 => ?_,
    fun x => ⟨(d_le_iff_rank _ _ r).mp (hb1 x), ?_⟩⟩
  · refine sumInter_map_eq A W φ hφ1 (fun x => ?_) (hWinv φ hφ1 hφ2)
    obtain ⟨x', hx'⟩ := hφ2 x
    exact ⟨x', φ.symm_apply_eq.mpr hx'.symm⟩
  · rw [← Kr_eq_ceil]
    exact (d_le_iff_rank _ _ _).mp (hb2 x)

end VectorSpace

end KPFull.PartB
