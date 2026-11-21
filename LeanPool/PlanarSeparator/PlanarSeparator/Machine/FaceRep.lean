/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Front

/-!
# The separator program: a representative dart on every face

The faces of the input map are the cycles of the face permutation `φ i = ro (rv i)`. The program
`frep` scans the darts `d = 0, 1, …, m - 1`; when `d` has no representative yet, it walks
around the face of `d` and gives each of its darts the representative `d` (stored as `d + 1` at
`11 m + i`). Every dart gets the smallest dart of its face (`frepF`), within `22 m + 2` steps.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The program -/

/-- One step around the face: `FR e := d + 1`, `e := φ e`, `r91 := [e = d]`. -/
def tBody : Stmt :=
  .seq (block [.addN 69 110 89, .storeN 69 90, .addN 70 89 89, .addN 70 70 89, .addN 70 70 107,
    .addN 70 70 101, .readIn 92 70, .addN 70 92 92, .addN 70 70 92, .addN 70 70 107,
    .addN 70 70 102, .readIn 89 70])
  (.ifLtN 89 87 .skip (.ifLtN 87 89 .skip (.instr (.copyN 91 101))))

/-- The walk around the face of `r87 = d`. -/
def trav : Stmt := .seq (block [.copyN 89 87, .addN 90 87 101,
  .copyN 91 100]) (.whileLtN 91 101 tBody)

/-- One dart `r87 = d`. -/
def fBody : Stmt :=
  .seq (block [.addN 69 110 87,
    .loadN 88 69]) (.seq (.ifLtN 88 101 trav .skip) (.instr (.addN 87 87 101)))

/-- **Face representatives.** -/
def frep : Stmt := .seq (.instr (.copyN 87 100)) (.whileLtN 87 105 fBody)

/-! ### Orbits of a numeric permutation -/

section orbit

variable {m : ℕ} {f : ℕ → ℕ}

/-- `j` lies on the cycle of `i`. -/
def Orb (f : ℕ → ℕ) (i j : ℕ) : Prop := ∃ k, f^[k] i = j

/-- A permutation of `[0, m)` all of whose points are periodic. -/
structure NPerm (m : ℕ) (f : ℕ → ℕ) : Prop where
  lt : ∀ i < m, f i < m
  inj : ∀ i < m, ∀ j < m, f i = f j → i = j
  per : ∀ i < m, ∃ p, 1 ≤ p ∧ f^[p] i = i

theorem iter_lt (h : NPerm m f) {i : ℕ} (hi : i < m) (k : ℕ) : f^[k] i < m := by
  induction k with
  | zero => exact hi
  | succ k ih => rw [Function.iterate_succ_apply']; exact h.lt _ ih

theorem iter_mul (h : ∀ i, f^[0] i = i) {p i : ℕ} (hp : f^[p] i = i) (s : ℕ) : f^[p * s] i = i := by
  induction s with
  | zero => exact h i
  | succ s ih => rw [Nat.mul_succ, Function.iterate_add_apply, hp, ih]

theorem Orb.refl (i : ℕ) : Orb f i i := ⟨0, rfl⟩

theorem Orb.trans {i j l : ℕ} (h1 : Orb f i j) (h2 : Orb f j l) : Orb f i l := by
  obtain ⟨a, rfl⟩ := h1; obtain ⟨b, rfl⟩ := h2
  exact ⟨b + a, Function.iterate_add_apply _ _ _ _⟩

theorem Orb.symm (h : NPerm m f) {i j : ℕ} (hi : i < m) (hij : Orb f i j) : Orb f j i := by
  obtain ⟨k, rfl⟩ := hij
  obtain ⟨p, hp1, hp⟩ := h.per i hi
  refine ⟨p * k - k, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k hp1)]
  exact iter_mul (fun _ => rfl) hp k

/-- The smallest dart of the cycle. -/
noncomputable def frepF (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  open Classical in Nat.find (⟨i, Orb.refl i⟩ : ∃ j, Orb f i j)

theorem frepF_orb (i : ℕ) : Orb f i (frepF f i) := by
  classical
  exact Nat.find_spec (⟨i, Orb.refl i⟩ : ∃ j, Orb f i j)

theorem frepF_le (i : ℕ) : frepF f i ≤ i := by
  classical
  exact Nat.find_min' (⟨i, Orb.refl i⟩ : ∃ j, Orb f i j) (Orb.refl i)

theorem frepF_eq (h : NPerm m f) {i j : ℕ} (hi : i < m) (hij : Orb f i j) :
    frepF f i = frepF f j := by
  classical
  have hj : j < m := by obtain ⟨k, rfl⟩ := hij; exact iter_lt h hi k
  have h1 : ∀ x, Orb f i x ↔ Orb f j x := fun x =>
    ⟨fun h' => (hij.symm h hi).trans h', fun h' => hij.trans h'⟩
  unfold frepF
  exact le_antisymm (Nat.find_min' _ ((h1 _).2 (Nat.find_spec (⟨j, Orb.refl j⟩ : ∃ x, Orb f j x))))
    (Nat.find_min' _ ((h1 _).1 (Nat.find_spec (⟨i, Orb.refl i⟩ : ∃ x, Orb f i x))))

/-- The first return to `d`. -/
noncomputable def per1 (h : NPerm m f) {d : ℕ} (hd : d < m) : ℕ :=
  open Classical in Nat.find (h.per d hd)

theorem per1_spec (h : NPerm m f) {d : ℕ} (hd : d < m) :
    1 ≤ per1 h hd ∧ f^[per1 h hd] d = d := by
  classical
  exact Nat.find_spec (h.per d hd)

theorem per1_min (h : NPerm m f) {d : ℕ} (hd : d < m) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < per1 h hd) :
    f^[k] d ≠ d := by
  classical
  exact fun e => Nat.find_min (h.per d hd) hk ⟨hk1, e⟩

theorem orb_lt_per (h : NPerm m f) {d x : ℕ} (hd : d < m) (hx : Orb f d x) :
    ∃ k < per1 h hd, f^[k] d = x := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨p1, hp⟩ := per1_spec h hd
  refine ⟨k % per1 h hd, Nat.mod_lt _ (by omega), ?_⟩
  conv_rhs => rw [← Nat.mod_add_div k (per1 h hd)]
  rw [Function.iterate_add_apply, iter_mul (fun _ => rfl) hp]

theorem iter_inj (h : NPerm m f) {i j : ℕ} (hi : i < m) (hj : j < m) (k : ℕ)
    (e : f^[k] i = f^[k] j) : i = j := by
  induction k generalizing i j with
  | zero => exact e
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at e
    exact h.inj i hi j hj (ih (h.lt i hi) (h.lt j hj) e)

open Classical in
theorem card_orb (h : NPerm m f) {d : ℕ} (hd : d < m) :
    #((range m).filter (fun x => Orb f d x)) = per1 h hd := by
  classical
  have : (range m).filter (fun x => Orb f d x) = (range (per1 h hd)).image (fun k => f^[k] d) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨-, hx⟩; obtain ⟨k, hk, e⟩ := orb_lt_per h hd hx; exact ⟨k, hk, e⟩
    · rintro ⟨k, -, rfl⟩; exact ⟨iter_lt h hd k, k, rfl⟩
  rw [this, card_image_of_injOn, card_range]
  intro a ha b hb e
  simp only [coe_range, Set.mem_Iio] at ha hb
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hab | hab
  · have e' : f^[a] (f^[b - a] d) = f^[a] d := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hab.le]; exact e.symm
    exact per1_min h hd (by omega) (by omega) (iter_inj h (iter_lt h hd _) hd a e')
  · have e' : f^[b] (f^[a - b] d) = f^[b] d := by
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hab.le]; exact e
    exact per1_min h hd (by omega) (by omega) (iter_inj h (iter_lt h hd _) hd b e')

/-- The darts whose representative is at least `i`. -/
noncomputable def cntU (m : ℕ) (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  #((range m).filter (fun x => i ≤ frepF f x))

theorem cntU_succ (h : NPerm m f) {i : ℕ} (hi : i < m) :
    cntU m f (i + 1) + (if frepF f i = i then per1 h hi else 0) = cntU m f i := by
  classical
  have hsplit : (range m).filter (fun x => i ≤ frepF f x) =
      (range m).filter (fun x => i + 1 ≤ frepF f x) ∪
        (range m).filter (fun x => frepF f x = i) := by
    ext x; simp only [mem_filter, mem_union, mem_range]; omega
  have hdisj : Disjoint ((range m).filter (fun x => i + 1 ≤ frepF f x))
      ((range m).filter (fun x => frepF f x = i)) :=
    disjoint_filter.2 fun x _ h1 h2 => by omega
  unfold cntU
  rw [hsplit, card_union_of_disjoint hdisj]
  congr 1
  split_ifs with hr
  · rw [← card_orb h hi]
    congr 1; ext x
    simp only [mem_filter, mem_range, and_congr_right_iff]
    intro hx
    constructor
    · intro hox; rw [← frepF_eq h hi hox, hr]
    · intro e; have := frepF_orb (f := f) x; rw [e] at this; exact this.symm h hx
  · symm; rw [card_eq_zero, filter_eq_empty_iff]
    intro x hx e
    have hox : Orb f x i := e ▸ frepF_orb x
    have := frepF_eq h (mem_range.1 hx) hox
    rw [e] at this
    exact hr this.symm

end orbit

section proofs

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 2 * n + 3 * m + 10 ≤ W) (hPW : ∀ j, P.data.getD j 0 ≤ W)
  (hf : NPerm m (ph rv ro))
include hN hIn hW hPW hf

open Classical in
omit hPW in
/-- **The walk around a face.** -/
theorem trav_exec {d : ℕ} (hd : d < m) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (h87 : c.nreg 87 = d) :
    ∃ c' k, Exec P W trav c c' k ∧ k ≤ 19 * per1 hf hd + 5 ∧ c'.output = c.output ∧
      (∀ r, (100 ≤ r ∨ r = 87) → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < 11 * m ∨ 12 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x < m, c'.nmem (11 * m + x) =
        if Orb (ph rv ro) d x then d + 1 else c.nmem (11 * m + x)) := by
  classical
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  set f := ph rv ro
  obtain ⟨hp1, hpd⟩ := per1_spec hf hd
  let I : ℕ → Config → Prop := fun k c' => WordsBounded W c' ∧ c'.output = c.output ∧
    (∀ r, (100 ≤ r ∨ r = 87) → c'.nreg r = c.nreg r) ∧ c'.nreg 89 = f^[k] d ∧
    c'.nreg 90 = d + 1 ∧ c'.nreg 91 = (if 1 ≤ k ∧ f^[k] d = d then 1 else 0) ∧ k ≤ per1 hf hd ∧
    (∀ a, (a < 11 * m ∨ 12 * m ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ x < m, c'.nmem (11 * m + x) =
      if (∃ k' < k, f^[k'] d = x) then d + 1 else c.nmem (11 * m + x))
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 89 87, .addN 90 87 101,
      .copyN 91 100]) c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 3 := by
    exec_block
    · config_simp; omega
    refine ⟨⟨‹_›, rfl, fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; rw [h87]; rfl, by config_simp; rw [h87, a1], by config_simp; simp [a0],
      by omega, fun a _ => rfl, fun x _ => by simp⟩, rfl⟩
  obtain ⟨k', c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ :=
    Exec.whileLtN_ghost (P := P) (W := W) (a := 91) (b := 101)
    (body := tBody) I (fun k _ => 19 * (per1 hf hd - k)) (fun k c' h => h.1)
    (fun k c' h hlt => by
      obtain ⟨hw, ho, hr, h89, h90, h91, hk, hfr, hm⟩ := h
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (Or.inl (by omega)), a1]
      have g87 : c'.nreg 87 = d := by rw [hr 87 (Or.inr rfl), h87]
      have g107 : c'.nreg 107 = 2 * n + 3 := by rw [hr 107 (Or.inl (by omega)), a7]
      have g102 : c'.nreg 102 = 2 := by rw [hr 102 (Or.inl (by omega)), a2]
      have g110 : c'.nreg 110 = 11 * m := by rw [hr 110 (Or.inl (by omega)), a10]
      rw [h91, g101] at hlt
      have hkl : k < per1 hf hd := by
        by_contra hc'
        have e1 : k = per1 hf hd := by omega
        have e2 : 1 ≤ k ∧ f^[k] d = d := ⟨by omega, by rw [e1]; exact hpd⟩
        rw [ite_eq_left e2] at hlt; omega
      generalize he : f^[k] d = e at h89
      have hem : e < m := he ▸ iter_lt hf hd k
      have hrv := hN.rv_lt _ hem
      have hro := hN.ro_lt _ hrv
      have r1 : P.data.getD (c'.nreg 89 + c'.nreg 89 + c'.nreg 89 + c'.nreg 107 + c'.nreg 101) 0 =
          rv e := by
        rw [h89, g107, g101, show e + e + e + (2 * n + 3) + 1 = 2 * n + 3 + 3 * e + 1 by omega]
        exact hIn.rv_eq _ hem
      have r2 : P.data.getD (rv e + rv e + rv e + c'.nreg 107 + c'.nreg 102) 0 = ro (rv e) := by
        rw [g107, g102, show rv e + rv e + rv e + (2 * n + 3) + 2 =
          2 * n + 3 + 3 * rv e + 2 by omega]
        exact hIn.ro_eq _ hrv
      have hfe : f^[k + 1] d = ro (rv e) := by
        rw [Function.iterate_succ_apply', he]; rfl
      unfold tBody
      refine ⟨k + 1, ?_⟩
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [r1, r2]); omega)
      rw [r1] at *
      rw [r2] at *
      have hmem : ∀ x < m, upd c'.nmem (c'.nreg 110 + c'.nreg 89) (c'.nreg 90) (11 * m + x) =
          if (∃ k' < k + 1, f^[k'] d = x) then d + 1 else c.nmem (11 * m + x) := by
        intro x hx
        rw [g110, h89, h90, upd_apply]
        by_cases hxe : x = e
        · rw [ite_eq_left (by omega), ite_eq_left ⟨k, by omega, by rw [he, hxe]⟩]
        · rw [ite_eq_right (by omega), hm x hx]
          congr 1; apply propext
          constructor
          · rintro ⟨k', hk', e'⟩; exact ⟨k', by omega, e'⟩
          · rintro ⟨k', hk', e'⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | rfl
            · exact ⟨k', h, e'⟩
            · exact absurd (e'.symm.trans he) hxe
      have hfr' : ∀ a, (a < 11 * m ∨ 12 * m ≤ a) →
          upd c'.nmem (c'.nreg 110 + c'.nreg 89) (c'.nreg 90) a = c.nmem a := by
        intro a ha; rw [upd_other _ _ _ (by rw [g110, h89]; omega)]; exact hfr a ha
      have h91z : c'.nreg 91 = 0 := by
        rw [h91]; split_ifs with hh
        · rw [ite_eq_left hh] at hlt; omega
        · rfl
      have hI' : ∀ c₃ : Config, WordsBounded W c₃ → c₃.output = c.output →
          (∀ r, (100 ≤ r ∨ r = 87) → c₃.nreg r = c.nreg r) → c₃.nreg 89 = ro (rv e) →
          c₃.nreg 90 = d + 1 → c₃.nreg 91 = (if ro (rv e) = d then 1 else 0) →
          c₃.nmem = upd c'.nmem (c'.nreg 110 + c'.nreg 89) (c'.nreg 90) → I (k + 1) c₃ := by
        intro c₃ w3 o3 r3 g89 g90 g91 m3
        refine ⟨w3, o3, r3, by rw [g89, hfe], g90, ?_, by omega,
          fun a ha => by rw [m3]; exact hfr' a ha,
          fun x hx => by rw [m3]; exact hmem x hx⟩
        rw [g91, hfe]
        by_cases hh : ro (rv e) = d
        · rw [ite_eq_left hh, ite_eq_left ⟨by omega, hh⟩]
        · rw [ite_eq_right hh, ite_eq_right (fun h' => hh h'.2)]
      have hkk : 19 * (per1 hf hd - (k + 1)) + 19 ≤ 19 * (per1 hf hd - k) := by omega
      rcases Nat.lt_trichotomy (ro (rv e)) d with hlt' | heq | hgt
      · refine spec_ifLtN_true (by config_simp; rw [g87]; exact hlt') ?_
        refine spec_skip ‹_› ⟨hI' _ ‹_› (by config_simp; exact ho) (fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr')
          (by config_simp) (by config_simp; exact h90)
          (by config_simp; rw [h91z, ite_eq_right (by omega)]) (by config_simp), by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [g87]; omega) ?_
        refine spec_ifLtN_false (by config_simp; rw [g87]; omega) ?_
        refine spec_instr (Exec.copyN ‹_› 91 101) fun hw' => ⟨hI' _ hw' (by config_simp; exact ho)
          (fun r hr' => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr')
          (by config_simp) (by config_simp; exact h90)
          (by config_simp; rw [g101, ite_eq_left heq]) (by config_simp), by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [g87]; omega) ?_
        refine spec_ifLtN_true (by config_simp; rw [g87]; exact hgt) ?_
        refine spec_skip ‹_› ⟨hI' _ ‹_› (by config_simp; exact ho) (fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr')
          (by config_simp) (by config_simp; exact h90)
          (by config_simp; rw [h91z, ite_eq_right (by omega)]) (by config_simp), by omega⟩) hI₁
  obtain ⟨hw₂, ho₂, hr₂, h89, h90, h91, hk, hfr, hm⟩ := hI₂
  have g101 : c₂.nreg 101 = 1 := by rw [hr₂ 101 (Or.inl (by omega)), a1]
  rw [h91, g101] at hn₂
  have hk' : k' = per1 hf hd := by
    split_ifs at hn₂ with hh
    · exact le_antisymm hk (Nat.find_min' _ hh)
    · omega
  subst hk'
  refine ⟨c₂, 3 + k₂, .seq e₁ e₂, by omega, ho₂, hr₂, hfr, fun x hx => ?_⟩
  rw [hm x hx]
  congr 1; apply propext
  exact ⟨fun ⟨k, hk, e⟩ => ⟨k, e⟩, fun h => orb_lt_per hf hd h⟩


omit hPW in
/-- **Face representatives.** -/
theorem frep_exec (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hz : ∀ x < m, c.nmem (11 * m + x) = 0) :
    ∃ c' k, Exec P W frep c c' k ∧ k ≤ 30 * m + 3 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, (a < 11 * m ∨ 12 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x < m, c'.nmem (11 * m + x) = frepF (ph rv ro) x + 1) := by
  classical
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  set f := ph rv ro
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ c'.output = c.output ∧
    (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 87 ≤ m ∧
    (∀ a, (a < 11 * m ∨ 12 * m ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ x < m, c'.nmem (11 * m + x) = if frepF f x < c'.nreg 87 then frepF f x + 1 else 0)
  have e₁ := Exec.copyN (P := P) hc 87 100
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 87)
    (b := 105) (body := fBody) I (fun c' => 11 * (m - c'.nreg 87) + 19 * cntU m f (c'.nreg 87))
    (fun c' h => h.1)
    (fun c' h hlt => by
      obtain ⟨hw, ho, hr, h87, hfr, hm⟩ := h
      have g105 : c'.nreg 105 = m := by rw [hr 105 (by omega), a5]
      have g110 : c'.nreg 110 = 11 * m := by rw [hr 110 (by omega), a10]
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega), a1]
      rw [g105] at hlt
      generalize hi : c'.nreg 87 = i at h87 hm hlt
      have hcu := cntU_succ hf hlt
      have hL' : Lay n m c' := Lay.of ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
        a14, a15, a16, a17, a18, a19, a20, a21⟩ fun r h1 _ => hr r h1
      have r1 : c'.nmem (c'.nreg 110 + c'.nreg 87) =
          if frepF f i < i then frepF f i + 1 else 0 := by
        rw [g110, hi]; exact hm i hlt
      unfold fBody
      refine spec_seq ?_
      exec_block
      · rw [g110, hi]; omega
      rw [r1] at *
      refine spec_seq ?_
      by_cases hfi : frepF f i < i
      · -- already done
        refine spec_ifLtN_false (by config_simp; rw [ite_eq_left hfi, g101]; omega) ?_
        refine spec_skip ‹_› ?_
        refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [hi, g101]; omega)) fun hw' => ?_
        refine ⟨⟨hw', by config_simp; exact ho, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
          by config_simp; rw [hi, g101]; omega, fun a ha => by config_simp; exact hfr a ha,
          fun x hx => ?_⟩, ?_⟩
        · config_simp; rw [hm x hx, hi, g101]
          by_cases hx' : frepF f x = i
          · exfalso
            have hox : Orb f x i := hx' ▸ frepF_orb x
            have := frepF_eq hf hx hox
            rw [hx'] at this; omega
          · split_ifs <;> first | rfl | omega
        · config_simp; rw [hi, g101, ← hcu, ite_eq_right (by omega)]; omega
      · -- a new face
        have hfi' : frepF f i = i := le_antisymm (frepF_le i) (by omega)
        refine spec_ifLtN_true (by config_simp; rw [ite_eq_right hfi, g101]; omega) ?_
        refine spec_use (trav_exec hN hIn hW hf hlt _ ‹_› (hL'.of fun r h1 _ => by
          config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by config_simp; exact hi)) ?_
        intro c₃ k₃ hk₃ hw₃ ⟨ho₃, hr₃, hfr₃, hm₃⟩
        config_simp at hr₃
        refine spec_instr (Exec.addN hw₃ _ _ _ (by
          rw [hr₃ 87 (Or.inr rfl), hr₃ 101 (Or.inl (by omega))]
          config_simp; rw [hi, g101]; omega)) fun hw' => ?_
        refine ⟨⟨hw', by config_simp; rw [ho₃]; exact ho, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs
          · omega
          · rw [hr₃ r (Or.inl hr')]
            simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
          by
            config_simp; rw [hr₃ 87 (Or.inr rfl), hr₃ 101 (Or.inl (by omega))]
            config_simp; rw [hi, g101]; omega,
          fun a ha => by config_simp; rw [hfr₃ a ha]; config_simp; exact hfr a ha, fun x hx => ?_⟩,
            ?_⟩
        · config_simp
          rw [hr₃ 87 (Or.inr rfl), hr₃ 101 (Or.inl (by omega))]; config_simp
          rw [hi, g101, hm₃ x hx]; config_simp; rw [hm x hx]
          by_cases hox : Orb f i x
          · have := frepF_eq hf hlt hox
            rw [ite_eq_left hox, ite_eq_left (by omega)]; omega
          · rw [ite_eq_right hox]
            have hne : frepF f x ≠ i := fun e => by
              have h1 : Orb f x i := e ▸ frepF_orb x
              exact hox (h1.symm hf hx)
            split_ifs <;> first | rfl | omega
        · config_simp
          rw [hr₃ 87 (Or.inr rfl), hr₃ 101 (Or.inl (by omega))]; config_simp
          rw [hi, g101, ← hcu, ite_eq_left hfi']; omega)
    ⟨e₁.wb_right, rfl, fun r hr => by simp only [upd_apply]; split_ifs <;> omega,
      by simp only [upd_apply, ↓reduceIte]; omega, fun a _ => rfl,
      fun x hx => by simp only [upd_apply, ↓reduceIte, a0, Nat.not_lt_zero]; exact hz x hx⟩
  obtain ⟨hw₂, ho₂, hr₂, h87, hfr₂, hm₂⟩ := hI₂
  have g105 : c₂.nreg 105 = m := by rw [hr₂ 105 (by omega), a5]
  rw [g105] at hn₂
  have hm87 : c₂.nreg 87 = m := by omega
  refine ⟨c₂, 1 + k₂, .seq e₁ e₂, ?_, ho₂, hr₂, hfr₂, fun x hx => ?_⟩
  · have : cntU m f 0 ≤ m := (card_le_card (filter_subset _ _)).trans (by simp)
    simp only [upd_apply, ↓reduceIte, a0] at hk₂
    omega
  · rw [hm₂ x hx, hm87, ite_eq_left (lt_of_le_of_lt (frepF_le x) hx)]

end proofs

end SepProg

end PlanarSeparator
