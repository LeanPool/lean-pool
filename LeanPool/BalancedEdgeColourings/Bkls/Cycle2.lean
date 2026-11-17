/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Cycle

/-!
# Colouring one cycle, indexed by `ℕ` (Balister–Kostochka–Li–Schelp 2004, Lemma 3)

The cycle has vertices `0, …, r - 1` and edges `h 0, …, h (r - 1)` (edge `i` joins `i` and
`i + 1`, edge `r - 1` joins `r - 1` and `0`); vertex `i` sees `cset r h i`.

* `natCaseA`: vertex `0` is not internally matched and a colour `a` exists with `a ∉ F₀` and
  `a ∈ F_{r-1}`: colour edge `0` with `a`, then the path `1, …, r - 1` by `path_fixed`.
* `natCaseC`: every vertex is internally matched, `0 ~ l` with `l` the least distance of a matched
  pair: colour edges `0, …, l - 1` by the fixed pattern `pre l` (`0, …, 1`, so that `0` sees colour
  `0` and `l` sees `{1, 2}`), edge `l` with `2`, then the path `l + 1, …, r - 1`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

/-- The colour set of vertex `i` of the cycle `0, …, r - 1`. -/
def cset (r : ℕ) (h : ℕ → Fin 3) (i : ℕ) : Finset (Fin 3) :=
  if i = 0 then {h (r - 1), h 0} else pset h i

/-- The cycle conditions. -/
def NatGood (r : ℕ) (ns : ℕ → PState) (h : ℕ → Fin 3) : Prop :=
  (∀ i, i + 1 < r → h i ≠ h (i + 1)) ∧ h (r - 1) ≠ h 0 ∧
    (∀ i F, i < r → ns i = .ext F → cset r h i ≠ F) ∧
    (∀ i j, i < r → ns i = .int j → cset r h i ≠ cset r h j)

/-- A symmetric internal matching on the cycle without loops or adjacent pairs. -/
def NatSym (r : ℕ) (ns : ℕ → PState) : Prop :=
  ∀ i j, i < r → ns i = .int j → ns j = .int i ∧ j < r ∧ j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧
    ¬ (i = 0 ∧ j = r - 1) ∧ ¬ (j = 0 ∧ i = r - 1)

theorem natCaseA (r : ℕ) (hr : 3 ≤ r) (ns : ℕ → PState) (hsym : NatSym r ns)
    (h0 : ∀ j, ns 0 ≠ .int j) (a : Fin 3) (ha0 : ∀ F, ns 0 = .ext F → a ∉ F)
    (har : ∀ F, ns (r - 1) = .ext F → a ∈ F) : ∃ h, NatGood r ns h := by
  obtain ⟨g, hg0, hprop, hgn, hext, hint⟩ := path_fixed (r - 1) (by omega) a a ns
    (fun i j hi1 hin hj => by
      obtain ⟨h1, h2, h3, -⟩ := hsym i j (by omega) hj
      refine ⟨h1, h3, ?_, by omega⟩
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · rw [hj0] at h1; exact absurd h1 (h0 i)
      · exact hj0)
    har
    (fun s hs => by
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hsym (r - 1) s (by omega) hs
      have : s ≠ 0 := fun e => by rw [e] at h1; exact h0 _ h1
      omega)
  refine ⟨g, fun i hi => hprop i (by omega), by rw [hg0]; exact hgn, fun i F hi hF => ?_,
    fun i j hi hj => ?_⟩
  · unfold cset
    split_ifs with hi0
    · rw [hi0] at hF
      intro e
      have : a ∈ ({g (r - 1), g 0} : Finset (Fin 3)) := by rw [hg0]; simp
      rw [e] at this; exact ha0 F hF this
    · exact hext i F (by omega) (by omega) hF
  · have hi0 : i ≠ 0 := by rintro rfl; exact h0 j hj
    obtain ⟨h1, h2, h3, -⟩ := hsym i j hi hj
    have hj0 : j ≠ 0 := by rintro rfl; exact h0 i h1
    unfold cset; rw [ite_eq_right hi0, ite_eq_right hj0]
    exact hint i j (by omega) (by omega) hj

/-- The colours of the edges `0, …, l - 1` in `natCaseC`. -/
def pre (l k : ℕ) : Fin 3 :=
  if l = 3 then (if k = 0 then 0 else if k = 1 then 2 else 1)
  else if k + 1 = l then 1 else if k = 0 ∨ k + 2 = l then 0 else if k % 2 = 1 then 2 else 1

theorem pre_zero {l : ℕ} (hl : 2 ≤ l) : pre l 0 = 0 := by
  unfold pre; split_ifs <;> omega

theorem pre_last {l : ℕ} (hl : 2 ≤ l) : pre l (l - 1) = 1 := by
  unfold pre; split_ifs <;> omega

theorem pre_prev {l : ℕ} (hl : 2 ≤ l) (h3 : l ≠ 3) : pre l (l - 2) = 0 := by
  unfold pre; split_ifs <;> omega

theorem pre_prop {l : ℕ} (k : ℕ) (hk : k + 1 < l) : pre l k ≠ pre l (k + 1) := by
  unfold pre
  split_ifs <;> (try simp only [false_or, not_false_eq_true] at *) <;> first | decide | omega

/-- The state of a path vertex in `natCaseC`: partners among `0, …, l` become restrictions. -/
def cst (l : ℕ) (p : ℕ → Fin 3) : PState → PState
  | .free => .free
  | .ext F => .ext F
  | .int j => if l < j then .int (j - l) else .ext (pset p j)

theorem cst_of_lt {l : ℕ} {p : ℕ → Fin 3} {k : ℕ} (h : l < k) :
    cst l p (.int k) = .int (k - l) := by
  simp only [cst, ite_eq_left h]

theorem cst_of_le {l : ℕ} {p : ℕ → Fin 3} {k : ℕ} (h : ¬ l < k) :
    cst l p (.int k) = .ext (pset p k) := by
  simp only [cst, ite_eq_right h]

theorem cst_int {l : ℕ} {p : ℕ → Fin 3} {s : PState} {j : ℕ} (h : cst l p s = .int j) :
    ∃ k, s = .int k ∧ l < k ∧ j = k - l := by
  cases s with
  | free => cases h
  | ext F => cases h
  | int k =>
    by_cases hk : l < k
    · rw [cst_of_lt hk] at h; exact ⟨k, rfl, hk, (PState.int.inj h).symm⟩
    · rw [cst_of_le hk] at h; cases h

theorem cst_ext {l : ℕ} {p : ℕ → Fin 3} {s : PState} {F : Finset (Fin 3)}
    (h : cst l p s = .ext F) : s = .ext F ∨ ∃ k, s = .int k ∧ ¬ l < k ∧ F = pset p k := by
  cases s with
  | free => cases h
  | ext F' => left; simp only [cst] at h; rw [h]
  | int k =>
    by_cases hk : l < k
    · rw [cst_of_lt hk] at h; cases h
    · rw [cst_of_le hk] at h; exact Or.inr ⟨k, rfl, hk, (PState.ext.inj h).symm⟩

theorem natCaseC (r l : ℕ) (ns : ℕ → PState) (hsym : NatSym r ns)
    (hnoext : ∀ i F, i < r → ns i ≠ .ext F) (hl : 2 ≤ l) (hlr : l + 2 ≤ r)
    (h0 : ns 0 = .int l)
    (hmin : ∀ i j, i < r → ns i = .int j → i < j → l ≤ j - i ∧ l ≤ r - (j - i))
    (h3 : ns (l - 1) = .int (r - 1) → l ≠ 3) : ∃ h, NatGood r ns h := by
  have hl0 : ns l = .int 0 := (hsym 0 l (by omega) h0).1
  have hfar : ∀ i j, 1 ≤ i → i < l → ns i = .int j → l < j := by
    intro i j hi1 hil hj
    obtain ⟨h1, h2, h3', -⟩ := hsym i j (by omega) hj
    have hj0 : j ≠ 0 := by
      rintro rfl; rw [h0] at h1; have := PState.int.inj h1; omega
    have hjl : j ≠ l := by
      rintro rfl; rw [hl0] at h1; have := PState.int.inj h1; omega
    by_contra hc
    rcases Nat.lt_or_ge i j with hij | hij
    · have := (hmin i j (by omega) hj hij).1; omega
    · have := (hmin j i (by omega) h1 (by omega)).1; omega
  have hnl : l + (r - 1 - l) = r - 1 := by omega
  obtain ⟨g, hg0, hprop, hgn, hext, hint⟩ :=
    path_fixed (r - 1 - l) (by omega) 2 0 (fun i => cst l (pre l) (ns (l + i)))
    (fun i j hi1 hin hj => by
      obtain ⟨k, hk, hlk, rfl⟩ := cst_int hj
      obtain ⟨h1, h2, h3', -⟩ := hsym (l + i) k (by omega) hk
      refine ⟨?_, by omega, by omega, by omega⟩
      show cst l (pre l) (ns (l + (k - l))) = _
      rw [show l + (k - l) = k by omega, h1, cst_of_lt (by omega : l < l + i),
        show l + i - l = i by omega])
    (fun F hF => by
      rcases cst_ext hF with hF' | ⟨k, hk, hlk, rfl⟩
      · exact absurd hF' (hnoext _ _ (by omega))
      · rw [hnl] at hk
        obtain ⟨h1, h2, h3', h4, h5, h6, h7⟩ := hsym (r - 1) k (by omega) hk
        have hk0 : k ≠ 0 := by
          rintro rfl; rw [h0] at h1; have := PState.int.inj h1; omega
        have hkl : k ≠ l := by
          rintro rfl; rw [hl0] at h1; have := PState.int.inj h1; omega
        have hkm := (hmin k (r - 1) (by omega) h1 (by omega)).2
        have hk' : k = l - 1 := by omega
        subst hk'
        have hl3 := h3 h1
        unfold pset
        rw [show l - 1 - 1 = l - 2 by omega, pre_prev hl hl3]
        simp)
    (fun s hs => by
      obtain ⟨k, hk, hlk, rfl⟩ := cst_int hs
      rw [hnl] at hk
      obtain ⟨h1, h2, h3', h4, h5, -⟩ := hsym (r - 1) k (by omega) hk
      omega)
  let h : ℕ → Fin 3 := fun i => if i < l then pre l i else g (i - l)
  have hlt : ∀ i, i < l → h i = pre l i := fun i hi => ite_eq_left hi
  have hge : ∀ i, l ≤ i → h i = g (i - l) := fun i hi => ite_eq_right (by omega)
  have hc0 : cset r h 0 = {g (r - 1 - l), 0} := by
    unfold cset; rw [ite_eq_left rfl, hge (r - 1) (by omega), hlt 0 (by omega), pre_zero hl]
  have hcl : cset r h l = {1, 2} := by
    unfold cset pset
    rw [ite_eq_right (by omega), hlt (l - 1) (by omega), hge l le_rfl, pre_last hl,
        Nat.sub_self, hg0]
  have hcpre : ∀ i, 1 ≤ i → i < l → cset r h i = pset (pre l) i := by
    intro i hi1 hil
    unfold cset pset
    rw [ite_eq_right (by omega), hlt (i - 1) (by omega), hlt i hil]
  have hcpath : ∀ i, l < i → cset r h i = pset g (i - l) := by
    intro i hli
    unfold cset pset
    rw [ite_eq_right (by omega), hge (i - 1) (by omega), hge i (by omega),
      show i - 1 - l = i - l - 1 by omega]
  have hsep : cset r h 0 ≠ cset r h l := by
    rw [hc0, hcl]
    intro e
    have : (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by rw [← e]; simp
    simp at this
  refine ⟨h, fun i hi => ?_, ?_, fun i F hi hF => absurd hF (hnoext i F hi), fun i j hi hj => ?_⟩
  · rcases Nat.lt_or_ge (i + 1) l with hil | hil
    · rw [hlt i (by omega), hlt (i + 1) hil]; exact pre_prop i hil
    · rcases Nat.eq_or_lt_of_le hil with hil | hil
      · rw [hlt i (by omega), ← hil, hge l le_rfl, Nat.sub_self, hg0,
          show i = l - 1 by omega, pre_last hl]
        decide
      · rw [hge i (by omega), hge (i + 1) (by omega), show i + 1 - l = i - l + 1 by omega]
        exact hprop (i - l) (by omega)
  · rw [hge (r - 1) (by omega), hlt 0 (by omega), pre_zero hl]; exact hgn
  · obtain ⟨h1, h2, h3', -⟩ := hsym i j hi hj
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · rw [hi0, h0] at hj
      rw [hi0, ← PState.int.inj hj]; exact hsep
    rcases Nat.lt_trichotomy i l with hil | hil | hil
    · -- `i` in the prefix, `j` on the path
      have hlj := hfar i j hi0 hil hj
      rw [hcpre i hi0 hil, hcpath j hlj]
      have hpj : (fun i => cst l (pre l) (ns (l + i))) (j - l) = .ext (pset (pre l) i) := by
        change cst l (pre l) (ns (l + (j - l))) = _
        rw [show l + (j - l) = j by omega, h1, cst_of_le (by omega)]
      exact fun e => hext (j - l) _ (by omega) (by omega) hpj e.symm
    · rw [hil, hl0] at hj
      rw [hil, ← PState.int.inj hj]; exact fun e => hsep e.symm
    · -- `i` on the path
      have hj0 : j ≠ 0 := by
        rintro rfl; rw [h0] at h1; have := PState.int.inj h1; omega
      have hjl : j ≠ l := by
        rintro rfl; rw [hl0] at h1; have := PState.int.inj h1; omega
      rw [hcpath i hil]
      rcases Nat.lt_or_ge l j with hlj | hlj
      · rw [hcpath j hlj]
        have hpi : (fun i => cst l (pre l) (ns (l + i))) (i - l) = .int (j - l) := by
          change cst l (pre l) (ns (l + (i - l))) = _
          rw [show l + (i - l) = i by omega, hj, cst_of_lt hlj]
        exact hint (i - l) (j - l) (by omega) (by omega) hpi
      · rw [hcpre j (by omega) (by omega)]
        have hpi : (fun i => cst l (pre l) (ns (l + i))) (i - l) = .ext (pset (pre l) j) := by
          change cst l (pre l) (ns (l + (i - l))) = _
          rw [show l + (i - l) = i by omega, hj, cst_of_le (by omega)]
        exact hext (i - l) _ (by omega) (by omega) hpi

end Bkls

end LeanPool.BalancedEdgeColourings
