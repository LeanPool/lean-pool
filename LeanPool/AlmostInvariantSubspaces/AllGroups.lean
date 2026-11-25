/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Average
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Almost invariant elements of a lattice, for all groups

Idea of the proof: a probability measure on the group for which the minimum of the mean distance is
nearly maximal, and several weights `t`.
-/

@[expose] public section

namespace AlmostInvariant.AllGroups

open AlmostInvariant (avg avg_add avg_sub avg_mul avg_const avg_mono avg_sum avg_double)

variable {L G : Type*} [Lattice L] [Group G]

/-- Mean distance from `s` to the translates `σ i u`, with weight `t`. -/
noncomputable def f (act : G → L ≃o L) (rk : L → ℤ) (u : L) {ι : Type} [Fintype ι] (σ : ι → G)
    (t : ℝ) (s : L) : ℝ :=
  avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ s)) + t * ((rk s : ℝ) - rk u)

/-- The infimum of the mean distance. -/
noncomputable def a (act : G → L ≃o L) (rk : L → ℤ) (u : L) {ι : Type} [Fintype ι] (σ : ι → G)
    (t : ℝ) : ℝ :=
  ⨅ s, f act rk u σ t s

section basic
variable (act : G → L ≃o L) (hmul : ∀ g h x, act (g * h) x = act g (act h x))
  (rk : L → ℤ) (hstrict : StrictMono rk)
  (hmod : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y)
  (hinv : ∀ g x, rk (act g x) = rk x) (u : L)
  {ι : Type} [Fintype ι] [Nonempty ι] (σ : ι → G)

include hstrict hinv in
omit [Group G] in
theorem f_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (s : L) : 0 ≤ f act rk u σ t s := by
  have hm : Monotone rk := hstrict.monotone
  have h : ∀ i, -(t * ((rk s : ℝ) - rk u)) ≤ (rk u : ℝ) - rk (act (σ i) u ⊓ s) := by
    intro i
    have e1 : (rk (act (σ i) u ⊓ s) : ℝ) ≤ rk u := by
      have : rk (act (σ i) u ⊓ s) ≤ rk (act (σ i) u) := hm inf_le_left
      rw [hinv] at this
      exact_mod_cast this
    have e2 : (rk (act (σ i) u ⊓ s) : ℝ) ≤ rk s := by exact_mod_cast hm inf_le_right
    nlinarith
  have h2 := avg_mono h
  rw [avg_const] at h2
  unfold f
  linarith

include hstrict hinv in
omit [Group G] in
theorem f_bdd {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : BddBelow (Set.range (f act rk u σ t)) :=
  ⟨0, by rintro _ ⟨s, rfl⟩; exact f_nonneg act rk hstrict hinv u σ h0 h1 s⟩

include hstrict hinv in
omit [Group G] in
theorem a_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (s : L) : a act rk u σ t ≤ f act rk u σ t s :=
  ciInf_le (f_bdd act rk hstrict hinv u σ h0 h1) s

include hstrict hmod in
omit [Group G] [Nonempty ι] in
theorem f_sub (t : ℝ) (s s' : L) : f act rk u σ t (s ⊓ s') + f act rk u σ t (s ⊔ s') ≤
    f act rk u σ t s + f act rk u σ t s' := by
  have hm : Monotone rk := hstrict.monotone
  have h : ∀ i, ((rk u : ℝ) - rk (act (σ i) u ⊓ (s ⊓ s'))) + ((rk u : ℝ) - rk (act (σ i)
      u ⊓ (s ⊔ s'))) ≤
      ((rk u : ℝ) - rk (act (σ i) u ⊓ s)) + ((rk u : ℝ) - rk (act (σ i) u ⊓ s')) := by
    intro i
    set x := act (σ i) u
    have h1 := hmod (x ⊓ s) (x ⊓ s')
    have h2 : rk ((x ⊓ s) ⊔ (x ⊓ s')) ≤ rk (x ⊓ (s ⊔ s')) :=
      hm (sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right))
    have h3 : rk ((x ⊓ s) ⊓ (x ⊓ s')) ≤ rk (x ⊓ (s ⊓ s')) :=
      hm (le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
    have h5 : rk (x ⊓ s) + rk (x ⊓ s') ≤ rk (x ⊓ (s ⊔ s')) + rk (x ⊓ (s ⊓ s')) := by linarith
    have h6 : (rk (x ⊓ s) : ℝ) + rk (x ⊓ s') ≤ rk (x ⊓ (s ⊔ s')) + rk (x ⊓ (s ⊓ s')) := by
      exact_mod_cast h5
    linarith
  have h2 := avg_mono h
  rw [avg_add, avg_add] at h2
  have h4 : ((rk (s ⊔ s') : ℝ)) + rk (s ⊓ s') = rk s + rk s' := by exact_mod_cast hmod s s'
  have h5 : t * ((rk (s ⊔ s') : ℝ) - rk u) + t * ((rk (s ⊓ s') : ℝ) - rk u) =
      t * ((rk s : ℝ) - rk u) + t * ((rk s' : ℝ) - rk u) := by
    rw [← mul_add, ← mul_add]
    congr 1
    linarith
  unfold f
  linarith

include hmul hinv in
omit [Nonempty ι] in
theorem f_translate (t : ℝ) (g : G) (s : L) :
    f act rk u (fun i => g * σ i) t (act g s) = f act rk u σ t s := by
  unfold f
  rw [hinv]
  congr 1
  unfold avg
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : act (g * σ i) u ⊓ act g s = act g (act (σ i) u ⊓ s) := by rw [hmul, (act g).map_inf]
  dsimp only
  rw [this, hinv]

theorem f_double (t : ℝ) (g : G) (s : L) :
    f act rk u (Sum.elim σ (fun i => g * σ i)) t s =
      (f act rk u σ t s + f act rk u (fun i => g * σ i) t s) / 2 := by
  unfold f
  have : (fun i : ι ⊕ ι => (rk u : ℝ) - rk (act (Sum.elim σ (fun i => g * σ i) i) u ⊓ s)) =
      Sum.elim (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ s)) (fun i => (rk u : ℝ)
          - rk (act (g * σ i) u ⊓ s)) := by
    funext i
    cases i <;> rfl
  rw [this, avg_double]
  ring

include hmul in
theorem act_one (x : L) : act 1 x = x := by
  apply (act 1).injective
  rw [← hmul, one_mul]

include hmul in
theorem act_inv (g : G) (x : L) : act g (act g⁻¹ x) = x := by
  rw [← hmul, mul_inv_cancel, act_one act hmul]

include hmul hstrict hinv in
theorem a_translate {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (g : G) (s : L) :
    a act rk u σ t ≤ f act rk u (fun i => g * σ i) t s := by
  have h := f_translate act hmul rk hinv u σ t g (act g⁻¹ s)
  rw [act_inv act hmul] at h
  rw [h]
  exact a_le act rk hstrict hinv u σ h0 h1 _

include hmul hstrict hinv in
theorem a_double {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (g : G) :
    a act rk u σ t ≤ a act rk u (Sum.elim σ (fun i => g * σ i)) t := by
  have : Nonempty L := ⟨u⟩
  refine le_ciInf fun s => ?_
  rw [f_double]
  have e1 := a_le act rk hstrict hinv u σ h0 h1 s
  have e2 := a_translate act hmul rk hstrict hinv u σ h0 h1 g s
  linarith

include hinv in
omit [Group G] in
theorem a_le_r {t : ℝ} (hstrict : StrictMono rk) (h0 : 0 ≤ t) (h1 : t ≤ 1) (r : ℤ)
    (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) : a act rk u σ t ≤ r := by
  refine (a_le act rk hstrict hinv u σ h0 h1 u).trans ?_
  have h : ∀ i, (rk u : ℝ) - rk (act (σ i) u ⊓ u) ≤ r := fun i => by exact_mod_cast hr (σ i)
  have h2 := avg_mono h
  rw [avg_const] at h2
  unfold f
  linarith

include hmul hstrict hinv in
/-- Step 1: a near-minimizer for a doubled measure is a near-minimizer for `σ` and, after
translation, again. -/
theorem step_one {n : ℕ} (t : ℕ → ℝ) (ht0 : ∀ j, 0 ≤ t j) (ht1 : ∀ j, t j ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hsup : ∀ (κ : Type) [Fintype κ] [Nonempty κ] (τ : κ → G),
      ∑ j ∈ Finset.range n, a act rk u τ (t j) ≤ ∑ j ∈ Finset.range n, a act rk u σ (t j) + ε)
    {j : ℕ} (hj : j < n) (g : G) :
    ∃ s, f act rk u σ (t j) s ≤ a act rk u σ (t j) + 4 * ε ∧
      f act rk u σ (t j) (act g⁻¹ s) ≤ a act rk u σ (t j) + 4 * ε := by
  have : Nonempty L := ⟨u⟩
  set τ := Sum.elim σ (fun i => g * σ i)
  have hge : ∀ i, a act rk u σ (t i) ≤ a act rk u τ (t i) := fun i =>
    a_double act hmul rk hstrict hinv u σ (ht0 i) (ht1 i) g
  have h1 := hsup (ι ⊕ ι) τ
  have h2 : a act rk u τ (t j) - a act rk u σ (t j) ≤
      ∑ i ∈ Finset.range n, (a act rk u τ (t i) - a act rk u σ (t i)) :=
    Finset.single_le_sum (f := fun i => a act rk u τ (t i) - a act rk u σ (t i))
      (fun i _ => sub_nonneg.mpr (hge i)) (Finset.mem_range.mpr hj)
  rw [Finset.sum_sub_distrib] at h2
  have h3 : a act rk u τ (t j) ≤ a act rk u σ (t j) + ε := by linarith
  obtain ⟨s, hs⟩ := exists_lt_of_ciInf_lt (f := f act rk u τ (t j))
    (show a act rk u τ (t j) < a act rk u τ (t j) + ε by linarith)
  have hd := f_double act rk u σ (t j) g s
  have e1 := a_le act rk hstrict hinv u σ (ht0 j) (ht1 j) s
  have e2 := a_translate act hmul rk hstrict hinv u σ (ht0 j) (ht1 j) g s
  have e3 := f_translate act hmul rk hinv u σ (t j) g (act g⁻¹ s)
  rw [act_inv act hmul] at e3
  refine ⟨s, ?_, ?_⟩
  · have : f act rk u τ (t j) s = _ := hd
    linarith
  · rw [← e3]
    have : f act rk u τ (t j) s = _ := hd
    linarith

omit [Group G] [Nonempty ι] in
theorem f_level (t t' : ℝ) (s : L) :
    f act rk u σ t' s = f act rk u σ t s + (t' - t) * ((rk s : ℝ) - rk u) := by
  unfold f; ring

include hinv in
omit [Group G] in
theorem f_fixed (t : ℝ) (w : L) (hw : ∀ g, act g w = w) :
    f act rk u σ t w = (1 - t) * ((rk u : ℝ) - rk (w ⊓ u)) + t * ((rk w : ℝ) - rk (w ⊓ u)) := by
  have h : ∀ i, (rk u : ℝ) - rk (act (σ i) u ⊓ w) = (rk u : ℝ) - rk (w ⊓ u) := by
    intro i
    have : act (σ i) u ⊓ w = act (σ i) (u ⊓ w) := by rw [(act (σ i)).map_inf, hw]
    rw [this, hinv, inf_comm]
  unfold f
  rw [show (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ w)) = fun _ => (rk u : ℝ) - rk (w ⊓ u)
      from funext h,
    avg_const]
  ring

include hstrict hmod in
omit [Group G] [Nonempty ι] in
/-- The two near-minimal pairs at different levels are nested. -/
theorem chain {ti tj ε : ℝ} (hε : 0 ≤ ε) (hij : 16 * ε < tj - ti) (X Y : L)
    (hX : f act rk u σ ti X ≤ a act rk u σ ti + 8 * ε)
    (hY : f act rk u σ tj Y ≤ a act rk u σ tj + 8 * ε)
    (ai : ∀ s, a act rk u σ ti ≤ f act rk u σ ti s) (aj : ∀ s, a act rk u σ tj
        ≤ f act rk u σ tj s) :
    Y ≤ X := by
  have h1 := aj (X ⊓ Y)
  have h2 := ai (X ⊔ Y)
  have h3 := f_sub act rk hstrict hmod u σ ti X Y
  have l1 := f_level act rk u σ ti tj (X ⊓ Y)
  have l2 := f_level act rk u σ ti tj Y
  have hx : (0 : ℝ) ≤ (rk Y : ℝ) - rk (X ⊓ Y) := by
    have : rk (X ⊓ Y) ≤ rk Y := hstrict.monotone inf_le_right
    have : (rk (X ⊓ Y) : ℝ) ≤ rk Y := by exact_mod_cast this
    linarith
  have key : (tj - ti) * ((rk Y : ℝ) - rk (X ⊓ Y)) ≤ 16 * ε := by nlinarith
  have hlt : (rk Y : ℝ) - rk (X ⊓ Y) < 1 := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < tj - ti := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcon hpos.le]
  have hle : rk Y ≤ rk (X ⊓ Y) := by
    have : ((rk Y - rk (X ⊓ Y) : ℤ) : ℝ) < 1 := by push_cast; linarith
    have : rk Y - rk (X ⊓ Y) < 1 := by exact_mod_cast this
    omega
  by_contra hcon
  have : X ⊓ Y < Y := lt_of_le_of_ne inf_le_right (fun h => hcon (h ▸ inf_le_left))
  exact absurd (hstrict this) (not_lt.mpr hle)

include hstrict hmod in
theorem psi_mono (x y z w : L) (hzw : z ≤ w) :
    rk (x ⊓ z) - rk (x ⊓ y ⊓ z) ≤ rk (x ⊓ w) - rk (x ⊓ y ⊓ w) := by
  have hm := hstrict.monotone
  have h1 := hmod (x ⊓ z) (x ⊓ y ⊓ w)
  have h2 : rk ((x ⊓ z) ⊔ (x ⊓ y ⊓ w)) ≤ rk (x ⊓ w) :=
    hm (sup_le (inf_le_inf_left _ hzw) (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
  have h3 : (x ⊓ z) ⊓ (x ⊓ y ⊓ w) = x ⊓ y ⊓ z := by
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (inf_le_left.trans
        inf_le_right)))
        (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (le_inf inf_le_left (inf_le_right.trans hzw))
  rw [h3] at h1
  linarith

include hstrict hmod in
theorem psi_step (x y P Q : L) (hPQ : P ≤ Q) :
    rk (x ⊓ Q) - rk (x ⊓ P) - (rk (x ⊓ ((y ⊓ Q) ⊔ P)) - rk (x ⊓ P)) ≤
      (rk (x ⊓ Q) - rk (x ⊓ y ⊓ Q)) - (rk (x ⊓ P) - rk (x ⊓ y ⊓ P)) := by
  have hm := hstrict.monotone
  have h1 := hmod (x ⊓ y ⊓ Q) (x ⊓ P)
  have h2 : rk ((x ⊓ y ⊓ Q) ⊔ (x ⊓ P)) ≤ rk (x ⊓ ((y ⊓ Q) ⊔ P)) :=
    hm (sup_le (le_inf (inf_le_left.trans inf_le_left)
      (le_sup_of_le_left (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
      (inf_le_inf_left _ le_sup_right))
  have h3 : (x ⊓ y ⊓ Q) ⊓ (x ⊓ P) = x ⊓ y ⊓ P := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans hPQ)) (le_inf (inf_le_left.trans
        inf_le_left) inf_le_right)
  rw [h3] at h1
  linarith

include hmul hstrict hmod hinv in
theorem psi_le_r (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) (g h : G) (z : L) :
    rk (act g u ⊓ z) - rk (act g u ⊓ act h u ⊓ z) ≤ r := by
  have hm := hstrict.monotone
  set x := act g u
  set y := act h u
  have h1 := hmod (x ⊓ z) (x ⊓ y)
  have h2 : rk ((x ⊓ z) ⊔ (x ⊓ y)) ≤ rk x := hm (sup_le inf_le_left inf_le_left)
  have h3 : (x ⊓ z) ⊓ (x ⊓ y) = x ⊓ y ⊓ z := by
    rw [inf_comm (x ⊓ y) z, inf_comm x z, inf_assoc, ← inf_assoc x x y, inf_idem]
  rw [h3] at h1
  have h4 : rk x - rk (x ⊓ y) ≤ r := by
    have e : x ⊓ y = act g (u ⊓ act (g⁻¹ * h) u) := by
      rw [(act g).map_inf, hmul, act_inv act hmul]
    rw [e, hinv, hinv, inf_comm]
    exact hr _
  linarith

include hstrict in
theorem psi_nonneg (x y z : L) : 0 ≤ rk (x ⊓ z) - rk (x ⊓ y ⊓ z) := by
  have : rk (x ⊓ y ⊓ z) ≤ rk (x ⊓ z) := hstrict.monotone (inf_le_inf_right _ inf_le_left)
  linarith

include hstrict hmod in
/-- Telescoping along the chain `P (m) ≤ Q (m) ≤ P (m - 1) ≤ ...`. -/
theorem telescope (x y : L) (P Q : ℕ → L) (_hPQ : ∀ j, P j ≤ Q j) (hQP : ∀ j, Q (j + 1) ≤ P j)
    (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), ((rk (x ⊓ Q j) - rk (x ⊓ y ⊓ Q j)) - (rk (x ⊓ P j)
        - rk (x ⊓ y ⊓ P j))) ≤
      (rk (x ⊓ Q 0) - rk (x ⊓ y ⊓ Q 0)) - (rk (x ⊓ P m) - rk (x ⊓ y ⊓ P m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have := psi_mono rk hstrict hmod x y (Q (m + 1)) (P m) (hQP m)
    linarith

include hmul hstrict hmod hinv in
/-- The main step: some level has a unique near-minimizer, and it is invariant. -/
theorem exists_fixed_of_levels (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r)
    {n : ℕ} (hn : 0 < n) (t : ℕ → ℝ) (ht0 : ∀ j, 0 ≤ t j) (ht1 : ∀ j, t j ≤ 1)
    {ε κ : ℝ} (hε : 0 < ε) (hsep : ∀ i j, i < j → j < n → 16 * ε < t j - t i)
    (hκ : ∀ j, j < n → κ ≤ t j * (1 - t j)) (hbig : (r : ℝ) < n * (κ - 16 * ε))
    (hsup : ∀ (κ : Type) [Fintype κ] [Nonempty κ] (τ : κ → G),
      ∑ j ∈ Finset.range n, a act rk u τ (t j) ≤ ∑ j ∈ Finset.range n, a act rk u σ (t j) + ε) :
    ∃ j, j < n ∧ ∃ w, (∀ g, act g w = w) ∧
      (1 - t j) * ((rk u : ℝ) - rk (w ⊓ u)) + t j * ((rk w : ℝ) - rk (w ⊓ u)) ≤ a act rk u σ (t j)
          + 4 * ε := by
  classical
  have : Nonempty L := ⟨u⟩
  have aleq : ∀ j s, a act rk u σ (t j) ≤ f act rk u σ (t j) s := fun j s =>
    a_le act rk hstrict hinv u σ (ht0 j) (ht1 j) s
  by_contra hno
  push Not at hno
  -- at every level there are two different near-minimizers
  have two : ∀ j, j < n → ∃ S T, S ≠ T ∧ f act rk u σ (t j) S ≤ a act rk u σ (t j) + 4 * ε ∧
      f act rk u σ (t j) T ≤ a act rk u σ (t j) + 4 * ε := by
    intro j hj
    obtain ⟨s0, hs0⟩ := exists_lt_of_ciInf_lt (f := f act rk u σ (t j))
      (show a act rk u σ (t j) < a act rk u σ (t j) + 4 * ε by linarith)
    by_contra hcon
    push Not at hcon
    have hfix : ∀ g, act g s0 = s0 := by
      intro g
      obtain ⟨s1, h1, h2⟩ := step_one act hmul rk hstrict hinv u σ t ht0 ht1 hε hsup hj g⁻¹
      rw [inv_inv] at h2
      have e1 : s1 = s0 := by
        by_contra hne
        have := hcon s1 s0 hne h1
        linarith
      have e2 : act g s1 = s0 := by
        by_contra hne
        have := hcon _ s0 hne h2
        linarith
      rw [e1] at e2
      exact e2
    have hv := hno j hj s0 hfix
    rw [← f_fixed act rk hinv u σ (t j) s0 hfix] at hv
    linarith
  have two' : ∀ j, ∃ P Q : L, j < n → (P < Q ∧ f act rk u σ (t j) P ≤ a act rk u σ (t j) + 8 * ε ∧
      f act rk u σ (t j) Q ≤ a act rk u σ (t j) + 8 * ε) := by
    intro j
    by_cases hj : j < n
    · obtain ⟨S, T, hST, hS, hT⟩ := two j hj
      refine ⟨S ⊓ T, S ⊔ T, fun _ => ⟨?_, ?_, ?_⟩⟩
      · refine lt_of_le_of_ne (inf_le_left.trans le_sup_left) fun h => hST ?_
        have h1 : S ≤ T := by
          have : S ≤ S ⊓ T := by rw [h]; exact le_sup_left
          exact this.trans inf_le_right
        have h2 : T ≤ S := by
          have : T ≤ S ⊓ T := by rw [h]; exact le_sup_right
          exact this.trans inf_le_left
        exact le_antisymm h1 h2
      · have := f_sub act rk hstrict hmod u σ (t j) S T
        have := aleq j (S ⊔ T)
        linarith
      · have := f_sub act rk hstrict hmod u σ (t j) S T
        have := aleq j (S ⊓ T)
        linarith
    · exact ⟨u, u, fun h => absurd h hj⟩
  choose P Q hPQ using two'
  -- the chain
  have hle : ∀ j, j < n → P j ≤ Q j := fun j hj => (hPQ j hj).1.le
  have hQP : ∀ j, j + 1 < n → Q (j + 1) ≤ P j := fun j hj =>
    chain act rk hstrict hmod u σ hε.le (hsep j (j + 1) (Nat.lt_succ_self j) hj) (P j) (Q (j + 1))
      (hPQ j (by omega)).2.1 (hPQ (j + 1) hj).2.2 (aleq j) (aleq (j + 1))
  -- extend the chain beyond n by constants, to telescope
  set P' : ℕ → L := fun j => if j < n then P j else P (n - 1)
  set Q' : ℕ → L := fun j => if j < n then Q j else P (n - 1)
  have hPQ' : ∀ j, P' j ≤ Q' j := by
    intro j; simp only [P', Q']; split_ifs with h
    · exact hle j h
    · exact le_rfl
  have hQP' : ∀ j, Q' (j + 1) ≤ P' j := by
    intro j; simp only [P', Q']
    split_ifs with h1 h2 h2
    · exact hQP j h1
    · omega
    · have : j = n - 1 := by omega
      subst this; exact le_rfl
    · exact le_rfl
  -- numbers
  set d : ℕ → ι → ℝ := fun j i => (rk (act (σ i) u ⊓ Q j) : ℝ) - rk (act (σ i) u ⊓ P j)
  set c : ℕ → ι → ι → ℝ := fun j i k =>
    (rk (act (σ i) u ⊓ ((act (σ k) u ⊓ Q j) ⊔ P j)) : ℝ) - rk (act (σ i) u ⊓ P j)
  -- (1) for all i k the sum over the levels is at most r
  have hsum : ∀ i k, ∑ j ∈ Finset.range n, (d j i - c j i k) ≤ r := by
    intro i k
    have tel := telescope rk hstrict hmod (act (σ i) u) (act (σ k) u) P' Q' hPQ' hQP' (n - 1)
    rw [Nat.sub_add_cancel hn] at tel
    have hpr := psi_le_r act hmul rk hstrict hmod hinv u r hr (σ i) (σ k) (Q' 0)
    have hpn := psi_nonneg rk hstrict (act (σ i) u) (act (σ k) u) (P' (n - 1))
    have hterm : ∀ j ∈ Finset.range n, d j i - c j i k ≤
        (((rk (act (σ i) u ⊓ Q' j) - rk (act (σ i) u ⊓ act (σ k) u ⊓ Q' j)) -
          (rk (act (σ i) u ⊓ P' j) - rk (act (σ i) u ⊓ act (σ k) u ⊓ P' j)) : ℤ) : ℝ) := by
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      have e1 : P' j = P j := by simp [P', hj']
      have e2 : Q' j = Q j := by simp [Q', hj']
      rw [e1, e2]
      have := psi_step rk hstrict hmod (act (σ i) u) (act (σ k) u) (P j) (Q j) (hle j hj')
      simp only [d, c]
      push_cast
      have : ((rk (act (σ i) u ⊓ Q j) - rk (act (σ i) u ⊓ P j) -
          (rk (act (σ i) u ⊓ (act (σ k) u ⊓ Q j ⊔ P j)) - rk (act (σ i) u ⊓ P j)) : ℤ) : ℝ) ≤
          ((rk (act (σ i) u ⊓ Q j) - rk (act (σ i) u ⊓ act (σ k) u ⊓ Q j) -
          (rk (act (σ i) u ⊓ P j) - rk (act (σ i) u ⊓ act (σ k) u ⊓ P j)) : ℤ) : ℝ) := by
        exact_mod_cast this
      push_cast at this
      linarith
    have h1 := Finset.sum_le_sum hterm
    have h2 : (∑ j ∈ Finset.range n, (((rk (act (σ i) u ⊓ Q' j) - rk (act (σ i) u ⊓ act (σ k)
        u ⊓ Q' j)) -
          (rk (act (σ i) u ⊓ P' j) - rk (act (σ i) u ⊓ act (σ k) u ⊓ P' j)) : ℤ) : ℝ)) ≤ r := by
      rw [← Int.cast_sum]
      exact_mod_cast tel.trans (by linarith)
    linarith
  -- (2) for each level the double mean is at least κ - 16 ε
  have hlev : ∀ j, j < n → κ - 16 * ε ≤ avg (fun i => avg (fun k => d j i - c j i k)) := by
    intro j hj
    obtain ⟨hlt, hPn, hQn⟩ := hPQ j hj
    have aP := aleq j (P j)
    set tt := t j
    set nj : ℝ := (rk (Q j) : ℝ) - rk (P j)
    have hnj : 1 ≤ nj := by
      have : rk (P j) < rk (Q j) := hstrict hlt
      have : rk (P j) + 1 ≤ rk (Q j) := this
      have : (rk (P j) : ℝ) + 1 ≤ rk (Q j) := by exact_mod_cast this
      simp only [nj]; linarith
    -- f Q - f P = t n_j - mean d
    have eQP : f act rk u σ tt (Q j) - f act rk u σ tt (P j) = tt * nj - avg (d j) := by
      unfold f
      have : avg (d j) = avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ P j)) -
          avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ Q j)) := by
        rw [← avg_sub]; congr 1; funext i; simp only [d]; ring
      rw [this]; simp only [nj]; ring
    have hd_lo : tt * nj - 8 * ε ≤ avg (d j) := by linarith
    have hd_hi : avg (d j) ≤ tt * nj + 8 * ε := by
      have := aleq j (Q j); linarith
    -- for each k: mean over i of c ≤ t d_k + 8 ε
    have hc : ∀ k, avg (fun i => c j i k) ≤ tt * d j k + 8 * ε := by
      intro k
      set R := (act (σ k) u ⊓ Q j) ⊔ P j
      have aR := aleq j R
      have eR : f act rk u σ tt R - f act rk u σ tt (P j) = tt * ((rk R : ℝ) - rk (P j))
          - avg (fun i => c j i k) := by
        unfold f
        have : avg (fun i => c j i k) = avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ P j)) -
            avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ R)) := by
          rw [← avg_sub]; congr 1; funext i; simp only [c, R]; ring
        rw [this]; ring
      have hRP : (rk R : ℝ) - rk (P j) = d j k := by
        have h1 := hmod (act (σ k) u ⊓ Q j) (P j)
        have h2 : (act (σ k) u ⊓ Q j) ⊓ P j = act (σ k) u ⊓ P j := by
          rw [inf_assoc, inf_eq_right.mpr (hle j hj)]
        rw [h2] at h1
        simp only [d, R]
        have : ((rk (act (σ k) u ⊓ Q j ⊔ P j) + rk (act (σ k) u ⊓ P j) : ℤ) : ℝ) =
            ((rk (act (σ k) u ⊓ Q j) + rk (P j) : ℤ) : ℝ) := by rw [h1]
        push_cast at this
        linarith
      rw [hRP] at eR
      linarith
    have hcc : avg (fun i => avg (fun k => c j i k)) ≤ tt * avg (d j) + 8 * ε := by
      have swap : avg (fun i => avg (fun k => c j i k)) = avg (fun k => avg (fun i => c j i k))
          := by
        simp only [avg]
        rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]
      rw [swap]
      have := avg_mono hc
      rw [avg_add, avg_mul, avg_const] at this
      exact this
    have e : avg (fun i => avg (fun k => d j i - c j i k)) = avg (d j) - avg (fun i => avg (fun k
        => c j i k)) := by
      have : (fun i => avg (fun k => d j i - c j i k)) = fun i => d j i - avg (fun k => c j i k)
          := by
        funext i; rw [avg_sub, avg_const]
      rw [this, avg_sub]
    rw [e]
    have hk := hκ j hj
    have ht0' := ht0 j
    have ht1' := ht1 j
    have m1 := mul_le_mul_of_nonneg_left hd_lo (show (0 : ℝ) ≤ 1 - tt by linarith)
    have m2 := mul_le_mul_of_nonneg_left hnj (mul_nonneg ht0' (show (0 : ℝ) ≤ 1 - tt by linarith))
    have m3 := mul_nonneg hε.le ht0'
    nlinarith
  -- (3) combine
  have htot : avg (fun i => avg (fun k => ∑ j ∈ Finset.range n, (d j i - c j i k))) ≤ r := by
    have h1 : ∀ i, avg (fun k => ∑ j ∈ Finset.range n, (d j i - c j i k)) ≤ r := by
      intro i
      have := avg_mono (fun k => hsum i k)
      rwa [avg_const] at this
    have := avg_mono h1
    rwa [avg_const] at this
  have hswap : avg (fun i => avg (fun k => ∑ j ∈ Finset.range n, (d j i - c j i k))) =
      ∑ j ∈ Finset.range n, avg (fun i => avg (fun k => d j i - c j i k)) := by
    have : (fun i => avg (fun k => ∑ j ∈ Finset.range n, (d j i - c j i k))) =
        fun i => ∑ j ∈ Finset.range n, avg (fun k => d j i - c j i k) := by
      funext i; rw [avg_sum]
    rw [this, avg_sum]
  have hlow : (n : ℝ) * (κ - 16 * ε) ≤ ∑ j ∈ Finset.range n, avg (fun i => avg (fun k => d j i - c
      j i k)) := by
    have := Finset.sum_le_sum (s := Finset.range n) (fun j hj => hlev j (Finset.mem_range.mp hj))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  linarith

end basic

section final
variable (act : G → L ≃o L) (hmul : ∀ g h x, act (g * h) x = act g (act h x))
  (rk : L → ℤ) (hstrict : StrictMono rk)
  (hmod : ∀ x y, rk (x ⊔ y) + rk (x ⊓ y) = rk x + rk y)
  (hinv : ∀ g x, rk (act g x) = rk x) (u : L)

include hmul hstrict hmod hinv in
/-- **Weighted form for all groups.** For every interval `[lo, hi] ⊂ (0,1)` and `θ > 0` there are
a weight `t ∈ [lo, hi]` and a fixed
element `w` with `(1 - t) rk(u / w ⊓ u) + t rk(w / w ⊓ u) ≤ r + θ`. -/
theorem exists_fixed_weighted (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r)
    {lo hi θ : ℝ} (hlo : 0 < lo) (hlohi : lo < hi) (hhi : hi < 1) (hθ : 0 < θ) :
    ∃ t, lo ≤ t ∧ t ≤ hi ∧ ∃ w, (∀ g, act g w = w) ∧
      (1 - t) * ((rk u : ℝ) - rk (w ⊓ u)) + t * ((rk w : ℝ) - rk (w ⊓ u)) ≤ r + θ := by
  classical
  have hr0 : (0 : ℝ) ≤ r := by
    have := hr 1
    rw [act_one act hmul, inf_idem] at this
    exact_mod_cast (by linarith : (0 : ℤ) ≤ r)
  set κ := lo * (1 - hi) with hκdef
  have hκ : 0 < κ := mul_pos hlo (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ((r : ℝ) + 1) / κ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : 0 < n := by exact_mod_cast hnpos
  set η := (hi - lo) / n with hηdef
  have hη : 0 < η := div_pos (by linarith) hnpos
  set ε := min (θ / 4) (min (η / 32) (κ / 32)) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hε1 : ε ≤ θ / 4 := min_le_left _ _
  have hε2 : ε ≤ η / 32 := (min_le_right _ _).trans (min_le_left _ _)
  have hε3 : ε ≤ κ / 32 := (min_le_right _ _).trans (min_le_right _ _)
  set t : ℕ → ℝ := fun j => lo + (min j n : ℕ) * η with htdef
  have hnη : (n : ℝ) * η = hi - lo := by rw [hηdef]; field_simp
  have htlo : ∀ j, lo ≤ t j := fun j => by
    have : (0 : ℝ) ≤ (min j n : ℕ) * η := by positivity
    simp only [htdef]; linarith
  have hthi : ∀ j, t j ≤ hi := fun j => by
    have h1 : ((min j n : ℕ) : ℝ) ≤ n := by exact_mod_cast min_le_right j n
    have : ((min j n : ℕ) : ℝ) * η ≤ n * η := mul_le_mul_of_nonneg_right h1 hη.le
    simp only [htdef]; linarith
  have ht0 : ∀ j, 0 ≤ t j := fun j => (hlo.le.trans (htlo j))
  have ht1 : ∀ j, t j ≤ 1 := fun j => (hthi j).trans hhi.le
  have hsep : ∀ i j, i < j → j < n → 16 * ε < t j - t i := by
    intro i j hij hjn
    have e1 : min i n = i := min_eq_left (by omega)
    have e2 : min j n = j := min_eq_left (by omega)
    simp only [htdef, e1, e2]
    have : ((i : ℝ) + 1) ≤ j := by exact_mod_cast hij
    nlinarith
  have hκt : ∀ j, j < n → κ ≤ t j * (1 - t j) := by
    intro j _
    have a1 := htlo j
    have a2 := hthi j
    have : lo * (1 - hi) ≤ t j * (1 - t j) := by nlinarith
    exact this
  have hbig : (r : ℝ) < n * (κ - 16 * ε) := by
    have h1 : κ / 2 ≤ κ - 16 * ε := by linarith
    have h2 : 2 * ((r : ℝ) + 1) < n * κ := by
      rw [div_lt_iff₀ hκ] at hn; linarith
    nlinarith
  -- a nearly maximal measure
  set A : Set ℝ := {x | ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (τ : ι → G),
    x = ∑ j ∈ Finset.range n, a act rk u τ (t j)} with hAdef
  have hAne : A.Nonempty := ⟨_, Unit, inferInstance, inferInstance, fun _ => (1 : G), rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨n * r, ?_⟩
    rintro x ⟨ι, _, _, τ, rfl⟩
    have := Finset.sum_le_sum (s := Finset.range n) (fun j _ =>
      a_le_r act rk hinv u τ hstrict (ht0 j) (ht1 j) r hr)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  obtain ⟨x, ⟨ι, hF, hN, σ, rfl⟩, hx⟩ := exists_lt_of_lt_csSup hAne (show sSup A - ε < sSup A by
      linarith)
  have hsup : ∀ (κ' : Type) [Fintype κ'] [Nonempty κ'] (τ : κ' → G),
      ∑ j ∈ Finset.range n, a act rk u τ (t j) ≤ ∑ j ∈ Finset.range n, a act rk u σ (t j) + ε := by
    intro κ' _ _ τ
    have : ∑ j ∈ Finset.range n, a act rk u τ (t j) ∈ A := ⟨κ', inferInstance, inferInstance, τ,
        rfl⟩
    have := le_csSup hAbdd this
    linarith
  obtain ⟨j, hj, w, hw, hval⟩ := exists_fixed_of_levels act hmul rk hstrict hmod hinv u σ r hr hn0
      t ht0 ht1 hε
    hsep hκt hbig hsup
  have har := a_le_r act rk hinv u σ hstrict (ht0 j) (ht1 j) r hr
  exact ⟨t j, htlo j, hthi j, w, hw, by linarith⟩

include hmul hstrict hmod hinv in
/-- **Total error at most `2r`, for every group.** -/
theorem exists_fixed_total (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) :
    ∃ w, (∀ g, act g w = w) ∧ (rk u - rk (w ⊓ u)) + (rk w - rk (w ⊓ u)) ≤ 2 * r := by
  have hr0 : (0 : ℤ) ≤ r := by
    have := hr 1
    rw [act_one act hmul, inf_idem] at this
    linarith
  have hR : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  set δ : ℝ := 1 / (8 * (2 * r + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ2 : δ * (2 * r + 1) = 1 / 8 := by rw [hδ]; field_simp
  have hδsmall : δ ≤ 1 / 8 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨t, htl, hth, w, hw, hv⟩ := exists_fixed_weighted act hmul rk hstrict hmod hinv u r hr
    (lo := 1 / 2 - δ) (hi := 1 / 2 + δ) (θ := 1 / 8) (by linarith) (by linarith) (by linarith)
        (by norm_num)
  refine ⟨w, hw, ?_⟩
  have ha : (0 : ℝ) ≤ (rk u : ℝ) - rk (w ⊓ u) := by
    have : rk (w ⊓ u) ≤ rk u := hstrict.monotone inf_le_right
    have : (rk (w ⊓ u) : ℝ) ≤ rk u := by exact_mod_cast this
    linarith
  have hb : (0 : ℝ) ≤ (rk w : ℝ) - rk (w ⊓ u) := by
    have : rk (w ⊓ u) ≤ rk w := hstrict.monotone inf_le_left
    have : (rk (w ⊓ u) : ℝ) ≤ rk w := by exact_mod_cast this
    linarith
  by_contra hcon
  push Not at hcon
  have hc : (2 * r + 1 : ℝ) ≤ ((rk u : ℝ) - rk (w ⊓ u)) + ((rk w : ℝ) - rk (w ⊓ u)) := by
    have : 2 * r + 1 ≤ (rk u - rk (w ⊓ u)) + (rk w - rk (w ⊓ u)) := hcon
    exact_mod_cast this
  have m1 := mul_le_mul_of_nonneg_right (show 1 / 2 - δ ≤ 1 - t by linarith) ha
  have m2 := mul_le_mul_of_nonneg_right (show 1 / 2 - δ ≤ t by linarith) hb
  have m3 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 / 2 - δ by linarith)
  nlinarith

include hmul hstrict hmod hinv in
/-- **The one-sided form of Kazhdan and Polishchuk, for every group:** `rk(w / w ⊓ u) ≤ r` and
`rk(u / w ⊓ u) ≤ r (r + 1)`. -/
theorem exists_fixed_one_sided (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) :
    ∃ w, (∀ g, act g w = w) ∧ rk w - rk (w ⊓ u) ≤ r ∧ rk u - rk (w ⊓ u) ≤ r * (r + 1) := by
  have hr0 : (0 : ℤ) ≤ r := by
    have := hr 1
    rw [act_one act hmul, inf_idem] at this
    linarith
  rcases hr0.lt_or_eq with hpos | hzero
  · have hR1 : (1 : ℝ) ≤ r := by exact_mod_cast hpos
    set R : ℝ := r + 1 with hRdef
    have hR : 2 ≤ R := by linarith
    set x : ℝ := 1 / R with hxdef
    have hxR : x * R = 1 := by rw [hxdef]; field_simp
    have hx0 : 0 < x := by positivity
    have hx2 : x ≤ 1 / 2 := by
      rw [hxdef, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    set δ : ℝ := x ^ 3 / 8 with hδdef
    have hδ0 : 0 < δ := by positivity
    have hδx : δ ≤ x / 32 := by
      have : x ^ 2 ≤ 1 / 4 := by nlinarith
      rw [hδdef]; nlinarith
    obtain ⟨t, htl, hth, w, hw, hv⟩ := exists_fixed_weighted act hmul rk hstrict hmod hinv u r hr
      (lo := 1 - x + δ) (hi := 1 - x + 2 * δ) (θ := δ / 2) (by linarith) (by linarith)
          (by linarith) (by linarith)
    refine ⟨w, hw, ?_, ?_⟩
    · have ha : (0 : ℝ) ≤ (rk u : ℝ) - rk (w ⊓ u) := by
        have : rk (w ⊓ u) ≤ rk u := hstrict.monotone inf_le_right
        have : (rk (w ⊓ u) : ℝ) ≤ rk u := by exact_mod_cast this
        linarith
      by_contra hcon
      push Not at hcon
      have hc : (r + 1 : ℝ) ≤ (rk w : ℝ) - rk (w ⊓ u) := by
        have : r + 1 ≤ rk w - rk (w ⊓ u) := hcon
        exact_mod_cast this
      have m1 := mul_nonneg (show (0 : ℝ) ≤ 1 - t by linarith) ha
      have m2 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ t by linarith)
      have m3 := mul_le_mul_of_nonneg_right htl (show (0 : ℝ) ≤ R by linarith)
      -- t * R ≥ (1 - x + δ) R = R - 1 + δ R ≥ r + δ
      have : (1 - x + δ) * R = r + δ * R := by
        have : (1 - x + δ) * R = R - x * R + δ * R := by ring
        rw [this, hxR]; ring
      nlinarith
    · have hb : (0 : ℝ) ≤ (rk w : ℝ) - rk (w ⊓ u) := by
        have : rk (w ⊓ u) ≤ rk w := hstrict.monotone inf_le_left
        have : (rk (w ⊓ u) : ℝ) ≤ rk w := by exact_mod_cast this
        linarith
      by_contra hcon
      push Not at hcon
      have hc : (r * (r + 1) + 1 : ℝ) ≤ (rk u : ℝ) - rk (w ⊓ u) := by
        have : r * (r + 1) + 1 ≤ rk u - rk (w ⊓ u) := hcon
        exact_mod_cast this
      have m1 := mul_nonneg (show (0 : ℝ) ≤ t by linarith) hb
      have m2 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 - t by linarith)
      -- (1 - t)(r (r+1) + 1) ≥ (x - 2 δ)(R^2 - R + 1) = R - 1 + x - 2 δ (R^2 - R + 1) > r + δ / 2
      have h1 : (x - 2 * δ) * (r * (r + 1) + 1) ≤ (1 - t) * (r * (r + 1) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have e1 : x * (r * (r + 1) + 1) = r + x := by
        have : (r : ℝ) * (r + 1) + 1 = R * R - R + 1 := by rw [hRdef]; ring
        rw [this]
        have : x * (R * R - R + 1) = (x * R) * R - x * R + x := by ring
        rw [this, hxR]; rw [hRdef]; ring
      have e2 : δ * (r * (r + 1) + 1) * 8 = x * (x * x * (r * (r + 1) + 1)) := by rw [hδdef]; ring
      have e3 : x * x * (r * (r + 1) + 1) = 1 - x + x * x := by
        have : (r : ℝ) * (r + 1) + 1 = R * R - R + 1 := by rw [hRdef]; ring
        rw [this]
        have : x * x * (R * R - R + 1) = (x * R) * (x * R) - x * (x * R) + x * x := by ring
        rw [this, hxR]; ring
      rw [e3] at e2
      have : δ * (r * (r + 1) + 1) ≤ x / 8 := by nlinarith
      nlinarith
  · subst hzero
    obtain ⟨w, hw, h⟩ := exists_fixed_total act hmul rk hstrict hmod hinv u 0 hr
    have ha : rk (w ⊓ u) ≤ rk u := hstrict.monotone inf_le_right
    have hb : rk (w ⊓ u) ≤ rk w := hstrict.monotone inf_le_left
    exact ⟨w, hw, by linarith, by linarith⟩

end final

open Module in
/-- **Kazhdan-Polishchuk for every group, finite-dimensional `V`.** -/
theorem almost_invariant_subspace_all {K V G : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] (ρ : G →* (V ≃ₗ[K] V)) (A : Submodule K V) (r : ℕ)
    (hr : ∀ g, finrank K A ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r) :
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r) ∧
    (∃ W : Submodule K V, (∀ g, W.map (ρ g : V →ₗ[K] V) = W) ∧
      finrank K W ≤ finrank K (W ⊓ A : Submodule K V) + r ∧
      finrank K A ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1)) := by
  classical
  set act : G → Submodule K V ≃o Submodule K V := fun g => Submodule.orderIsoMapComap (ρ g)
  have hmul : ∀ g h a, act (g * h) a = act g (act h a) := by
    intro g h a
    ext x
    simp only [act, Submodule.orderIsoMapComap_apply, Submodule.mem_map, map_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ρ h y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  set rk : Submodule K V → ℤ := fun S => (finrank K S : ℤ)
  have hstrict : StrictMono rk := fun S T hST => by
    have h := Submodule.finrank_lt_finrank_of_lt hST
    change (finrank K S : ℤ) < finrank K T
    exact_mod_cast h
  have hmod : ∀ S T, rk (S ⊔ T) + rk (S ⊓ T) = rk S + rk T := fun S T => by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S T
    change (finrank K (S ⊔ T : Submodule K V) : ℤ) + finrank K (S ⊓ T : Submodule K V)
        = finrank K S + finrank K T
    exact_mod_cast h
  have hinv : ∀ g S, rk (act g S) = rk S := fun g S => by
    have h := LinearEquiv.finrank_map_eq (ρ g) S
    change (finrank K (S.map (ρ g : V →ₗ[K] V)) : ℤ) = finrank K S
    exact_mod_cast h
  have hr' : ∀ g, rk A - rk (act g A ⊓ A) ≤ r := fun g => by
    have h' : (finrank K A : ℤ) ≤ finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) + r := by
      exact_mod_cast hr g
    change (finrank K A : ℤ) - finrank K (A.map (ρ g : V →ₗ[K] V) ⊓ A : Submodule K V) ≤ r
    linarith
  constructor
  · obtain ⟨W, hW, h⟩ := AlmostInvariant.AllGroups.exists_fixed_total act hmul rk hstrict hmod
      hinv A r hr'
    refine ⟨W, hW, ?_⟩
    have : (finrank K W : ℤ) + finrank K A ≤ 2 * finrank K (W ⊓ A : Submodule K V) + 2 * r := by
      simp only [rk] at h; linarith
    exact_mod_cast this
  · obtain ⟨W, hW, h1, h2⟩ := AlmostInvariant.AllGroups.exists_fixed_one_sided act hmul rk hstrict
      hmod hinv A r hr'
    refine ⟨W, hW, ?_, ?_⟩
    · have : (finrank K W : ℤ) ≤ finrank K (W ⊓ A : Submodule K V) + r := by
        simp only [rk] at h1; linarith
      exact_mod_cast this
    · have : (finrank K A : ℤ) ≤ finrank K (W ⊓ A : Submodule K V) + r * (r + 1) := by
        simp only [rk] at h2; linarith
      exact_mod_cast this

end AlmostInvariant.AllGroups
