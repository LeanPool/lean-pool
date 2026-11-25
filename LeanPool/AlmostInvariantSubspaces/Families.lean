/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.AlmostInvariantSubspaces.Average
public import LeanPool.AlmostInvariantSubspaces.Length
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

/-!
# Kazhdan-Polishchuk Theorem A for families: one-sided bounds `r` and `r (r + 1)`, every group,
any dimension

Source of the problem: D. Kazhdan and A. Polishchuk, *Almost invariant subspaces and operators*,
arXiv 2107.08085,
Pure Appl. Math. Q. 19 (2023), Theorem A (the setting of a family).

A group `G` acts on a module `M` over a ring (by automorphisms of the lattice of submodules:
linear or semilinear actions),
and `A : X → Submodule R M` is a `G`-invariant family with `ℓ(A x / (A x ∩ A y)) ≤ r` for all `x,
y`. Then there is a
`G`-invariant `W` with `ℓ(W / (W ∩ A x)) ≤ r` and `ℓ(A x / (A x ∩ W)) ≤ r (r + 1)` for EVERY `x`.
Here `ℓ` is the length;
for vector spaces it is the dimension. No finiteness of `G`, `X` or of the dimension is assumed.

Proof (`PROOF.md`, sections 1-2), in Lean:
* `KPFamLat`: a lattice with a strictly monotone modular integer rank, a group of rank-preserving
  automorphisms, and one
  element `u`. The levels argument of the single-orbit proof (a measure on the orbit of `u` for
  which the sum over several
  levels `t` of the minima of `f_{σ,t}` is nearly maximal) gives a level with a unique
  near-minimizer; it is fixed by the group.
  New here: the near-minimizer is kept (not only its value), and the first-order inequalities at
  it, with the competitors
  `w ⊔ B` and `w ⊓ B`, bound the distance from `w` to EVERY element `B` that is within `r` of all
  translates of `u`.
  Such a `B` need not lie in the support of the measure.
* `KPFamilies`: the lattice of submodules commensurable with one member `A x0`, with the rank `S ↦
  [S : A x0]`
  (from the single-orbit Lean files of the release), and the translation to lengths and dimensions.
-/

@[expose] public section

namespace KPFamLat

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

include hstrict hmod in
omit [Group G] in
/-- **First-order inequalities at a near-minimizer** (`PROOF.md`, section 2, inequalities (1) and
(2)). Let `w` be a
`θ`-near-minimizer of `f_{σ,t}`, and let `B` be any element within `r` of every translate of `u`,
in both directions.
Comparing `w` with `w ⊔ B` gives `(1 - t) rk(B / B ⊓ w) ≤ r + θ`; comparing `w` with `w ⊓ B` gives
`t rk(w / w ⊓ B) ≤ r + θ`. The element `B` need not be in the support of the measure. -/
theorem first_order {t θ : ℝ} (r : ℤ) (w B : L)
    (hw : ∀ s, f act rk u σ t w ≤ f act rk u σ t s + θ)
    (hB1 : ∀ g, rk B - rk (B ⊓ act g u) ≤ r)
    (hB2 : ∀ g, rk (act g u) - rk (act g u ⊓ B) ≤ r) :
    (1 - t) * ((rk B : ℝ) - rk (B ⊓ w)) ≤ r + θ ∧ t * ((rk w : ℝ) - rk (w ⊓ B)) ≤ r + θ := by
  have hm : Monotone rk := hstrict.monotone
  constructor
  · -- the competitor `w ⊔ B`
    have h1 := hw (w ⊔ B)
    have key : ∀ i, ((rk B : ℝ) - rk (B ⊓ w)) - r ≤
        (rk (act (σ i) u ⊓ (w ⊔ B)) : ℝ) - rk (act (σ i) u ⊓ w) := by
      intro i
      have e1 := hmod (act (σ i) u ⊓ w) (B ⊓ act (σ i) u)
      have e2 : rk ((act (σ i) u ⊓ w) ⊔ (B ⊓ act (σ i) u)) ≤ rk (act (σ i) u ⊓ (w ⊔ B)) :=
        hm (sup_le (inf_le_inf_left _ le_sup_left) (le_inf inf_le_right (inf_le_left.trans
            le_sup_right)))
      have e3 : rk ((act (σ i) u ⊓ w) ⊓ (B ⊓ act (σ i) u)) ≤ rk (B ⊓ w) :=
        hm (le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_right))
      have e4 := hB1 (σ i)
      have e5 : rk B - rk (B ⊓ w) - r ≤ rk (act (σ i) u ⊓ (w ⊔ B)) - rk (act (σ i) u ⊓ w) := by
        linarith
      exact_mod_cast e5
    have h2 := avg_mono key
    rw [avg_const] at h2
    have e6 : avg (fun i => (rk (act (σ i) u ⊓ (w ⊔ B)) : ℝ) - rk (act (σ i) u ⊓ w)) =
        avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ w)) -
          avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ (w ⊔ B))) := by
      rw [← avg_sub]; congr 1; funext i; ring
    have e7 : ((rk (w ⊔ B) : ℤ) : ℝ) + rk (w ⊓ B) = rk w + rk B := by exact_mod_cast hmod w B
    have e8 : (rk (w ⊓ B) : ℝ) = rk (B ⊓ w) := by rw [inf_comm]
    have e9 : t * ((rk (w ⊔ B) : ℝ) - rk w) = t * ((rk B : ℝ) - rk (B ⊓ w)) := by
      congr 1; linarith
    unfold f at h1
    linarith
  · -- the competitor `w ⊓ B`
    have h1 := hw (w ⊓ B)
    have key : ∀ i, (rk (act (σ i) u ⊓ w) : ℝ) - rk (act (σ i) u ⊓ (w ⊓ B)) ≤ r := by
      intro i
      have e1 := hmod (act (σ i) u ⊓ w) (act (σ i) u ⊓ B)
      have e2 : rk ((act (σ i) u ⊓ w) ⊔ (act (σ i) u ⊓ B)) ≤ rk (act (σ i) u)
          := hm (sup_le inf_le_left inf_le_left)
      have e3 : rk ((act (σ i) u ⊓ w) ⊓ (act (σ i) u ⊓ B)) ≤ rk (act (σ i) u ⊓ (w ⊓ B)) :=
        hm (le_inf (inf_le_left.trans inf_le_left)
          (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
      have e4 := hB2 (σ i)
      have e5 : rk (act (σ i) u ⊓ w) - rk (act (σ i) u ⊓ (w ⊓ B)) ≤ r := by linarith
      exact_mod_cast e5
    have h2 := avg_mono key
    rw [avg_const] at h2
    have e6 : avg (fun i => (rk (act (σ i) u ⊓ w) : ℝ) - rk (act (σ i) u ⊓ (w ⊓ B))) =
        avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ (w ⊓ B))) -
          avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ w)) := by
      rw [← avg_sub]; congr 1; funext i; ring
    unfold f at h1
    linarith

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
/-- The main step: some level has a unique near-minimizer, and it is invariant. Unlike the
single-orbit file, the
conclusion keeps the near-minimizer property itself (`f w ≤ a + 4 ε`), which the first-order
inequalities need. -/
theorem exists_fixed_of_levels (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r)
    {n : ℕ} (hn : 0 < n) (t : ℕ → ℝ) (ht0 : ∀ j, 0 ≤ t j) (ht1 : ∀ j, t j ≤ 1)
    {ε κ : ℝ} (hε : 0 < ε) (hsep : ∀ i j, i < j → j < n → 16 * ε < t j - t i)
    (hκ : ∀ j, j < n → κ ≤ t j * (1 - t j)) (hbig : (r : ℝ) < n * (κ - 16 * ε))
    (hsup : ∀ (κ : Type) [Fintype κ] [Nonempty κ] (τ : κ → G),
      ∑ j ∈ Finset.range n, a act rk u τ (t j) ≤ ∑ j ∈ Finset.range n, a act rk u σ (t j) + ε) :
    ∃ j, j < n ∧ ∃ w, (∀ g, act g w = w) ∧ f act rk u σ (t j) w ≤ a act rk u σ (t j) + 4 * ε := by
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
/-- **Levels and first-order bounds, for all groups.** For every interval `[lo, hi] ⊂ (0,1)` and
`θ > 0` there are a level
`t ∈ [lo, hi]` and a fixed element `w` such that every `B` within `r` of all translates of `u`, in
both directions, has
`(1 - t) rk(B / B ⊓ w) ≤ r + θ` and `t rk(w / w ⊓ B) ≤ r + θ`. -/
theorem exists_fixed_first_order (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r)
    {lo hi θ : ℝ} (hlo : 0 < lo) (hlohi : lo < hi) (hhi : hi < 1) (hθ : 0 < θ) :
    ∃ t, lo ≤ t ∧ t ≤ hi ∧ ∃ w, (∀ g, act g w = w) ∧
      (∀ B, (∀ g, rk B - rk (B ⊓ act g u) ≤ r) → (∀ g, rk (act g u) - rk (act g u ⊓ B) ≤ r) →
        (1 - t) * ((rk B : ℝ) - rk (B ⊓ w)) ≤ r + θ ∧ t * ((rk w : ℝ) - rk (w ⊓ B)) ≤ r + θ) ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (σ : ι → G),
        ∀ E, avg (fun i => (rk (act (σ i) u ⊓ E) : ℝ) - rk (act (σ i) u ⊓ w)) ≤ t * ((rk E : ℝ)
            - rk w) + θ := by
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
  have hnear : ∀ s, f act rk u σ (t j) w ≤ f act rk u σ (t j) s + 4 * ε := fun s => by
    have := a_le act rk hstrict hinv u σ (ht0 j) (ht1 j) s
    linarith
  refine ⟨t j, htlo j, hthi j, w, hw, fun B hB1 hB2 => ?_, ι, hF, hN, σ, fun E => ?_⟩
  · obtain ⟨h1, h2⟩ := first_order act rk hstrict hmod u σ r w B hnear hB1 hB2
    exact ⟨by linarith, by linarith⟩
  · -- the enlargement inequality (1) of section 2 of `PROOF.md`, for every competitor `E`
    have h1 := hnear E
    have e6 : avg (fun i => (rk (act (σ i) u ⊓ E) : ℝ) - rk (act (σ i) u ⊓ w)) =
        avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ w)) -
          avg (fun i => (rk u : ℝ) - rk (act (σ i) u ⊓ E)) := by
      rw [← avg_sub]; congr 1; funext i; ring
    unfold f at h1
    linarith

include hmul hstrict hmod hinv in
/-- **Families, one-sided, every group (lattice form).** There is a fixed `w` such that every `B`
within `r` of all
translates of `u`, in both directions, has `rk(w / w ⊓ B) ≤ r` and `rk(B / B ⊓ w) ≤ r (r + 1)`.
Moreover `w` satisfies the
enlargement inequality (1) of section 2 of `PROOF.md` for a measure (uniform on a list `σ` of
translates), at a level `t` with
`r / (r + 1) ≤ t` and `(t - r / (r + 1)) r (r + 1) + τ < 1 / (r + 1)` (conditions (3)); section 3
needs this. -/
theorem exists_fixed_family_one_sided (r : ℤ) (hr : ∀ g, rk u - rk (act g u ⊓ u) ≤ r) :
    ∃ w, (∀ g, act g w = w) ∧
      (∀ B, (∀ g, rk B - rk (B ⊓ act g u) ≤ r) → (∀ g, rk (act g u) - rk (act g u ⊓ B) ≤ r) →
        rk w - rk (w ⊓ B) ≤ r ∧ rk B - rk (B ⊓ w) ≤ r * (r + 1)) ∧
      ∃ (t τ : ℝ) (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (σ : ι → G), 0 ≤ τ ∧ (r : ℝ) / (r
          + 1) ≤ t ∧
        (t - r / (r + 1)) * (r * (r + 1)) + τ < 1 / (r + 1) ∧
        ∀ E, avg (fun i => (rk (act (σ i) u ⊓ E) : ℝ) - rk (act (σ i) u ⊓ w)) ≤ t * ((rk E : ℝ)
            - rk w) + τ := by
  have hr0 : (0 : ℤ) ≤ r := by
    have := hr 1
    rw [act_one act hmul, inf_idem] at this
    linarith
  have hR0 : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = r + 1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = r * R + 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by linarith
  have hRne : R ≠ 0 := by linarith
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ (r : ℝ) * R := mul_nonneg hR0 (by linarith)
    linarith
  have hQne : Q ≠ 0 := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / R := ⟨_, rfl⟩
  have hxR : x * R = 1 := by rw [hx]; exact div_mul_cancel₀ 1 hRne
  have hx0 : 0 < x := by rw [hx]; exact one_div_pos.mpr (by linarith)
  have hx1 : x ≤ 1 := by
    have : x * 1 ≤ x * R := mul_le_mul_of_nonneg_left hR1 hx0.le
    linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = x / (4 * Q) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by linarith
  have hηQ : η * (4 * Q) = x := by
    rw [hη]; exact div_mul_cancel₀ x (mul_pos (by norm_num) hQpos).ne'
  have hη0 : 0 < η := by rw [hη]; exact div_pos hx0 (mul_pos (by norm_num) hQpos)
  have hηx : η ≤ x / 4 := by
    have : η * 4 ≤ η * (4 * Q) := mul_le_mul_of_nonneg_left (by linarith) hη0.le
    linarith
  obtain ⟨t, htl, hth, w, hw, hB, ι, hF, hN, σ, hE⟩ := exists_fixed_first_order act hmul rk
      hstrict hmod hinv u r hr
    (lo := 1 - x + η) (hi := 1 - x + 2 * η) (θ := η / 2) (by linarith) (by linarith) (by linarith)
        (by linarith)
  have hrx : (r : ℝ) / (r + 1) = 1 - x := by
    rw [← hR, div_eq_mul_one_div, ← hx]
    have e : (r : ℝ) * x = R * x - x := by rw [hR]; ring
    linarith
  have hx' : (1 : ℝ) / (r + 1) = x := by rw [← hR, hx]
  have e3 : 2 * η * ((r : ℝ) * (r + 1)) = x / 2 - 2 * η := by
    rw [← hηQ, hQ, hR]; ring
  have htc : (t - (r : ℝ) / (r + 1)) * ((r : ℝ) * (r + 1)) + η / 2 < 1 / (r + 1) := by
    rw [hrx, hx']
    have hp : (t - (1 - x)) * ((r : ℝ) * (r + 1)) ≤ 2 * η * ((r : ℝ) * (r + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hR0 (by linarith))
    linarith
  have htr : (r : ℝ) / (r + 1) ≤ t := by rw [hrx]; linarith
  refine ⟨w, hw, fun B hB1 hB2 => ?_, t, η / 2, ι, hF, hN, σ, by linarith, htr, htc, hE⟩
  obtain ⟨h1, h2⟩ := hB B hB1 hB2
  constructor
  · -- `t rk(w / w ⊓ B) ≤ r + η / 2` and `t (r + 1) > r + η / 2`
    by_contra hcon
    push Not at hcon
    have hc : R ≤ (rk w : ℝ) - rk (w ⊓ B) := by
      have : r + 1 ≤ rk w - rk (w ⊓ B) := hcon
      have : ((r + 1 : ℤ) : ℝ) ≤ ((rk w - rk (w ⊓ B) : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have m1 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ t by linarith)
    have m2 := mul_le_mul_of_nonneg_right htl (show (0 : ℝ) ≤ R by linarith)
    have e : (1 - x + η) * R = r + η * R := by
      have : (1 - x + η) * R = R - x * R + η * R := by ring
      rw [this, hxR, hR]; ring
    have m3 : η ≤ η * R := le_mul_of_one_le_right hη0.le hR1
    linarith
  · -- `(1 - t) rk(B / B ⊓ w) ≤ r + η / 2` and `(1 - t) (r (r + 1) + 1) > r + η / 2`
    by_contra hcon
    push Not at hcon
    have hc : Q ≤ (rk B : ℝ) - rk (B ⊓ w) := by
      have : r * (r + 1) + 1 ≤ rk B - rk (B ⊓ w) := hcon
      have : ((r * (r + 1) + 1 : ℤ) : ℝ) ≤ ((rk B - rk (B ⊓ w) : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this
      rw [hQ, hR]
      linarith
    have m1 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 - t by linarith)
    have m2 : (x - 2 * η) * Q ≤ (1 - t) * Q := mul_le_mul_of_nonneg_right (by linarith)
        (by linarith)
    have e1 : x * Q = r + x := by
      rw [hQ]
      have : x * (r * R + 1) = r * (x * R) + x := by ring
      rw [this, hxR]; ring
    have e2 : 2 * η * Q = x / 2 := by linarith
    linarith

end final

end KPFamLat

namespace KPFamilies

open AlmostInvariant (d d_inf d_sup d_add d_eq_zero d_mono_left d_anti_right d_map
  d_self d_triangle)

open Submodule

section Commensurable

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- `d X (X ⊓ Y ⊓ Z) ≤ d X Y + d X Z`. -/
theorem d_lower (X Y Z : Submodule R M) : d X (X ⊓ Y ⊓ Z) ≤ d X Y + d X Z := by
  rw [d_add (A := X) (B := X ⊓ Y) (C := X ⊓ Y ⊓ Z) inf_le_left inf_le_left, d_inf, d_inf]
  gcongr
  exact d_mono_left inf_le_left

/-- The relative index `[X : Y]`. -/
noncomputable def idx (X Y : Submodule R M) : ℤ := ((d X Y).toNat : ℤ) - (d Y X).toNat

theorem idx_eq_of_lower {X Y B : Submodule R M} (hX : B ≤ X) (hY : B ≤ Y) (fX : d X B ≠ ⊤)
    (fY : d Y B ≠ ⊤) :
    idx X Y = ((d X B).toNat : ℤ) - (d Y B).toNat := by
  have hXY : B ≤ X ⊓ Y := le_inf hX hY
  have e1 : d X B = d X Y + d (X ⊓ Y) B := by rw [d_add hXY inf_le_left, d_inf]
  have e2 : d Y B = d Y X + d (X ⊓ Y) B := by rw [inf_comm, d_add (le_inf hY hX) inf_le_left, d_inf]
  have f1 : d X Y ≠ ⊤ := fun h => fX (by rw [e1, h, top_add])
  have f2 : d Y X ≠ ⊤ := fun h => fY (by rw [e2, h, top_add])
  have f3 : d (X ⊓ Y) B ≠ ⊤ := fun h => fX (by rw [e1, h, add_top])
  rw [idx, e1, e2, ENat.toNat_add f1 f3, ENat.toNat_add f2 f3]
  push_cast
  ring

/-- Pairwise finite distances. -/
def PF (X Y : Submodule R M) : Prop := d X Y ≠ ⊤ ∧ d Y X ≠ ⊤

theorem idx_add {X Y Z : Submodule R M} (hXY : PF X Y) (hYZ : PF Y Z) (hXZ : PF X Z) :
    idx X Z = idx X Y + idx Y Z := by
  set B := X ⊓ Y ⊓ Z with hB
  have bX : B ≤ X := inf_le_left.trans inf_le_left
  have bY : B ≤ Y := inf_le_left.trans inf_le_right
  have bZ : B ≤ Z := inf_le_right
  have fX : d X B ≠ ⊤ := ne_top_of_le_ne_top (by simp [hXY.1, hXZ.1]) (d_lower X Y Z)
  have fY : d Y B ≠ ⊤ := by
    have e : B = Y ⊓ X ⊓ Z := by rw [hB, inf_comm X Y]
    rw [e]; exact ne_top_of_le_ne_top (by simp [hXY.2, hYZ.1]) (d_lower Y X Z)
  have fZ : d Z B ≠ ⊤ := by
    have e : B = Z ⊓ X ⊓ Y := by
      rw [hB, inf_comm (X ⊓ Y) Z, inf_assoc]
    rw [e]; exact ne_top_of_le_ne_top (by simp [hXZ.2, hYZ.2]) (d_lower Z X Y)
  rw [idx_eq_of_lower bX bZ fX fZ, idx_eq_of_lower bX bY fX fY, idx_eq_of_lower bY bZ fY fZ]
  ring

/-- Commensurable with `A`. -/
def IsComm (A S : Submodule R M) : Prop := d S A ≠ ⊤ ∧ d A S ≠ ⊤

theorem comm_inf {A S T : Submodule R M} (hS : IsComm A S) (hT : IsComm A T) : IsComm A (S ⊓ T)
    := by
  refine ⟨ne_top_of_le_ne_top hS.1 (d_mono_left inf_le_left), ?_⟩
  have h : d A (S ⊓ T) ≤ d A S + d A T := by
    rw [← d_inf A (S ⊓ T), ← inf_assoc]
    exact d_lower A S T
  exact ne_top_of_le_ne_top (by simp [hS.2, hT.2]) h

theorem comm_sup {A S T : Submodule R M} (hS : IsComm A S) (hT : IsComm A T) : IsComm A (S ⊔ T)
    := by
  refine ⟨?_, ne_top_of_le_ne_top hS.2 (d_anti_right le_sup_left)⟩
  have h : d (S ⊔ T) A ≤ d S A + d T A := by
    rw [← d_sup (S ⊔ T) A]
    have e : S ⊔ T ⊔ A = T ⊔ (S ⊔ A) := by
      rw [sup_comm S T, sup_assoc]
    rw [d_add (A := S ⊔ T ⊔ A) (B := S ⊔ A) (C := A) le_sup_right
      (sup_le_sup_right le_sup_left A), e, d_sup, d_sup, add_comm]
    gcongr
    exact d_anti_right le_sup_right
  exact ne_top_of_le_ne_top (by simp [hS.1, hT.1]) h

theorem pf_of_comm {A S T : Submodule R M} (hS : IsComm A S) (hT : IsComm A T) : PF S T :=
  ⟨ne_top_of_le_ne_top (by simp [hS.1, hT.2]) (d_triangle S A T),
   ne_top_of_le_ne_top (by simp [hT.1, hS.2]) (d_triangle T A S)⟩

theorem pf_A {A S : Submodule R M} (hS : IsComm A S) : PF S A := ⟨hS.1, hS.2⟩

theorem comm_self (A : Submodule R M) : IsComm A A := by
  have : d A A = 0 := d_eq_zero.mpr le_rfl
  exact ⟨by simp [this], by simp [this]⟩

variable (A : Submodule R M)

/-- The lattice of submodules commensurable with `A`. -/
abbrev CL := {S : Submodule R M // IsComm A S}

instance : Lattice (CL A) :=
  Subtype.lattice (fun _ _ hx hy => comm_sup hx hy) (fun _ _ hx hy => comm_inf hx hy)

/-- The rank `S ↦ [S : A]`. -/
noncomputable def rkA (S : CL A) : ℤ := idx S.1 A

theorem rkA_strict : StrictMono (rkA A) := by
  intro S T hST
  have hle : S.1 ≤ T.1 := hST.le
  have hne : ¬ T.1 ≤ S.1 := fun h => (ne_of_lt hST) (Subtype.ext (le_antisymm hle h))
  have e := idx_add (pf_of_comm T.2 S.2) (pf_A S.2) (pf_A T.2)
  have h0 : d S.1 T.1 = 0 := d_eq_zero.mpr hle
  have h1 : d T.1 S.1 ≠ 0 := fun h => hne (d_eq_zero.mp h)
  have h2 : d T.1 S.1 ≠ ⊤ := (pf_of_comm T.2 S.2).1
  have h3 : 0 < (d T.1 S.1).toNat := by
    rcases Nat.eq_zero_or_pos (d T.1 S.1).toNat with h | h
    · exact absurd ((ENat.toNat_eq_zero).mp h) (by tauto)
    · exact h
  have key : idx T.1 S.1 = (d T.1 S.1).toNat := by rw [idx, h0]; simp
  change idx S.1 A < idx T.1 A
  rw [e, key]
  have : (0 : ℤ) < (d T.1 S.1).toNat := by exact_mod_cast h3
  linarith

theorem rkA_mod (S T : CL A) : rkA A (S ⊔ T) + rkA A (S ⊓ T) = rkA A S + rkA A T := by
  have cs : IsComm A (S.1 ⊔ T.1) := comm_sup S.2 T.2
  have ci : IsComm A (S.1 ⊓ T.1) := comm_inf S.2 T.2
  have e1 := idx_add (pf_of_comm cs S.2) (pf_A S.2) (pf_A cs)
  have e2 := idx_add (pf_of_comm ci T.2) (pf_A T.2) (pf_A ci)
  have k1 : idx (S.1 ⊔ T.1) S.1 = (d T.1 S.1).toNat := by
    rw [idx, sup_comm, d_sup, d_eq_zero.mpr (le_sup_right : S.1 ≤ T.1 ⊔ S.1)]
    simp
  have k2 : idx (S.1 ⊓ T.1) T.1 = - (d T.1 S.1).toNat := by
    rw [idx, d_eq_zero.mpr (inf_le_right : S.1 ⊓ T.1 ≤ T.1), inf_comm, d_inf]
    simp
  change idx (S.1 ⊔ T.1) A + idx (S.1 ⊓ T.1) A = idx S.1 A + idx T.1 A
  rw [e1, e2, k1, k2]
  ring

variable {G : Type*} [Group G] (ρ : G →* (Submodule R M ≃o Submodule R M))

theorem ρmul (g h : G) (x : Submodule R M) : ρ (g * h) x = ρ g (ρ h x) := by
  simp [map_mul]

theorem ρinv (g : G) (x : Submodule R M) : ρ g⁻¹ (ρ g x) = x := by
  rw [← ρmul, inv_mul_cancel, map_one]; rfl

theorem ρinv' (g : G) (x : Submodule R M) : ρ g (ρ g⁻¹ x) = x := by
  rw [← ρmul, mul_inv_cancel, map_one]; rfl

variable (r : ℕ) (hr : ∀ g, d A (ρ g A) ≤ r)
include hr

theorem dgA (g : G) : d (ρ g A) A ≤ r := by
  have := hr g⁻¹
  rw [← d_map (ρ g) A (ρ g⁻¹ A), ρinv'] at this
  exact this

theorem comm_act (g : G) {S : Submodule R M} (hS : IsComm A S) : IsComm A (ρ g S) := by
  have h1 : d (ρ g S) A ≤ d S A + r := by
    calc d (ρ g S) A ≤ d (ρ g S) (ρ g A) + d (ρ g A) A := d_triangle _ _ _
      _ ≤ d S A + r := by rw [d_map]; gcongr; exact dgA A ρ r hr g
  have h2 : d A (ρ g S) ≤ r + d A S := by
    calc d A (ρ g S) ≤ d A (ρ g A) + d (ρ g A) (ρ g S) := d_triangle _ _ _
      _ ≤ r + d A S := by rw [d_map]; gcongr; exact hr g
  exact ⟨ne_top_of_le_ne_top (by simp [hS.1]) h1, ne_top_of_le_ne_top (by simp [hS.2]) h2⟩

/-- The action on the commensurable lattice. -/
noncomputable def actCL (g : G) : CL A ≃o CL A where
  toFun S := ⟨ρ g S.1, comm_act A ρ r hr g S.2⟩
  invFun S := ⟨ρ g⁻¹ S.1, comm_act A ρ r hr g⁻¹ S.2⟩
  left_inv S := Subtype.ext (ρinv ρ g S.1)
  right_inv S := Subtype.ext (ρinv' ρ g S.1)
  map_rel_iff' := by
    intro S T
    change ρ g S.1 ≤ ρ g T.1 ↔ S.1 ≤ T.1
    exact (ρ g).le_iff_le

theorem actCL_mul (g h : G) (S : CL A) : actCL A ρ r hr (g * h) S = actCL A ρ r hr g (actCL A ρ r
    hr h S) :=
  Subtype.ext (ρmul ρ g h S.1)

/-- `g ↦ [gA : A]` is a homomorphism with values in `[-r, r]`, so it is zero. -/
theorem chi_zero (g : G) : idx (ρ g A) A = 0 := by
  have cA : ∀ k : G, IsComm A (ρ k A) := fun k => comm_act A ρ r hr k (comm_self A)
  have hom : ∀ g h : G, idx (ρ (g * h) A) A = idx (ρ g A) A + idx (ρ h A) A := by
    intro g h
    have cgh : IsComm A (ρ g (ρ h A)) := by
      have := cA (g * h)
      rwa [ρmul] at this
    rw [ρmul, idx_add (pf_of_comm cgh (cA g)) (pf_A (cA g)) (pf_A cgh)]
    have : idx (ρ g (ρ h A)) (ρ g A) = idx (ρ h A) A := by simp only [idx, d_map]
    rw [this]; ring
  have bnd : ∀ k : G, |idx (ρ k A) A| ≤ r := by
    intro k
    have a1 := dgA A ρ r hr k
    have a2 := hr k
    have t1 : (d (ρ k A) A).toNat ≤ r := by
      have := ENat.toNat_le_toNat a1 (by simp)
      simpa using this
    have t2 : (d A (ρ k A)).toNat ≤ r := by
      have := ENat.toNat_le_toNat a2 (by simp)
      simpa using this
    rw [idx, abs_le]
    constructor <;> omega
  have pw : ∀ n : ℕ, idx (ρ (g ^ n) A) A = n * idx (ρ g A) A := by
    intro n
    induction n with
    | zero => simp [idx, d_eq_zero.mpr le_rfl]
    | succ n ih => rw [pow_succ, hom, ih]; push_cast; ring
  have h := bnd (g ^ (r + 1))
  rw [pw, abs_mul] at h
  have : |((r + 1 : ℕ) : ℤ)| = r + 1 := by rw [abs_of_nonneg (by positivity)]; push_cast; ring
  rw [this] at h
  by_contra hne
  have : 1 ≤ |idx (ρ g A) A| := Int.one_le_abs hne
  nlinarith

theorem rkA_inv (g : G) (S : CL A) : rkA A (actCL A ρ r hr g S) = rkA A S := by
  have cg : IsComm A (ρ g A) := comm_act A ρ r hr g (comm_self A)
  have cS : IsComm A (ρ g S.1) := comm_act A ρ r hr g S.2
  change idx (ρ g S.1) A = idx S.1 A
  rw [idx_add (pf_of_comm cS cg) (pf_A cg) (pf_A cS), chi_zero A ρ r hr g]
  simp only [idx, d_map, add_zero]

end Commensurable

section Families

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- In the commensurable lattice, a difference of ranks is a length: `[S : A] - [S ∩ T : A] = ℓ(S
/ S ∩ T)`. -/
theorem rkA_sub_inf (A : Submodule R M) (S T : CL A) : rkA A S - rkA A (S ⊓ T)
    = ((d S.1 T.1).toNat : ℤ) := by
  have cST : IsComm A (S.1 ⊓ T.1) := comm_inf S.2 T.2
  have e := idx_add (pf_of_comm S.2 cST) (pf_A cST) (pf_A S.2)
  have k : idx S.1 (S.1 ⊓ T.1) = (d S.1 T.1).toNat := by
    rw [idx, d_inf, d_eq_zero.mpr (inf_le_left : S.1 ⊓ T.1 ≤ S.1)]
    simp
  change idx S.1 A - idx (S.1 ⊓ T.1) A = _
  rw [e, k]
  ring

/-- **Kazhdan-Polishchuk Theorem A for families, one-sided form, with the data of the
near-minimizer.** Every group,
every ring, every module; the group acts by automorphisms of the lattice of submodules (linear or
semilinear actions).
If the family `A : X → Submodule R M` is invariant (each `g` maps each member to a member) and
`ℓ(A x / (A x ∩ A y)) ≤ r` for all `x, y`, then there is an invariant `W` with `ℓ(W / (W ∩ A x)) ≤
r` and
`ℓ(A x / (A x ∩ W)) ≤ r (r + 1)` for every `x`. Moreover `W` satisfies the enlargement inequality
(1) of `PROOF.md`,
section 2 for a probability measure `wt` on a finite set `s` of indices, at a level `t` with
conditions (3):
`∑_y wt y ℓ(((A y ⊔ W) ⊓ E) / W) ≤ t ℓ(E / W) + τ` for every `E ⊇ W` with `ℓ(E / W)` finite. -/
theorem kp_family_export {G X : Type*} [Group G] [Nonempty X] (ρ : G →* (Submodule R M ≃o
    Submodule R M))
    (A : X → Submodule R M) (hA : ∀ g x, ∃ y, ρ g (A x) = A y) (r : ℕ) (hr : ∀ x y, d (A x) (A y)
        ≤ r) :
    ∃ W : Submodule R M, (∀ g, ρ g W = W) ∧
      (∀ x, d W (A x) ≤ r ∧ d (A x) W ≤ ((r * (r + 1) : ℕ) : ℕ∞)) ∧
      ∃ (s : Finset X) (wt : X → ℝ) (t τ : ℝ), (∀ y ∈ s, 0 ≤ wt y) ∧ ∑ y ∈ s, wt y = 1 ∧ 0 ≤ τ ∧
        (r : ℝ) / (r + 1) ≤ t ∧ (t - r / (r + 1)) * (r * (r + 1)) + τ < 1 / (r + 1) ∧
        ∀ E : Submodule R M, W ≤ E → d E W ≠ ⊤ →
          ∑ y ∈ s, wt y * ((d ((A y ⊔ W) ⊓ E) W).toNat : ℝ) ≤ t * ((d E W).toNat : ℝ) + τ := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty X›
  have hr0 : ∀ g, d (A x0) (ρ g (A x0)) ≤ r := by
    intro g
    obtain ⟨y, hy⟩ := hA g x0
    rw [hy]
    exact hr x0 y
  have commx : ∀ x, IsComm (A x0) (A x) := fun x =>
    ⟨ne_top_of_le_ne_top (by simp) (hr x x0), ne_top_of_le_ne_top (by simp) (hr x0 x)⟩
  have toNat_le : ∀ x y, (d (A x) (A y)).toNat ≤ r := by
    intro x y
    have := ENat.toNat_le_toNat (hr x y) (by simp)
    simpa using this
  -- the action on the commensurable lattice, and the translates of `u = A x0`
  have actval : ∀ g (S : CL (A x0)), (actCL (A x0) ρ r hr0 g S).1 = ρ g S.1 := fun g S => rfl
  let u : CL (A x0) := ⟨A x0, comm_self (A x0)⟩
  have uval : u.1 = A x0 := rfl
  have hr' : ∀ g, rkA (A x0) u - rkA (A x0) (actCL (A x0) ρ r hr0 g u ⊓ u) ≤ (r : ℤ) := by
    intro g
    rw [inf_comm, rkA_sub_inf, actval, uval]
    obtain ⟨y, hy⟩ := hA g x0
    rw [hy]
    exact_mod_cast toNat_le x0 y
  obtain ⟨w, hw, hB, t, τ, ι, hF, hN, σ, hτ, ht1, ht2, hE⟩ :=
    KPFamLat.exists_fixed_family_one_sided (actCL (A x0) ρ r hr0) (actCL_mul (A x0) ρ r hr0)
        (rkA (A x0))
      (rkA_strict (A x0)) (rkA_mod (A x0)) (rkA_inv (A x0) ρ r hr0) u (r : ℤ) hr'
  refine ⟨w.1, fun g => congrArg Subtype.val (hw g), fun x => ?_, ?_⟩
  · -- the two pointwise bounds
    let B : CL (A x0) := ⟨A x, commx x⟩
    have Bval : B.1 = A x := rfl
    have hB1 : ∀ g, rkA (A x0) B - rkA (A x0) (B ⊓ actCL (A x0) ρ r hr0 g u) ≤ (r : ℤ) := by
      intro g
      rw [rkA_sub_inf, actval, uval, Bval]
      obtain ⟨y, hy⟩ := hA g x0
      rw [hy]
      exact_mod_cast toNat_le x y
    have hB2 : ∀ g, rkA (A x0) (actCL (A x0) ρ r hr0 g u) -
        rkA (A x0) (actCL (A x0) ρ r hr0 g u ⊓ B) ≤ (r : ℤ) := by
      intro g
      rw [rkA_sub_inf, actval, uval, Bval]
      obtain ⟨y, hy⟩ := hA g x0
      rw [hy]
      exact_mod_cast toNat_le y x
    obtain ⟨h1, h2⟩ := hB B hB1 hB2
    rw [rkA_sub_inf, Bval] at h1 h2
    have f1 : d w.1 (A x) ≠ ⊤ := (pf_of_comm w.2 (commx x)).1
    have f2 : d (A x) w.1 ≠ ⊤ := (pf_of_comm (commx x) w.2).1
    constructor
    · have : (d w.1 (A x)).toNat ≤ r := by exact_mod_cast h1
      rw [← ENat.natCast_toNat f1]
      exact_mod_cast this
    · have : (d (A x) w.1).toNat ≤ r * (r + 1) := by exact_mod_cast h2
      rw [← ENat.natCast_toNat f2]
      exact_mod_cast this
  · -- the measure, pushed to the index set `X`
    let yf : ι → X := fun i => Classical.choose (hA (σ i) x0)
    have hyf : ∀ i, ρ (σ i) (A x0) = A (yf i) := fun i => Classical.choose_spec (hA (σ i) x0)
    let wt : X → ℝ := fun y => ((Finset.univ.filter (fun i => yf i = y)).card : ℝ) / Fintype.card ι
    have hsum : ∀ F : X → ℝ,
        ∑ y ∈ Finset.univ.image yf, wt y * F y = AlmostInvariant.avg (fun i => F (yf i)) := by
      intro F
      simp only [AlmostInvariant.avg, wt]
      rw [Finset.sum_comp F yf, Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [nsmul_eq_mul]
      ring
    have ht1' : (r : ℝ) / (r + 1) ≤ t := by push_cast at ht1; exact ht1
    have ht2' : (t - r / (r + 1)) * (r * (r + 1)) + τ < 1 / (r + 1) := by
      push_cast at ht2; exact ht2
    refine ⟨Finset.univ.image yf, wt, t, τ, fun y _ => div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _),
      ?_, hτ, ht1', ht2', ?_⟩
    · have h := hsum (fun _ => 1)
      simp only [mul_one] at h
      rw [h, AlmostInvariant.avg_const]
    · intro E hWE hfin
      have commE : IsComm (A x0) E := by
        refine ⟨?_, ?_⟩
        · have h1 : d E (A x0) ≤ d E w.1 + d w.1 (A x0) := d_triangle _ _ _
          exact ne_top_of_le_ne_top (by simp [hfin, w.2.1]) h1
        · exact ne_top_of_le_ne_top w.2.2 (d_anti_right hWE)
      let E' : CL (A x0) := ⟨E, commE⟩
      have hwE : w ≤ E' := hWE
      have h := hE E'
      have hEw : ((rkA (A x0) E' : ℝ) - rkA (A x0) w) = ((d E w.1).toNat : ℝ) := by
        have e := rkA_sub_inf (A x0) E' w
        rw [inf_eq_right.mpr hwE] at e
        exact_mod_cast e
      rw [hEw] at h
      have key : ∀ i, ((d ((A (yf i) ⊔ w.1) ⊓ E) w.1).toNat : ℝ) =
          (rkA (A x0) (actCL (A x0) ρ r hr0 (σ i) u ⊓ E') : ℝ) -
            rkA (A x0) (actCL (A x0) ρ r hr0 (σ i) u ⊓ w) := by
        intro i
        have e1 : actCL (A x0) ρ r hr0 (σ i) u ⊓ w = (actCL (A x0) ρ r hr0 (σ i) u ⊓ E') ⊓ w := by
          rw [inf_assoc, inf_eq_right.mpr hwE]
        have e2 : (actCL (A x0) ρ r hr0 (σ i) u ⊓ E').1 = A (yf i) ⊓ E := by
          change ρ (σ i) (A x0) ⊓ E = A (yf i) ⊓ E
          rw [hyf i]
        have e3 : (A (yf i) ⊔ w.1) ⊓ E = w.1 ⊔ (A (yf i) ⊓ E) := by
          rw [sup_comm]
          exact sup_inf_assoc_of_le _ hWE
        rw [e1, ← Int.cast_sub, rkA_sub_inf, e2, e3, sup_comm, d_sup]
        norm_cast
      calc ∑ y ∈ Finset.univ.image yf, wt y * ((d ((A y ⊔ w.1) ⊓ E) w.1).toNat : ℝ)
          = AlmostInvariant.avg (fun i => ((d ((A (yf i) ⊔ w.1) ⊓ E) w.1).toNat : ℝ)) := hsum _
        _ = AlmostInvariant.avg (fun i => (rkA (A x0) (actCL (A x0) ρ r hr0 (σ i) u ⊓ E') : ℝ) -
              rkA (A x0) (actCL (A x0) ρ r hr0 (σ i) u ⊓ w)) := by
            congr 1
            funext i
            exact key i
        _ ≤ t * ((d E w.1).toNat : ℝ) + τ := h

/-- **Kazhdan-Polishchuk Theorem A for families, one-sided form, every group, every ring, every
module.** The group acts by
automorphisms of the lattice of submodules (for example by linear or semilinear automorphisms of
`M`). If the family
`A : X → Submodule R M` is invariant (each `g` maps each member to a member) and `ℓ(A x / (A x ∩ A
y)) ≤ r` for all `x, y`,
then there is an invariant `W` with `ℓ(W / (W ∩ A x)) ≤ r` and `ℓ(A x / (A x ∩ W)) ≤ r (r + 1)`
for every `x`. -/
theorem kp_family_lattice {G X : Type*} [Group G] (ρ : G →* (Submodule R M ≃o Submodule R M))
    (A : X → Submodule R M) (hA : ∀ g x, ∃ y, ρ g (A x) = A y) (r : ℕ) (hr : ∀ x y, d (A x) (A y)
        ≤ r) :
    ∃ W : Submodule R M, (∀ g, ρ g W = W) ∧ ∀ x, d W (A x) ≤ r ∧ d (A x) W ≤ ((r * (r + 1) : ℕ)
        : ℕ∞) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨⊥, fun g => (ρ g).map_bot, fun x => isEmptyElim x⟩
  · obtain ⟨W, hW, h, -⟩ := kp_family_export ρ A hA r hr
    exact ⟨W, hW, h⟩

/-- A linear action gives an action on the lattice of submodules. -/
def linearAct {G : Type*} [Group G] (ρ : G →* (M ≃ₗ[R] M)) : G →* (Submodule R M ≃o Submodule R M)
    where
  toFun g := Submodule.orderIsoMapComap (ρ g)
  map_one' := by
    ext S x
    simp
  map_mul' g h := by
    ext S x
    simp only [map_mul, Submodule.orderIsoMapComap_apply, RelIso.mul_apply, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ρ h y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩

theorem linearAct_apply {G : Type*} [Group G] (ρ : G →* (M ≃ₗ[R] M)) (g : G) (S : Submodule R M) :
    linearAct ρ g S = S.map (ρ g : M →ₗ[R] M) := rfl

/-- The export for linear actions (the interface for the finite-form proof, part B). -/
theorem kp_family_export_linear {G X : Type*} [Group G] [Nonempty X] (ρ : G →* (M ≃ₗ[R] M))
    (A : X → Submodule R M) (hA : ∀ g x, ∃ y, (A x).map (ρ g : M →ₗ[R] M) = A y) (r : ℕ)
    (hr : ∀ x y, d (A x) (A y) ≤ r) :
    ∃ W : Submodule R M, (∀ g, W.map (ρ g : M →ₗ[R] M) = W) ∧
      (∀ x, d W (A x) ≤ r ∧ d (A x) W ≤ ((r * (r + 1) : ℕ) : ℕ∞)) ∧
      ∃ (s : Finset X) (wt : X → ℝ) (t τ : ℝ), (∀ y ∈ s, 0 ≤ wt y) ∧ ∑ y ∈ s, wt y = 1 ∧ 0 ≤ τ ∧
        (r : ℝ) / (r + 1) ≤ t ∧ (t - r / (r + 1)) * (r * (r + 1)) + τ < 1 / (r + 1) ∧
        ∀ E : Submodule R M, W ≤ E → d E W ≠ ⊤ →
          ∑ y ∈ s, wt y * ((d ((A y ⊔ W) ⊓ E) W).toNat : ℝ) ≤ t * ((d E W).toNat : ℝ) + τ := by
  have hA' : ∀ g x, ∃ y, linearAct ρ g (A x) = A y := by
    intro g x
    obtain ⟨y, hy⟩ := hA g x
    exact ⟨y, by rw [linearAct_apply]; exact hy⟩
  obtain ⟨W, hW, h⟩ := kp_family_export (linearAct ρ) A hA' r hr
  refine ⟨W, fun g => ?_, h⟩
  rw [← linearAct_apply]
  exact hW g

/-- **Modules over any ring, linear actions, lengths.** -/
theorem kp_family_one_sided_module {G X : Type*} [Group G] (ρ : G →* (M ≃ₗ[R] M)) (A : X
    → Submodule R M)
    (hA : ∀ g x, ∃ y, (A x).map (ρ g : M →ₗ[R] M) = A y) (r : ℕ)
    (hr : ∀ x y, Module.length R (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ W : Submodule R M, (∀ g, W.map (ρ g : M →ₗ[R] M) = W) ∧
      ∀ x, Module.length R (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.length R (A x ⧸ W.submoduleOf (A x)) ≤ ((r * (r + 1) : ℕ) : ℕ∞) := by
  have hA' : ∀ g x, ∃ y, linearAct ρ g (A x) = A y := by
    intro g x
    obtain ⟨y, hy⟩ := hA g x
    exact ⟨y, by rw [linearAct_apply]; exact hy⟩
  obtain ⟨W, hW, h⟩ := kp_family_lattice (linearAct ρ) A hA' r hr
  refine ⟨W, fun g => ?_, h⟩
  rw [← linearAct_apply]
  exact hW g

end Families

open Module in
/-- **(S1) Theorem A, one-sided form, families, with a polynomial bound** (the statement of
`Challenge/StatementFull.lean`, verbatim). Any group `G`, any `G`-set `X`, any equivariant family
`A_x`, any dimension,
any division ring. If `dim A_x / (A_x ∩ A_y) ≤ r` for all `x, y`, there is a `G`-invariant `W` with
`dim W / (W ∩ A_x) ≤ r` and `dim A_x / (W ∩ A_x) ≤ r (r + 1)` for every `x`. -/
theorem kp_family_one_sided {K V G X : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [Group G] [MulAction G X] (ρ : G →* (V ≃ₗ[K] V)) (A : X → Submodule K V)
    (hA : ∀ (g : G) (x : X), A (g • x) = (A x).map (ρ g : V →ₗ[K] V)) (r : ℕ)
    (hr : ∀ x y : X, Module.rank K (A x ⧸ (A y).submoduleOf (A x)) ≤ r) :
    ∃ W : Submodule K V, (∀ g : G, W.map (ρ g : V →ₗ[K] V) = W) ∧
      ∀ x : X, Module.rank K (W ⧸ (A x).submoduleOf W) ≤ r ∧
        Module.rank K (A x ⧸ W.submoduleOf (A x)) ≤ (r * (r + 1) : ℕ) := by
  have hr' : ∀ x y, Module.length K (A x ⧸ (A y).submoduleOf (A x)) ≤ r := by
    intro x y
    rw [Module.length_eq_rank, Cardinal.toENat_le_natCast]
    exact hr x y
  obtain ⟨W, hW, h⟩ := kp_family_one_sided_module ρ A (fun g x => ⟨g • x, (hA g x).symm⟩) r hr'
  refine ⟨W, hW, fun x => ⟨?_, ?_⟩⟩
  · have h1 := (h x).1
    rw [Module.length_eq_rank, Cardinal.toENat_le_natCast] at h1
    exact h1
  · have h2 := (h x).2
    rw [Module.length_eq_rank, Cardinal.toENat_le_natCast] at h2
    exact h2

end KPFamilies
