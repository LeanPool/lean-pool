/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — Beck–Fiala rounding for hypergraph degree profiles

A deterministic rounding theorem in the style of Beck–Fiala: if every edge of a hypergraph `H`
meets at most `k` vertices, then any fractional selection `y : H → [0,1]` can be rounded to an
integral selection `S ⊆ H` whose vertex degrees agree with the fractional degrees up to an additive
error `k` — *independently of the size of `H`*.

* `Nibble.BeckFiala.floating` — the edges whose fractional value is neither `0` nor `1`.
* `Nibble.BeckFiala.exists_step` — one step of the iterative rounding: move along a nonzero vector
  in the kernel of the *active* constraints (those meeting more than `k` floating edges) until some
  floating value hits `0` or `1`.  Active degrees are preserved exactly and the number of floating
  edges strictly drops.
* `Nibble.BeckFiala.exists_rounding` — the rounding theorem, by induction on the number of floating
  edges.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Fractional rounding with bounded incidence discrepancy -/

@[expose] public section

open Finset

namespace Nibble.BeckFiala

variable {V : Type*} [DecidableEq V]

/-- The **floating** edges of a fractional selection: those whose value is neither `0` nor `1`. -/
noncomputable def floating (H : Finset (Finset V)) (y : Finset V → ℝ) : Finset (Finset V) :=
  H.filter (fun t => y t ≠ 0 ∧ y t ≠ 1)

omit [DecidableEq V] in
theorem floating_subset (H : Finset (Finset V)) (y : Finset V → ℝ) : floating H y ⊆ H :=
  Finset.filter_subset _ _

omit [DecidableEq V] in
theorem notMem_floating_iff {H : Finset (Finset V)} {y : Finset V → ℝ} {t : Finset V}
    (ht : t ∈ H) : t ∉ floating H y ↔ y t = 0 ∨ y t = 1 := by
  unfold floating
  simp only [Finset.mem_filter, ht, true_and, not_and_or, not_not]

/-- The **active** vertices of a floating set: those meeting more than `k` floating edges. -/
noncomputable def active (F : Finset (Finset V)) (k : ℕ) : Finset V :=
  (F.biUnion id).filter (fun x => k < (F.filter (fun t => x ∈ t)).card)

theorem mem_active_iff {F : Finset (Finset V)} {k : ℕ} {x : V} :
    x ∈ active F k ↔ k < (F.filter (fun t => x ∈ t)).card := by
  unfold active
  simp only [Finset.mem_filter, Finset.mem_biUnion, id]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) h)
    rw [Finset.mem_filter] at ht
    exact ⟨t, ht.1, ht.2⟩

/-- **Few active vertices.**  If every edge of the floating family meets at most `k` vertices and
the family is nonempty, then there are strictly fewer active vertices than floating edges. -/
theorem card_active_lt {F : Finset (Finset V)} {k : ℕ} (hk : ∀ t ∈ F, t.card ≤ k)
    (hF : F.Nonempty) : (active F k).card < F.card := by
  have hcount : ∑ x ∈ active F k, (F.filter (fun t => x ∈ t)).card
      ≤ ∑ t ∈ F, ((active F k).filter (fun x => x ∈ t)).card := by
    have h1 : ∀ x : V, (F.filter (fun t => x ∈ t)).card
        = ∑ t ∈ F, if x ∈ t then 1 else 0 := by
      intro x; rw [Finset.card_filter]
    have h2 : ∀ t : Finset V, ((active F k).filter (fun x => x ∈ t)).card
        = ∑ x ∈ active F k, if x ∈ t then 1 else 0 := by
      intro t; rw [Finset.card_filter]
    simp only [h1, h2]
    rw [Finset.sum_comm]
  have hle : ∑ t ∈ F, ((active F k).filter (fun x => x ∈ t)).card ≤ F.card * k := by
    calc ∑ t ∈ F, ((active F k).filter (fun x => x ∈ t)).card
        ≤ ∑ t ∈ F, k := by
          refine Finset.sum_le_sum fun t ht => ?_
          refine le_trans (Finset.card_le_card ?_) (hk t ht)
          intro x hx
          exact (Finset.mem_filter.mp hx).2
      _ = F.card * k := by rw [Finset.sum_const, smul_eq_mul]
  have hlow : (active F k).card * (k + 1) ≤ ∑ x ∈ active F k, (F.filter (fun t => x ∈ t)).card := by
    calc (active F k).card * (k + 1) = ∑ _x ∈ active F k, (k + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ active F k, (F.filter (fun t => x ∈ t)).card :=
          Finset.sum_le_sum fun x hx => mem_active_iff.mp hx
  have hFpos : 0 < F.card := Finset.card_pos.mpr hF
  nlinarith [hcount, hle, hlow]

/-- Existence of a nonzero vector annihilated by all active constraints. -/
theorem exists_kernel_vector {F : Finset (Finset V)} {k : ℕ} (hk : ∀ t ∈ F, t.card ≤ k)
    (hF : F.Nonempty) :
    ∃ U : Finset V → ℝ, (∀ t, t ∉ F → U t = 0) ∧ (∃ t ∈ F, U t ≠ 0) ∧
      ∀ x ∈ active F k, ∑ t ∈ F.filter (fun t => x ∈ t), U t = 0 := by
  set A : Finset V := active F k with hA
  have hcard : Fintype.card {x // x ∈ A} < Fintype.card {t // t ∈ F} := by
    simpa [Fintype.card_coe] using card_active_lt hk hF
  -- the constraint map
  let φ : ({t // t ∈ F} → ℝ) →ₗ[ℝ] ({x // x ∈ A} → ℝ) :=
    { toFun := fun u x => ∑ t : {t // t ∈ F}, if (x : V) ∈ (t : Finset V) then u t else 0
      map_add' := by
        intro u v
        funext x
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun t _ => by by_cases h : (x : V) ∈ (t : Finset V) <;> simp [h]
      map_smul' := by
        intro c u
        funext x
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by
          by_cases h : (x : V) ∈ (t : Finset V) <;> simp [h] }
  have hker : ∃ u : {t // t ∈ F} → ℝ, u ≠ 0 ∧ φ u = 0 := by
    by_contra hc
    push Not at hc
    have hinj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro m hm
      by_contra hm0
      exact (hc m hm0 hm).elim
    have := LinearMap.finrank_le_finrank_of_injective (f := φ) hinj
    simp only [Module.finrank_fintype_fun_eq_card] at this
    omega
  obtain ⟨u, hu0, huker⟩ := hker
  refine ⟨fun t => if h : t ∈ F then u ⟨t, h⟩ else 0, ?_, ?_, ?_⟩
  · intro t ht; simp [ht]
  · by_contra hcon
    push Not at hcon
    apply hu0
    funext t
    have := hcon t.1 t.2
    simpa using this
  · intro x hx
    have hker0 := congrFun huker ⟨x, hx⟩
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hker0
    change ∑ t ∈ F.filter (fun t => x ∈ t), (if h : t ∈ F then u ⟨t, h⟩ else 0) = 0
    calc ∑ t ∈ F.filter (fun t => x ∈ t), (if h : t ∈ F then u ⟨t, h⟩ else 0)
        = ∑ t : {t // t ∈ F}, (if (x : V) ∈ (t : Finset V) then u t else 0) := by
          rw [Finset.sum_filter, ← Finset.sum_coe_sort F
            (fun s => if x ∈ s then (if h : s ∈ F then u ⟨s, h⟩ else 0) else 0)]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases h : (x : V) ∈ (t : Finset V) <;> simp [h, t.2]
      _ = 0 := hker0

/-- **One rounding step.**  Given a fractional selection with a nonempty floating set, there is
another one with strictly fewer floating edges, which agrees with the old one off the floating set
and has exactly the same degree at every active vertex. -/
theorem exists_step (k : ℕ) (H : Finset (Finset V)) (hk : ∀ t ∈ H, t.card ≤ k)
    (y : Finset V → ℝ) (hy0 : ∀ t ∈ H, 0 ≤ y t) (hy1 : ∀ t ∈ H, y t ≤ 1)
    (hF : (floating H y).Nonempty) :
    ∃ y' : Finset V → ℝ, (∀ t ∈ H, 0 ≤ y' t) ∧ (∀ t ∈ H, y' t ≤ 1) ∧
      (∀ t, t ∉ floating H y → y' t = y t) ∧
      (floating H y').card < (floating H y).card ∧
      (∀ x : V, k < ((floating H y).filter (fun t => x ∈ t)).card →
        ∑ t ∈ H.filter (fun t => x ∈ t), y' t = ∑ t ∈ H.filter (fun t => x ∈ t), y t) := by
  set F := floating H y with hFdef
  have hFH : F ⊆ H := floating_subset H y
  have hkF : ∀ t ∈ F, t.card ≤ k := fun t ht => hk t (hFH ht)
  -- strict bounds on floating values
  have hstrict : ∀ t ∈ F, 0 < y t ∧ y t < 1 := by
    intro t ht
    rw [hFdef, floating, Finset.mem_filter] at ht
    obtain ⟨htH, hne0, hne1⟩ := ht
    exact ⟨lt_of_le_of_ne (hy0 t htH) (Ne.symm hne0), lt_of_le_of_ne (hy1 t htH) hne1⟩
  obtain ⟨U, hUoff, ⟨t₁, ht₁F, ht₁ne⟩, hUker⟩ := exists_kernel_vector hkF hF
  -- the support of `U`
  set P : Finset (Finset V) := F.filter (fun t => U t ≠ 0) with hPdef
  have hPne : P.Nonempty := ⟨t₁, Finset.mem_filter.mpr ⟨ht₁F, ht₁ne⟩⟩
  set c : Finset V → ℝ := fun t => if 0 < U t then (1 - y t) / U t else (-(y t)) / U t with hcdef
  have hcpos : ∀ t ∈ P, 0 < c t := by
    intro t ht
    rw [hPdef, Finset.mem_filter] at ht
    obtain ⟨htF, htU⟩ := ht
    obtain ⟨hy0t, hy1t⟩ := hstrict t htF
    rw [hcdef]
    by_cases h : 0 < U t
    · simp only [h, ite_true]; exact div_pos (by linarith) h
    · simp only [h, ite_false]
      have hUneg : U t < 0 := lt_of_le_of_ne (not_lt.mp h) htU
      exact div_pos_of_neg_of_neg (by linarith) hUneg
  set lam : ℝ := (P.image c).min' (hPne.image c) with hlamdef
  have hlammem : lam ∈ P.image c := Finset.min'_mem _ _
  obtain ⟨t₀, ht₀P, ht₀c⟩ := Finset.mem_image.mp hlammem
  have hlampos : 0 < lam := by rw [← ht₀c]; exact hcpos t₀ ht₀P
  have hlamle : ∀ t ∈ P, lam ≤ c t := fun t ht =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem c ht)
  refine ⟨fun t => y t + lam * U t, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro t ht
    change (0 : ℝ) ≤ y t + lam * U t
    by_cases htF : t ∈ F
    · by_cases hU : U t = 0
      · simp only [hU, mul_zero, add_zero]; exact hy0 t ht
      · have htP : t ∈ P := Finset.mem_filter.mpr ⟨htF, hU⟩
        rcases lt_trichotomy (U t) 0 with hneg | hzero | hpos
        · have hc : c t = (-(y t)) / U t := by rw [hcdef]; simp [not_lt.mpr hneg.le]
          have h1 : lam * U t ≥ c t * U t := by
            have := hlamle t htP
            nlinarith only [hneg, this]
          have h2 : c t * U t = -(y t) := by
            rw [hc]; field_simp
          linarith only [h1, h2]
        · exact absurd hzero hU
        · have := hy0 t ht
          nlinarith [hlampos.le]
    · rw [hUoff t htF]; simpa using hy0 t ht
  · -- ≤ 1
    intro t ht
    change y t + lam * U t ≤ 1
    by_cases htF : t ∈ F
    · by_cases hU : U t = 0
      · simp only [hU, mul_zero, add_zero]; exact hy1 t ht
      · have htP : t ∈ P := Finset.mem_filter.mpr ⟨htF, hU⟩
        rcases lt_trichotomy (U t) 0 with hneg | hzero | hpos
        · have := hy1 t ht
          nlinarith [hlampos.le]
        · exact absurd hzero hU
        · have hc : c t = (1 - y t) / U t := by rw [hcdef]; simp [hpos]
          have h1 : lam * U t ≤ c t * U t := by
            have := hlamle t htP
            nlinarith only [hpos, this]
          have h2 : c t * U t = 1 - y t := by rw [hc]; field_simp
          linarith only [h1, h2]
    · rw [hUoff t htF]; simpa using hy1 t ht
  · intro t ht
    change y t + lam * U t = y t
    rw [hUoff t ht]; ring
  · -- fewer floating
    have ht₀F : t₀ ∈ F := (Finset.mem_filter.mp ht₀P).1
    have ht₀U : U t₀ ≠ 0 := (Finset.mem_filter.mp ht₀P).2
    have ht₀fix : y t₀ + lam * U t₀ = 0 ∨ y t₀ + lam * U t₀ = 1 := by
      rcases lt_trichotomy (U t₀) 0 with hneg | hzero | hpos
      · left
        have hc : c t₀ = (-(y t₀)) / U t₀ := by rw [hcdef]; simp [not_lt.mpr hneg.le]
        have : lam * U t₀ = -(y t₀) := by
          rw [← ht₀c, hc]; field_simp
        linarith only [this]
      · exact absurd hzero ht₀U
      · right
        have hc : c t₀ = (1 - y t₀) / U t₀ := by rw [hcdef]; simp [hpos]
        have : lam * U t₀ = 1 - y t₀ := by
          rw [← ht₀c, hc]; field_simp
        linarith only [this]
    have hsub : floating H (fun t => y t + lam * U t) ⊆ F.erase t₀ := by
      intro t ht
      rw [floating, Finset.mem_filter] at ht
      obtain ⟨htH, hne0, hne1⟩ := ht
      have htF : t ∈ F := by
        by_contra hcon
        rw [hUoff t hcon] at hne0 hne1
        simp only [mul_zero, add_zero] at hne0 hne1
        rcases (notMem_floating_iff (y := y) htH).mp hcon with h | h
        · exact hne0 h
        · exact hne1 h
      refine Finset.mem_erase.mpr ⟨?_, htF⟩
      rintro rfl
      rcases ht₀fix with h | h
      · exact hne0 h
      · exact hne1 h
    calc (floating H (fun t => y t + lam * U t)).card ≤ (F.erase t₀).card :=
          Finset.card_le_card hsub
      _ < F.card := Finset.card_erase_lt_of_mem ht₀F
  · -- active degrees preserved
    intro x hx
    change ∑ t ∈ H.filter (fun t => x ∈ t), (y t + lam * U t) = _
    have hxA : x ∈ active F k := mem_active_iff.mpr hx
    have hzero := hUker x hxA
    have hsplit : ∑ t ∈ H.filter (fun t => x ∈ t), (y t + lam * U t)
        = ∑ t ∈ H.filter (fun t => x ∈ t), y t
          + lam * ∑ t ∈ H.filter (fun t => x ∈ t), U t := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit]
    have hUH : ∑ t ∈ H.filter (fun t => x ∈ t), U t
        = ∑ t ∈ F.filter (fun t => x ∈ t), U t := by
      refine (Finset.sum_subset (Finset.filter_subset_filter _ hFH) ?_).symm
      intro t ht htn
      rw [Finset.mem_filter] at ht
      have : t ∉ F := by
        intro hcon
        exact htn (Finset.mem_filter.mpr ⟨hcon, ht.2⟩)
      exact hUoff t this
    rw [hUH, hzero, mul_zero, add_zero]

/-- **Beck–Fiala rounding.**  If every edge of `H` has at most `k` vertices, every fractional
selection `y : H → [0,1]` can be rounded to a subfamily `S ⊆ H` (keeping the edges of value `1` and
discarding those of value `0`) whose degree at every vertex differs from the fractional degree by at
most `k`. -/
theorem exists_rounding (k : ℕ) (H : Finset (Finset V)) (hk : ∀ t ∈ H, t.card ≤ k)
    (y : Finset V → ℝ) (hy0 : ∀ t ∈ H, 0 ≤ y t) (hy1 : ∀ t ∈ H, y t ≤ 1) :
    ∃ S ⊆ H, (∀ t ∈ H, y t = 1 → t ∈ S) ∧ (∀ t ∈ H, y t = 0 → t ∉ S) ∧
      ∀ x : V, |((S.filter (fun t => x ∈ t)).card : ℝ)
        - ∑ t ∈ H.filter (fun t => x ∈ t), y t| ≤ k := by
  generalize hn : (floating H y).card = n
  induction n using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · -- no floating edges: take the edges of value 1
      refine ⟨H.filter (fun t => y t = 1), Finset.filter_subset _ _, ?_, ?_, ?_⟩
      · intro t ht h1; exact Finset.mem_filter.mpr ⟨ht, h1⟩
      · intro t ht h0 hmem
        have := (Finset.mem_filter.mp hmem).2
        rw [h0] at this; norm_num at this
      · intro x
        have hempty : floating H y = ∅ := Finset.card_eq_zero.mp hn
        have hval : ∀ t ∈ H, y t = 0 ∨ y t = 1 := by
          intro t ht
          refine (notMem_floating_iff ht).mp ?_
          rw [hempty]; exact Finset.notMem_empty t
        have hsum : (((H.filter (fun t => y t = 1)).filter (fun t => x ∈ t)).card : ℝ)
            = ∑ t ∈ H.filter (fun t => x ∈ t), y t := by
          rw [Finset.filter_comm, Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl fun t ht => ?_
          have htH := (Finset.mem_filter.mp ht).1
          rcases hval t htH with h0 | h1
          · simp [h0]
          · simp [h1]
        rw [hsum, sub_self, abs_zero]
        exact Nat.cast_nonneg k
    · -- at least one floating edge: take a rounding step
      have hFne : (floating H y).Nonempty := by
        rw [← Finset.card_pos, hn]; exact hnpos
      obtain ⟨y', hy'0, hy'1, hoff, hlt, hact⟩ := exists_step k H hk y hy0 hy1 hFne
      obtain ⟨S, hSH, hS1, hS0, hSbound⟩ :=
        ih (floating H y').card (by omega) y' hy'0 hy'1 rfl
      refine ⟨S, hSH, ?_, ?_, ?_⟩
      · intro t ht h1
        refine hS1 t ht ?_
        rw [hoff t ((notMem_floating_iff ht).mpr (Or.inr h1))]; exact h1
      · intro t ht h0
        refine hS0 t ht ?_
        rw [hoff t ((notMem_floating_iff ht).mpr (Or.inl h0))]; exact h0
      · intro x
        by_cases hxa : k < ((floating H y).filter (fun t => x ∈ t)).card
        · rw [← hact x hxa]; exact hSbound x
        · -- inactive vertex: bound the error directly
          push Not at hxa
          have hfset : (H.filter (fun t => x ∈ t)).filter (fun t => t ∈ S)
              = S.filter (fun t => x ∈ t) := by
            ext t
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨⟨-, hx⟩, hS⟩; exact ⟨hS, hx⟩
            · rintro ⟨hS, hx⟩; exact ⟨⟨hSH hS, hx⟩, hS⟩
          have hrepr : ((S.filter (fun t => x ∈ t)).card : ℝ)
              = ∑ t ∈ H.filter (fun t => x ∈ t), (if t ∈ S then (1 : ℝ) else 0) := by
            rw [← hfset, Finset.card_filter]
            push_cast
            rfl
          rw [hrepr, ← Finset.sum_sub_distrib]
          have hterm : ∀ t ∈ H.filter (fun t => x ∈ t),
              |(if t ∈ S then (1 : ℝ) else 0) - y t|
                ≤ (if t ∈ floating H y then (1 : ℝ) else 0) := by
            intro t ht
            have htH := (Finset.mem_filter.mp ht).1
            by_cases hfl : t ∈ floating H y
            · simp only [hfl, ite_true]
              have h0 := hy0 t htH
              have h1 := hy1 t htH
              by_cases hS : t ∈ S <;> simp only [hS, ite_true, ite_false] <;>
                rw [abs_le] <;> constructor <;> linarith
            · simp only [hfl, ite_false]
              rcases (notMem_floating_iff htH).mp hfl with h | h
              · have hy' : y' t = 0 := by rw [hoff t hfl]; exact h
                have : t ∉ S := hS0 t htH hy'
                simp [this, h]
              · have hy' : y' t = 1 := by rw [hoff t hfl]; exact h
                have : t ∈ S := hS1 t htH hy'
                simp [this, h]
          calc |∑ t ∈ H.filter (fun t => x ∈ t), ((if t ∈ S then (1 : ℝ) else 0) - y t)|
              ≤ ∑ t ∈ H.filter (fun t => x ∈ t), |(if t ∈ S then (1 : ℝ) else 0) - y t| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ t ∈ H.filter (fun t => x ∈ t), (if t ∈ floating H y then (1 : ℝ) else 0) :=
                Finset.sum_le_sum hterm
            _ = (((H.filter (fun t => x ∈ t)).filter (fun t => t ∈ floating H y)).card : ℝ) := by
                rw [Finset.card_filter]; push_cast; rfl
            _ = (((floating H y).filter (fun t => x ∈ t)).card : ℝ) := by
                congr 1
                congr 1
                ext t
                simp only [Finset.mem_filter]
                constructor
                · rintro ⟨⟨-, hx⟩, hf⟩; exact ⟨hf, hx⟩
                · rintro ⟨hf, hx⟩; exact ⟨⟨floating_subset H y hf, hx⟩, hf⟩
            _ ≤ (k : ℝ) := by exact_mod_cast hxa

end Nibble.BeckFiala
