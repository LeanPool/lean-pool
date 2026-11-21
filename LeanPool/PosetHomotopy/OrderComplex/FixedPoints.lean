/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PosetHomotopy.OrderComplex.EulerChar
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Euler characteristics of posets with a group action (roadmap 3.5)

Let a finite group `P` act on a finite partial order `T` by monotone maps. If the fixed subposet
of every nontrivial subgroup has alternating chain count `1`, then the alternating chain
count of `T` is congruent to `1` modulo `|P|` (`chainEulerChar_modEq_of_fixedPoints`). This
is a finite-poset variant of K. S. Brown, « Euler characteristics of groups: the p-fractional
part », Invent. Math. 29 (1975), 1–5, Theorem 1. For the fixed order complexes, the chain-count
hypothesis replaces Brown's stronger acyclicity hypothesis.

The route: a chain mapped to itself is fixed pointwise (`mem_ptStab_of_image_eq`), so the chains
fixed by a subgroup `Q` are those of the fixed subposet. Writing `e H` for the signed count of the
chains whose pointwise stabilizer is exactly `H`, the hypothesis reads `Σ_{H ≥ Q} e H = 1` for
`Q ≠ ⊥`; downward induction gives `e ⊤ = 1` and `e Q = 0` for `⊥ < Q < ⊤`, and `e ⊥` is divisible
by `|P|`, since `P` permutes the chains with trivial stabilizer in free orbits.
-/

@[expose] public section

open Finset MulAction

namespace LeanPool.PosetHomotopy

universe u v

variable {P : Type v} {T : Type u} [Group P] [PartialOrder T] [MulAction P T]
  (hmono : ∀ (g : P) (x y : T), x ≤ y → g • x ≤ g • y)

include hmono

theorem smul_le_smul_iff_of_monotone (g : P) {x y : T} : g • x ≤ g • y ↔ x ≤ y :=
  ⟨fun h => by simpa using hmono g⁻¹ _ _ h, hmono g x y⟩

theorem smul_lt_smul_iff_of_monotone (g : P) {x y : T} : g • x < g • y ↔ x < y := by
  simp only [lt_iff_le_not_ge, smul_le_smul_iff_of_monotone hmono]

/-- An element of a finite group acting monotonically fixes every point it moves to a comparable
point. -/
theorem smul_eq_of_smul_le [Finite P] (g : P) (x : T) (h : g • x ≤ x) : g • x = x := by
  by_contra hne
  have hlt : g • x < x := lt_of_le_of_ne h hne
  have key : ∀ n : ℕ, g ^ (n + 1) • x < x := by
    intro n
    induction n with
    | zero => simpa using hlt
    | succ n ih =>
      rw [pow_succ', mul_smul]
      exact lt_of_le_of_lt ((smul_le_smul_iff_of_monotone hmono g).2 ih.le) hlt
  obtain ⟨k, hk, hk'⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  have h' := key (k - 1)
  rw [Nat.sub_add_cancel hk, hk', one_smul] at h'
  exact lt_irrefl _ h'

theorem smul_eq_of_comparable [Finite P] (g : P) (x : T) (h : g • x ≤ x ∨ x ≤ g • x) :
    g • x = x := by
  rcases h with h | h
  · exact smul_eq_of_smul_le hmono g x h
  · have : g⁻¹ • x ≤ x := by simpa using hmono g⁻¹ _ _ h
    have h' := smul_eq_of_smul_le hmono g⁻¹ x this
    rw [inv_smul_eq_iff] at h'
    exact h'.symm

omit hmono [PartialOrder T] in
/-- The pointwise stabilizer of a finite set. -/
def ptStab (σ : Finset T) : Subgroup P := ⨅ x ∈ σ, stabilizer P x

omit hmono [PartialOrder T] in
theorem mem_ptStab {σ : Finset T} {g : P} : g ∈ ptStab σ ↔ ∀ x ∈ σ, g • x = x := by
  simp [ptStab, Subgroup.mem_iInf]

/-- A chain mapped onto itself by an element of a finite group acting monotonically is fixed
pointwise. -/
theorem mem_ptStab_of_image_eq [Finite P] [DecidableEq T] {σ : Finset T}
    (hσ : IsChain (· ≤ ·) (σ : Set T)) {g : P} (h : σ.image (g • ·) = σ) : g ∈ ptStab σ := by
  rw [mem_ptStab]
  intro x hx
  have hgx : g • x ∈ σ := h ▸ Finset.mem_image_of_mem _ hx
  exact smul_eq_of_comparable hmono g x (hσ.total (Finset.mem_coe.2 hgx) (Finset.mem_coe.2 hx))

theorem isChainFinset_image [DecidableEq T] {σ : Finset T} (hσ : IsChainFinset σ) (g : P) :
    IsChainFinset (σ.image (g • ·)) := by
  refine ⟨hσ.1.image _, ?_⟩
  rw [Finset.coe_image]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
  rcases hσ.2.total ha hb with h | h
  · exact Or.inl (hmono g a b h)
  · exact Or.inr (hmono g b a h)

open Classical in
/-- The signed count of the chains with trivial pointwise stabilizer is divisible by `|P|`. -/
theorem card_dvd_sum_ptStab_eq_bot [Fintype P] [Fintype T] :
    (Fintype.card P : ℤ) ∣ ∑ σ ∈ (univ.powerset.filter IsChainFinset).filter
      (fun σ : Finset T => ptStab (P := P) σ = ⊥), (-1 : ℤ) ^ (σ.card + 1) := by
  classical
  set D := (univ.powerset.filter IsChainFinset).filter
    (fun σ : Finset T => ptStab (P := P) σ = ⊥)
  have hD : ∀ σ ∈ D, ∀ g : P, σ.image (g • ·) ∈ D := by
    intro σ hσ g
    simp only [D, Finset.mem_filter, Finset.mem_powerset] at hσ ⊢
    refine ⟨⟨Finset.subset_univ _, isChainFinset_image hmono hσ.1.2 g⟩, ?_⟩
    rw [eq_bot_iff]
    intro h hh
    have : g⁻¹ * h * g ∈ ptStab (P := P) σ := by
      rw [mem_ptStab] at hh ⊢
      intro x hx
      have := hh (g • x) (Finset.mem_image_of_mem _ hx)
      rw [mul_smul, mul_smul, this, inv_smul_smul]
    rw [hσ.2, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    have h' : g * (g⁻¹ * h * g) * g⁻¹ = 1 := by rw [this, mul_one, mul_inv_cancel]
    simpa [mul_assoc] using h'
  let X := {σ // σ ∈ D}
  let act : MulAction P X :=
    { smul g σ := ⟨σ.1.image (g • ·), hD σ.1 σ.2 g⟩
      one_smul σ := Subtype.ext (by
        change σ.1.image ((1 : P) • ·) = σ.1
        simp)
      mul_smul g h σ := Subtype.ext (by
        change σ.1.image ((g * h) • ·) = (σ.1.image (h • ·)).image (g • ·)
        rw [Finset.image_image]
        congr 1
        funext x
        exact mul_smul g h x) }
  have hcard : ∀ (g : P) (σ : X), (g • σ).1.card = σ.1.card := fun g σ =>
    Finset.card_image_of_injective _ (MulAction.injective g)
  have hstab : ∀ σ : X, stabilizer P σ = ⊥ := by
    intro σ
    rw [eq_bot_iff]
    intro g hg
    have himg : σ.1.image (g • ·) = σ.1 := congrArg Subtype.val (mem_stabilizer_iff.1 hg)
    have hσ := σ.2
    simp only [D, Finset.mem_filter] at hσ
    have := mem_ptStab_of_image_eq hmono hσ.1.2.2 himg
    rwa [hσ.2] at this
  rw [← Finset.sum_coe_sort D]
  change (Fintype.card P : ℤ) ∣ ∑ σ : X, (-1 : ℤ) ^ (σ.1.card + 1)
  rw [← (selfEquivSigmaOrbits P X).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have hconst : ∀ y : orbit P ω.out,
      (-1 : ℤ) ^ (((selfEquivSigmaOrbits P X).symm ⟨ω, y⟩).1.card + 1) =
        (-1 : ℤ) ^ (ω.out.1.card + 1) := by
    intro y
    obtain ⟨g, hg⟩ := y.2
    change (-1 : ℤ) ^ ((y : X).1.card + 1) = _
    rw [← hg, hcard]
  rw [Finset.sum_congr rfl fun y _ => hconst y, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ]
  have h := card_orbit_mul_card_stabilizer_eq_card_group P ω.out
  have h1 : Fintype.card (stabilizer P ω.out) = 1 :=
    Fintype.card_eq_one_iff.2 ⟨1, fun x => Subtype.ext (by
      have hx : (x : P) ∈ (⊥ : Subgroup P) := hstab ω.out ▸ x.2
      exact Subgroup.mem_bot.1 hx)⟩
  rw [h1, mul_one] at h
  rw [h]
  exact dvd_mul_right _ _

/-- **Roadmap 3.5.** If a finite group `P` acts monotonically on a finite partial order `T` and
the fixed subposet of every nontrivial subgroup has Euler characteristic `1`, then the Euler
characteristic of `T` is congruent to `1` modulo `|P|`. -/
theorem chainEulerChar_modEq_of_fixedPoints [Finite P] [Finite T]
    (h : ∀ Q : Subgroup P, Q ≠ ⊥ → chainEulerChar {x : T // ∀ g ∈ Q, g • x = x} = 1) :
    chainEulerChar T ≡ 1 [ZMOD (Nat.card P : ℤ)] := by
  classical
  by_cases hP : Nontrivial P
  swap
  · rw [not_nontrivial_iff_subsingleton] at hP
    rw [Nat.card_eq_one_iff_unique.2 ⟨hP, ⟨1⟩⟩, Nat.cast_one]
    exact Int.modEq_one
  let := Fintype.ofFinite T
  let := Fintype.ofFinite P
  have : Finite (Subgroup P) := Finite.of_injective _ SetLike.coe_injective
  let := Fintype.ofFinite (Subgroup P)
  set C := (univ : Finset T).powerset.filter IsChainFinset with hC
  -- the signed count of the chains with pointwise stabilizer exactly `H`
  set e : Subgroup P → ℤ := fun H =>
    ∑ σ ∈ C.filter (fun σ => ptStab (P := P) σ = H), (-1 : ℤ) ^ (σ.card + 1) with he
  have hF : ∀ Q : Subgroup P, chainEulerChar {x : T // ∀ g ∈ Q, g • x = x} =
      ∑ H ∈ univ.filter (Q ≤ ·), e H := by
    intro Q
    rw [chainEulerChar_subtype]
    unfold chainSum
    have hfilter : (univ.filter fun x : T => ∀ g ∈ Q, g • x = x).powerset.filter IsChainFinset =
        C.filter fun σ => Q ≤ ptStab (P := P) σ := by
      ext σ
      simp only [hC, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hσ, hch⟩
        exact ⟨⟨Finset.subset_univ _, hch⟩, fun g hg => mem_ptStab.2 fun x hx =>
          (Finset.mem_filter.1 (hσ hx)).2 g hg⟩
      · rintro ⟨⟨-, hch⟩, hσ⟩
        exact ⟨fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, fun g hg =>
          mem_ptStab.1 (hσ hg) x hx⟩, hch⟩
    rw [hfilter, ← Finset.sum_fiberwise_of_maps_to (g := fun σ => ptStab (P := P) σ)
      (t := univ.filter (Q ≤ ·)) (fun σ hσ => by
        simpa using (Finset.mem_filter.1 hσ).2)]
    refine Finset.sum_congr rfl fun H hH => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext σ
    simp only [Finset.mem_filter]
    have hQH := (Finset.mem_filter.1 hH).2
    constructor
    · rintro ⟨h₁, -, h₂⟩; exact ⟨h₁, h₂⟩
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, h₂ ▸ hQH, h₂⟩
  have hind : ∀ Q : Subgroup P, Q ≠ ⊥ → e Q = if Q = ⊤ then 1 else 0 := by
    intro Q
    induction Q using WellFoundedGT.induction with
    | ind Q ih =>
      intro hQ
      have h1 : ∑ H ∈ univ.filter (Q ≤ ·), e H = 1 := (hF Q).symm.trans (h Q hQ)
      have hmem : Q ∈ univ.filter (Q ≤ ·) := by simp
      rw [← Finset.add_sum_erase _ _ hmem] at h1
      have hgt : ∑ H ∈ (univ.filter (Q ≤ ·)).erase Q, e H = if Q = ⊤ then 0 else 1 := by
        have : ∀ H ∈ (univ.filter (Q ≤ ·)).erase Q, e H = if H = ⊤ then 1 else 0 := by
          intro H hH
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hH
          have hlt : Q < H := lt_of_le_of_ne hH.2 (Ne.symm hH.1)
          exact ih H hlt (ne_bot_of_gt hlt)
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, le_top, and_true]
        by_cases hQt : Q = ⊤
        · simp [hQt]
        · simp [hQt, Ne.symm hQt]
      rw [hgt] at h1
      by_cases hQt : Q = ⊤
      · simp only [hQt, ↓reduceIte, add_zero] at h1 ⊢; exact h1
      · simp only [hQt, ↓reduceIte] at h1 ⊢; linarith
  have hsum : chainEulerChar T = ∑ H : Subgroup P, e H := by
    rw [chainEulerChar_eq_chainSum]
    unfold chainSum
    exact (Finset.sum_fiberwise_of_maps_to (g := fun σ => ptStab (P := P) σ) (t := univ)
      (fun _ _ => Finset.mem_univ _) _).symm
  have hbot : (⊥ : Subgroup P) ≠ ⊤ := bot_ne_top
  have hrest : ∑ H ∈ (univ : Finset (Subgroup P)).erase ⊥, e H = 1 := by
    have : ∀ H ∈ (univ : Finset (Subgroup P)).erase ⊥, e H = if H = ⊤ then 1 else 0 :=
      fun H hH => hind H (Finset.mem_erase.1 hH).1
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp [Ne.symm hbot]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⊥), hrest, Int.modEq_iff_dvd,
    Nat.card_eq_fintype_card]
  have hdiv := card_dvd_sum_ptStab_eq_bot (P := P) hmono
  rw [show (1 : ℤ) - (e ⊥ + 1) = -e ⊥ by ring]
  exact (dvd_neg).2 hdiv

end LeanPool.PosetHomotopy
