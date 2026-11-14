/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.RingTheory.GradedAlgebra.Radical

public import Mathlib.Tactic.Common
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.HData

/-!
# Hyperplane sections and prime filtrations

* `hilb_top`: the unit ideal has Hilbert function `0`.
* `hilb_hasData_or_zero`: the Hilbert function of a homogeneous ideal is eventually zero or has data
  `(a, c)` with `c > 0`.
* `hilb_section`: **hyperplane section** (Philippon, Lemma 3.1). Let `f` be homogeneous of degree
  `e ≥ 1` and a non-zero-divisor mod `J`, i.e. `(J : f) = J`. If `hilb J` has data `(a+1, c)`, then
  `hilb (J + (f))` has data `(a, e c)`. If `hilb J` has data `(0, c)`, then `hilb (J + (f))` is
  eventually zero.
* `exists_assoc_prime`: a homogeneous `J ≠ (1)` has a homogeneous `g ∉ J` with `(J : g)` prime.
* `hilb_filtration`: **prime filtration**. For homogeneous `J` there are homogeneous primes
  `P₁, …, P_r ⊇ J` and shifts `a_i` with `hilb J k = Σ hilb P_i (k − a_i)` for large `k`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

/-! ### More on data -/

theorem HasData.shiftR {f : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c) (e : ℕ) :
    HasData (fun k => f (k - e)) a c :=
  HasData.of_shiftN (e := e) (by simpa using h)

theorem hasData_congr {f g : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c)
    (hfg : ∀ᶠ k in Filter.atTop, f k = g k) : HasData g a c := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hfg
  have hsh : (fun k => g (k + k0)) = fun k => f (k + k0) := funext fun k => (hk0 _ (by omega)).symm
  apply HasData.of_shiftN (e := k0)
  rw [hsh]
  refine ⟨h.1, ?_⟩
  have hshiftN : ∀ (n : ℕ) (h : ℕ → ℤ), Δ^[n] (fun k => h (k + k0)) = fun k => (Δ^[n] h) (k +
    k0) := by
    intro n
    induction n with
    | zero => intro h; rfl
    | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        show Δ (fun k => h (k + k0)) = fun k => Δ h (k + k0) from by
          funext k; change h (k + 1 + k0) - h (k + k0) = h (k + k0 + 1) - h (k + k0); ring_nf, ih]
  rw [hshiftN]
  obtain ⟨k1, hk1⟩ := Filter.eventually_atTop.mp h.2
  exact Filter.eventually_atTop.mpr ⟨k1, fun k hk => hk1 _ (by omega)⟩

theorem HasData.add_zero {f g : ℕ → ℤ} {a : ℕ} {c : ℤ} (h : HasData f a c)
    (hg : ∀ᶠ k in Filter.atTop, g k = 0) : HasData (f + g) a c :=
  hasData_congr h (by filter_upwards [hg] with k hk; simp [hk])

theorem HasData.add_lt {f g : ℕ → ℤ} {a b : ℕ} {c d : ℤ} (hf : HasData f a c) (hg : HasData g b d)
    (hab : a < b) : HasData (f + g) b d := by
  refine ⟨hg.1, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have hz := iter_Δ_const hf.2 (j + 1) (by omega)
  filter_upwards [hz, hg.2] with k h1 h2
  rw [show a + (j + 1) = a + j + 1 by ring] at h1
  rw [iter_Δ_add, Pi.add_apply, h1, h2, zero_add]

theorem HasData.add_eq {f g : ℕ → ℤ} {a : ℕ} {c d : ℤ} (hf : HasData f a c) (hg : HasData g a d)
    (hcd : c + d ≠ 0) : HasData (f + g) a (c + d) := by
  refine ⟨hcd, ?_⟩
  filter_upwards [hf.2, hg.2] with k h1 h2
  rw [iter_Δ_add, Pi.add_apply, h1, h2]

variable {K : Type*} [Field K] {m : ℕ}

local notation "A" => MvPolynomial (Fin m) K

/-! ### Basic facts on `hilb` -/

theorem Jdeg_top (k : ℕ) : Jdeg (⊤ : Ideal A) k = Adeg K m k := by
  simp [Jdeg]

theorem hilb_top (k : ℕ) : hilb (⊤ : Ideal A) k = 0 := by
  rw [hilb, Jdeg_top, Nat.sub_self]

/-- The Hilbert function of a homogeneous ideal is eventually zero or has positive degree. -/
theorem hilb_hasData_or_zero (J : Ideal A) (hJ : HomIdeal J) :
    (∀ᶠ k in Filter.atTop, (hilb J k : ℤ) = 0) ∨
      ∃ a c, 0 < c ∧ HasData (fun k => (hilb J k : ℤ)) a c := by
  by_cases h : ∀ᶠ k in Filter.atTop, (hilb J k : ℤ) = 0
  · exact Or.inl h
  · obtain ⟨a, c, hd⟩ := HasData.exists (hilb_evPoly J hJ) h
    exact Or.inr ⟨a, c, hd.pos (Filter.Eventually.of_forall fun k => by positivity), hd⟩

/-! ### Hyperplane sections (Philippon, Lemma 3.1) -/

/-- **Hyperplane section.** If `f` (homogeneous of degree `e ≥ 1`) is a non-zero-divisor modulo `J`
and `hilb J` has dimension `a + 1` and degree `c`, then `hilb (J + (f))` has dimension `a` and
degree
`e c`. -/
theorem hilb_section {J : Ideal A} (hJ : HomIdeal J) {f : A} {e : ℕ} (hf : f.IsHomogeneous e)
    (hf0 : f ≠ 0) (he : 1 ≤ e) (hnzd : colonX J f = J) {a : ℕ} {c : ℤ}
    (hd : HasData (fun k => (hilb J k : ℤ)) (a + 1) c) :
    HasData (fun k => (hilb (J ⊔ Ideal.span {f}) k : ℤ)) a (e * c) := by
  refine HasData.of_sub_shift he hd fun k => ?_
  have := hilb_colon_hom hJ hf hf0 k
  rw [hnzd] at this
  change ((hilb (J ⊔ Ideal.span {f}) (k + e) : ℕ) : ℤ) = (hilb J (k + e) : ℤ) - (hilb J k : ℤ)
  omega

/-- A hyperplane section of a zero-dimensional ideal is eventually zero. -/
theorem hilb_section_zero {J : Ideal A} (hJ : HomIdeal J) {f : A} {e : ℕ} (hf : f.IsHomogeneous e)
    (hf0 : f ≠ 0) (hnzd : colonX J f = J) {c : ℤ}
    (hd : HasData (fun k => (hilb J k : ℤ)) 0 c) :
    ∀ᶠ k in Filter.atTop, (hilb (J ⊔ Ideal.span {f}) k : ℤ) = 0 := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hd.2
  refine Filter.eventually_atTop.mpr ⟨k0 + e, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show e ≤ k by omega)
  have h := hilb_colon_hom hJ hf hf0 j
  rw [hnzd] at h
  have h1 : (hilb J (j + e) : ℤ) = c := hk0 _ (by omega)
  have h2 : (hilb J j : ℤ) = c := hk0 _ (by omega)
  rw [add_comm e j]
  omega

/-! ### Associated primes and prime filtrations -/

section Graded

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homIdeal_iff_isHomogeneous (J : Ideal A) :
    HomIdeal J ↔ J.IsHomogeneous (homogeneousSubmodule (Fin m) K) := by
  constructor
  · intro h i x hx
    have e := decomposition.decompose'_apply (σ := Fin m) (R := K) x i
    change ((DirectSum.decompose (homogeneousSubmodule (Fin m) K) x) i : A) ∈ J
    rw [show ((DirectSum.decompose (homogeneousSubmodule (Fin m) K) x) i : A) =
      homogeneousComponent i x from e]
    exact h x hx i
  · intro h p hp n
    exact homogeneousComponent_mem_of_mem h hp n

/-- A homogeneous ideal is prime as soon as it is prime on homogeneous elements. -/
theorem isPrime_of_hom {P : Ideal A} (hP : HomIdeal P) (hne : P ≠ ⊤)
    (h : ∀ {x y : A} {a b : ℕ}, x.IsHomogeneous a → y.IsHomogeneous b → x * y ∈ P → x ∈ P ∨ y ∈ P) :
    P.IsPrime :=
  ((homIdeal_iff_isHomogeneous P).mp hP).isPrime_of_homogeneous_mem_or_mem hne
    fun ⟨_, ha⟩ ⟨_, hb⟩ hxy => h ((mem_homogeneousSubmodule _ _).mp ha)
      ((mem_homogeneousSubmodule _ _).mp hb) hxy

end Graded

theorem colonX_ne_top {J : Ideal A} {g : A} (hg : g ∉ J) : colonX J g ≠ ⊤ := fun h =>
  hg (by simpa [mem_colonX] using (Ideal.eq_top_iff_one _).mp h)

/-- **Associated primes.** A homogeneous `J ≠ (1)` has a homogeneous `g ∉ J` with `(J : g)`
  prime. -/
theorem exists_assoc_prime {J : Ideal A} (hJ : HomIdeal J) (hne : J ≠ ⊤) :
    ∃ g : A, ∃ e, g.IsHomogeneous e ∧ g ∉ J ∧ (colonX J g).IsPrime := by
  let S : Set (Ideal A) := {Q | ∃ g e, g.IsHomogeneous e ∧ g ∉ J ∧ Q = colonX J g}
  have hS : S.Nonempty := ⟨colonX J 1, 1, 0, isHomogeneous_one _ _,
    fun h => hne ((Ideal.eq_top_iff_one _).mpr h), rfl⟩
  obtain ⟨Q, ⟨g, e, hg, hgJ, rfl⟩, hmax⟩ := (wellFounded_gt (α := Ideal A)).has_min S hS
  refine ⟨g, e, hg, hgJ, isPrime_of_hom (hJ.colon_hom hg) (colonX_ne_top hgJ) ?_⟩
  intro x y a b hx _ hxy
  by_cases hxQ : x ∈ colonX J g
  · exact Or.inl hxQ
  right
  have hgx : g * x ∉ J := hxQ
  have hle : colonX J g ≤ colonX J (g * x) := fun q hq => by
    simp only [mem_colonX] at hq ⊢
    rw [mul_comm g x, mul_assoc]
    exact J.mul_mem_left x hq
  have heq : colonX J g = colonX J (g * x) :=
    eq_of_le_of_not_lt hle (hmax _ ⟨g * x, e + a, hg.mul hx, hgx, rfl⟩)
  rw [heq, mem_colonX, mul_assoc]
  exact hxy

/-- **Prime filtration** of the Hilbert function. -/
theorem hilb_filtration (J : Ideal A) (hJ : HomIdeal J) :
    ∃ L : List (Ideal A × ℕ), (∀ x ∈ L, HomIdeal x.1 ∧ x.1.IsPrime ∧ J ≤ x.1) ∧
      ∀ᶠ k in Filter.atTop, (hilb J k : ℤ) = (L.map fun x => (hilb x.1 (k - x.2) : ℤ)).sum := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  by_cases htop : J = ⊤
  · subst htop
    exact ⟨[], by simp, Filter.Eventually.of_forall fun k => by simp [hilb_top]⟩
  obtain ⟨g, e, hg, hgJ, hP⟩ := exists_assoc_prime hJ htop
  have hg0 : g ≠ 0 := fun h => hgJ (h ▸ J.zero_mem)
  have hlt : J < J ⊔ Ideal.span {g} :=
    lt_of_le_of_ne le_sup_left fun h => hgJ (h ▸ Submodule.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨L, hL, hsum⟩ := ih _ hlt (hJ.sup_hom hg)
  refine ⟨(colonX J g, e) :: L, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hJ.colon_hom hg, hP, le_colonX J g⟩
    · obtain ⟨h1, h2, h3⟩ := hL x hx
      exact ⟨h1, h2, le_sup_left.trans h3⟩
  · obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hsum
    refine Filter.eventually_atTop.mpr ⟨k0 + e, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show e ≤ k by omega)
    have h := hilb_colon_hom hJ hg hg0 j
    rw [List.map_cons, List.sum_cons, ← hk0 _ (by omega), add_comm e j, Nat.add_sub_cancel]
    push_cast [h]
    ring

end StrongSix.M2

end LeanPool
