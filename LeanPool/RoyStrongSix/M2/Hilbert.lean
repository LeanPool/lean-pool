/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Order.Filter.Defs

/-!
# Hilbert functions of homogeneous ideals

Let `A = K[z₁, …, z_m]` with the standard grading, `A_k` the homogeneous polynomials of degree
`k`, and
`J` a homogeneous ideal. The **Hilbert function** is

  `hilb J k = dim A_k − dim (J ∩ A_k)`.

* `hilb_colon`: for a variable `z = X i`,
  `hilb J (k+1) = hilb (J + (z)) (k+1) + hilb (J : z) k`.
  This is the exact sequence `0 → (A/(J:z))(−1) →z→ A/J → A/(J+z) → 0`, read off in degree `k+1`.
* `hilb_evPoly` (**Hilbert–Serre**, qualitative form): some iterated forward difference of
  `k ↦ hilb J k` vanishes for all large `k`, so `hilb J` is eventually a polynomial. The proof is by
  Noetherian induction on `J` using `hilb_colon`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule

namespace StrongSix.M2

variable {K : Type*} [Field K] {m : ℕ}

local notation "A" => MvPolynomial (Fin m) K

/-- A homogeneous ideal: closed under taking homogeneous components. -/
def HomIdeal (J : Ideal A) : Prop := ∀ p ∈ J, ∀ n, homogeneousComponent n p ∈ J

/-- `A_k`. -/
abbrev Adeg (K : Type*) [Field K] (m k : ℕ) : Submodule K (MvPolynomial (Fin m) K) :=
  homogeneousSubmodule (Fin m) K k

instance (k : ℕ) : FiniteDimensional K (Adeg K m k) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (σ := Fin m) (R := K) k)

/-- `J ∩ A_k`, as a `K`-subspace. -/
noncomputable def Jdeg (J : Ideal A) (k : ℕ) : Submodule K A := J.restrictScalars K ⊓ Adeg K m k

instance (J : Ideal A) (k : ℕ) : FiniteDimensional K (Jdeg J k) :=
  Submodule.finiteDimensional_of_le inf_le_right

/-- **The Hilbert function** `dim A_k − dim J_k`. -/
noncomputable def hilb (J : Ideal A) (k : ℕ) : ℕ :=
  finrank K (Adeg K m k) - finrank K (Jdeg J k)

theorem finrank_Jdeg_le (J : Ideal A) (k : ℕ) : finrank K (Jdeg J k) ≤ finrank K (Adeg K m k) :=
  Submodule.finrank_mono inf_le_right

/-- The colon ideal `(J : z) = {q | z q ∈ J}`. -/
noncomputable def colonX (J : Ideal A) (z : A) : Ideal A := Submodule.comap (LinearMap.mulLeft A
  z) J

theorem mem_colonX {J : Ideal A} {z q : A} : q ∈ colonX J z ↔ z * q ∈ J := Iff.rfl

theorem le_colonX (J : Ideal A) (z : A) : J ≤ colonX J z := fun _ hq => J.mul_mem_left z hq

/-! ### Homogeneous components of `X i * q` -/

theorem degree_sub_single {d : Fin m →₀ ℕ} {i : Fin m} (hi : i ∈ d.support) :
    (d - Finsupp.single i 1).degree + 1 = d.degree := by
  have hle : Finsupp.single i 1 ≤ d := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add, Finsupp.degree_single] at this
  exact this

theorem homogeneousComponent_X_mul (i : Fin m) (n : ℕ) (q : A) :
    homogeneousComponent (n + 1) (X i * q) = X i * homogeneousComponent n q := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_X_mul', coeff_X_mul']
  by_cases hi : i ∈ d.support
  · simp only [hi, ↓reduceIte, coeff_homogeneousComponent]
    have h := degree_sub_single hi
    by_cases hd : d.degree = n + 1
    · simp only [hd, show (d - Finsupp.single i 1).degree = n by omega, ↓reduceIte]
    · simp only [hd, show (d - Finsupp.single i 1).degree ≠ n by omega, ↓reduceIte]
  · simp [hi]

theorem homogeneousComponent_zero_X_mul (i : Fin m) (q : A) :
    homogeneousComponent 0 (X i * q) = 0 := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_X_mul']
  by_cases hi : i ∈ d.support
  · have h := degree_sub_single hi
    simp [show d.degree ≠ 0 by omega]
  · simp [hi]

/-! ### Homogeneity is preserved -/

theorem HomIdeal.sup_X {J : Ideal A} (hJ : HomIdeal J) (i : Fin m) :
    HomIdeal (J ⊔ Ideal.span {X i}) := by
  intro p hp n
  obtain ⟨j, hj, r, hr, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [map_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (hJ j hj n)) (Submodule.mem_sup_right ?_)
  rw [mul_comm]
  cases n with
  | zero => rw [homogeneousComponent_zero_X_mul]; exact zero_mem _
  | succ n =>
    rw [homogeneousComponent_X_mul]
    exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩

theorem HomIdeal.colonX {J : Ideal A} (hJ : HomIdeal J) (i : Fin m) :
    HomIdeal (colonX J (X i)) := by
  intro q hq n
  rw [mem_colonX, ← homogeneousComponent_X_mul]
  exact hJ _ hq _

/-! ### The colon identity -/

/-- Multiplication by `z`, as a `K`-linear map. -/
noncomputable abbrev mz (z : A) : A →ₗ[K] A := LinearMap.mulLeft K z

theorem mz_injective (i : Fin m) : Function.Injective (mz (K := K) (X i : A)) := fun a b h => by
  have : (X i : A) * a = X i * b := h
  exact mul_left_cancel₀ (X_ne_zero i) this

theorem mem_Adeg_X_mul {i : Fin m} {k : ℕ} {a : A} (ha : a ∈ Adeg K m k) :
    X i * a ∈ Adeg K m (k + 1) := by
  have := (isHomogeneous_X K i).mul ha
  rw [add_comm] at this
  exact this

/-- `(J + (z))_{k+1} = J_{k+1} + z A_k`. -/
theorem Jdeg_sup_X {J : Ideal A} (hJ : HomIdeal J) (i : Fin m) (k : ℕ) :
    Jdeg (J ⊔ Ideal.span {X i}) (k + 1) = Jdeg J (k + 1) ⊔ (Adeg K m k).map (mz (X i)) := by
  apply le_antisymm
  · rintro p ⟨hp, hpk⟩
    obtain ⟨j, hj, r, hr, hsum⟩ := Submodule.mem_sup.mp hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hpe : p = homogeneousComponent (k + 1) p := (homogeneousComponent_of_mem hpk).trans (by
      simp) |>.symm
    rw [hpe, ← hsum, map_add, mul_comm q, homogeneousComponent_X_mul]
    refine Submodule.add_mem_sup ⟨hJ j hj (k + 1), homogeneousComponent_isHomogeneous _ _⟩ ?_
    exact ⟨_, homogeneousComponent_isHomogeneous _ _, rfl⟩
  · refine sup_le (inf_le_inf_right _ (Submodule.restrictScalars_mono _ le_sup_left)) ?_
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨a, mul_comm _ _⟩), ?_⟩
    exact mem_Adeg_X_mul ha

/-- `J_{k+1} ∩ z A_k = z (J : z)_k`. -/
theorem Jdeg_inf_X {J : Ideal A} (i : Fin m) (k : ℕ) :
    Jdeg J (k + 1) ⊓ (Adeg K m k).map (mz (X i)) = (Jdeg (colonX J (X i)) k).map (mz (X i)) := by
  apply le_antisymm
  · rintro p ⟨⟨hpJ, -⟩, a, ha, rfl⟩
    exact ⟨a, ⟨hpJ, ha⟩, rfl⟩
  · rintro _ ⟨a, ⟨haJ, ha⟩, rfl⟩
    exact ⟨⟨haJ, mem_Adeg_X_mul ha⟩, a, ha, rfl⟩

theorem finrank_map_mz (i : Fin m) (U : Submodule K A) :
    finrank K (U.map (mz (X i))) = finrank K U :=
  LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (mz_injective i) U).symm

/-- **The colon identity.** -/
theorem hilb_colon {J : Ideal A} (hJ : HomIdeal J) (i : Fin m) (k : ℕ) :
    hilb J (k + 1) = hilb (J ⊔ Ideal.span {X i}) (k + 1) + hilb (colonX J (X i)) k := by
  unfold hilb
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Jdeg J (k + 1)) ((Adeg K m k).map (mz (X i)))
  rw [← Jdeg_sup_X hJ i k, Jdeg_inf_X i k, finrank_map_mz, finrank_map_mz] at h1
  have h2 := finrank_Jdeg_le (J ⊔ Ideal.span {X i}) (k + 1)
  have h3 := finrank_Jdeg_le (colonX J (X i)) k
  have h4 := finrank_Jdeg_le J (k + 1)
  omega

/-! ### Eventually polynomial functions -/

/-- `Δ f (k) = f (k+1) − f k`. -/
abbrev Δ (f : ℕ → ℤ) : ℕ → ℤ := fwdDiff 1 f

/-- `f` is eventually polynomial: some iterated forward difference vanishes for large `k`. -/
def EvPoly (f : ℕ → ℤ) : Prop := ∃ n, ∀ᶠ k in Filter.atTop, (Δ^[n] f) k = 0

/-- The shift `k ↦ f (k+1)`. -/
abbrev shift (f : ℕ → ℤ) : ℕ → ℤ := fun k => f (k + 1)

theorem Δ_add (f g : ℕ → ℤ) : Δ (f + g) = Δ f + Δ g := by
  funext k; simp [fwdDiff]

theorem iter_Δ_add (n : ℕ) (f g : ℕ → ℤ) : Δ^[n] (f + g) = Δ^[n] f + Δ^[n] g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, Δ_add, ih]

theorem iter_Δ_shift (n : ℕ) (f : ℕ → ℤ) : Δ^[n] (shift f) = shift (Δ^[n] f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show Δ (shift f) = shift (Δ f) from rfl, ih]

theorem iter_Δ_eventually_zero {f : ℕ → ℤ} {n : ℕ} (h : ∀ᶠ k in Filter.atTop, (Δ^[n] f) k = 0) :
    ∀ᶠ k in Filter.atTop, (Δ^[n + 1] f) k = 0 := by
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp h
  refine Filter.eventually_atTop.mpr ⟨k0, fun k hk => ?_⟩
  rw [Function.iterate_succ_apply']
  change (Δ^[n] f) (k + 1) - (Δ^[n] f) k = 0
  rw [hk0 k hk, hk0 (k + 1) (by omega), sub_zero]

theorem iter_Δ_eventually_zero_le {f : ℕ → ℤ} {n n' : ℕ} (hn : n ≤ n')
    (h : ∀ᶠ k in Filter.atTop, (Δ^[n] f) k = 0) : ∀ᶠ k in Filter.atTop, (Δ^[n'] f) k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction j with
  | zero => exact h
  | succ j ih => exact iter_Δ_eventually_zero (ih (by omega))

theorem EvPoly.add {f g : ℕ → ℤ} (hf : EvPoly f) (hg : EvPoly g) : EvPoly (f + g) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨max a b, ?_⟩
  filter_upwards [iter_Δ_eventually_zero_le (le_max_left a b) ha,
    iter_Δ_eventually_zero_le (le_max_right a b) hb] with k h1 h2
  rw [iter_Δ_add, Pi.add_apply, h1, h2, add_zero]

theorem EvPoly.of_shift {f : ℕ → ℤ} (h : EvPoly (shift f)) : EvPoly f := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [iter_Δ_shift] at hn
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hn
  exact Filter.eventually_atTop.mpr ⟨k0 + 1, fun k hk => by
    have := hk0 (k - 1) (by omega)
    simpa [shift, show k - 1 + 1 = k by omega] using this⟩

theorem EvPoly.shift {f : ℕ → ℤ} (h : EvPoly f) : EvPoly (shift f) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [iter_Δ_shift]
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp hn
  exact Filter.eventually_atTop.mpr ⟨k0, fun k hk => hk0 (k + 1) (by omega)⟩

theorem EvPoly.of_Δ {f : ℕ → ℤ} (h : EvPoly (Δ f)) : EvPoly f := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

theorem EvPoly.of_eventually_zero {f : ℕ → ℤ} (h : ∀ᶠ k in Filter.atTop, f k = 0) : EvPoly f :=
  ⟨0, h⟩

/-! ### Hilbert–Serre -/

theorem monomial_eq_X_mul {d : Fin m →₀ ℕ} {i : Fin m} (hi : 1 ≤ d i) (c : K) :
    monomial d c = X i * monomial (d - Finsupp.single i 1) c := by
  rw [X, monomial_mul_monomial, one_mul, add_comm, tsub_add_cancel_of_le
    (Finsupp.single_le_iff.mpr hi)]

/-- If `J` contains every variable, `A_k ⊆ J` for `k ≥ 1`. -/
theorem Adeg_le_of_all_X {J : Ideal A} (hall : ∀ i, X i ∈ J) {k : ℕ} (hk : 1 ≤ k) :
    Adeg K m k ≤ J.restrictScalars K := by
  intro p hp
  change p ∈ J
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = k := by
    by_contra h; exact (Finsupp.mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  have : ∃ i, 1 ≤ d i := by
    by_contra h
    push Not at h
    have : d = 0 := Finsupp.ext fun i => by simpa using Nat.lt_one_iff.mp (h i)
    rw [this, map_zero] at hdeg; omega
  obtain ⟨i, hi⟩ := this
  rw [monomial_eq_X_mul hi]
  exact J.mul_mem_right _ (hall i)

theorem hilb_eq_zero_of_all_X {J : Ideal A} (hall : ∀ i, X i ∈ J) {k : ℕ} (hk : 1 ≤ k) :
    hilb J k = 0 := by
  unfold hilb
  have : Jdeg J k = Adeg K m k := le_antisymm inf_le_right (le_inf (Adeg_le_of_all_X hall hk)
    le_rfl)
  rw [this, Nat.sub_self]

/-- **Hilbert–Serre** (qualitative): the Hilbert function of a homogeneous ideal is eventually a
polynomial. -/
theorem hilb_evPoly (J : Ideal A) (hJ : HomIdeal J) : EvPoly fun k => (hilb J k : ℤ) := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  by_cases hall : ∀ i, X i ∈ J
  · exact EvPoly.of_eventually_zero (Filter.eventually_atTop.mpr ⟨1, fun k hk => by
      simp [hilb_eq_zero_of_all_X hall hk]⟩)
  push Not at hall
  obtain ⟨i, hi⟩ := hall
  have hsup : J < J ⊔ Ideal.span {X i} :=
    lt_of_le_of_ne le_sup_left fun h => hi (h ▸ Submodule.mem_sup_right (Ideal.subset_span rfl))
  have hP1 := ih _ hsup (hJ.sup_X i)
  by_cases hc : colonX J (X i) = J
  · -- `z` is a non-zero-divisor: `Δ hilb J = shift (hilb (J + z))`
    refine EvPoly.of_Δ ?_
    have : Δ (fun k => (hilb J k : ℤ)) = shift fun k => (hilb (J ⊔ Ideal.span {X i}) k : ℤ) := by
      funext k
      have := hilb_colon hJ i k
      rw [hc] at this
      change (hilb J (k + 1) : ℤ) - hilb J k = hilb (J ⊔ Ideal.span {X i}) (k + 1)
      omega
    rw [this]
    exact hP1.shift
  · have hlt : J < colonX J (X i) := lt_of_le_of_ne (le_colonX J (X i)) (Ne.symm hc)
    have hP2 := ih _ hlt (hJ.colonX i)
    refine EvPoly.of_shift ?_
    have : shift (fun k => (hilb J k : ℤ)) =
        shift (fun k => (hilb (J ⊔ Ideal.span {X i}) k : ℤ)) + fun k => (hilb (colonX J (X i)) k
          : ℤ) := by
      funext k
      simp only [shift, Pi.add_apply]
      have := hilb_colon hJ i k
      omega
    rw [this]
    exact hP1.shift.add hP2

end StrongSix.M2

end LeanPool
