/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.GM07.Section11b
import LeanPool.GraphMinor.Surface.ArcInPath
import LeanPool.GraphMinor.Surface.DiscMerge
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Graph Minors VII, Section 11: Proof of (11.2)

This file proves Graph Minors VII, (11.2) (`nonNullHomotopicOArc_in_curve`, pages 249–250):
if `S` is a surface and `φ : C(Circle, S)` is non-null-homotopic in `S`, then `range φ` contains
a non-null-homotopic `O`-arc `F`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology Metric unitInterval
open GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-! ## Subpaths and Unit-Square Homotopy Criterion for `Circle` -/

/-- Every `w : Circle` is of the form `Circle.exp (2 * Real.pi * u.1)` for some `u : unitInterval`.
-/
theorem exists_unitInterval_exp (w : Circle) :
    ∃ u : unitInterval, Circle.exp (2 * Real.pi * (u : ℝ)) = w := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  let θ : ℝ := toIcoMod h2pi 0 (Complex.arg w)
  have hθ0 : 0 ≤ θ := (toIcoMod_mem_Ico h2pi 0 (Complex.arg w)).1
  have hθ1 : θ ≤ 2 * Real.pi := by linarith [(toIcoMod_mem_Ico h2pi 0 (Complex.arg w)).2]
  let u : unitInterval := ⟨θ / (2 * Real.pi), div_nonneg hθ0 h2pi.le, (div_le_one h2pi).mpr hθ1⟩
  refine ⟨u, ?_⟩
  have hmul : 2 * Real.pi * (u : ℝ) = θ := mul_div_cancel₀ θ h2pi.ne'
  rw [hmul]
  have h1 : θ = Complex.arg w - toIcoDiv h2pi 0 (Complex.arg w) • (2 * Real.pi) := rfl
  have h2 : Circle.exp θ = Circle.exp (Complex.arg w) := by
    rw [h1, zsmul_eq_mul]
    exact Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi 0 (Complex.arg w), by push_cast; ring⟩
  exact h2.trans (Circle.exp_arg w)

/-- Criterion for `ClosedCurvesHomotopicIn Z φ₀ φ₁` via a homotopy `H : C(unitInterval ×
unitInterval, S)`
satisfying `H (1, s) = H (0, s)`. -/
theorem closedCurvesHomotopicIn_of_unitInterval {Z : Set S} {φ₀ φ₁ : C(Circle, S)}
    (H : C(unitInterval × unitInterval, S))
    (hHZ : ∀ p, H p ∈ Z)
    (hper : ∀ s : unitInterval, H (1, s) = H (0, s))
    (h0 : ∀ u : unitInterval, H (u, 0) = φ₀ (Circle.exp (2 * Real.pi * (u : ℝ))))
    (h1 : ∀ u : unitInterval, H (u, 1) = φ₁ (Circle.exp (2 * Real.pi * (u : ℝ)))) :
    ClosedCurvesHomotopicIn Z φ₀ φ₁ := by
  let Ψ := concatLoopParam one_pos (fun _ : Fin 1 => H) (fun _ s => hper s)
  have hΨ_exp : ∀ (u : unitInterval) (s : unitInterval),
      Ψ (Circle.exp (2 * Real.pi * (u : ℝ)), s) = H (u, s) := by
    intro u s
    have h := concatLoopParam_exp one_pos (fun _ : Fin 1 => H) (fun _ r => hper r) (u : ℝ) s
    simp only [Nat.cast_one, div_one] at h
    rw [h]
    have h2 := chainFun_int_add one_pos (fun _ : Fin 1 => H) (fun _ r => hper r) 0 u s
    simp only [Int.cast_zero, zero_add] at h2
    exact h2
  refine ⟨Ψ, ?_, fun w => ?_, fun w => ?_⟩
  · rintro ⟨w, s⟩
    obtain ⟨u, rfl⟩ := exists_unitInterval_exp w
    rw [hΨ_exp]
    exact hHZ (u, s)
  · obtain ⟨u, rfl⟩ := exists_unitInterval_exp w
    rw [hΨ_exp, h0]
  · obtain ⟨u, rfl⟩ := exists_unitInterval_exp w
    rw [hΨ_exp, h1]

/-- Transitivity of `ClosedCurvesHomotopicIn Z`. -/
theorem closedCurvesHomotopicIn_trans' {Z : Set S} {φ₀ φ₁ φ₂ : C(Circle, S)}
    (h₁ : ClosedCurvesHomotopicIn Z φ₀ φ₁) (h₂ : ClosedCurvesHomotopicIn Z φ₁ φ₂) :
    ClosedCurvesHomotopicIn Z φ₀ φ₂ :=
  Surface.ClosedCurvesHomotopicIn.trans h₁ h₂

/-- Symmetry of `ClosedCurvesHomotopicIn Z`. -/
theorem ClosedCurvesHomotopicIn.symm {Z : Set S} {φ₀ φ₁ : C(Circle, S)}
    (h : ClosedCurvesHomotopicIn Z φ₀ φ₁) : ClosedCurvesHomotopicIn Z φ₁ φ₀ := by
  obtain ⟨Ψ, hΨZ, hΨ0, hΨ1⟩ := h
  refine ⟨Ψ.comp ⟨fun p => (p.1, unitInterval.symm p.2),
    continuous_fst.prodMk (continuous_symm.comp continuous_snd)⟩,
    fun p => hΨZ _, fun x => ?_, fun x => ?_⟩
  · change Ψ (x, unitInterval.symm 0) = φ₁ x
    have h0 : unitInterval.symm 0 = 1 := by ext; simp
    rw [h0, hΨ1]
  · change Ψ (x, unitInterval.symm 1) = φ₀ x
    have h1 : unitInterval.symm 1 = 0 := by ext; simp
    rw [h1, hΨ0]

/-- If `ClosedCurvesHomotopicIn Z φ₀ φ₁` and `ClosedCurveIsNullHomotopicIn Z φ₁`, then
`ClosedCurveIsNullHomotopicIn Z φ₀`. -/
theorem closedCurveIsNullHomotopicIn_of_homotopic {Z : Set S} {φ₀ φ₁ : C(Circle, S)}
    (hhom : ClosedCurvesHomotopicIn Z φ₀ φ₁) (hnull : ClosedCurveIsNullHomotopicIn Z φ₁) :
    ClosedCurveIsNullHomotopicIn Z φ₀ := by
  obtain ⟨c, hc, hc_hom⟩ := hnull
  exact ⟨c, hc, closedCurvesHomotopicIn_trans' hhom hc_hom⟩

/-- The linear subpath of `γ : C(unitInterval, S)` from `s` to `t` (`u ↦ γ ((1 - u) * s + u * t)`).
-/
noncomputable def subPathSeg (γ : C(unitInterval, S)) (s t : unitInterval) : C(unitInterval, S) :=
  ⟨fun u => γ ⟨(1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * (t : ℝ),
    by nlinarith [u.2.1, u.2.2, s.2.1, t.2.1],
    by nlinarith [u.2.1, u.2.2, s.2.2, t.2.2]⟩, by fun_prop⟩

@[simp]
theorem subPathSeg_zero (γ : C(unitInterval, S)) (s t : unitInterval) :
    subPathSeg γ s t 0 = γ s := by
  dsimp [subPathSeg]
  congr 1
  ext
  change (1 - (0 : ℝ)) * (s : ℝ) + (0 : ℝ) * (t : ℝ) = (s : ℝ)
  ring

@[simp]
theorem subPathSeg_one (γ : C(unitInterval, S)) (s t : unitInterval) :
    subPathSeg γ s t 1 = γ t := by
  dsimp [subPathSeg]
  congr 1
  ext
  change (1 - (1 : ℝ)) * (s : ℝ) + (1 : ℝ) * (t : ℝ) = (t : ℝ)
  ring

theorem subPathSeg_self (γ : C(unitInterval, S)) (a u : unitInterval) :
    subPathSeg γ a a u = γ a := by
  dsimp [subPathSeg]
  congr 1
  ext
  change (1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (a : ℝ) = (a : ℝ)
  ring

theorem range_subPathSeg_subset (γ : C(unitInterval, S)) (s t : unitInterval) :
    range (subPathSeg γ s t) ⊆ range γ := by
  rintro _ ⟨u, rfl⟩
  exact mem_range_self _

theorem injective_subPathSeg {γ : C(unitInterval, S)} (hγ : Injective γ)
    {s t : unitInterval} (hst : (s : ℝ) < (t : ℝ)) :
    Injective (subPathSeg γ s t) := by
  intro u₁ u₂ heq
  have h1 := Subtype.ext_iff.mp (hγ heq)
  dsimp at h1
  ext
  nlinarith

/-! ## Periodic Chain Function `chainReal` and Operations on `concatLoop` -/

/-- The `n`-periodic continuous function `ℝ → S` associated to `γ : Fin n → C(unitInterval, S)`. -/
noncomputable def chainReal {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S)) (x : ℝ) : S :=
  chainFun (P := Unit) hn (fun i => (γ i).comp ⟨Prod.fst, continuous_fst⟩) (x, ())

theorem continuous_chainReal {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) :
    Continuous (chainReal hn γ) :=
  (continuous_chainFun (P := Unit) hn (fun i => (γ i).comp ⟨Prod.fst, continuous_fst⟩)
    (fun i _ => hmatch i)).comp (continuous_id.prodMk continuous_const)

theorem chainReal_add_nat {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S)) (x : ℝ) :
    chainReal hn γ (x + (n : ℝ)) = chainReal hn γ x :=
  chainFun_add_nat (P := Unit) hn (fun i => (γ i).comp ⟨Prod.fst, continuous_fst⟩) x ()

theorem chainReal_int_add {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) (k : ℤ) (t : unitInterval) :
    chainReal hn γ ((k : ℝ) + (t : ℝ)) = γ (intModFin hn k) t :=
  chainFun_int_add (P := Unit) hn (fun i => (γ i).comp ⟨Prod.fst, continuous_fst⟩)
    (fun i _ => hmatch i) k t ()

theorem chainReal_nat_add {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) (i : Fin n) (t : unitInterval) :
    chainReal hn γ ((i.1 : ℝ) + (t : ℝ)) = γ i t := by
  have h := chainReal_int_add hn γ hmatch (i.1 : ℤ) t
  simp only [Int.cast_natCast] at h
  rw [intModFin_nat hn i] at h
  exact h

theorem concatLoop_exp_mul {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) (x : ℝ) :
    concatLoop hn γ hmatch (Circle.exp (2 * Real.pi * x)) = chainReal hn γ (x * (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : 2 * Real.pi * x = 2 * Real.pi * (x * (n : ℝ)) / (n : ℝ) := by field_simp
  rw [h1]
  exact concatLoopParam_exp (P := Unit) hn (fun i => (γ i).comp ⟨Prod.fst, continuous_fst⟩)
    (fun i _ => hmatch i) (x * (n : ℝ)) ()

/-- Cyclic rotation of a chain `γ : Fin n → C(unitInterval, S)` by `k : ℕ` steps. -/
def rotateChain {n : ℕ} (hn : 0 < n) (k : ℕ) (γ : Fin n → C(unitInterval, S)) (i : Fin n) :
    C(unitInterval, S) :=
  γ ⟨(i.1 + k) % n, Nat.mod_lt _ hn⟩

theorem rotateChain_match {n : ℕ} (hn : 0 < n) (k : ℕ) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) (i : Fin n) :
    rotateChain hn k γ i 1 = rotateChain hn k γ (finNext hn i) 0 := by
  dsimp [rotateChain]
  rw [hmatch]
  have hfin : finNext hn ⟨(i.1 + k) % n, Nat.mod_lt _ hn⟩ =
      ⟨((finNext hn i).1 + k) % n, Nat.mod_lt _ hn⟩ := by
    ext
    dsimp [finNext]
    rw [Nat.mod_add_mod, Nat.mod_add_mod, show i.1 + k + 1 = i.1 + 1 + k by omega]
  rw [hfin]

theorem chainReal_rotateChain {n : ℕ} (hn : 0 < n) (k : ℕ) (γ : Fin n → C(unitInterval, S))
    (x : ℝ) :
    chainReal hn (rotateChain hn k γ) x = chainReal hn γ (x + (k : ℝ)) := by
  dsimp [chainReal, chainFun, rotateChain]
  have hfl : ⌊x + (k : ℤ)⌋ = ⌊x⌋ + (k : ℤ) := Int.floor_add_intCast x k
  have hfr : unitFract (x + (k : ℤ)) = unitFract x := Subtype.ext (Int.fract_add_intCast x k)
  have hcast : x + (k : ℝ) = x + ((k : ℤ) : ℝ) := by push_cast; rfl
  rw [hcast, hfl, hfr]
  have hmod : (⟨((intModFin hn ⌊x⌋).1 + k) % n, Nat.mod_lt _ hn⟩ : Fin n) =
      intModFin hn (⌊x⌋ + (k : ℤ)) := by
    ext
    dsimp [intModFin]
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hnn1 : 0 ≤ ⌊x⌋ % (n : ℤ) := Int.emod_nonneg ⌊x⌋ hnZ.ne'
    have h1 : (⌊x⌋ + (k : ℤ)) % (n : ℤ) = (⌊x⌋ % (n : ℤ) + (k : ℤ)) % (n : ℤ) := by
      rw [Int.add_emod (⌊x⌋ % (n : ℤ)) (k : ℤ), Int.emod_emod, ← Int.add_emod]
    have h2 : ⌊x⌋ % (n : ℤ) + (k : ℤ) = (((⌊x⌋ % (n : ℤ)).toNat + k : ℕ) : ℤ) := by omega
    rw [h1, h2, ← Int.natCast_emod, Int.toNat_natCast]
  rw [hmod]

/-- Rotating a chain `γ` by `k` steps produces a homotopic `concatLoop`. -/
theorem concatLoop_rotateChain_homotopic {n : ℕ} (hn : 0 < n) (k : ℕ)
    (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0) :
    ClosedCurvesHomotopicIn univ (concatLoop hn γ hmatch)
      (concatLoop hn (rotateChain hn k γ) (rotateChain_match hn k γ hmatch)) := by
  let H : C(unitInterval × unitInterval, S) :=
    ⟨fun p => chainReal hn γ ((p.1 : ℝ) * (n : ℝ) + (p.2 : ℝ) * (k : ℝ)),
      (continuous_chainReal hn γ hmatch).comp (by fun_prop)⟩
  refine closedCurvesHomotopicIn_of_unitInterval H (fun _ => mem_univ _)
    (fun s => ?_) (fun u => ?_) (fun u => ?_)
  · change chainReal hn γ (1 * (n : ℝ) + (s : ℝ) * (k : ℝ)) =
      chainReal hn γ (0 * (n : ℝ) + (s : ℝ) * (k : ℝ))
    rw [one_mul, zero_mul, zero_add, add_comm (n : ℝ), chainReal_add_nat]
  · change chainReal hn γ ((u : ℝ) * (n : ℝ) + 0 * (k : ℝ)) = _
    rw [zero_mul, add_zero, concatLoop_exp_mul]
  · change chainReal hn γ ((u : ℝ) * (n : ℝ) + 1 * (k : ℝ)) = _
    rw [one_mul, concatLoop_exp_mul, chainReal_rotateChain]

/-- The first `n - 1` pieces of a chain `γ : Fin n → C(unitInterval, S)`. -/
def dropLastChain {n : ℕ} (γ : Fin n → C(unitInterval, S)) (i : Fin (n - 1)) :
    C(unitInterval, S) :=
  γ ⟨i.1, by omega⟩

theorem dropLastChain_match {n : ℕ} (hn2 : 2 ≤ n)
    (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext (by omega) i) 0)
    (hconst : ∀ t : unitInterval, γ ⟨n - 1, by omega⟩ t = γ ⟨0, by omega⟩ 0)
    (i : Fin (n - 1)) :
    dropLastChain γ i 1 = dropLastChain γ (finNext (by omega : 0 < n - 1) i) 0 := by
  dsimp [dropLastChain, finNext]
  by_cases hlast : i.1 + 1 = n - 1
  · simp only [hlast, Nat.mod_self]
    have hi := hmatch ⟨i.1, by omega⟩
    dsimp [finNext] at hi
    have hmod : (i.1 + 1) % n = n - 1 := by
      rw [hlast]
      exact Nat.mod_eq_of_lt (by omega)
    have hi' : γ ⟨i.1, by omega⟩ 1 = γ ⟨n - 1, by omega⟩ 0 := by
      simpa [hmod] using hi
    exact hi'.trans (hconst 0)
  · have hlt : i.1 + 1 < n - 1 := by omega
    have hmod1 : (i.1 + 1) % (n - 1) = i.1 + 1 := Nat.mod_eq_of_lt hlt
    have hmod2 : (i.1 + 1) % n = i.1 + 1 := Nat.mod_eq_of_lt (by omega)
    have hi := hmatch ⟨i.1, by omega⟩
    dsimp [finNext] at hi
    simpa [hmod1, hmod2] using hi

/-- Dropping the last piece of a chain when it is constant gives a homotopic `concatLoop` of `n - 1`
pieces. -/
theorem concatLoop_drop_last_const {n : ℕ} (hn2 : 2 ≤ n)
    (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext (by omega) i) 0)
    (hconst : ∀ t : unitInterval, γ ⟨n - 1, by omega⟩ t = γ ⟨0, by omega⟩ 0) :
    ClosedCurvesHomotopicIn univ (concatLoop (by omega) γ hmatch)
      (concatLoop (by omega : 0 < n - 1) (dropLastChain γ)
        (dropLastChain_match hn2 γ hmatch hconst)) := by
  have hn : 0 < n := by omega
  have hn' : 0 < n - 1 := by omega
  let γ' := dropLastChain γ
  let hmatch' := dropLastChain_match hn2 γ hmatch hconst
  let H : C(unitInterval × unitInterval, S) :=
    ⟨fun p => chainReal hn γ ((p.1 : ℝ) * ((1 - (p.2 : ℝ)) * (n : ℝ) + (p.2 : ℝ) *
      ((n - 1 : ℕ) : ℝ))),
      (continuous_chainReal hn γ hmatch).comp (by fun_prop)⟩
  refine closedCurvesHomotopicIn_of_unitInterval H (fun _ => mem_univ _)
    (fun s => ?_) (fun u => ?_) (fun u => ?_)
  · change chainReal hn γ (1 * ((1 - (s : ℝ)) * (n : ℝ) + (s : ℝ) * ((n - 1 : ℕ) : ℝ))) =
      chainReal hn γ (0 * ((1 - (s : ℝ)) * (n : ℝ) + (s : ℝ) * ((n - 1 : ℕ) : ℝ)))
    rw [one_mul, zero_mul]
    let t : unitInterval := unitInterval.symm s
    have ht : (t : ℝ) = 1 - (s : ℝ) := rfl
    have h_eq : (1 - (s : ℝ)) * (n : ℝ) + (s : ℝ) * ((n - 1 : ℕ) : ℝ) =
        ((n - 1 : ℕ) : ℝ) + (t : ℝ) := by
      have hn_eq : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
      rw [hn_eq, ht]
      ring
    have h0 : chainReal hn γ 0 = γ ⟨0, hn⟩ 0 := by
      have := chainReal_nat_add hn γ hmatch ⟨0, hn⟩ 0
      simpa using this
    rw [h_eq, chainReal_nat_add hn γ hmatch ⟨n - 1, by omega⟩ t, h0]
    exact hconst t
  · change chainReal hn γ ((u : ℝ) * ((1 - 0) * (n : ℝ) + 0 * ((n - 1 : ℕ) : ℝ))) = _
    rw [sub_zero, one_mul, zero_mul, add_zero, concatLoop_exp_mul]
  · change chainReal hn γ ((u : ℝ) * ((1 - 1) * (n : ℝ) + 1 * ((n - 1 : ℕ) : ℝ))) = _
    rw [sub_self, zero_mul, one_mul, zero_add, concatLoop_exp_mul]
    by_cases hu1 : (u : ℝ) = 1
    · rw [hu1, one_mul]
      have h1 : chainReal hn γ (((n - 1 : ℕ) : ℝ) + ((0 : unitInterval) : ℝ)) =
          γ ⟨n - 1, by omega⟩ 0 := chainReal_nat_add hn γ hmatch ⟨n - 1, by omega⟩ 0
      simp only [Set.Icc.coe_zero, add_zero] at h1
      have h2 : chainReal hn' γ' ((0 : ℝ) + ((n - 1 : ℕ) : ℝ)) = chainReal hn' γ' 0 :=
        chainReal_add_nat hn' γ' 0
      have h3 : chainReal hn' γ' ((((⟨0, hn'⟩ : Fin (n - 1)).1 : ℝ)) + ((0 : unitInterval) : ℝ)) =
          γ' ⟨0, hn'⟩ 0 :=
        chainReal_nat_add hn' γ' hmatch' ⟨0, hn'⟩ 0
      simp only [Nat.cast_zero, Set.Icc.coe_zero, add_zero, zero_add] at h2 h3
      rw [h1, hconst 0, h2, h3]
      rfl
    · have hu_lt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 hu1
      let y : ℝ := (u : ℝ) * ((n - 1 : ℕ) : ℝ)
      have hy0 : 0 ≤ y := mul_nonneg u.2.1 (by positivity)
      have hnm_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hn'
      have hy_lt : y < ((n - 1 : ℕ) : ℝ) := by
        simpa [y] using mul_lt_of_lt_one_left hnm_pos hu_lt
      have hfl_nn : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
      have hfl_lt : ⌊y⌋ < ((n - 1 : ℕ) : ℤ) := by
        rw [Int.floor_lt]
        exact_mod_cast hy_lt
      let k : ℕ := ⌊y⌋.toNat
      have hk_lt : k < n - 1 := by omega
      have hk_eq : (k : ℝ) + (unitFract y : ℝ) = y := by
        have hfl_eq : (k : ℤ) = ⌊y⌋ := Int.toNat_of_nonneg hfl_nn
        change ((k : ℤ) : ℝ) + Int.fract y = y
        rw [hfl_eq, Int.floor_add_fract]
      change chainReal hn γ y = chainReal hn' γ' y
      rw [← hk_eq, chainReal_nat_add hn γ hmatch ⟨k, by omega⟩ (unitFract y),
        chainReal_nat_add hn' γ' hmatch' ⟨k, hk_lt⟩ (unitFract y)]
      rfl

/-! ## Contracting a Null-Homotopic Loop to a Constant Path Rel Endpoints -/

/-- Any closed curve `L : C(Circle, S)` turned into a path `unitInterval → S` (`t ↦ L (Circle.exp (2
* Real.pi * t))`). -/
noncomputable def loopToPath (L : C(Circle, S)) : C(unitInterval, S) :=
  curvePiece one_pos L ⟨0, one_pos⟩

@[simp]
theorem loopToPath_zero (L : C(Circle, S)) : loopToPath L 0 = L 1 := by
  dsimp [loopToPath, curvePiece]
  simp

@[simp]
theorem loopToPath_one (L : C(Circle, S)) : loopToPath L 1 = L 1 := by
  dsimp [loopToPath, curvePiece]
  simp [Circle.exp_two_pi]

theorem loopToPath_apply (L : C(Circle, S)) (t : unitInterval) :
    loopToPath L t = L (Circle.exp (2 * Real.pi * (t : ℝ))) := by
  dsimp [loopToPath, curvePiece]
  simp

/-- If `L : C(Circle, S)` is null-homotopic in `univ`, then `loopToPath L` is path-homotopic in
`univ` relative to `{0, 1}` to the constant path `ContinuousMap.const unitInterval (L 1)`. -/
theorem pathsHomotopicRelIn_const_of_nullHomotopic {L : C(Circle, S)}
    (hnull : ClosedCurveIsNullHomotopicIn univ L) :
    PathsHomotopicRelIn univ (loopToPath L) (ContinuousMap.const unitInterval (L 1)) := by
  obtain ⟨c, _, Ψ, _, hΨ0, hΨ1⟩ := hnull
  let β : C(unitInterval, S) := ⟨fun s => Ψ (1, s), Ψ.continuous.comp
    (continuous_const.prodMk continuous_id)⟩
  have hβ0 : β 0 = L 1 := hΨ0 1
  have hβ1 : β 1 = c := hΨ1 1
  -- Homotopy 1: reparameterize `loopToPath L` to stay at `L 1` on `[0, 1/3]` and `[2/3, 1]`.
  have hL0 : (ContinuousMap.const unitInterval (L 1)) 1 = loopToPath L 0 :=
    (loopToPath_zero L).symm
  have hL1 : (ContinuousMap.const unitInterval (L 1)) 1 = loopToPath L 1 :=
    (loopToPath_one L).symm
  let H₁ : C(unitInterval × unitInterval, S) :=
    reparamHomotopy (ContinuousMap.const unitInterval (L 1)) (loopToPath L)
      (ContinuousMap.const unitInterval (L 1)) hL0 hL1
  -- Homotopy 2: deform the middle `[1/3, 2/3]` via `Ψ` while whiskering on `[0, 1/3]` and `[2/3,
  -- 1]` by `β`.
  let g₁ : unitInterval × unitInterval → S := fun p =>
    β (projIcc 0 1 zero_le_one ((p.2 : ℝ) * (3 * (p.1 : ℝ))))
  let g₂ : unitInterval × unitInterval → S := fun p =>
    Ψ (Circle.exp (2 * Real.pi * (projIcc 0 1 zero_le_one (3 * (p.1 : ℝ) - 1) : ℝ)), p.2)
  let g₃ : unitInterval × unitInterval → S := fun p =>
    β (projIcc 0 1 zero_le_one ((p.2 : ℝ) * (3 * (1 - (p.1 : ℝ)))))
  have hg₁ : Continuous g₁ := by fun_prop
  have hg₂ : Continuous g₂ := by fun_prop
  have hg₃ : Continuous g₃ := by fun_prop
  let g₁₂ : unitInterval × unitInterval → S :=
    fun p => if (p.1 : ℝ) ≤ 1 / 3 then g₁ p else g₂ p
  have hg₁₂ : Continuous g₁₂ := by
    refine Continuous.if_le hg₁ hg₂ (continuous_subtype_val.comp continuous_fst) continuous_const ?_
    intro p hp
    have hp_s : projIcc 0 1 zero_le_one ((p.2 : ℝ) * (3 * (p.1 : ℝ))) = p.2 := by
      rw [hp, show (p.2 : ℝ) * (3 * (1 / 3 : ℝ)) = (p.2 : ℝ) by ring]
      exact projIcc_of_mem zero_le_one p.2.2
    have hp0 : projIcc 0 1 zero_le_one (3 * (p.1 : ℝ) - 1) = 0 := by
      rw [hp]; ext; simp
    change β _ = Ψ _
    rw [hp_s, hp0]
    simp [β]
  let g_all : unitInterval × unitInterval → S :=
    fun p => if (p.1 : ℝ) ≤ 2 / 3 then g₁₂ p else g₃ p
  have hg_all : Continuous g_all := by
    refine Continuous.if_le hg₁₂ hg₃ (continuous_subtype_val.comp continuous_fst) continuous_const
      ?_
    intro p hp
    have hnot : ¬ ((p.1 : ℝ) ≤ 1 / 3) := by linarith
    have hp1 : projIcc 0 1 zero_le_one (3 * (p.1 : ℝ) - 1) = 1 := by
      rw [hp]; ext; change max (0 : ℝ) (min 1 (3 * (2 / 3) - 1)) = 1; norm_num
    have hp_s : projIcc 0 1 zero_le_one ((p.2 : ℝ) * (3 * (1 - (p.1 : ℝ)))) = p.2 := by
      rw [hp, show (p.2 : ℝ) * (3 * (1 - (2 / 3 : ℝ))) = (p.2 : ℝ) by ring]
      exact projIcc_of_mem zero_le_one p.2.2
    dsimp [g₁₂]
    simp only [hnot, ↓reduceIte]
    change Ψ _ = β _
    rw [hp1, hp_s]
    simp [β, Circle.exp_two_pi]
  let H₂ : C(unitInterval × unitInterval, S) := ⟨g_all, hg_all⟩
  -- Homotopy 3: contract the `β`-loop back to `β 0 = L 1`.
  let H₃ : C(unitInterval × unitInterval, S) :=
    ⟨fun p => β (projIcc 0 1 zero_le_one
      ((1 - (p.2 : ℝ)) * min (3 * (p.1 : ℝ)) (3 * (1 - (p.1 : ℝ))))), by fun_prop⟩
  have h12 : ∀ t : unitInterval, H₁ (t, 1) = H₂ (t, 0) := by
    intro t
    dsimp [H₁]
    rw [reparamHomotopy_one]
    simp only [whiskerHomotopy, H₂, g_all, g₁₂, g₁, g₂, g₃,
      ContinuousMap.coe_mk, ContinuousMap.const_apply]
    split_ifs with h23 h13
    · have h0 : projIcc 0 1 zero_le_one (((0 : unitInterval) : ℝ) * (3 * (t : ℝ))) = 0 := by
        rw [Icc.coe_zero, zero_mul]
        exact projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
      rw [h0, hβ0]
    · rw [hΨ0, loopToPath_apply]
    · have h0 : projIcc 0 1 zero_le_one (((0 : unitInterval) : ℝ) * (3 * (1 - (t : ℝ)))) = 0 := by
        rw [Icc.coe_zero, zero_mul]
        exact projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
      rw [h0, hβ0]
  have h23_match : ∀ t : unitInterval, H₂ (t, 1) = H₃ (t, 0) := by
    intro t
    dsimp [H₂, H₃, g_all, g₁₂, g₁, g₂, g₃]
    simp only [sub_zero, one_mul]
    split_ifs with h23 h13
    · have hmin : min (3 * (t : ℝ)) (3 * (1 - (t : ℝ))) = 3 * (t : ℝ) :=
        min_eq_left (by linarith)
      rw [hmin]
    · have hge1 : 1 ≤ min (3 * (t : ℝ)) (3 * (1 - (t : ℝ))) :=
        le_min (by linarith) (by linarith)
      rw [projIcc_of_right_le zero_le_one hge1, hΨ1]
      exact hβ1.symm
    · have hmin : min (3 * (t : ℝ)) (3 * (1 - (t : ℝ))) = 3 * (1 - (t : ℝ)) :=
        min_eq_right (by linarith)
      rw [hmin]
  let s₁ : unitInterval × unitInterval → unitInterval × unitInterval :=
    fun p => (p.1, projIcc 0 1 zero_le_one (3 * (p.2 : ℝ)))
  let s₂ : unitInterval × unitInterval → unitInterval × unitInterval :=
    fun p => (p.1, projIcc 0 1 zero_le_one (3 * (p.2 : ℝ) - 1))
  let s₃ : unitInterval × unitInterval → unitInterval × unitInterval :=
    fun p => (p.1, projIcc 0 1 zero_le_one (3 * (p.2 : ℝ) - 2))
  let F₁₂ : unitInterval × unitInterval → S :=
    fun p => if (p.2 : ℝ) ≤ 1 / 3 then H₁ (s₁ p) else H₂ (s₂ p)
  have hF₁₂ : Continuous F₁₂ := by
    refine Continuous.if_le (by fun_prop) (by fun_prop)
      (continuous_subtype_val.comp continuous_snd) continuous_const ?_
    intro p hp
    have hp1 : projIcc 0 1 zero_le_one (3 * (p.2 : ℝ)) = 1 := by
      rw [hp]; ext; change max (0 : ℝ) (min 1 (3 * (1 / 3))) = 1; norm_num
    have hp0 : projIcc 0 1 zero_le_one (3 * (p.2 : ℝ) - 1) = 0 := by
      rw [hp]; ext; simp
    change H₁ (p.1, _) = H₂ (p.1, _)
    rw [hp1, hp0, h12]
  let F_all : unitInterval × unitInterval → S :=
    fun p => if (p.2 : ℝ) ≤ 2 / 3 then F₁₂ p else H₃ (s₃ p)
  have hF_all : Continuous F_all := by
    refine Continuous.if_le hF₁₂ (by fun_prop)
      (continuous_subtype_val.comp continuous_snd) continuous_const ?_
    intro p hp
    have hnot : ¬ ((p.2 : ℝ) ≤ 1 / 3) := by linarith
    have hp1 : projIcc 0 1 zero_le_one (3 * (p.2 : ℝ) - 1) = 1 := by
      rw [hp]; ext; change max (0 : ℝ) (min 1 (3 * (2 / 3) - 1)) = 1; norm_num
    have hp0 : projIcc 0 1 zero_le_one (3 * (p.2 : ℝ) - 2) = 0 := by
      rw [hp]; ext; change max (0 : ℝ) (min 1 (3 * (2 / 3) - 2)) = 0; norm_num
    dsimp [F₁₂]
    simp only [hnot, ↓reduceIte]
    change H₂ (p.1, _) = H₃ (p.1, _)
    rw [hp1, hp0, h23_match]
  refine ⟨⟨F_all, hF_all⟩, fun _ => mem_univ _, fun t => ?_, fun t => ?_, fun s => ?_, fun s => ?_⟩
  · dsimp [F_all, F₁₂, s₁, H₁]
    split_ifs with h1 h2
    · have hp0 : projIcc 0 1 zero_le_one (3 * (0 : ℝ)) = 0 := by
        rw [mul_zero]; exact projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
      rw [hp0]
      exact reparamHomotopy_zero _ _ _ _ _ t
    · norm_num at h2
    · norm_num at h1
  · dsimp [F_all, s₃]
    split_ifs with h1
    · norm_num at h1
    · have hp1 : projIcc 0 1 zero_le_one (3 * (1 : ℝ) - 2) = 1 := by
        ext; change max (0 : ℝ) (min 1 (3 * 1 - 2)) = 1; norm_num
      rw [hp1]
      dsimp [H₃]
      simp only [sub_self, zero_mul]
      have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
        projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
      rw [h0, hβ0]
  · dsimp [F_all, F₁₂, s₁, s₂, s₃, H₁]
    split_ifs with h1 h2
    · exact reparamHomotopy_left _ _ _ _ _ _
    · dsimp [H₂, g_all, g₁₂, g₁]
      split_ifs with h3 h4
      · simp only [mul_zero]
        have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
          projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
        rw [h0, hβ0, loopToPath_zero]
      · norm_num at h4
      · norm_num at h3
    · dsimp [H₃]
      have harg : (1 - (projIcc 0 1 zero_le_one (3 * (s : ℝ) - 2) : ℝ)) *
          min (3 * 0) (3 * (1 - 0)) = 0 := by norm_num
      have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
        projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
      rw [harg, h0, hβ0, loopToPath_zero]
  · dsimp [F_all, F₁₂, s₁, s₂, s₃, H₁]
    split_ifs with h1 h2
    · exact reparamHomotopy_right _ _ _ _ _ _
    · dsimp [H₂, g_all, g₃]
      split_ifs with h3
      · norm_num at h3
      · simp only [sub_self, mul_zero]
        have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
          projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
        rw [h0, hβ0, loopToPath_one]
    · dsimp [H₃]
      have harg : (1 - (projIcc 0 1 zero_le_one (3 * (s : ℝ) - 2) : ℝ)) *
          min (3 * 1) (3 * (1 - 1)) = 0 := by norm_num
      have h0 : projIcc 0 1 zero_le_one (0 : ℝ) = 0 :=
        projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)
      rw [harg, h0, hβ0, loopToPath_one]

/-! ## Splitting a Loop at a Non-Adjacent Self-Intersection -/

/-- First sub-chain when splitting `γ` at `γ ⟨0, hn⟩ s = γ j t`. -/
noncomputable def splitChain₁ {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (j : Fin n) (s t : unitInterval) (k : Fin (j.1 + 1)) : C(unitInterval, S) :=
  if k.1 = 0 then subPathSeg (γ ⟨0, hn⟩) s 1
  else if hkj : k.1 < j.1 then γ ⟨k.1, Nat.lt_trans hkj j.2⟩
  else subPathSeg (γ j) 0 t

/-- Second sub-chain when splitting `γ` at `γ ⟨0, hn⟩ s = γ j t`. -/
noncomputable def splitChain₂ {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (j : Fin n) (s t : unitInterval) (k : Fin (n - j.1 + 1)) : C(unitInterval, S) :=
  if k.1 = 0 then subPathSeg (γ j) t 1
  else if hkn : k.1 < n - j.1 then γ ⟨j.1 + k.1, by omega⟩
  else subPathSeg (γ ⟨0, hn⟩) 0 s

theorem splitChain₁_match {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0)
    (j : Fin n) (hj1 : 2 ≤ j.1) (s t : unitInterval) (heq : γ ⟨0, hn⟩ s = γ j t)
    (k : Fin (j.1 + 1)) :
    splitChain₁ hn γ j s t k 1 =
      splitChain₁ hn γ j s t (finNext (by omega : 0 < j.1 + 1) k) 0 := by
  have ha : 0 < j.1 + 1 := by omega
  by_cases hk0 : k.1 = 0
  · have hfn : finNext ha k = ⟨1, by omega⟩ := by
      ext; dsimp [finNext]; rw [hk0]; exact Nat.mod_eq_of_lt (by omega)
    rw [hfn]
    dsimp [splitChain₁]
    simp only [hk0, ↓reduceIte, ↓reduceDIte, show 1 < j.1 by omega, subPathSeg_one]
    have h0 := hmatch ⟨0, hn⟩
    have hfn0 : finNext hn ⟨0, hn⟩ = ⟨1, by omega⟩ := by
      ext; dsimp [finNext]; exact Nat.mod_eq_of_lt (by omega)
    rwa [hfn0] at h0
  · by_cases hkj : k.1 < j.1
    · by_cases hk_last : k.1 + 1 = j.1
      · have hfn : finNext ha k = ⟨j.1, by omega⟩ := by
          ext; dsimp [finNext]; rw [hk_last]; exact Nat.mod_eq_of_lt (by omega)
        rw [hfn]
        dsimp [splitChain₁]
        simp only [hk0, hkj, ↓reduceIte, ↓reduceDIte, show j.1 ≠ 0 by omega, lt_irrefl,
          subPathSeg_zero]
        have hk_m := hmatch ⟨k.1, by omega⟩
        have hfn_n : finNext hn ⟨k.1, by omega⟩ = j := by
          ext; dsimp [finNext]; rw [hk_last]; exact Nat.mod_eq_of_lt j.2
        rwa [hfn_n] at hk_m
      · have hlt' : k.1 + 1 < j.1 := by omega
        have hfn : finNext ha k = ⟨k.1 + 1, by omega⟩ := by
          ext; dsimp [finNext]; exact Nat.mod_eq_of_lt (by omega)
        rw [hfn]
        dsimp [splitChain₁]
        simp only [hk0, hkj, ↓reduceIte, ↓reduceDIte, hlt']
        have hk_m := hmatch ⟨k.1, by omega⟩
        have hfn_n : finNext hn ⟨k.1, by omega⟩ = ⟨k.1 + 1, by omega⟩ := by
          ext; dsimp [finNext]; exact Nat.mod_eq_of_lt (by omega)
        rwa [hfn_n] at hk_m
    · have hk_eq : k.1 = j.1 := by omega
      have hfn : finNext ha k = ⟨0, ha⟩ := by
        ext; dsimp [finNext]; rw [hk_eq, Nat.mod_self]
      rw [hfn]
      dsimp [splitChain₁]
      simp only [hk0, hkj, ↓reduceIte, ↓reduceDIte, subPathSeg_one, subPathSeg_zero]
      exact heq.symm

theorem splitChain₂_match {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0)
    (j : Fin n) (hj2 : j.1 + 2 ≤ n) (s t : unitInterval) (heq : γ ⟨0, hn⟩ s = γ j t)
    (k : Fin (n - j.1 + 1)) :
    splitChain₂ hn γ j s t k 1 =
      splitChain₂ hn γ j s t (finNext (by omega : 0 < n - j.1 + 1) k) 0 := by
  have hb : 0 < n - j.1 + 1 := by omega
  by_cases hk0 : k.1 = 0
  · have hfn : finNext hb k = ⟨1, by omega⟩ := by
      ext; dsimp [finNext]; rw [hk0]; exact Nat.mod_eq_of_lt (by omega)
    rw [hfn]
    dsimp [splitChain₂]
    simp only [hk0, ↓reduceIte, ↓reduceDIte, show 1 < n - j.1 by omega, subPathSeg_one]
    have hj_m := hmatch j
    have hfn_n : finNext hn j = ⟨j.1 + 1, by omega⟩ := by
      ext; dsimp [finNext]; exact Nat.mod_eq_of_lt (by omega)
    rwa [hfn_n] at hj_m
  · by_cases hkn : k.1 < n - j.1
    · by_cases hk_last : k.1 + 1 = n - j.1
      · have hfn : finNext hb k = ⟨n - j.1, by omega⟩ := by
          ext; dsimp [finNext]; rw [hk_last]; exact Nat.mod_eq_of_lt (by omega)
        rw [hfn]
        dsimp [splitChain₂]
        simp only [hk0, hkn, ↓reduceIte, ↓reduceDIte, show n - j.1 ≠ 0 by omega, lt_irrefl,
          subPathSeg_zero]
        have hk_m := hmatch ⟨j.1 + k.1, by omega⟩
        have hfn_n : finNext hn ⟨j.1 + k.1, by omega⟩ = ⟨0, hn⟩ := by
          ext; dsimp [finNext]; rw [show j.1 + k.1 + 1 = n by omega, Nat.mod_self]
        rwa [hfn_n] at hk_m
      · have hlt' : k.1 + 1 < n - j.1 := by omega
        have hfn : finNext hb k = ⟨k.1 + 1, by omega⟩ := by
          ext; dsimp [finNext]; exact Nat.mod_eq_of_lt (by omega)
        rw [hfn]
        dsimp [splitChain₂]
        simp only [hk0, hkn, ↓reduceIte, ↓reduceDIte, hlt']
        have hk_m := hmatch ⟨j.1 + k.1, by omega⟩
        have hfn_n : finNext hn ⟨j.1 + k.1, by omega⟩ = ⟨j.1 + (k.1 + 1), by omega⟩ := by
          ext; dsimp [finNext]
          rw [show j.1 + k.1 + 1 = j.1 + (k.1 + 1) by omega]
          exact Nat.mod_eq_of_lt (by omega)
        rwa [hfn_n] at hk_m
    · have hk_eq : k.1 = n - j.1 := by omega
      have hfn : finNext hb k = ⟨0, hb⟩ := by
        ext; dsimp [finNext]; rw [hk_eq, Nat.mod_self]
      rw [hfn]
      dsimp [splitChain₂]
      simp only [hk0, hkn, ↓reduceIte, ↓reduceDIte, subPathSeg_one, subPathSeg_zero]
      exact heq

private theorem agrees_with_loop_path_of_piece_agreement
    {m : ℕ} (hm : 0 < m) (δ : Fin m → C(unitInterval, S))
    (hmatch : ∀ k : Fin m, δ k 1 = δ (finNext hm k) 0)
    (F : ℝ → S) (hpiece : ∀ (k : Fin m) (r : unitInterval),
      F ((k.1 : ℝ) + (r : ℝ)) = δ k r) (τ : unitInterval) :
    F ((τ : ℝ) * (m : ℝ)) = loopToPath (concatLoop hm δ hmatch) τ := by
  rw [loopToPath_apply, concatLoop_exp_mul]
  by_cases hτ1 : (τ : ℝ) = 1
  · rw [hτ1, one_mul]
    have hlast : m - 1 < m := Nat.sub_lt hm zero_lt_one
    have hcast : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + ((1 : unitInterval) : ℝ) := by
      rw [Set.Icc.coe_one]
      exact_mod_cast (Nat.sub_add_cancel hm).symm
    have hperiod : chainReal hm δ (m : ℝ) = chainReal hm δ 0 := by
      simpa only [zero_add] using chainReal_add_nat hm δ 0
    have hstart : chainReal hm δ 0 = δ ⟨0, hm⟩ 0 := by
      simpa only [Nat.cast_zero, Set.Icc.coe_zero, add_zero] using
        chainReal_nat_add hm δ hmatch ⟨0, hm⟩ 0
    have hnext : finNext hm ⟨m - 1, hlast⟩ = ⟨0, hm⟩ := by
      ext
      dsimp [finNext]
      rw [Nat.sub_add_cancel hm, Nat.mod_self]
    calc
      F (m : ℝ) = δ ⟨m - 1, hlast⟩ 1 := hcast.symm ▸ hpiece ⟨m - 1, hlast⟩ 1
      _ = δ ⟨0, hm⟩ 0 := by rw [hmatch, hnext]
      _ = chainReal hm δ (m : ℝ) := (hperiod.trans hstart).symm
  · have hτ_lt : (τ : ℝ) < 1 := lt_of_le_of_ne τ.2.2 hτ1
    let y : ℝ := (τ : ℝ) * (m : ℝ)
    have hy0 : 0 ≤ y := mul_nonneg τ.2.1 (by positivity)
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hy_lt : y < (m : ℝ) := mul_lt_of_lt_one_left hm_pos hτ_lt
    have hfl_nn : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
    have hfl_lt : ⌊y⌋ < (m : ℤ) := by rw [Int.floor_lt]; exact_mod_cast hy_lt
    let k : ℕ := ⌊y⌋.toNat
    have hk_lt : k < m := by omega
    have hk_eq : (k : ℝ) + (unitFract y : ℝ) = y := by
      have hfl_eq : (k : ℤ) = ⌊y⌋ := Int.toNat_of_nonneg hfl_nn
      change ((k : ℤ) : ℝ) + Int.fract y = y
      rw [hfl_eq, Int.floor_add_fract]
    change F y = chainReal hm δ y
    rw [← hk_eq, hpiece ⟨k, hk_lt⟩ (unitFract y),
      chainReal_nat_add hm δ hmatch ⟨k, hk_lt⟩ (unitFract y)]

private theorem chainReal_split_first
    {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0)
    (j : Fin n) (s t : unitInterval)
    {u₁ : ℝ → ℝ}
    (hu₁_left : ∀ y : ℝ, y ≤ 1 → u₁ y = (1 - y) * (s : ℝ) + y)
    (hu₁_mid : ∀ y : ℝ, 1 ≤ y → y ≤ (j.1 : ℝ) → u₁ y = y)
    (hu₁_right : ∀ y : ℝ, (j.1 : ℝ) ≤ y →
      u₁ y = (j.1 : ℝ) + (y - (j.1 : ℝ)) * (t : ℝ))
    (k : Fin (j.1 + 1)) (r : unitInterval) :
    chainReal hn γ (u₁ ((k.1 : ℝ) + (r : ℝ))) = splitChain₁ hn γ j s t k r := by
  dsimp [splitChain₁]
  by_cases hk0 : k.1 = 0
  · simp only [hk0, ↓reduceIte, Nat.cast_zero, zero_add]
    rw [hu₁_left (r : ℝ) r.2.2]
    let v : unitInterval := ⟨(1 - (r : ℝ)) * (s : ℝ) + (r : ℝ) * 1,
      by nlinarith [r.2.1, r.2.2, s.2.1], by nlinarith [r.2.1, r.2.2, s.2.2]⟩
    have hv : (1 - (r : ℝ)) * (s : ℝ) + (r : ℝ) = ((0 : ℕ) : ℝ) + (v : ℝ) := by
      dsimp [v]; ring
    rw [hv, chainReal_nat_add hn γ hmatch ⟨0, hn⟩ v]
    rfl
  · by_cases hkj : k.1 < j.1
    · simp only [hk0, hkj, ↓reduceIte, ↓reduceDIte]
      have hk1 : (1 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ k.1)
      have hkj' : (k.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast (by omega : k.1 + 1 ≤ j.1)
      rw [hu₁_mid ((k.1 : ℝ) + (r : ℝ)) (by linarith [r.2.1]) (by linarith [r.2.2]),
        chainReal_nat_add hn γ hmatch ⟨k.1, by omega⟩ r]
    · have hk_eq : k.1 = j.1 := by omega
      simp only [hk0, hkj, ↓reduceIte, ↓reduceDIte]
      rw [hk_eq, hu₁_right ((j.1 : ℝ) + (r : ℝ)) (by linarith [r.2.1])]
      let v : unitInterval := ⟨(1 - (r : ℝ)) * 0 + (r : ℝ) * (t : ℝ),
        by nlinarith [r.2.1, r.2.2, t.2.1], by nlinarith [r.2.1, r.2.2, t.2.2]⟩
      have hv : (j.1 : ℝ) + ((j.1 : ℝ) + (r : ℝ) - (j.1 : ℝ)) * (t : ℝ) =
          (j.1 : ℝ) + (v : ℝ) := by dsimp [v]; ring
      rw [hv, chainReal_nat_add hn γ hmatch j v]
      rfl

private theorem chainReal_split_second
    {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0)
    (j : Fin n) (s t : unitInterval)
    {u₂ : ℝ → ℝ}
    (hu₂_left : ∀ y : ℝ, y ≤ 1 → u₂ y = (j.1 : ℝ) + (1 - y) * (t : ℝ) + y)
    (hu₂_mid : ∀ y : ℝ, 1 ≤ y → y ≤ ((n - j.1 : ℕ) : ℝ) → u₂ y = (j.1 : ℝ) + y)
    (hu₂_right : ∀ y : ℝ, ((n - j.1 : ℕ) : ℝ) ≤ y →
      u₂ y = (n : ℝ) + (y - ((n - j.1 : ℕ) : ℝ)) * (s : ℝ))
    (k : Fin (n - j.1 + 1)) (r : unitInterval) :
    chainReal hn γ (u₂ ((k.1 : ℝ) + (r : ℝ))) = splitChain₂ hn γ j s t k r := by
  dsimp [splitChain₂]
  by_cases hk0 : k.1 = 0
  · simp only [hk0, ↓reduceIte, Nat.cast_zero, zero_add]
    rw [hu₂_left (r : ℝ) r.2.2]
    let v : unitInterval := ⟨(1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) * 1,
      by nlinarith [r.2.1, r.2.2, t.2.1], by nlinarith [r.2.1, r.2.2, t.2.2]⟩
    have hv : (j.1 : ℝ) + (1 - (r : ℝ)) * (t : ℝ) + (r : ℝ) = (j.1 : ℝ) + (v : ℝ) := by
      dsimp [v]; ring
    rw [hv, chainReal_nat_add hn γ hmatch j v]
    rfl
  · by_cases hkn : k.1 < n - j.1
    · simp only [hk0, hkn, ↓reduceIte, ↓reduceDIte]
      have hk1 : (1 : ℝ) ≤ (k.1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ k.1)
      have hkn' : (k.1 : ℝ) + 1 ≤ ((n - j.1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : k.1 + 1 ≤ n - j.1)
      rw [hu₂_mid ((k.1 : ℝ) + (r : ℝ)) (by linarith [r.2.1]) (by linarith [r.2.2])]
      have hsum : (j.1 : ℝ) + ((k.1 : ℝ) + (r : ℝ)) = (((j.1 + k.1 : ℕ) : ℝ) + (r : ℝ)) := by
        push_cast; ring
      rw [hsum, chainReal_nat_add hn γ hmatch ⟨j.1 + k.1, by omega⟩ r]
    · have hk_eq : k.1 = n - j.1 := by omega
      simp only [hk0, hkn, ↓reduceIte, ↓reduceDIte]
      rw [hk_eq, hu₂_right (((n - j.1 : ℕ) : ℝ) + (r : ℝ)) (by linarith [r.2.1])]
      let v : unitInterval := ⟨(1 - (r : ℝ)) * 0 + (r : ℝ) * (s : ℝ),
        by nlinarith [r.2.1, r.2.2, s.2.1], by nlinarith [r.2.1, r.2.2, s.2.2]⟩
      have hv : (n : ℝ) + (((n - j.1 : ℕ) : ℝ) + (r : ℝ) - ((n - j.1 : ℕ) : ℝ)) * (s : ℝ) =
          (((0 : ℕ) : ℝ) + (v : ℝ)) + (n : ℝ) := by dsimp [v]; ring
      rw [hv, chainReal_add_nat, chainReal_nat_add hn γ hmatch ⟨0, hn⟩ v]
      rfl

private theorem homotopic_of_two_piece_reparam
    {n : ℕ} (hn : 0 < n) (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0)
    (j : Fin n) (s t : unitInterval)
    {u₁ u₂ : ℝ → ℝ} (hu₁_cont : Continuous u₁) (hu₂_cont : Continuous u₂)
    (hu₁_left : ∀ y : ℝ, y ≤ 1 → u₁ y = (1 - y) * (s : ℝ) + y)
    (hu₁_right : ∀ y : ℝ, (j.1 : ℝ) ≤ y →
      u₁ y = (j.1 : ℝ) + (y - (j.1 : ℝ)) * (t : ℝ))
    (hu₂_left : ∀ y : ℝ, y ≤ 1 → u₂ y = (j.1 : ℝ) + (1 - y) * (t : ℝ) + y)
    (hu₂_right : ∀ y : ℝ, ((n - j.1 : ℕ) : ℝ) ≤ y →
      u₂ y = (n : ℝ) + (y - ((n - j.1 : ℕ) : ℝ)) * (s : ℝ))
    (htwo : 0 < 2) (δ : Fin 2 → C(unitInterval, S))
    (hmatch_δ : ∀ i : Fin 2, δ i 1 = δ (finNext htwo i) 0)
    (hf_u₁_all : ∀ τ : unitInterval,
      chainReal hn γ (u₁ ((τ : ℝ) * ((j.1 + 1 : ℕ) : ℝ))) = δ ⟨0, htwo⟩ τ)
    (hf_u₂_all : ∀ τ : unitInterval,
      chainReal hn γ (u₂ ((τ : ℝ) * ((n - j.1 + 1 : ℕ) : ℝ))) = δ ⟨1, by omega⟩ τ) :
    ClosedCurvesHomotopicIn univ (concatLoop hn γ hmatch) (concatLoop htwo δ hmatch_δ) := by
  let β_map : ℝ → ℝ := fun x =>
    if x ≤ 1 / 2 then u₁ (2 * x * ((j.1 + 1 : ℕ) : ℝ))
    else u₂ ((2 * x - 1) * ((n - j.1 + 1 : ℕ) : ℝ))
  have hβ_cont : Continuous β_map := by
    refine Continuous.if_le (hu₁_cont.comp (by fun_prop)) (hu₂_cont.comp (by fun_prop))
      continuous_id continuous_const ?_
    intro x hx
    rw [hx]
    have h1 : (2 : ℝ) * (1 / 2) * ((j.1 + 1 : ℕ) : ℝ) = (j.1 : ℝ) + 1 := by push_cast; ring
    have h2 : ((2 : ℝ) * (1 / 2) - 1) * ((n - j.1 + 1 : ℕ) : ℝ) = 0 := by ring
    rw [h1, h2, hu₁_right ((j.1 : ℝ) + 1) (by linarith), hu₂_left 0 zero_le_one]
    ring
  let H_reparam : C(unitInterval × unitInterval, S) :=
    ⟨fun p => chainReal hn γ ((1 - (p.2 : ℝ)) * ((p.1 : ℝ) * (n : ℝ)) + (p.2 : ℝ) * β_map
      (p.1 : ℝ)),
      (continuous_chainReal hn γ hmatch).comp (by fun_prop)⟩
  refine closedCurvesHomotopicIn_of_unitInterval H_reparam (fun _ => mem_univ _)
    (fun r => ?_) (fun u => ?_) (fun u => ?_)
  · change chainReal hn γ ((1 - (r : ℝ)) * (1 * (n : ℝ)) + (r : ℝ) * β_map 1) =
      chainReal hn γ ((1 - (r : ℝ)) * (0 * (n : ℝ)) + (r : ℝ) * β_map 0)
    have hβ0 : β_map 0 = (s : ℝ) := by
      dsimp [β_map]
      have h0_le : (0 : ℝ) ≤ 1 / 2 := by norm_num
      simp only [h0_le, ↓reduceIte, mul_zero, zero_mul]
      rw [hu₁_left 0 zero_le_one]
      ring
    have hβ1 : β_map 1 = (n : ℝ) + (s : ℝ) := by
      dsimp [β_map]
      have hnot : ¬ ((1 : ℝ) ≤ 1 / 2) := by norm_num
      simp only [hnot, ↓reduceIte]
      have h1 : (2 * (1 : ℝ) - 1) * ((n - j.1 + 1 : ℕ) : ℝ) = ((n - j.1 : ℕ) : ℝ) + 1 := by
        push_cast; ring
      rw [h1, hu₂_right (((n - j.1 : ℕ) : ℝ) + 1) (by linarith)]
      ring
    rw [hβ0, hβ1,
      show (1 - (r : ℝ)) * (1 * (n : ℝ)) + (r : ℝ) * ((n : ℝ) + (s : ℝ)) =
        ((1 - (r : ℝ)) * (0 * (n : ℝ)) + (r : ℝ) * (s : ℝ)) + (n : ℝ) by ring,
      chainReal_add_nat]
  · change chainReal hn γ ((1 - 0) * ((u : ℝ) * (n : ℝ)) + 0 * β_map (u : ℝ)) = _
    rw [sub_zero, one_mul, zero_mul, add_zero, concatLoop_exp_mul]
  · change chainReal hn γ ((1 - 1) * ((u : ℝ) * (n : ℝ)) + 1 * β_map (u : ℝ)) = _
    rw [sub_self, zero_mul, one_mul, zero_add, concatLoop_exp_mul]
    dsimp [β_map]
    split_ifs with hu
    · let τ : unitInterval := ⟨2 * (u : ℝ), by linarith [u.2.1], by linarith⟩
      have h1 : 2 * (u : ℝ) * ((j.1 + 1 : ℕ) : ℝ) = (τ : ℝ) * ((j.1 + 1 : ℕ) : ℝ) := rfl
      have h2 : (u : ℝ) * (2 : ℝ) = ((0 : ℕ) : ℝ) + (τ : ℝ) := by dsimp [τ]; ring
      rw [h1, hf_u₁_all τ, h2, chainReal_nat_add htwo δ hmatch_δ ⟨0, htwo⟩ τ]
    · have hgt : 1 / 2 < (u : ℝ) := not_le.mp hu
      let τ : unitInterval := ⟨2 * (u : ℝ) - 1, by linarith, by linarith [u.2.2]⟩
      have h1 : (2 * (u : ℝ) - 1) * ((n - j.1 + 1 : ℕ) : ℝ) =
          (τ : ℝ) * ((n - j.1 + 1 : ℕ) : ℝ) := rfl
      have h2 : (u : ℝ) * (2 : ℝ) = ((1 : ℕ) : ℝ) + (τ : ℝ) := by dsimp [τ]; ring
      rw [h1, hf_u₂_all τ, h2, chainReal_nat_add htwo δ hmatch_δ ⟨1, by omega⟩ τ]

/-- If `γ : Fin n → C(unitInterval, S)` has `γ ⟨0, hn⟩ s = γ j t` with `2 ≤ j.1` and `j.1 + 2 ≤ n`,
and both resulting sub-loops of `< n` pieces are null-homotopic in `univ`, then `concatLoop hn γ`
is null-homotopic in `univ`. -/
theorem nullHomotopic_of_split_nonadjacent {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval, S))
    (hmatch : ∀ i : Fin n, γ i 1 = γ (finNext hn i) 0)
    (j : Fin n) (hj1 : 2 ≤ j.1) (hj2 : j.1 + 2 ≤ n)
    (s t : unitInterval) (heq : γ ⟨0, hn⟩ s = γ j t)
    (hnull₁ : ClosedCurveIsNullHomotopicIn univ
      (concatLoop (by omega : 0 < j.1 + 1) (splitChain₁ hn γ j s t)
        (splitChain₁_match hn γ hmatch j hj1 s t heq)))
    (hnull₂ : ClosedCurveIsNullHomotopicIn univ
      (concatLoop (by omega : 0 < n - j.1 + 1) (splitChain₂ hn γ j s t)
        (splitChain₂_match hn γ hmatch j hj2 s t heq))) :
    ClosedCurveIsNullHomotopicIn univ (concatLoop hn γ hmatch) := by
  have ha : 0 < j.1 + 1 := by omega
  have hb : 0 < n - j.1 + 1 := by omega
  let γ₁ := splitChain₁ hn γ j s t
  let γ₂ := splitChain₂ hn γ j s t
  let hmatch₁ := splitChain₁_match hn γ hmatch j hj1 s t heq
  let hmatch₂ := splitChain₂_match hn γ hmatch j hj2 s t heq
  let L₁ := concatLoop ha γ₁ hmatch₁
  let L₂ := concatLoop hb γ₂ hmatch₂
  let p₀ : S := γ ⟨0, hn⟩ s
  have hL₁_1 : L₁ 1 = p₀ := by
    have h := concatLoop_exp_piece ha γ₁ hmatch₁ ⟨0, ha⟩ 0
    simp only [Nat.cast_zero, Set.Icc.coe_zero, add_zero, mul_zero, zero_div, Circle.exp_zero] at h
    rw [h]
    dsimp [γ₁, splitChain₁]
    simp [p₀]
  have hL₂_1 : L₂ 1 = p₀ := by
    have h := concatLoop_exp_piece hb γ₂ hmatch₂ ⟨0, hb⟩ 0
    simp only [Nat.cast_zero, Set.Icc.coe_zero, add_zero, mul_zero, zero_div, Circle.exp_zero] at h
    rw [h]
    dsimp [γ₂, splitChain₂]
    simp [p₀, heq]
  have htwo : 0 < 2 := by omega
  let δ : Fin 2 → C(unitInterval, S) := fun i => if i.1 = 0 then loopToPath L₁ else loopToPath L₂
  have hmatch_δ : ∀ i : Fin 2, δ i 1 = δ (finNext htwo i) 0 := by
    intro i
    dsimp [δ, finNext]
    split_ifs <;> simp [hL₁_1, hL₂_1]
  obtain ⟨H₁, _, hH₁0, hH₁1, hH₁s0, hH₁s1⟩ := pathsHomotopicRelIn_const_of_nullHomotopic hnull₁
  obtain ⟨H₂, _, hH₂0, hH₂1, hH₂s0, hH₂s1⟩ := pathsHomotopicRelIn_const_of_nullHomotopic hnull₂
  let δ_const : Fin 2 → C(unitInterval, S) := fun _ => ContinuousMap.const unitInterval p₀
  have hmatch_const : ∀ i : Fin 2, δ_const i 1 = δ_const (finNext htwo i) 0 := fun _ => rfl
  let H_δ : Fin 2 → C(unitInterval × unitInterval, S) := fun i => if i.1 = 0 then H₁ else H₂
  have hhom_const : ClosedCurvesHomotopicIn univ
      (concatLoop htwo δ hmatch_δ) (concatLoop htwo δ_const hmatch_const) := by
    refine concatLoop_homotopic htwo δ δ_const hmatch_δ hmatch_const H_δ
      (fun _ _ => mem_univ _) (fun i r => ?_) (fun i r => ?_) (fun i r => ?_)
    · dsimp [H_δ, δ]; split_ifs
      · exact hH₁0 r
      · exact hH₂0 r
    · dsimp [H_δ, δ_const]; split_ifs
      · rw [hH₁1 r]
        exact hL₁_1
      · rw [hH₂1 r]
        exact hL₂_1
    · by_cases hi0 : i.1 = 0
      · have hfn : finNext htwo i = ⟨1, by omega⟩ := by
          ext; dsimp [finNext]; rw [hi0]
        rw [hfn]
        dsimp [H_δ]
        simp only [hi0, ↓reduceIte]
        rw [hH₁s1 r, hH₂s0 r, loopToPath_one, loopToPath_zero, hL₁_1, hL₂_1]
      · have hi1 : i.1 = 1 := by omega
        have hfn : finNext htwo i = ⟨0, htwo⟩ := by
          ext; dsimp [finNext]; rw [hi1]
        rw [hfn]
        dsimp [H_δ]
        simp only [hi0, ↓reduceIte]
        rw [hH₂s1 r, hH₁s0 r, loopToPath_one, loopToPath_zero, hL₂_1, hL₁_1]
  have hδ_const_eq : concatLoop htwo δ_const hmatch_const = ContinuousMap.const Circle p₀ := by
    ext w
    obtain ⟨u, rfl⟩ := exists_unitInterval_exp w
    rw [concatLoop_exp_mul]
    dsimp [chainReal, chainFun, δ_const]
  have hδ_null : ClosedCurveIsNullHomotopicIn univ (concatLoop htwo δ hmatch_δ) := by
    refine ⟨p₀, mem_univ p₀, ?_⟩
    rwa [← hδ_const_eq]
  -- Now show `concatLoop hn γ hmatch` is homotopic to `concatLoop htwo δ hmatch_δ`.
  let u₁ : ℝ → ℝ := fun y =>
    if y ≤ 1 then (1 - y) * (s : ℝ) + y
    else if y ≤ (j.1 : ℝ) then y
    else (j.1 : ℝ) + (y - (j.1 : ℝ)) * (t : ℝ)
  let u₂ : ℝ → ℝ := fun y =>
    if y ≤ 1 then (j.1 : ℝ) + (1 - y) * (t : ℝ) + y
    else if y ≤ ((n - j.1 : ℕ) : ℝ) then (j.1 : ℝ) + y
    else (n : ℝ) + (y - ((n - j.1 : ℕ) : ℝ)) * (s : ℝ)
  have hu₁_cont : Continuous u₁ := by
    refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le continuous_id (by fun_prop) continuous_id continuous_const
        (fun y hy => by rw [hy]; ring)
    · intro y hy
      rw [hy]
      have h1j : (1 : ℝ) ≤ (j.1 : ℝ) := by
        have : (2 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast hj1
        linarith
      simp only [h1j, ↓reduceIte]
      ring
  have hu₂_cont : Continuous u₂ := by
    refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
    · refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const (fun y hy
      => by
        rw [hy]
        have : (j.1 : ℝ) + ((n - j.1 : ℕ) : ℝ) = (n : ℝ) := by
          exact_mod_cast Nat.add_sub_of_le (by omega : j.1 ≤ n)
        nlinarith)
    · intro y hy
      rw [hy]
      have h1n : (1 : ℝ) ≤ ((n - j.1 : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ ((n - j.1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - j.1)
        linarith
      simp only [h1n, ↓reduceIte]
      ring
  have hu₁_left : ∀ y : ℝ, y ≤ 1 → u₁ y = (1 - y) * (s : ℝ) + y := by
    intro y hy; dsimp [u₁]; split_ifs; rfl
  have hu₁_mid : ∀ y : ℝ, 1 ≤ y → y ≤ (j.1 : ℝ) → u₁ y = y := by
    intro y hy1 hyj; dsimp [u₁]; split_ifs with h1
    · have : y = 1 := le_antisymm h1 hy1
      rw [this]; ring
    · rfl
  have hu₁_right : ∀ y : ℝ, (j.1 : ℝ) ≤ y → u₁ y = (j.1 : ℝ) + (y - (j.1 : ℝ)) * (t : ℝ) := by
    intro y hy
    have hj2_real : (2 : ℝ) ≤ (j.1 : ℝ) := by exact_mod_cast hj1
    have hnot1 : ¬ (y ≤ 1) := by linarith
    dsimp [u₁]
    simp only [hnot1, ↓reduceIte]
    split_ifs with h2
    · have : y = (j.1 : ℝ) := le_antisymm h2 hy
      rw [this]; ring
    · rfl
  have hu₂_left : ∀ y : ℝ, y ≤ 1 → u₂ y = (j.1 : ℝ) + (1 - y) * (t : ℝ) + y := by
    intro y hy; dsimp [u₂]; split_ifs; rfl
  have hu₂_mid : ∀ y : ℝ, 1 ≤ y → y ≤ ((n - j.1 : ℕ) : ℝ) → u₂ y = (j.1 : ℝ) + y := by
    intro y hy1 hyn; dsimp [u₂]; split_ifs with h1
    · have : y = 1 := le_antisymm h1 hy1
      rw [this]; ring
    · rfl
  have hu₂_right : ∀ y : ℝ, ((n - j.1 : ℕ) : ℝ) ≤ y →
      u₂ y = (n : ℝ) + (y - ((n - j.1 : ℕ) : ℝ)) * (s : ℝ) := by
    intro y hy
    have h2 : (2 : ℝ) ≤ ((n - j.1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - j.1)
    have hnot1 : ¬ (y ≤ 1) := by linarith
    have hsum : (j.1 : ℝ) + ((n - j.1 : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.add_sub_of_le (by omega : j.1 ≤ n)
    dsimp [u₂]
    simp only [hnot1, ↓reduceIte]
    split_ifs with h_le
    · have : y = ((n - j.1 : ℕ) : ℝ) := le_antisymm h_le hy
      rw [this]; linarith
    · rfl
  have hf_u₁ := chainReal_split_first hn γ hmatch j s t hu₁_left hu₁_mid hu₁_right
  have hf_u₂ := chainReal_split_second hn γ hmatch j s t hu₂_left hu₂_mid hu₂_right
  have hf_u₁_all :=
    agrees_with_loop_path_of_piece_agreement ha γ₁ hmatch₁ (chainReal hn γ ∘ u₁) hf_u₁
  have hf_u₂_all :=
    agrees_with_loop_path_of_piece_agreement hb γ₂ hmatch₂ (chainReal hn γ ∘ u₂) hf_u₂
  have hhom_reparam := homotopic_of_two_piece_reparam hn γ hmatch j s t
    hu₁_cont hu₂_cont hu₁_left hu₁_right hu₂_left hu₂_right htwo δ hmatch_δ hf_u₁_all hf_u₂_all
  exact closedCurveIsNullHomotopicIn_of_homotopic hhom_reparam hδ_null

/-! ## Proof of (11.2): Non-Null-Homotopic `O`-Arc in a Non-Null-Homotopic Closed Curve -/

private structure CurveChartCover (S : Type u) [TopologicalSpace S] where
  small : S → Set S
  chart : S → Set S
  interpolate : S → S → S → unitInterval → S
  mem_small : ∀ z, z ∈ small z
  isOpen_small : ∀ z, IsOpen (small z)
  small_subset_chart : ∀ z, small z ⊆ chart z
  pair_subset_chart : ∀ z₁ z₂, (small z₁ ∩ small z₂).Nonempty →
    ∃ w ∈ ({z₁, z₂} : Set S), small z₁ ∪ small z₂ ⊆ chart w
  flat_pair : ∀ z₁ z₂, IsFlat (small z₁ ∪ small z₂)
  interpolate_zero : ∀ z, ∀ x ∈ chart z, ∀ y ∈ chart z, interpolate z x y 0 = x
  interpolate_one : ∀ z, ∀ x ∈ chart z, ∀ y ∈ chart z, interpolate z x y 1 = y
  interpolate_diag : ∀ z, ∀ x ∈ chart z, ∀ t, interpolate z x x t = x
  interpolate_continuous : ∀ z, ∀ γ₀ γ₁ : C(unitInterval, S),
    range γ₀ ⊆ chart z → range γ₁ ⊆ chart z →
    Continuous (fun p : unitInterval × unitInterval => interpolate z (γ₀ p.1) (γ₁ p.1) p.2)

private theorem exists_curve_chart_cover (hS : IsSurface S) : Nonempty (CurveChartCover S) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : SecondCountableTopology S := secondCountable_of_manifold hS.2.2
  let : MetricSpace S := TopologicalSpace.metrizableSpaceMetric S
  -- Step 1: Open cover `U z ⊆ ball z (ε z / 3)` and chart balls `W z` with interpolation `pt z`.
  have hW_ex : ∀ z : S, ∃ (W : Set S) (pt : S → S → unitInterval → S),
      z ∈ W ∧ IsOpen W ∧ IsFlat W ∧
      (∀ y₁ ∈ W, ∀ y₂ ∈ W, ∀ s, pt y₁ y₂ s ∈ W) ∧
      (∀ y₁ ∈ W, ∀ y₂ ∈ W, pt y₁ y₂ 0 = y₁) ∧
      (∀ y₁ ∈ W, ∀ y₂ ∈ W, pt y₁ y₂ 1 = y₂) ∧
      (∀ y ∈ W, ∀ s, pt y y s = y) ∧
      (∀ γ₀ γ₁ : C(unitInterval, S), range γ₀ ⊆ W → range γ₁ ⊆ W →
        Continuous (fun p : unitInterval × unitInterval => pt (γ₀ p.1) (γ₁ p.1) p.2)) := by
    intro z
    obtain ⟨W, pt, _, hzW, hW_open, _, hW_flat, hpt_mem, hpt0, hpt1, hpt_diag, hpt_cont⟩ :=
      exists_chart_ball_interp hS z isOpen_univ (mem_univ z)
    exact ⟨W, pt, hzW, hW_open, hW_flat, hpt_mem, hpt0, hpt1, hpt_diag, hpt_cont⟩
  choose W pt hzW hW_open hW_flat _hpt_mem hpt0 hpt1 hpt_diag hpt_cont using hW_ex
  have hε_ex : ∀ z : S, ∃ ε : ℝ, 0 < ε ∧ closedBall z ε ⊆ W z := by
    intro z
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hW_open z) z (hzW z)
    exact ⟨r / 2, half_pos hr, fun y hy => hball (lt_of_le_of_lt (mem_closedBall.mp hy)
      (half_lt_self hr))⟩
  choose ε hε_pos hε_ball using hε_ex
  have hU_ex : ∀ z : S, ∃ U : Set S, U ⊆ ball z (ε z / 3) ∧ z ∈ U ∧ IsOpen U := by
    intro z
    have hpos : 0 < ε z / 3 := by linarith [hε_pos z]
    exact ⟨ball z (ε z / 3), Subset.rfl, mem_ball_self hpos, isOpen_ball⟩
  choose U hU_ball hzU hU_open using hU_ex
  have hU_sub_W : ∀ z : S, U z ⊆ W z := fun z y hy =>
    hε_ball z (mem_closedBall.mpr (by linarith [mem_ball.mp (hU_ball z hy), hε_pos z]))
  have hU_pair : ∀ z₁ z₂ : S, (U z₁ ∩ U z₂).Nonempty →
      ∃ w ∈ ({z₁, z₂} : Set S), U z₁ ∪ U z₂ ⊆ W w := by
    intro z₁ z₂ ⟨u, hu₁, hu₂⟩
    have hu₁' : dist u z₁ < ε z₁ / 3 := mem_ball.mp (hU_ball z₁ hu₁)
    have hu₂' : dist u z₂ < ε z₂ / 3 := mem_ball.mp (hU_ball z₂ hu₂)
    by_cases hle : ε z₁ ≤ ε z₂
    · refine ⟨z₂, Or.inr (mem_singleton z₂), fun y hy => hε_ball z₂ (mem_closedBall.mpr ?_)⟩
      rcases hy with hy₁ | hy₂
      · have hy₁' : dist y z₁ < ε z₁ / 3 := mem_ball.mp (hU_ball z₁ hy₁)
        have htri : dist y z₂ ≤ dist y z₁ + dist z₁ u + dist u z₂ := dist_triangle4 y z₁ u z₂
        rw [dist_comm z₁ u] at htri; linarith
      · have hy₂' : dist y z₂ < ε z₂ / 3 := mem_ball.mp (hU_ball z₂ hy₂)
        linarith [hε_pos z₂]
    · have hgt : ε z₂ < ε z₁ := not_le.mp hle
      refine ⟨z₁, Or.inl rfl, fun y hy => hε_ball z₁ (mem_closedBall.mpr ?_)⟩
      rcases hy with hy₁ | hy₂
      · have hy₁' : dist y z₁ < ε z₁ / 3 := mem_ball.mp (hU_ball z₁ hy₁)
        linarith [hε_pos z₁]
      · have hy₂' : dist y z₂ < ε z₂ / 3 := mem_ball.mp (hU_ball z₂ hy₂)
        have htri : dist y z₁ ≤ dist y z₂ + dist z₂ u + dist u z₁ := dist_triangle4 y z₂ u z₁
        rw [dist_comm z₂ u] at htri; linarith
  have hU_flat_union : ∀ z₁ z₂ : S, IsFlat (U z₁ ∪ U z₂) := by
    intro z₁ z₂ ψ hψ
    by_cases hne : (U z₁ ∩ U z₂).Nonempty
    · obtain ⟨w, _, hsub⟩ := hU_pair z₁ z₂ hne
      exact hW_flat w ψ (hψ.trans hsub)
    · have hdisj : U z₁ ∩ U z₂ = ∅ := not_nonempty_iff_eq_empty.mp hne
      have hconn : IsPreconnected (range ψ) := isPreconnected_range ψ.continuous
      rcases isPreconnected_iff_subset_of_disjoint.mp hconn (U z₁) (U z₂)
        (hU_open z₁) (hU_open z₂) hψ (by rw [hdisj, inter_empty]) with h₁ | h₂
      · exact hW_flat z₁ ψ (h₁.trans (hU_sub_W z₁))
      · exact hW_flat z₂ ψ (h₂.trans (hU_sub_W z₂))
  exact ⟨⟨U, W, pt, hzU, hU_open, hU_sub_W, hU_pair, hU_flat_union,
    hpt0, hpt1, hpt_diag, hpt_cont⟩⟩

private def GoodChain (φ : C(Circle, S)) (U : S → Set S)
    (m : ℕ) (hm : 0 < m) (γ : Fin m → C(unitInterval, S))
    (hmatch : ∀ i, γ i 1 = γ (finNext hm i) 0) (z : Fin m → S) : Prop :=
  (∀ i, range (γ i) ⊆ range φ) ∧ (∀ i, range (γ i) ⊆ U (z i)) ∧
    ¬ ClosedCurveIsNullHomotopicIn univ (concatLoop hm γ hmatch)

private def HasGoodChain (φ : C(Circle, S)) (U : S → Set S) (m : ℕ) : Prop :=
  ∃ (hm : 0 < m) (γ : Fin m → C(unitInterval, S))
    (hmatch : ∀ i, γ i 1 = γ (finNext hm i) 0) (z : Fin m → S),
    GoodChain φ U m hm γ hmatch z

private theorem good_chain_rotate
    {φ : C(Circle, S)} {U : S → Set S} {n : ℕ} (hn : 0 < n) :
    ∀ (k : ℕ) {γ hmatch z}, GoodChain φ U n hn γ hmatch z →
      GoodChain φ U n hn (rotateChain hn k γ) (rotateChain_match hn k γ hmatch)
        (fun i => z ⟨(i.1 + k) % n, Nat.mod_lt _ hn⟩) := by
  intro k γ hmatch z ⟨hφ_sub, hU_sub, hnot_null⟩
  refine ⟨fun i => hφ_sub _, fun i => hU_sub _, fun hnull => hnot_null ?_⟩
  exact closedCurveIsNullHomotopicIn_of_homotopic
    (concatLoop_rotateChain_homotopic hn k γ hmatch) hnull

private theorem minimal_good_chain_not_constant
    {φ : C(Circle, S)} {U : S → Set S} {n : ℕ} (hn : 0 < n)
    (hn3 : 3 ≤ n) (hn_min : ∀ m < n, ¬ HasGoodChain φ U m) :
    ∀ {γ hmatch z}, GoodChain φ U n hn γ hmatch z →
      ∀ i : Fin n, ¬ (∀ t : unitInterval, γ i t = γ i 0) := by
  intro γ hmatch z hgood i hconst
  have hrot := good_chain_rotate hn (i.1 + 1) hgood
  let γ_r := rotateChain hn (i.1 + 1) γ
  let hmatch_r := rotateChain_match hn (i.1 + 1) γ hmatch
  let z_r : Fin n → S := fun j => z ⟨(j.1 + (i.1 + 1)) % n, Nat.mod_lt _ hn⟩
  have hlast_eq : (⟨(n - 1 + (i.1 + 1)) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
    ext
    simp only [show n - 1 + (i.1 + 1) = i.1 + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.2]
  have hconst_r : ∀ t : unitInterval, γ_r ⟨n - 1, by omega⟩ t = γ_r ⟨0, hn⟩ 0 := by
    intro t
    have h1 : γ_r ⟨n - 1, by omega⟩ t = γ i t := by
      dsimp [γ_r, rotateChain]; rw [hlast_eq]
    have h1' : γ_r ⟨n - 1, by omega⟩ 1 = γ i 1 := by
      dsimp [γ_r, rotateChain]; rw [hlast_eq]
    have h3 : γ_r ⟨n - 1, by omega⟩ 1 = γ_r ⟨0, hn⟩ 0 := by
      have hm := hmatch_r ⟨n - 1, by omega⟩
      dsimp [finNext] at hm
      have hmod : (n - 1 + 1) % n = 0 := by rw [show n - 1 + 1 = n by omega, Nat.mod_self]
      simpa [hmod] using hm
    rw [h1, hconst t, ← hconst 1, ← h1', h3]
  have hhom_drop := concatLoop_drop_last_const (by omega : 2 ≤ n) γ_r hmatch_r hconst_r
  have hn' : 0 < n - 1 := by omega
  refine hn_min (n - 1) (by omega) ⟨hn', dropLastChain γ_r,
    dropLastChain_match (by omega) γ_r hmatch_r hconst_r, fun j => z_r ⟨j.1, by omega⟩,
    fun j => hrot.1 ⟨j.1, by omega⟩, fun j => hrot.2.1 ⟨j.1, by omega⟩, fun hnull => hrot.2.2 ?_⟩
  exact closedCurveIsNullHomotopicIn_of_homotopic hhom_drop hnull

private theorem good_chain_endpoints_ne {φ : C(Circle, S)}
    (cover : CurveChartCover S) {n : ℕ} (hn : 0 < n) (hn3 : 3 ≤ n)
    (hGood_nonconst : ∀ {γ hmatch z}, GoodChain φ cover.small n hn γ hmatch z →
      ∀ i : Fin n, ¬ (∀ t : unitInterval, γ i t = γ i 0)) :
    ∀ {γ hmatch z}, GoodChain φ cover.small n hn γ hmatch z →
      ∀ i : Fin n, γ i 0 ≠ γ i 1 := by
  let W := cover.chart
  have hU_sub_W := cover.small_subset_chart
  have hpt0 := cover.interpolate_zero
  have hpt1 := cover.interpolate_one
  have hpt_diag := cover.interpolate_diag
  have hpt_cont := cover.interpolate_continuous
  intro γ hmatch z hgood i heq
  let c_i : C(unitInterval, S) := ContinuousMap.const unitInterval (γ i 0)
  have hc_i_W : range c_i ⊆ W (z i) := by
    rintro _ ⟨_, rfl⟩; exact hU_sub_W (z i) (hgood.2.1 i (mem_range_self 0))
  let γ' : Fin n → C(unitInterval, S) := fun m => if m = i then c_i else γ m
  have hmatch' : ∀ m : Fin n, γ' m 1 = γ' (finNext hn m) 0 := by
    intro m
    dsimp [γ', c_i]
    by_cases hm : m = i
    · subst hm
      by_cases hnext : finNext hn m = m
      · simp only [↓reduceIte, hnext]; rfl
      · simp only [↓reduceIte, hnext, ContinuousMap.const_apply]
        exact heq.trans (hmatch m)
    · by_cases hnext : finNext hn m = i
      · simp only [hm, hnext, ↓reduceIte, ContinuousMap.const_apply]
        rw [← hnext, ← hmatch m]
      · simp only [hm, hnext, ↓reduceIte, hmatch m]
  let H_i : C(unitInterval × unitInterval, S) :=
    ⟨fun p => cover.interpolate (z i) (γ i p.1) (c_i p.1) p.2,
      hpt_cont (z i) (γ i) c_i ((hgood.2.1 i).trans (hU_sub_W (z i))) hc_i_W⟩
  let H : Fin n → C(unitInterval × unitInterval, S) := fun m =>
    if m = i then H_i else ⟨fun p => γ m p.1, (γ m).continuous.comp continuous_fst⟩
  have hhom : ClosedCurvesHomotopicIn univ (concatLoop hn γ hmatch) (concatLoop hn γ' hmatch') := by
    refine concatLoop_homotopic hn γ γ' hmatch hmatch' H (fun _ _ => mem_univ _)
      (fun m t => ?_) (fun m t => ?_) (fun m s => ?_)
    · dsimp [H]
      by_cases hm : m = i
      · subst hm
        simp only [↓reduceIte, H_i]
        exact hpt0 (z m) _ (hU_sub_W (z m) (hgood.2.1 m (mem_range_self t))) _
          (hc_i_W (mem_range_self t))
      · simp only [hm, ↓reduceIte]; rfl
    · dsimp [H, γ']
      by_cases hm : m = i
      · subst hm
        simp only [↓reduceIte, H_i]
        exact hpt1 (z m) _ (hU_sub_W (z m) (hgood.2.1 m (mem_range_self t))) _
          (hc_i_W (mem_range_self t))
      · simp only [hm, ↓reduceIte]; rfl
    · dsimp [H]
      have hne_next : finNext hn i ≠ i := by
        intro hnext
        have := congrArg Fin.val hnext
        dsimp [finNext] at this
        by_cases hlast : i.1 + 1 = n
        · rw [hlast, Nat.mod_self] at this; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at this; omega
      by_cases hm : m = i
      · subst hm
        simp only [↓reduceIte, hne_next, H_i, c_i]
        change cover.interpolate (z m) (γ m 1) (γ m 0) s = γ (finNext hn m) 0
        rw [← heq, hpt_diag (z m) _ (hU_sub_W (z m) (hgood.2.1 m (mem_range_self 0))) s,
          heq, hmatch m]
      · by_cases hnext : finNext hn m = i
        · simp only [hm, hnext, ↓reduceIte, H_i, c_i]
          change γ m 1 = cover.interpolate (z i) (γ i 0) (γ i 0) s
          rw [hpt_diag (z i) _ (hU_sub_W (z i) (hgood.2.1 i (mem_range_self 0))) s,
            ← hnext, hmatch m]
        · simp only [hm, hnext, ↓reduceIte]; exact hmatch m
  have hgood' : GoodChain φ cover.small n hn γ' hmatch' z := by
    refine ⟨fun m => ?_, fun m => ?_, fun hnull => hgood.2.2
      (closedCurveIsNullHomotopicIn_of_homotopic hhom hnull)⟩
    · dsimp [γ']; split_ifs with hm
      · rintro _ ⟨_, rfl⟩; exact hgood.1 i (mem_range_self 0)
      · exact hgood.1 m
    · dsimp [γ']; split_ifs with hm
      · subst hm; rintro _ ⟨_, rfl⟩; exact hgood.2.1 m (mem_range_self 0)
      · exact hgood.2.1 m
  refine hGood_nonconst hgood' i (fun t => ?_)
  dsimp [γ']; simp only [↓reduceIte, c_i, ContinuousMap.const_apply]

private theorem minimal_good_chain_nonadjacent_disjoint
    {φ : C(Circle, S)} {U : S → Set S} {n : ℕ} (hn : 0 < n)
    (hn_min : ∀ m < n, ¬ HasGoodChain φ U m) :
    ∀ {γ hmatch z}, GoodChain φ U n hn γ hmatch z →
      ∀ (i j : Fin n), j ≠ i → j ≠ finNext hn i → i ≠ finNext hn j →
        ∀ s t : unitInterval, γ i s ≠ γ j t := by
  intro γ hmatch z hgood i j hji hj_next hi_next s t heq
  have hrot := good_chain_rotate hn i.1 hgood
  let γ_r := rotateChain hn i.1 γ
  let hmatch_r := rotateChain_match hn i.1 γ hmatch
  let z_r : Fin n → S := fun k => z ⟨(k.1 + i.1) % n, Nat.mod_lt _ hn⟩
  let d : ℕ := (j.1 + n - i.1) % n
  have hd_lt : d < n := Nat.mod_lt _ hn
  let j' : Fin n := ⟨d, hd_lt⟩
  have hj'_val : (d + i.1) % n = j.1 := by
    dsimp [d]
    rw [Nat.mod_add_mod, show j.1 + n - i.1 + i.1 = j.1 + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
  have hd_ge2 : 2 ≤ d := by
    by_contra hlt2
    have h01 : d = 0 ∨ d = 1 := by omega
    rcases h01 with hd0 | hd1
    · rw [hd0, zero_add, Nat.mod_eq_of_lt i.2] at hj'_val
      exact hji (Fin.ext hj'_val.symm)
    · rw [hd1, add_comm 1 i.1] at hj'_val
      exact hj_next (Fin.ext hj'_val.symm)
  have hd_le : d + 2 ≤ n := by
    by_contra hgt
    have hd_n1 : d = n - 1 := by omega
    have h1 : (j.1 + 1) % n = i.1 := by
      have h2 : (d + 1 + i.1) % n = (j.1 + 1) % n := by
        rw [show d + 1 + i.1 = d + i.1 + 1 by omega, ← Nat.mod_add_mod, hj'_val]
      rw [hd_n1, show n - 1 + 1 + i.1 = i.1 + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt i.2] at h2
      exact h2.symm
    exact hi_next (Fin.ext h1.symm)
  have heq_r : γ_r ⟨0, hn⟩ s = γ_r j' t := by
    dsimp [γ_r, rotateChain, j']
    simp only [zero_add, Nat.mod_eq_of_lt i.2, hj'_val]
    exact heq
  -- Both sub-loops have `< n` pieces and satisfy `GoodChain` except for null-homotopy, so by
  -- `hn_min` they are null-homotopic!
  have hnull₁ : ClosedCurveIsNullHomotopicIn univ
      (concatLoop (by omega : 0 < d + 1) (splitChain₁ hn γ_r j' s t)
        (splitChain₁_match hn γ_r hmatch_r j' hd_ge2 s t heq_r)) := by
    by_contra hnot₁
    refine hn_min (d + 1) (by omega) ⟨by omega, splitChain₁ hn γ_r j' s t,
      splitChain₁_match hn γ_r hmatch_r j' hd_ge2 s t heq_r,
      fun k => if k.1 = 0 then z_r ⟨0, hn⟩ else if hkj : k.1 < d then z_r ⟨k.1, by omega⟩ else z_r
        j',
      fun k => ?_, fun k => ?_, hnot₁⟩
    · dsimp [splitChain₁]; split_ifs with hk0 hkj
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.1 ⟨0, hn⟩)
      · exact hrot.1 ⟨k.1, by omega⟩
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.1 j')
    · dsimp [splitChain₁]; split_ifs with hk0 hkj
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.2.1 ⟨0, hn⟩)
      · exact hrot.2.1 ⟨k.1, by omega⟩
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.2.1 j')
  have hnull₂ : ClosedCurveIsNullHomotopicIn univ
      (concatLoop (by omega : 0 < n - d + 1) (splitChain₂ hn γ_r j' s t)
        (splitChain₂_match hn γ_r hmatch_r j' hd_le s t heq_r)) := by
    by_contra hnot₂
    refine hn_min (n - d + 1) (by omega) ⟨by omega, splitChain₂ hn γ_r j' s t,
      splitChain₂_match hn γ_r hmatch_r j' hd_le s t heq_r,
      fun k => if k.1 = 0 then z_r j' else if hkn : k.1 < n - d then z_r ⟨d + k.1, by omega⟩ else
        z_r ⟨0, hn⟩,
      fun k => ?_, fun k => ?_, hnot₂⟩
    · dsimp [splitChain₂, j']; split_ifs with hk0 hkn
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.1 j')
      · exact hrot.1 ⟨d + k.1, by omega⟩
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.1 ⟨0, hn⟩)
    · dsimp [splitChain₂, j']; split_ifs with hk0 hkn
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.2.1 j')
      · exact hrot.2.1 ⟨d + k.1, by omega⟩
      · exact (range_subPathSeg_subset _ _ _).trans (hrot.2.1 ⟨0, hn⟩)
  exact hrot.2.2
    (nullHomotopic_of_split_nonadjacent hn γ_r hmatch_r j' hd_ge2 hd_le s t heq_r hnull₁ hnull₂)

private theorem exists_good_chain_with_injective_pieces [T2Space S]
    {φ : C(Circle, S)} (cover : CurveChartCover S) {n : ℕ} (hn : 0 < n)
    {γ₀ : Fin n → C(unitInterval, S)}
    {hmatch₀ : ∀ i, γ₀ i 1 = γ₀ (finNext hn i) 0} {z₀ : Fin n → S}
    (hγ₀_good : GoodChain φ cover.small n hn γ₀ hmatch₀ z₀)
    (hends : ∀ i, γ₀ i 0 ≠ γ₀ i 1) :
    ∃ (γ : Fin n → C(unitInterval, S)) (hmatch : ∀ i, γ i 1 = γ (finNext hn i) 0),
      GoodChain φ cover.small n hn γ hmatch z₀ ∧ (∀ i, Injective (γ i)) := by
  let W := cover.chart
  have hU_sub_W := cover.small_subset_chart
  have hpt0 := cover.interpolate_zero
  have hpt1 := cover.interpolate_one
  have hpt_diag := cover.interpolate_diag
  have hpt_cont := cover.interpolate_continuous
  -- Step 3: Replace each `γ₀ i` by an injective path `γ₁ i` with the same ends via (11.1)
  -- (`exists_arc_of_path`).
  have hinj_ex : ∀ i : Fin n, ∃ e : C(unitInterval, S),
      Injective e ∧ e 0 = γ₀ i 0 ∧ e 1 = γ₀ i 1 ∧ range e ⊆ range (γ₀ i) := by
    intro i
    obtain ⟨e, he_cont, he_inj, he0, he1, he_sub⟩ :=
      exists_arc_of_path (γ₀ i).continuous (hends i)
    exact ⟨⟨e, he_cont⟩, he_inj, he0, he1, he_sub⟩
  choose γ₁ hγ₁_inj hγ₁_0 hγ₁_1 hγ₁_sub using hinj_ex
  have hmatch₁ : ∀ i : Fin n, γ₁ i 1 = γ₁ (finNext hn i) 0 := by
    intro i; rw [hγ₁_1, hγ₁_0, hmatch₀]
  have hγ₁_good : GoodChain φ cover.small n hn γ₁ hmatch₁ z₀ := by
    refine ⟨fun i => (hγ₁_sub i).trans (hγ₀_good.1 i),
      fun i => (hγ₁_sub i).trans (hγ₀_good.2.1 i), fun hnull => hγ₀_good.2.2 ?_⟩
    let H : Fin n → C(unitInterval × unitInterval, S) := fun i =>
      ⟨fun p => cover.interpolate (z₀ i) (γ₀ i p.1) (γ₁ i p.1) p.2,
        hpt_cont (z₀ i) (γ₀ i) (γ₁ i) ((hγ₀_good.2.1 i).trans (hU_sub_W (z₀ i)))
          ((hγ₁_sub i).trans ((hγ₀_good.2.1 i).trans (hU_sub_W (z₀ i))))⟩
    refine closedCurveIsNullHomotopicIn_of_homotopic
      (concatLoop_homotopic hn γ₀ γ₁ hmatch₀ hmatch₁ H (fun _ _ => mem_univ _)
        (fun i t => hpt0 (z₀ i) _ (hU_sub_W (z₀ i) (hγ₀_good.2.1 i (mem_range_self t))) _
          (hU_sub_W (z₀ i) (hγ₀_good.2.1 i (hγ₁_sub i (mem_range_self t)))))
        (fun i t => hpt1 (z₀ i) _ (hU_sub_W (z₀ i) (hγ₀_good.2.1 i (mem_range_self t))) _
          (hU_sub_W (z₀ i) (hγ₀_good.2.1 i (hγ₁_sub i (mem_range_self t)))))
        (fun i s => ?_)) hnull
    change cover.interpolate (z₀ i) (γ₀ i 1) (γ₁ i 1) s = cover.interpolate (z₀ (finNext hn i)) (γ₀
      (finNext hn i) 0) (γ₁ (finNext hn i) 0) s
    rw [hγ₁_1, hpt_diag (z₀ i) _ (hU_sub_W (z₀ i) (hγ₀_good.2.1 i (mem_range_self 1))) s,
      hγ₁_0, hpt_diag (z₀ (finNext hn i)) _ (hU_sub_W _ (hγ₀_good.2.1 _
        (mem_range_self 0))) s, hmatch₀]
  exact ⟨γ₁, hmatch₁, hγ₁_good, hγ₁_inj⟩

private theorem homotopic_after_trimming_adjacent_pieces
    (cover : CurveChartCover S) {n : ℕ} (hn : 0 < n)
    (γ : Fin n → C(unitInterval, S)) (hmatch : ∀ i, γ i 1 = γ (finNext hn i) 0)
    (i : Fin n) (s₀ t₀ : unitInterval) {w : S} :
    let i' := finNext hn i
    let γ_i := subPathSeg (γ i) 0 s₀
    let γ_i' := subPathSeg (γ i') t₀ 1
    let γ' : Fin n → C(unitInterval, S) := fun k =>
      if k = i then γ_i else if k = i' then γ_i' else γ k
    (hii' : i' ≠ i) → (hi'_next : finNext hn i' ≠ i) →
    (hnext_ne_i' : finNext hn i' ≠ i') → (ht₀ : γ i' t₀ = γ i s₀) →
    (range (γ i) ⊆ cover.chart w) → (range (γ i') ⊆ cover.chart w) →
    (hmatch' : ∀ k, γ' k 1 = γ' (finNext hn k) 0) →
    ClosedCurvesHomotopicIn univ (concatLoop hn γ hmatch) (concatLoop hn γ' hmatch') := by
  intro i' γ_i γ_i' γ' hii' hi'_next hnext_ne_i' ht₀ hγi_W hγi'_W hmatch'
  have hpt0 := cover.interpolate_zero
  have hpt1 := cover.interpolate_one
  have hpt_diag := cover.interpolate_diag
  have hpt_cont := cover.interpolate_continuous
  have hγ_i_W := (range_subPathSeg_subset (γ i) 0 s₀).trans hγi_W
  have hγ_i'_W := (range_subPathSeg_subset (γ i') t₀ 1).trans hγi'_W
  let H_i : C(unitInterval × unitInterval, S) :=
    ⟨fun p => cover.interpolate w (γ i p.1) (γ_i p.1) p.2, hpt_cont w (γ i) γ_i hγi_W hγ_i_W⟩
  let H_i' : C(unitInterval × unitInterval, S) :=
    ⟨fun p => cover.interpolate w (γ i' p.1) (γ_i' p.1) p.2, hpt_cont w (γ i') γ_i' hγi'_W hγ_i'_W⟩
  let H : Fin n → C(unitInterval × unitInterval, S) := fun k =>
    if k = i then H_i
    else if k = i' then H_i'
    else ⟨fun p => γ k p.1, (γ k).continuous.comp continuous_fst⟩
  refine concatLoop_homotopic hn γ γ' hmatch hmatch' H (fun _ _ => mem_univ _)
    (fun k t => ?_) (fun k t => ?_) (fun k s => ?_)
  · dsimp [H]
    by_cases hk_i : k = i
    · subst k; simp only [↓reduceIte, H_i]
      exact hpt0 w _ (hγi_W (mem_range_self t)) _ (hγ_i_W (mem_range_self t))
    · by_cases hk_i' : k = i'
      · subst k; simp only [hk_i, ↓reduceIte, H_i']
        exact hpt0 w _ (hγi'_W (mem_range_self t)) _ (hγ_i'_W (mem_range_self t))
      · simp only [hk_i, hk_i', ↓reduceIte]; rfl
  · dsimp [H, γ']
    by_cases hk_i : k = i
    · subst k; simp only [↓reduceIte, H_i]
      exact hpt1 w _ (hγi_W (mem_range_self t)) _ (hγ_i_W (mem_range_self t))
    · by_cases hk_i' : k = i'
      · subst k; simp only [hk_i, ↓reduceIte, H_i']
        exact hpt1 w _ (hγi'_W (mem_range_self t)) _ (hγ_i'_W (mem_range_self t))
      · simp only [hk_i, hk_i', ↓reduceIte]; rfl
  · dsimp [H]
    by_cases hk_i : k = i
    · subst k
      change (if i = i then H_i else if i = i' then H_i' else _) (1, s) =
        (if i' = i then H_i else if i' = i' then H_i' else _) (0, s)
      simp only [↓reduceIte, hii', H_i, H_i']
      change cover.interpolate w (γ i 1) (γ_i 1) s = cover.interpolate w (γ i' 0) (γ_i' 0) s
      rw [hmatch i]
      dsimp [γ_i, γ_i']
      rw [subPathSeg_one, subPathSeg_zero, ht₀]
    · by_cases hk_i' : k = i'
      · subst k
        simp only [hk_i, ↓reduceIte, hi'_next, hnext_ne_i', H_i', γ_i']
        change cover.interpolate w (γ i' 1) (subPathSeg (γ i') t₀ 1 1) s = γ (finNext hn i') 0
        rw [subPathSeg_one, hpt_diag w _ (hγi'_W (mem_range_self 1)) s, hmatch i']
      · simp only [hk_i, hk_i', ↓reduceIte]
        by_cases hnext_i : finNext hn k = i
        · simp only [hnext_i, ↓reduceIte, H_i, γ_i]
          change γ k 1 = cover.interpolate w (γ i 0) (subPathSeg (γ i) 0 s₀ 0) s
          rw [subPathSeg_zero, hpt_diag w _ (hγi_W (mem_range_self 0)) s, ← hnext_i, hmatch k]
        · have hnext_k_ne_i' : finNext hn k ≠ i' := fun h =>
            hk_i ((finPrev_finNext hn k).symm.trans (by rw [h]; exact finPrev_finNext hn i))
          simp only [hnext_i, hnext_k_ne_i', ↓reduceIte]
          exact hmatch k

private theorem exists_good_chain_with_disjoint_adjacent_pieces [T2Space S]
    {φ : C(Circle, S)} (cover : CurveChartCover S)
    {n : ℕ} (hn : 0 < n) (hn3 : 3 ≤ n)
    {z₀ : Fin n → S} {γ₁ : Fin n → C(unitInterval, S)}
    {hmatch₁ : ∀ i, γ₁ i 1 = γ₁ (finNext hn i) 0}
    (hγ₁_good : GoodChain φ cover.small n hn γ₁ hmatch₁ z₀)
    (hγ₁_inj : ∀ i, Injective (γ₁ i))
    (hGood_nonconst : ∀ {γ hmatch z}, GoodChain φ cover.small n hn γ hmatch z →
      ∀ i : Fin n, ¬ (∀ t : unitInterval, γ i t = γ i 0)) :
    ∀ m : ℕ, m ≤ n →
      ∃ (γ : Fin n → C(unitInterval, S)) (hmatch : ∀ i, γ i 1 = γ (finNext hn i) 0),
        GoodChain φ cover.small n hn γ hmatch z₀ ∧
        (∀ i : Fin n, Injective (γ i)) ∧
        (∀ k : Fin n, k.1 < m → ∀ s t : unitInterval, γ k s = γ (finNext hn k) t → s = 1 ∧ t = 0)
          := by
  let W := cover.chart
  have hU_pair := cover.pair_subset_chart
  let U := cover.small
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨γ₁, hmatch₁, hγ₁_good, hγ₁_inj, fun k hk => absurd hk (Nat.not_lt_zero k.1)⟩
  | succ m ih =>
    intro hm_le
    obtain ⟨γ, hmatch, hgood, hinj, hadj⟩ := ih (by omega)
    let i : Fin n := ⟨m, hm_le⟩
    let i' : Fin n := finNext hn i
    have hii' : i' ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [i, i', finNext] at this
      by_cases hlast : m + 1 = n
      · rw [hlast, Nat.mod_self] at this; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at this; omega
    let Pre : Set unitInterval := (γ i) ⁻¹' range (γ i')
    have hPre_closed : IsClosed Pre :=
      (isCompact_range (γ i').continuous).isClosed.preimage (γ i).continuous
    have h1_mem : (1 : unitInterval) ∈ Pre := ⟨0, (hmatch i).symm⟩
    let s₀ : unitInterval := sInf Pre
    have hs₀_mem : s₀ ∈ Pre := hPre_closed.csInf_mem ⟨1, h1_mem⟩ (OrderBot.bddBelow Pre)
    have hs₀_le : ∀ s ∈ Pre, s₀ ≤ s := fun s hs => csInf_le (OrderBot.bddBelow Pre) hs
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : unitInterval, γ i' t₀ = γ i s₀ := hs₀_mem
    let γ_i : C(unitInterval, S) := subPathSeg (γ i) 0 s₀
    let γ_i' : C(unitInterval, S) := subPathSeg (γ i') t₀ 1
    let γ' : Fin n → C(unitInterval, S) := fun k =>
      if k = i then γ_i
      else if k = i' then γ_i'
      else γ k
    have hi'_next : finNext hn i' ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [i, i', finNext] at this
      rw [Nat.mod_add_mod] at this
      by_cases h1 : m + 1 + 1 < n
      · rw [Nat.mod_eq_of_lt h1] at this; omega
      · have hsub : m + 1 + 1 = m + 2 - n + n := by omega
        have h2 : (m + 1 + 1) % n = m + 2 - n := by
          conv_lhs => rw [hsub, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega : m + 2 - n < n)
        rw [h2] at this; omega
    have hnext_ne_i' : finNext hn i' ≠ i' := by
      intro heq
      have := congrArg Fin.val heq
      dsimp [finNext] at this
      by_cases hlast : i'.1 + 1 = n
      · rw [hlast, Nat.mod_self] at this; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at this; omega
    have hmatch' : ∀ k : Fin n, γ' k 1 = γ' (finNext hn k) 0 := by
      intro k
      dsimp [γ', γ_i, γ_i']
      by_cases hk_i : k = i
      · subst hk_i
        change (if i = i then subPathSeg (γ i) 0 s₀ else if i = i' then subPathSeg
          (γ i') t₀ 1 else γ i) 1 =
          (if i' = i then subPathSeg (γ i) 0 s₀ else if i' = i' then subPathSeg
            (γ i') t₀ 1 else γ i') 0
        simp only [↓reduceIte, hii', subPathSeg_one, subPathSeg_zero, ht₀]
      · by_cases hk_i' : k = i'
        · subst hk_i'
          simp only [hk_i, ↓reduceIte, hi'_next, hnext_ne_i', subPathSeg_one, hmatch i']
        · simp only [hk_i, hk_i', ↓reduceIte]
          by_cases hnext_i : finNext hn k = i
          · rw [hnext_i]
            simp only [↓reduceIte, subPathSeg_zero, ← hnext_i, hmatch k]
          · have hnext_k_ne_i' : finNext hn k ≠ i' := fun h =>
              hk_i ((finPrev_finNext hn k).symm.trans (by rw [h]; exact finPrev_finNext hn i))
            simp only [hnext_i, hnext_k_ne_i', ↓reduceIte, hmatch k]
    -- Homotopy from `γ` to `γ'` inside `W w` where `U (z₀ i) ∪ U (z₀ i') ⊆ W w`.
    have hU_nonempty : (U (z₀ i) ∩ U (z₀ i')).Nonempty :=
      ⟨γ i 1, hgood.2.1 i (mem_range_self 1), by
        rw [hmatch i]
        exact hgood.2.1 i' (mem_range_self 0)⟩
    obtain ⟨w, _, hUU_W⟩ := hU_pair (z₀ i) (z₀ i') hU_nonempty
    have hγi_W : range (γ i) ⊆ W w := (hgood.2.1 i).trans (subset_union_left.trans hUU_W)
    have hγi'_W : range (γ i') ⊆ W w := (hgood.2.1 i').trans (subset_union_right.trans hUU_W)
    have hγ'_sub : ∀ k : Fin n, range (γ' k) ⊆ range (γ k) := by
      intro k; dsimp [γ', γ_i, γ_i']; split_ifs with h1 h2
      · subst h1; exact range_subPathSeg_subset _ _ _
      · subst h2; exact range_subPathSeg_subset _ _ _
      · exact Subset.rfl
    have hhom :=
      homotopic_after_trimming_adjacent_pieces cover hn γ hmatch i s₀ t₀
        hii' hi'_next hnext_ne_i' ht₀ hγi_W hγi'_W hmatch'
    have hgood' : GoodChain φ cover.small n hn γ' hmatch' z₀ :=
      ⟨fun k => (hγ'_sub k).trans (hgood.1 k),
       fun k => (hγ'_sub k).trans (hgood.2.1 k),
       fun hnull => hgood.2.2 (closedCurveIsNullHomotopicIn_of_homotopic hhom hnull)⟩
    have hs₀_pos : (0 : ℝ) < (s₀ : ℝ) := by
      refine lt_of_le_of_ne s₀.2.1 fun h0 => ?_
      have hs₀_eq : s₀ = 0 := Subtype.ext h0.symm
      refine hGood_nonconst hgood' i (fun u => ?_)
      dsimp [γ', γ_i]; simp only [↓reduceIte, hs₀_eq, subPathSeg_self]
    have ht₀_lt1 : (t₀ : ℝ) < 1 := by
      refine lt_of_le_of_ne t₀.2.2 fun h1 => ?_
      have ht₀_eq : t₀ = 1 := Subtype.ext h1
      refine hGood_nonconst hgood' i' (fun u => ?_)
      dsimp [γ', γ_i']; simp only [hii', ↓reduceIte, ht₀_eq, subPathSeg_self]
    have hinj' : ∀ k : Fin n, Injective (γ' k) := by
      intro k; dsimp [γ', γ_i, γ_i']; split_ifs with h1 h2
      · subst h1; exact injective_subPathSeg (hinj i) hs₀_pos
      · subst h2; exact injective_subPathSeg (hinj i') ht₀_lt1
      · exact hinj k
    refine ⟨γ', hmatch', hgood', hinj', fun k hk u v huv => ?_⟩
    by_cases hk_eq_m : k.1 = m
    · have hki : k = i := Fin.ext hk_eq_m
      subst hki
      have huv_orig : γ' i u = γ' i' v := huv
      have hγ'i_u : γ' i u = γ i ⟨(1 - (u : ℝ)) * 0 + (u : ℝ) * (s₀ : ℝ),
          by nlinarith [u.2.1, u.2.2, s₀.2.1], by nlinarith [u.2.1, u.2.2, s₀.2.2]⟩ := by
        dsimp [γ', γ_i]; simp only [↓reduceIte]; rfl
      have hγ'i'_v : γ' i' v = γ i' ⟨(1 - (v : ℝ)) * (t₀ : ℝ) + (v : ℝ) * 1,
          by nlinarith [v.2.1, v.2.2, t₀.2.1], by nlinarith [v.2.1, v.2.2, t₀.2.2]⟩ := by
        dsimp [γ', γ_i']; simp only [hii', ↓reduceIte]; rfl
      rw [hγ'i_u, hγ'i'_v] at huv
      have hmem_Pre : (⟨(1 - (u : ℝ)) * 0 + (u : ℝ) * (s₀ : ℝ),
          by nlinarith [u.2.1, u.2.2, s₀.2.1], by nlinarith [u.2.1, u.2.2, s₀.2.2]⟩ : unitInterval)
            ∈ Pre :=
        ⟨_, huv.symm⟩
      have hle_s₀ : (s₀ : ℝ) ≤ (1 - (u : ℝ)) * 0 + (u : ℝ) * (s₀ : ℝ) := hs₀_le _ hmem_Pre
      have hu1 : u = 1 := by
        ext; change (u : ℝ) = 1
        nlinarith [u.2.2]
      rw [hu1, hmatch' i] at huv_orig
      exact ⟨hu1, hinj' i' huv_orig.symm⟩
    · have hk_lt_m : k.1 < m := by omega
      have hki : k ≠ i := fun h => hk_eq_m (congrArg Fin.val h)
      have hnext_ne_i' : finNext hn k ≠ i' := fun h =>
        hki ((finPrev_finNext hn k).symm.trans (by rw [h]; exact finPrev_finNext hn i))
      let paramMap : Fin n → unitInterval → unitInterval := fun q u =>
        if q = i then
          ⟨(1 - (u : ℝ)) * 0 + (u : ℝ) * (s₀ : ℝ),
            by nlinarith [u.2.1, u.2.2, s₀.2.1], by nlinarith [u.2.1, u.2.2, s₀.2.2]⟩
        else if q = i' then
          ⟨(1 - (u : ℝ)) * (t₀ : ℝ) + (u : ℝ) * 1,
            by nlinarith [u.2.1, u.2.2, t₀.2.1], by nlinarith [u.2.1, u.2.2, t₀.2.2]⟩
        else u
      have hγ'_param : ∀ (q : Fin n) (u : unitInterval), γ' q u = γ q (paramMap q u) := by
        intro q u; dsimp [γ', γ_i, γ_i', paramMap]; split_ifs with h1 h2
        · subst h1; rfl
        · subst h2; rfl
        · rfl
      rw [hγ'_param k u, hγ'_param (finNext hn k) v] at huv
      obtain ⟨hu_p, hv_p⟩ := hadj k hk_lt_m (paramMap k u) (paramMap (finNext hn k) v) huv
      refine ⟨?_, ?_⟩
      · dsimp [paramMap] at hu_p
        by_cases hki' : k = i'
        · simp only [hki', hii', ↓reduceIte] at hu_p
          have hval := congrArg Subtype.val hu_p
          dsimp at hval
          ext; change (u : ℝ) = 1
          nlinarith [ht₀_lt1]
        · simp only [hki, hki', ↓reduceIte] at hu_p
          exact hu_p
      · dsimp [paramMap] at hv_p
        by_cases hni : finNext hn k = i
        · simp only [hni, ↓reduceIte] at hv_p
          have hval := congrArg Subtype.val hv_p
          dsimp at hval
          ext; change (v : ℝ) = 0
          nlinarith [hs₀_pos]
        · simp only [hni, hnext_ne_i', ↓reduceIte] at hv_p
          exact hv_p

private theorem oArc_of_good_chain [T2Space S]
    {φ : C(Circle, S)} {U : S → Set S} {n : ℕ} (hn : 0 < n)
    {γ : Fin n → C(unitInterval, S)} {z₀ : Fin n → S}
    {hmatch : ∀ i, γ i 1 = γ (finNext hn i) 0}
    (hgood : GoodChain φ U n hn γ hmatch z₀)
    (hinj : ∀ i, Injective (γ i))
    (hadj : ∀ k : Fin n, k.1 < n → ∀ s t : unitInterval,
      γ k s = γ (finNext hn k) t → s = 1 ∧ t = 0)
    (hnonadj : ∀ (i j : Fin n), j ≠ i → j ≠ finNext hn i → i ≠ finNext hn j →
      ∀ s t : unitInterval, γ i s ≠ γ j t) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArc F := by
  let ψ : C(Circle, S) := concatLoop hn γ hmatch
  have hψ_rep : ∀ z : Circle, ∃ (i : Fin n) (t : unitInterval),
      (t : ℝ) < 1 ∧ z = Circle.exp (2 * Real.pi * ((i.1 : ℝ) + (t : ℝ)) / (n : ℝ)) ∧
      ψ z = γ i t := by
    intro z
    obtain ⟨u₀, rfl⟩ := exists_unitInterval_exp z
    let u : unitInterval := if (u₀ : ℝ) = 1 then 0 else u₀
    have hu_lt1 : (u : ℝ) < 1 := by
      dsimp [u]; split_ifs with h1
      · exact zero_lt_one
      · exact lt_of_le_of_ne u₀.2.2 h1
    have hu_exp : Circle.exp (2 * Real.pi * (u₀ : ℝ)) = Circle.exp (2 * Real.pi * (u : ℝ)) := by
      dsimp [u]; split_ifs with h1
      · rw [h1, mul_one, Set.Icc.coe_zero, mul_zero, Circle.exp_two_pi, Circle.exp_zero]
      · rfl
    let y : ℝ := (u : ℝ) * (n : ℝ)
    have hy0 : 0 ≤ y := mul_nonneg u.2.1 (by positivity)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hy_lt : y < (n : ℝ) := by simpa [y] using mul_lt_of_lt_one_left hn_pos hu_lt1
    have hfl_nn : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr hy0
    have hfl_lt : ⌊y⌋ < (n : ℤ) := by rw [Int.floor_lt]; exact_mod_cast hy_lt
    let i : Fin n := ⟨⌊y⌋.toNat, by omega⟩
    let t : unitInterval := unitFract y
    have ht_lt1 : (t : ℝ) < 1 := Int.fract_lt_one y
    have hi_eq : (i.1 : ℝ) + (t : ℝ) = y := by
      have hfl_eq : (i.1 : ℤ) = ⌊y⌋ := Int.toNat_of_nonneg hfl_nn
      change ((i.1 : ℤ) : ℝ) + Int.fract y = y
      rw [hfl_eq, Int.floor_add_fract]
    have hz_eq : Circle.exp (2 * Real.pi * (u₀ : ℝ)) =
        Circle.exp (2 * Real.pi * ((i.1 : ℝ) + (t : ℝ)) / (n : ℝ)) := by
      have hdiv : 2 * Real.pi * y / (n : ℝ) = 2 * Real.pi * (u : ℝ) := by
        dsimp [y]
        rw [← mul_assoc, mul_div_cancel_right₀ _ (ne_of_gt hn_pos)]
      rw [hu_exp, hi_eq, hdiv]
    refine ⟨i, t, ht_lt1, hz_eq, ?_⟩
    rw [hz_eq]
    exact concatLoop_exp_piece hn γ hmatch i t
  have hψ_inj : Injective ψ := by
    intro z₁ z₂ heq
    obtain ⟨i₁, t₁, ht₁_lt, rfl, hψ₁⟩ := hψ_rep z₁
    obtain ⟨i₂, t₂, ht₂_lt, rfl, hψ₂⟩ := hψ_rep z₂
    rw [hψ₁, hψ₂] at heq
    by_cases hi12 : i₂ = i₁
    · subst hi12
      rw [hinj _ heq]
    · by_cases hnext1 : i₂ = finNext hn i₁
      · subst hnext1
        obtain ⟨ht₁_1, _⟩ := hadj i₁ i₁.2 t₁ t₂ heq
        exact absurd (congrArg Subtype.val ht₁_1) (ne_of_lt ht₁_lt)
      · by_cases hnext2 : i₁ = finNext hn i₂
        · subst hnext2
          obtain ⟨ht₂_1, _⟩ := hadj i₂ i₂.2 t₂ t₁ heq.symm
          exact absurd (congrArg Subtype.val ht₂_1) (ne_of_lt ht₂_lt)
        · exact absurd heq (hnonadj i₁ i₂ hi12 hnext1 hnext2 t₁ t₂)
  have hψ_emb : IsEmbedding ψ := (ψ.continuous.isClosedEmbedding hψ_inj).isEmbedding
  let e_ψ : Circle ≃ₜ range ψ := hψ_emb.toHomeomorph
  refine ⟨range ψ, ⟨e_ψ⟩, ?_, ?_⟩
  · rw [range_concatLoop]
    exact iUnion_subset fun i => hgood.1 i
  · rintro ⟨φ_F, c, hc, H, hH_mem, hH0, hH1⟩
    let α : Circle ≃ₜ Circle := e_ψ.trans φ_F.symm
    let H' : C(Circle × unitInterval, S) :=
      H.comp ⟨fun p => (α p.1, p.2), (α.continuous.comp continuous_fst).prodMk continuous_snd⟩
    refine hgood.2.2 ⟨c, hc, H', fun p => hH_mem _, fun z => ?_, fun z => hH1 (α z)⟩
    change H (α z, 0) = ψ z
    rw [hH0 (α z)]
    have hα : φ_F (α z) = e_ψ z := φ_F.apply_symm_apply (e_ψ z)
    exact congrArg Subtype.val hα

/-- Graph Minors VII, (11.2) (pages 249–250):
"If $\Sigma$ is a surface, and $\phi \colon S^1 \to \Sigma$ is continuous and non-null-homotopic,
there is a non-null-homotopic $O$-arc included in $|\phi|$." -/
theorem nonNullHomotopicOArc_in_curve (hS : IsSurface S) (φ : C(Circle, S))
    (hφ : ¬ ClosedCurveIsNullHomotopicIn univ φ) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArc F := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨cover⟩ := exists_curve_chart_cover hS
  let U := cover.small
  have hzU := cover.mem_small
  have hU_open := cover.isOpen_small
  have hex_good : ∃ m : ℕ, HasGoodChain φ U m := by
    have hcov : range φ ⊆ ⋃ z ∈ (univ : Set S), U z :=
      fun y _ => mem_iUnion₂.mpr ⟨y, mem_univ y, hzU y⟩
    obtain ⟨m, hm, z, _, hpiece⟩ :=
      exists_subdivision_in_open_cover (fun z _ => hU_open z) φ hcov
    refine ⟨m, hm, curvePiece hm φ, curvePiece_match hm φ, z, ?_, hpiece, ?_⟩
    · intro i
      rintro _ ⟨t, rfl⟩
      exact mem_range_self _
    · rw [concatLoop_curvePiece hm φ]
      exact hφ
  let decidableGoodChain : DecidablePred (HasGoodChain φ U) := Classical.decPred _
  let n : ℕ := Nat.find hex_good
  have hn_good : HasGoodChain φ U n := Nat.find_spec hex_good
  have hn_min : ∀ m < n, ¬ HasGoodChain φ U m := fun m hm => Nat.find_min hex_good hm
  obtain ⟨hn, γ₀, hmatch₀, z₀, hγ₀_good⟩ := hn_good
  -- Claim (1): `3 ≤ n`.
  have hn3 : 3 ≤ n := by
    by_contra hlt3
    have hle2 : n ≤ 2 := by omega
    have hsub : range (concatLoop hn γ₀ hmatch₀) ⊆
        U (z₀ ⟨0, hn⟩) ∪ U (z₀ ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩) := by
      rw [range_concatLoop]
      refine iUnion_subset fun i y hy => ?_
      have hi : i.1 = 0 ∨ i.1 = n - 1 := by omega
      rcases hi with h0 | hn1
      · left
        have heq : i = ⟨0, hn⟩ := Fin.ext h0
        exact heq ▸ hγ₀_good.2.1 i hy
      · right
        have heq : i = ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := Fin.ext hn1
        exact heq ▸ hγ₀_good.2.1 i hy
    exact hγ₀_good.2.2 (cover.flat_pair _ _ (concatLoop hn γ₀ hmatch₀) hsub)
  have hnonconst : ∀ {γ hmatch z}, GoodChain φ U n hn γ hmatch z →
      ∀ i : Fin n, ¬ (∀ t : unitInterval, γ i t = γ i 0) :=
    fun hgood => minimal_good_chain_not_constant hn hn3 hn_min hgood
  obtain ⟨γ₁, hmatch₁, hγ₁_good, hγ₁_inj⟩ :=
    exists_good_chain_with_injective_pieces cover hn hγ₀_good
      (good_chain_endpoints_ne cover hn hn3 hnonconst hγ₀_good)
  obtain ⟨γ, hmatch, hgood, hinj, hadj⟩ :=
    exists_good_chain_with_disjoint_adjacent_pieces cover hn hn3 hγ₁_good hγ₁_inj hnonconst n le_rfl
  exact oArc_of_good_chain hn hgood hinj hadj
    (minimal_good_chain_nonadjacent_disjoint hn hn_min hgood)

end GraphMinor.GM07
