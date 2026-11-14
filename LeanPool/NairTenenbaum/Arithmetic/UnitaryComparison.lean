/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.PrimeSplitting

/-! # Finite comparison by whole prime-power splitting

Expanding a product over prime divisors gives coprime complementary factors,
so that the growth hypothesis is only used on coprime inputs. This is the
finite combinatorial step of the corrected comparison argument.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

/-- Product of a prime weight over the distinct prime divisors. -/
noncomputable def radicalProduct (l : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors, l p

theorem radicalProduct_nonneg {l : ℕ → ℝ} (hl : ∀ p, 0 ≤ l p) (n : ℕ) :
    0 ≤ radicalProduct l n := Finset.prod_nonneg (fun p _ => hl p)

@[simp] theorem radicalProduct_one (l : ℕ → ℝ) : radicalProduct l 1 = 1 := by
  simp [radicalProduct]

theorem radicalProduct_mul (l : ℕ → ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) : radicalProduct l (m * n) = radicalProduct l m * radicalProduct l n := by
  rw [radicalProduct, Nat.primeFactors_mul hm hn, Finset.prod_union]
  · rfl
  · exact hmn.disjoint_primeFactors

/-- Scalar versions of the existing tuple prime-support splitting. -/
def unitaryPart (n : ℕ+) (s : Finset ℕ) : ℕ+ := primeSelect (fun _ : Fin 1 => n) s 0

/-- The complementary whole-prime-power factor after a unitary selection. -/
def unitaryRest (n : ℕ+) (s : Finset ℕ) : ℕ+ := primeReject (fun _ : Fin 1 => n) s 0

theorem unitaryPart_mul_rest (n : ℕ+) (s : Finset ℕ) :
    unitaryPart n s * unitaryRest n s = n :=
  congrFun (primeSelect_mul_primeReject (fun _ : Fin 1 => n) s) 0

theorem unitaryPart_coprime_rest (n : ℕ+) (s : Finset ℕ) :
    Nat.Coprime (unitaryPart n s) (unitaryRest n s) :=
  primeSelect_primeReject_coprime (fun _ : Fin 1 => n) s 0 0

theorem unitaryPart_le (n : ℕ+) (s : Finset ℕ) : unitaryPart n s ≤ n := by
  have h := Nat.le_mul_of_pos_right (unitaryPart n s : ℕ) (unitaryRest n s).pos
  exact_mod_cast (show unitaryPart n s ≤ unitaryPart n s * unitaryRest n s from h).trans_eq
    (unitaryPart_mul_rest n s)

theorem unitaryRest_le (n : ℕ+) (s : Finset ℕ) : unitaryRest n s ≤ n := by
  have h := Nat.le_mul_of_pos_left (unitaryRest n s : ℕ) (unitaryPart n s).pos
  exact_mod_cast (show unitaryRest n s ≤ unitaryPart n s * unitaryRest n s from h).trans_eq
    (unitaryPart_mul_rest n s)

theorem unitaryPart_primeFactors (n : ℕ+) (s : Finset ℕ) :
    (unitaryPart n s : ℕ).primeFactors = (n : ℕ).primeFactors ∩ s :=
  primeFactors_primeSelect (fun _ : Fin 1 => n) s 0

theorem unitaryPart_support {n : ℕ+} {s : Finset ℕ} (hs : s ⊆ (n : ℕ).primeFactors) :
    (unitaryPart n s : ℕ).primeFactors = s := by
  rw [unitaryPart_primeFactors, Finset.inter_eq_right.mpr hs]

/-- Both the original integer and its selected prime set are recovered from
the resulting pair of factors. -/
theorem unitarySplit_injective {n m : ℕ+} {s t : Finset ℕ}
    (hs : s ⊆ (n : ℕ).primeFactors) (ht : t ⊆ (m : ℕ).primeFactors)
    (h : (unitaryPart n s, unitaryRest n s) = (unitaryPart m t, unitaryRest m t)) :
    n = m ∧ s = t := by
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  dsimp only at ha hb
  constructor
  · rw [← unitaryPart_mul_rest n s, ← unitaryPart_mul_rest m t, ha, hb]
  · rw [← unitaryPart_support hs, ← unitaryPart_support ht, ha]

/-- The prime-product expansion, with the coprime growth inequality applied
to every pair of complementary whole prime-power parts. -/
theorem unitary_comparison_pointwise {w U : ℕ+ → ℝ} {l : ℕ → ℝ}
    (hl : ∀ p, 0 ≤ l p)
    (hw : ∀ a b : ℕ+, Nat.Coprime a b → w (a * b) ≤ U a * w b) (n : ℕ+) :
    w n * radicalProduct (fun p => 1 + l p) n ≤
      ∑ s ∈ (n : ℕ).primeFactors.powerset,
        (U (unitaryPart n s) * radicalProduct l (unitaryPart n s)) * w (unitaryRest n s) := by
  classical
  rw [radicalProduct, Finset.prod_one_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have heq : radicalProduct l (unitaryPart n s) = ∏ p ∈ s, l p := by
    rw [radicalProduct, unitaryPart_support (Finset.mem_powerset.mp hs)]
  rw [heq]
  calc
    _ ≤ (U (unitaryPart n s) * w (unitaryRest n s)) * (∏ p ∈ s, l p) := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun p _ => hl p))
      simpa only [unitaryPart_mul_rest] using hw _ _ (unitaryPart_coprime_rest n s)
    _ = _ := by ring

/-- Uniform finite-sum comparison: a summable auxiliary convolution kernel
can be supplied afterward without changing this combinatorial statement. -/
theorem unitary_comparison_sum {w U : ℕ+ → ℝ} {l : ℕ → ℝ}
    (hw₀ : ∀ n, 0 ≤ w n) (hU : ∀ n, 0 ≤ U n) (hl : ∀ p, 0 ≤ l p)
    (hw : ∀ a b : ℕ+, Nat.Coprime a b → w (a * b) ≤ U a * w b) (N : ℕ+) :
    (∑ n ∈ Finset.Icc 1 N, w n * radicalProduct (fun p => 1 + l p) n) ≤
      (∑ a ∈ Finset.Icc 1 N, U a * radicalProduct l a) * (∑ b ∈ Finset.Icc 1 N, w b) := by
  classical
  let S := (Finset.Icc 1 N).sigma (fun n => (n : ℕ).primeFactors.powerset)
  let T := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let f : (Σ _n : ℕ+, Finset ℕ) → ℕ+ × ℕ+ :=
    fun x => (unitaryPart x.1 x.2, unitaryRest x.1 x.2)
  have hfmem : ∀ x ∈ S, f x ∈ T := by
    intro x hx
    obtain ⟨hn, _⟩ := Finset.mem_sigma.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨one_le, (unitaryPart_le _ _).trans
      (Finset.mem_Icc.mp hn).2⟩, Finset.mem_Icc.mpr ⟨one_le, (unitaryRest_le _ _).trans
      (Finset.mem_Icc.mp hn).2⟩⟩
  have hfinj : Set.InjOn f S := by
    intro x hx y hy hxy
    have h := unitarySplit_injective (Finset.mem_powerset.mp (Finset.mem_sigma.mp hx).2)
      (Finset.mem_powerset.mp (Finset.mem_sigma.mp hy).2) hxy
    obtain ⟨n, s⟩ := x
    obtain ⟨m, t⟩ := y
    obtain ⟨rfl, rfl⟩ := h
    rfl
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ s ∈ (n : ℕ).primeFactors.powerset,
        (U (unitaryPart n s) * radicalProduct l (unitaryPart n s)) * w (unitaryRest n s) :=
      Finset.sum_le_sum (fun n _ => unitary_comparison_pointwise hl hw n)
    _ = ∑ x ∈ S, (U (f x).1 * radicalProduct l (f x).1) * w (f x).2 := by
      rw [Finset.sum_sigma]
    _ ≤ ∑ x ∈ T, (U x.1 * radicalProduct l x.1) * w x.2 := by
      exact Finset.sum_le_sum_of_injOn f hfinj (Finset.image_subset_iff.mpr hfmem)
        (fun _ _ => le_rfl)
        (fun x _ _ => mul_nonneg (mul_nonneg (hU _) (radicalProduct_nonneg hl _)) (hw₀ _))
    _ = _ := by rw [Finset.sum_product, Finset.sum_mul_sum]

end NairTenenbaum
