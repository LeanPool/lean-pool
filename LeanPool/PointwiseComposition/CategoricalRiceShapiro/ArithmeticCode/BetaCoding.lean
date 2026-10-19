/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.NumeralEvaluation
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Induction

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Extending a Gödel beta code inside a model of Peano arithmetic

`eval_codeBeta_of_values` computes `codeBeta` at arbitrary elements of a model of
`𝐈𝐎𝐩𝐞𝐧`, but it says nothing about which value assignments are realized by some
code.  This file proves the one existence statement the recursion development
needs: in a model of `𝐏𝐀`, every beta code `n` and every index `l` admit a code
`n'` that agrees with `n` at every index below `l` and takes a prescribed value
at `l`.

The statement is given as a graph evaluation of
`codeBeta (Code.proj 0) (Code.proj 1)` rather than as an equation between
remainders.  A value-level statement would mention `%`, `π₁` and `π₂`, whose
elaboration demands an `𝐈𝐎𝐩𝐞𝐧` instance that `𝐏𝐀` does not supply while the
statement is being elaborated.

Pinned Foundation supplies internal finite sequences of nonstandard length, but
no arbitrary-model Chinese remainder theorem and no beta encoder, so the
supporting development is built here and kept private:

* a Bézout inverse, `exists_mul_mod_eq_one`, obtained from the least positive
  residue of a multiple of the argument;
* the internal factorial and the internal product of beta moduli, each defined
  by Foundation's `𝐈Σ₁` primitive recursion;
* coprimality of two beta moduli whose index difference divides the multiplier;
* simultaneous solution of the beta congruences prescribed by an internal
  sequence.

Nothing here uses `Nat.beta`, `Computes` or evaluation over standard `ℕ`.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁
open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace CategoricalRiceShapiro
namespace ArithmeticCode

section Internal

variable {V : Type*} [ORingStructure V]

section IOpen

variable [V↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

private lemma dvd_sub_of {d x y : V} (hx : d ∣ x) (hy : d ∣ y) : d ∣ x - y :=
  by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [zero_dvd_iff] at hx hy
    simp [hx, hy]
  · rcases lt_or_ge x y with h | h
    · simp [FFL.FirstOrder.Arithmetic.sub_spec_of_lt h]
    · obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      have hdp : 0 < d := pos_iff_ne_zero.mpr hd
      have hqp : q ≤ p := le_of_mul_le_mul_left h hdp
      exact ⟨p - q, (FFL.FirstOrder.Arithmetic.mul_sub hqp).symm⟩

private lemma mod_add_congr {m x₁ x₂ y₁ y₂ : V} (hm : 0 < m) (h₁ : x₁ % m = y₁ % m)
    (h₂ : x₂ % m = y₂ % m) : (x₁ + x₂) % m = (y₁ + y₂) % m := by
  rw [mod_add hm, h₁, h₂, ← mod_add hm]

private lemma mod_mul_congr {m x₁ x₂ y₁ y₂ : V} (hm : 0 < m) (h₁ : x₁ % m = y₁ % m)
    (h₂ : x₂ % m = y₂ % m) : (x₁ * x₂) % m = (y₁ * y₂) % m := by
  rw [mod_mul hm, h₁, h₂, ← mod_mul hm]

private lemma mod_mod_self {x m : V} (hm : 0 < m) : (x % m) % m = x % m :=
  mod_eq_self_of_lt (mod_lt x hm)

end IOpen

section ISigmaOne

variable [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

/-- A number coprime to a modulus above one has a multiplicative inverse there. -/
private theorem exists_mul_mod_eq_one {A m : V} (hm : 1 < m)
    (hco : ∀ d : V, d ∣ A → d ∣ m → d = 1) : ∃ u : V, (A * u) % m = 1 := by
  have hm0 : 0 < m := lt_trans _root_.zero_lt_one hm
  have hdef : Σ₀-Predicate (fun r : V => 0 < r ∧ ∃ u < m, (A * u) % m = r) := by
    definability
  have hAm : 0 < A % m := by
    rcases eq_or_ne (A % m) 0 with h | h
    · exact absurd (hco m (mod_eq_zero_iff_dvd.mp h) dvd_rfl) (ne_of_gt hm)
    · exact pos_iff_ne_zero.mpr h
  have hstart : (0 : V) < A % m ∧ ∃ u < m, (A * u) % m = A % m := ⟨hAm, 1, hm, by simp⟩
  obtain ⟨g, ⟨hgpos, u₀, -, hu₀⟩, hmin⟩ := ISigma0.least_number hdef hstart
  have hgm : g < m := lt_of_le_of_lt (not_lt.mp fun hc => hmin _ hc hstart) (mod_lt A hm0)
  have hgself : g % m = g := mod_eq_self_of_lt hgm
  -- no residue of a multiple of `A` lies strictly below the least positive one
  have hnew : ∀ s w : V, (A * w) % m = s → s < g → s = 0 := by
    intro s w hw hs
    by_contra h0
    exact hmin s hs ⟨pos_iff_ne_zero.mpr h0, w % m, mod_lt _ hm0,
      by rw [mod_mul_congr hm0 rfl (mod_mod_self hm0)]; exact hw⟩
  -- hence the least positive residue divides every residue
  have hstep : ∀ w z : V, (A * w) % m = z → g ∣ z := by
    intro w z hz
    have hzm : z < m := hz ▸ mod_lt _ hm0
    have hzk : g * (z / g) + z % g = z := div_add_mod z g
    have hr : z % g < g := mod_lt z hgpos
    have hKk : (m * (z / g + 1) - z / g) + z / g = m * (z / g + 1) :=
      sub_add_self_of_le (le_of_lt
        (lt_of_lt_of_le (lt_add_one _) (le_mul_self_of_pos_left hm0)))
    have harith : z + (m * (z / g + 1) - z / g) * g
        = z % g + m * ((z / g + 1) * g) := by
      calc z + (m * (z / g + 1) - z / g) * g
          = (g * (z / g) + z % g) + (m * (z / g + 1) - z / g) * g := by rw [hzk]
        _ = z % g + ((m * (z / g + 1) - z / g) + z / g) * g := by simp [mul_add, mul_comm, add_comm,
          add_assoc]
        _ = z % g + (m * (z / g + 1)) * g := by rw [hKk]
        _ = z % g + m * ((z / g + 1) * g) := by simp [mul_add, mul_comm, mul_left_comm, add_comm]
    have key : (A * (w + (m * (z / g + 1) - z / g) * u₀)) % m = z % g := by
      calc (A * (w + (m * (z / g + 1) - z / g) * u₀)) % m
          = (A * w + (m * (z / g + 1) - z / g) * (A * u₀)) % m := by
              congr 1
              simp [mul_add, mul_comm, mul_assoc, add_comm]
        _ = (z + (m * (z / g + 1) - z / g) * g) % m :=
              mod_add_congr hm0 (by rw [hz, mod_eq_self_of_lt hzm])
                (mod_mul_congr hm0 rfl (by rw [hu₀, hgself]))
        _ = (z % g + m * ((z / g + 1) * g)) % m := by rw [harith]
        _ = z % g := by
              rw [mod_add_mul' _ _ hm0, mod_eq_self_of_lt (lt_trans hr hgm)]
    exact mod_eq_zero_iff_dvd.mp (hnew _ _ key hr)
  -- and in particular divides the modulus
  have hgdvdm : g ∣ m := by
    have hr : m % g < g := mod_lt m hgpos
    have hrg : m % g ≤ g := le_of_lt hr
    have hmq : g * (m / g) + m % g = m := div_add_mod m g
    rcases eq_or_ne (m % g) 0 with h0 | h0
    · exact mod_eq_zero_iff_dvd.mp h0
    · exfalso
      have harith : (m / g + 1) * g = m + (g - m % g) := by
        calc (m / g + 1) * g = g * (m / g) + g := by simp [mul_add, mul_comm, add_comm]
          _ = g * (m / g) + ((g - m % g) + m % g) := by rw [sub_add_self_of_le hrg]
          _ = (g * (m / g) + m % g) + (g - m % g) := by simp [
            add_comm, add_left_comm, add_assoc]
          _ = m + (g - m % g) := by rw [hmq]
      have key : (A * ((m / g + 1) * u₀)) % m = g - m % g := by
        calc (A * ((m / g + 1) * u₀)) % m
            = ((m / g + 1) * (A * u₀)) % m := by congr 1; simp [mul_add, mul_comm, mul_left_comm,
              add_comm]
          _ = ((m / g + 1) * g) % m := mod_mul_congr hm0 rfl (by rw [hu₀, hgself])
          _ = (m + (g - m % g)) % m := by rw [harith]
          _ = g - m % g := by
                rw [mod_add_remove_left hm0, mod_eq_self_of_lt
                  (lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.sub_le_self _ _) hgm)]
      have hsub_lt : g - m % g < g := by
        have h : g - m % g < g - m % g + m % g :=
          lt_add_of_pos_right _ (pos_iff_ne_zero.mpr h0)
        rwa [sub_add_self_of_le hrg] at h
      exact absurd hr (not_lt.mpr (sub_eq_zero_iff_le.mp (hnew _ _ key hsub_lt)))
  have hgdvdA : g ∣ A := by
    have h₁ : g ∣ A % m := hstep 1 _ (by simp)
    have h₂ : m * (A / m) + A % m = A := div_add_mod A m
    exact h₂ ▸ Dvd.dvd.add (Dvd.dvd.mul_right hgdvdm _) h₁
  exact ⟨u₀, by rw [hu₀, hco g hgdvdA hgdvdm]⟩

namespace InternalFactorial
private def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = 1”
  succ := .mkSigma “y ih k. y = (k + 1) * ih”

private noncomputable def construction : PR.Construction V blueprint
    where
  zero _ := 1
  succ _ k ih := (k + 1) * ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]
end InternalFactorial

/-- The internal factorial. -/
private noncomputable def internalFactorial (k : V) : V :=
  InternalFactorial.construction.result ![] k

@[simp]
private lemma internalFactorial_zero : internalFactorial (0 : V) = 1 := by
  simp [internalFactorial, InternalFactorial.construction]

@[simp]
private lemma internalFactorial_succ (k : V) :
    internalFactorial (k + 1) = (k + 1) * internalFactorial k := by
  simp [internalFactorial, InternalFactorial.construction]

private noncomputable def internalFactorialGraph : Σ₁.Semisentence 2 :=
  InternalFactorial.blueprint.resultDef

private instance internalFactorial_defined :
    Σ₁-Function₁[V] internalFactorial via internalFactorialGraph :=
  .mk fun v ↦ by
    simp [InternalFactorial.construction.result_defined_iff, internalFactorialGraph,
      internalFactorial, _root_.Matrix.empty_eq]

private instance internalFactorial_definable : Σ₁-Function₁[V] internalFactorial :=
  internalFactorial_defined.to_definable

private instance internalFactorial_definable' (Γ m) :
    Γ-[m + 1]-Function₁[V] internalFactorial :=
  internalFactorial_definable.of_sigmaOne

namespace ModulusProduct
private def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y b. y = 1”
  succ := .mkSigma “y ih k b. y = ((k + 1) * b + 1) * ih”

private noncomputable def construction : PR.Construction V blueprint
    where
  zero _ := 1
  succ param k ih := ((k + 1) * param 0 + 1) * ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]
end ModulusProduct

/-- The internal product of the beta moduli below a given index. -/
private noncomputable def modulusProduct (b j : V) : V :=
  ModulusProduct.construction.result ![b] j

@[simp]
private lemma modulusProduct_zero (b : V) : modulusProduct b 0 = 1 := by
  simp [modulusProduct, ModulusProduct.construction]

@[simp]
private lemma modulusProduct_succ (b j : V) :
    modulusProduct b (j + 1) = ((j + 1) * b + 1) * modulusProduct b j := by
  simp [modulusProduct, ModulusProduct.construction]

private noncomputable def modulusProductGraph : Σ₁.Semisentence 3 :=
  ModulusProduct.blueprint.resultDef

private instance modulusProduct_defined :
    Σ₁-Function₂[V] (fun b j => modulusProduct b j) via
      modulusProductGraph.rew (Rew.subst ![#0, #2, #1]) :=
  .mk fun v ↦ by
    simp [ModulusProduct.construction.result_defined_iff, modulusProductGraph, modulusProduct,
      show (fun _ : Fin 1 => v 1) = (![v 1] : Fin 1 → V) from
          funext fun i => by rcases Fin.eq_zero i with rfl; simp]

private instance modulusProduct_definable :
    Σ₁-Function₂[V] (fun b j : V => modulusProduct b j) :=
  modulusProduct_defined.to_definable

private instance modulusProduct_definable' (Γ m) :
    Γ-[m + 1]-Function₂[V] (fun b j : V => modulusProduct b j) :=
  modulusProduct_definable.of_sigmaOne

private lemma internalFactorial_pos (k : V) : 0 < internalFactorial k :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp only [internalFactorial_succ]; exact mul_pos (by simp) ih

private lemma self_le_internalFactorial (k : V) : k ≤ internalFactorial k :=
  by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simp only [internalFactorial_succ]
    exact le_mul_self_of_pos_right (internalFactorial_pos k)

private lemma dvd_internalFactorial {j k : V} (hj : 0 < j) (hjk : j ≤ k) :
    j ∣ internalFactorial k :=
  by
  have main : ∀ k : V, ∀ j < k + 1, 0 < j → j ∣ internalFactorial k :=
    by
    intro k
    induction k using ISigma1.pi1_succ_induction
    · definability
    case zero =>
      intro j hj hjpos
      exact absurd (lt_succ_iff_le.mp hj) (not_le.mpr hjpos)
    case succ k ih =>
      intro j hj hjpos
      simp only [internalFactorial_succ]
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hj) with h | rfl
      · exact Dvd.dvd.mul_left (ih j h hjpos) _
      · exact Dvd.dvd.mul_right dvd_rfl _
  exact main k j (lt_succ_iff_le.mpr hjk) hj

private lemma dvd_modulusProduct {b i j : V} (hij : i < j) :
    ((i + 1) * b + 1) ∣ modulusProduct b j :=
  by
  have main : ∀ j : V, ∀ i < j, ((i + 1) * b + 1) ∣ modulusProduct b j :=
    by
    intro j
    induction j using ISigma1.pi1_succ_induction
    · definability
    case zero => intro i hi; exact absurd hi (by simp)
    case succ j ih =>
      intro i hi
      simp only [modulusProduct_succ]
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hi) with h | rfl
      · exact Dvd.dvd.mul_left (ih i h) _
      · exact Dvd.dvd.mul_right dvd_rfl _
  exact main j i hij

private lemma inv_mul {m a c : V} (hm : 1 < m)
    (ha : ∃ u : V, (a * u) % m = 1) (hc : ∃ w : V, (c * w) % m = 1) :
    ∃ z : V, (a * c * z) % m = 1 := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨w, hw⟩ := hc
  have hm0 : 0 < m := lt_trans _root_.zero_lt_one hm
  refine ⟨u * w, ?_⟩
  calc (a * c * (u * w)) % m = ((a * u) * (c * w)) % m := by congr 1; simp [mul_comm, mul_left_comm,
    ]
    _ = (((a * u) % m) * ((c * w) % m)) % m := mod_mul hm0
    _ = 1 := by rw [hu, hw, mul_one, mod_eq_self_of_lt hm]

/-- Two beta moduli whose index difference divides the multiplier have no common
divisor above one. -/
private lemma modulus_coprime {b i j : V} (hij : i < j) (hdvd : (j - i) ∣ b)
    (d : V) (hi : d ∣ (i + 1) * b + 1) (hj : d ∣ (j + 1) * b + 1) : d = 1 := by
  have hsum : ((i + 1) * b + 1) + (j - i) * b = (j + 1) * b + 1 := by
    have e : i + (j - i) = j := add_tsub_self_of_le (le_of_lt hij)
    calc ((i + 1) * b + 1) + (j - i) * b = ((i + (j - i)) + 1) * b + 1 := by simp [mul_add,
      mul_comm, add_comm, add_left_comm, add_assoc]
      _ = (j + 1) * b + 1 := by rw [e]
  have hdb : d ∣ (j - i) * b := by
    have e : ((j + 1) * b + 1) - ((i + 1) * b + 1) = (j - i) * b := by rw [← hsum]; simp
    exact e ▸ dvd_sub_of hj hi
  have hbb : d ∣ b * b := by
    obtain ⟨w, hw⟩ := hdvd
    have e : ((j - i) * b) * w = b * b := by
      calc ((j - i) * b) * w = ((j - i) * w) * b := by simp [mul_comm, mul_left_comm, ]
        _ = b * b := by rw [← hw]
    exact e ▸ Dvd.dvd.mul_right hdb w
  have hco : ∀ e : V, e ∣ b → e ∣ d → e = 1 := by
    intro e heb hed
    have h1 : e ∣ (i + 1) * b + 1 := Dvd.dvd.trans hed hi
    have h2 : e ∣ (i + 1) * b := Dvd.dvd.mul_left heb _
    have h3 : ((i + 1) * b + 1) - ((i + 1) * b) = 1 := by simp
    exact dvd_one_iff.mp (h3 ▸ dvd_sub_of h1 h2)
  rcases eq_or_ne d 1 with h | h
  · exact h
  · exfalso
    have hd0 : d ≠ 0 := by
      intro h0
      rw [h0, zero_dvd_iff] at hi
      simp at hi
    have hd1 : 1 < d := lt_of_le_of_ne (ne_zero_iff_one_le.mp hd0) (Ne.symm h)
    have hd0' : 0 < d := lt_trans _root_.zero_lt_one hd1
    obtain ⟨v, hv⟩ := exists_mul_mod_eq_one hd1 hco
    have hzero : (b * b * (v * v)) % d = 0 := by
      rw [mod_mul hd0', mod_eq_zero_iff_dvd.mpr hbb]
      simp
    have hone : (b * b * (v * v)) % d = 1 := by
      calc (b * b * (v * v)) % d = ((b * v) * (b * v)) % d := by congr 1; simp [mul_comm,
        mul_left_comm, ]
        _ = (((b * v) % d) * ((b * v) % d)) % d := mod_mul hd0'
        _ = 1 := by rw [hv, mul_one, mod_eq_self_of_lt hd1]
    exact absurd (hzero.symm.trans hone) zero_ne_one

/-- The product of the beta moduli below an index is invertible modulo the
modulus at that index. -/
private lemma exists_inv_modulusProduct {b L : V} (hm : 1 < (L + 1) * b + 1)
    (hcop : ∀ i < L, ∀ d : V, d ∣ (i + 1) * b + 1 → d ∣ (L + 1) * b + 1 → d = 1) :
    ∀ j ≤ L, ∃ u : V, (modulusProduct b j * u) % ((L + 1) * b + 1) = 1 :=
  by
  intro j
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _
    exact ⟨1, by rw [modulusProduct_zero, mul_one, mod_eq_self_of_lt hm]⟩
  case succ j ih =>
    intro hj
    have hjL : j < L := succ_le_iff_lt.mp hj
    rw [modulusProduct_succ]
    exact inv_mul hm (exists_mul_mod_eq_one hm (hcop j hjL)) (ih (le_of_lt hjL))

/-- Simultaneous solution of the beta congruences supplied by an internal
sequence. -/
private lemma exists_crt {s b : V} (hb : 0 < b)
    (hcop : ∀ i j : V, i < j → j < lh s → ∀ d : V,
      d ∣ (i + 1) * b + 1 → d ∣ (j + 1) * b + 1 → d = 1)
    (hlt : ∀ i < lh s, znth s i < (i + 1) * b + 1) :
    ∃ c : V, ∀ i < lh s, c % ((i + 1) * b + 1) = znth s i := by
  have hmod : ∀ i : V, 1 < (i + 1) * b + 1 := by
    intro i
    have : 0 < (i + 1) * b := mul_pos (by simp) hb
    simpa using this
  have main : ∀ L : V, L ≤ lh s → ∃ c : V, ∀ i < L, c % ((i + 1) * b + 1) = znth s i := by
    intro L
    induction L using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; exact ⟨0, by intro i hi; exact absurd hi (by simp)⟩
    case succ L ih =>
        intro hL
        have hLs : L < lh s := succ_le_iff_lt.mp hL
        obtain ⟨c, hc⟩ := ih (le_of_lt hLs)
        have hm : 1 < (L + 1) * b + 1 := hmod L
        have hm0 : 0 < (L + 1) * b + 1 := lt_trans _root_.zero_lt_one hm
        obtain ⟨u, hu⟩ := exists_inv_modulusProduct hm
          (fun i hiL d h₁ h₂ => hcop i L hiL hLs d h₁ h₂) L (le_refl L)
        have hclt : c < ((L + 1) * b + 1) * (c + 1) :=
          lt_of_lt_of_le (lt_add_one c) (le_mul_self_of_pos_left hm0)
        have hr : (znth s L + ((L + 1) * b + 1) * (c + 1) - c) + c
            = znth s L + ((L + 1) * b + 1) * (c + 1) :=
          sub_add_self_of_le (le_trans (le_of_lt hclt) le_add_self)
        refine ⟨c + u * (znth s L + ((L + 1) * b + 1) * (c + 1) - c) * modulusProduct b L, ?_⟩
        intro i hi
        rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hi) with hiL | rfl
        · rw [mod_add_remove_right_of_dvd
            (Dvd.dvd.mul_left (dvd_modulusProduct hiL) _) (lt_trans _root_.zero_lt_one (hmod i))]
          exact hc i hiL
        · have hres : (u * (znth s i + ((i + 1) * b + 1) * (c + 1) - c) * modulusProduct b i)
              % ((i + 1) * b + 1)
              = (znth s i + ((i + 1) * b + 1) * (c + 1) - c) % ((i + 1) * b + 1) := by
            calc (u * (znth s i + ((i + 1) * b + 1) * (c + 1) - c) * modulusProduct b i)
                  % ((i + 1) * b + 1)
                = ((znth s i + ((i + 1) * b + 1) * (c + 1) - c) * (modulusProduct b i * u))
                  % ((i + 1) * b + 1) := by
                    congr 1
                    simp [mul_add, mul_comm, mul_left_comm, mul_assoc, add_comm,
                      add_left_comm, add_assoc]
              _ = (((znth s i + ((i + 1) * b + 1) * (c + 1) - c) % ((i + 1) * b + 1))
                    * ((modulusProduct b i * u) % ((i + 1) * b + 1))) % ((i + 1) * b + 1) :=
                    mod_mul hm0
              _ = (znth s i + ((i + 1) * b + 1) * (c + 1) - c) % ((i + 1) * b + 1) := by
                    rw [hu, mul_one, mod_mod_self hm0]
          calc (c + u * (znth s i + ((i + 1) * b + 1) * (c + 1) - c) * modulusProduct b i)
                % ((i + 1) * b + 1)
              = (c + (znth s i + ((i + 1) * b + 1) * (c + 1) - c)) % ((i + 1) * b + 1) :=
                  mod_add_congr hm0 rfl hres
            _ = (znth s i + ((i + 1) * b + 1) * (c + 1)) % ((i + 1) * b + 1) := by
                  rw [add_comm c, hr]
            _ = znth s i := by
                  rw [mod_add_mul' _ _ hm0, mod_eq_self_of_lt (hlt i hLs)]
  exact main (lh s) (le_refl _)

/-- Gödel beta coding of an internal finite sequence. -/
private lemma exists_beta_of_seq {s : V} (hs : Seq s) :
    ∃ c b : V, 0 < b ∧ ∀ i < lh s, c % ((i + 1) * b + 1) = znth s i := by
  have hb : 0 < internalFactorial (s + lh s) := internalFactorial_pos _
  have hlt : ∀ i < lh s, znth s i < (i + 1) * internalFactorial (s + lh s) + 1 := by
    intro i hi
    calc znth s i < s := lt_of_mem_rng (hs.znth hi)
      _ ≤ s + lh s := le_self_add
      _ ≤ internalFactorial (s + lh s) := self_le_internalFactorial _
      _ ≤ (i + 1) * internalFactorial (s + lh s) := le_mul_self_of_pos_left (by simp)
      _ < (i + 1) * internalFactorial (s + lh s) + 1 := lt_add_one _
  have hcop : ∀ i j : V, i < j → j < lh s → ∀ d : V,
      d ∣ (i + 1) * internalFactorial (s + lh s) + 1 →
      d ∣ (j + 1) * internalFactorial (s + lh s) + 1 → d = 1 := by
    intro i j hij hj d h₁ h₂
    refine modulus_coprime hij (dvd_internalFactorial (pos_sub_iff_lt.mpr hij) ?_) d h₁ h₂
    calc j - i ≤ j := FFL.FirstOrder.Arithmetic.sub_le_self _ _
      _ ≤ s + lh s := le_trans (le_of_lt hj) le_add_self
  obtain ⟨c, hc⟩ := exists_crt hb hcop hlt
  exact ⟨c, internalFactorial (s + lh s), hb, hc⟩

end ISigmaOne

end Internal

/-- Every Gödel beta code extends to one that keeps its values below an index and
takes a prescribed value at that index.

The two evaluations are the graph of `codeBeta (Code.proj 0) (Code.proj 1)` at
the assignments `![n, i]` and `![n', i]`; `eval_codeBeta_of_values` identifies
that graph with the remainder the code computes. -/
theorem exists_codeBeta_extension
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    (n l x : M) :
    ∃ n' : M,
      (∀ i y : M, i < l →
        Semiformula.Evalb (y :> ![n, i])
          (code (codeBeta
            (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2)))) →
        Semiformula.Evalb (y :> ![n', i])
          (code (codeBeta
            (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2))))) ∧
      Semiformula.Evalb (x :> ![n', l])
        (code (codeBeta
          (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2)))) := by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ 1 :=
    models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  -- the graph of `codeBeta` on the two projections, at an arbitrary pair
  have hbeta : ∀ a i : M, Semiformula.Evalb
      ((FFL.FirstOrder.Arithmetic.pi₁ a %
        ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ a + 1)) :> ![a, i])
      (code (codeBeta (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2)))) := by
    intro a i
    exact eval_codeBeta_of_values _ _ a i ![a, i]
      ((eval_proj_iff _ _ _).mpr (by simp)) ((eval_proj_iff _ _ _).mpr (by simp))
  -- the sequence of old beta values below `l`, extended by `x` at `l`
  have hR : Σ₁-Relation (fun i y : M =>
      (i < l ∧ y = FFL.FirstOrder.Arithmetic.pi₁ n %
        ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n + 1)) ∨ (i = l ∧ y = x)) := by
    definability
  have hU : ∀ i < l + 1, ∃ y : M,
      (i < l ∧ y = FFL.FirstOrder.Arithmetic.pi₁ n %
        ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n + 1)) ∨ (i = l ∧ y = x) := by
    intro i hi
    rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hi) with h | rfl
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨x, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨s, hs, hlh, hsR⟩ := sigmaOne_skolem_seq hR hU
  obtain ⟨c, b, -, hc⟩ := exists_beta_of_seq hs
  have hval : ∀ i < l + 1,
      (i < l ∧ znth s i = FFL.FirstOrder.Arithmetic.pi₁ n %
        ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n + 1)) ∨ (i = l ∧ znth s i = x) :=
    fun i hi => hsR i (znth s i) (hs.znth (by rw [hlh]; exact hi))
  refine ⟨FFL.FirstOrder.Arithmetic.pair c b, ?_, ?_⟩
  · intro i y hi hy
    have hyval : y = FFL.FirstOrder.Arithmetic.pi₁ n %
        ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n + 1) := eval_unique hy (hbeta n i)
    have hcv : c % ((i + 1) * b + 1) = znth s i :=
      hc i (by rw [hlh]; exact lt_succ_iff_le.mpr (le_of_lt hi))
    have hzn : znth s i = FFL.FirstOrder.Arithmetic.pi₁ n %
        ((i + 1) * FFL.FirstOrder.Arithmetic.pi₂ n + 1) := by
      rcases hval i (lt_succ_iff_le.mpr (le_of_lt hi)) with ⟨-, h⟩ | ⟨rfl, -⟩
      · exact h
      · exact absurd hi (_root_.lt_irrefl _)
    have h := hbeta (FFL.FirstOrder.Arithmetic.pair c b) i
    rw [FFL.FirstOrder.Arithmetic.pi₁_pair, FFL.FirstOrder.Arithmetic.pi₂_pair,
      hcv, hzn, ← hyval] at h
    exact h
  · have hcv : c % ((l + 1) * b + 1) = znth s l := hc l (by rw [hlh]; exact lt_add_one l)
    have hzn : znth s l = x := by
      rcases hval l (lt_add_one l) with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h (_root_.lt_irrefl _)
      · exact h
    have h := hbeta (FFL.FirstOrder.Arithmetic.pair c b) l
    rw [FFL.FirstOrder.Arithmetic.pi₁_pair, FFL.FirstOrder.Arithmetic.pi₂_pair,
      hcv, hzn] at h
    exact h

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
