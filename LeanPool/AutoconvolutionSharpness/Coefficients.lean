/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.BlockExpansion
public import LeanPool.AutoconvolutionSharpness.Occupancy
public import LeanPool.AutoconvolutionSharpness.Estimate
public import LeanPool.AutoconvolutionSharpness.Flat

/-!
# The coefficients of the square

All rows at all levels are kept in one disjoint sum. Their exponents are
injective by digit recovery. Consequently each coefficient either vanishes or
is exactly the weight of its sole row. Distinct choices at the first K + 1
levels give whole runs of equal maximal - height coefficients.
-/

@[expose] public section

open Finset Polynomial
open scoped BigOperators

namespace Autoconvolutions.Blocks

private abbrev Ticket (m : ℕ) := Σ _ : ℕ, Row m

private noncomputable def tickets {m : ℕ} (I J : Finset (Fin m)) (n K D : ℕ) :
    Finset (Ticket m) :=
  (range (2 * K + 1)).sigma fun s => rows I J (2 * n - s) (2 * n + s) D

private noncomputable def weight {m : ℕ} (I J : Finset (Fin m)) (K : ℕ)
    (t : Ticket m) : ℝ :=
  (Nat.multinomial I t.2.1.1 : ℝ) * (Nat.multinomial J t.2.1.2 : ℝ) *
    (Flat.B K t.1).coeff t.2.2

private theorem mem_tickets {m n K D : ℕ} {I J : Finset (Fin m)} {t : Ticket m} :
    t ∈ tickets I J n K D ↔ t.1 ≤ 2 * K ∧ t.2 ∈ rows I J (2 * n - t.1) (2 * n + t.1) D := by
  simp only [tickets, mem_sigma, mem_range, Nat.lt_succ_iff]

private theorem square_expansion {m n K D : ℕ} (I J : Finset (Fin m))
    (hK : K < n) (hD : 4 * n < D) :
    (Construction.family Flat.P (gen D I) (gen D J) n K) ^ 2 =
    ∑ t ∈ tickets I J n K D, monomial (rowKey D t.2) (weight I J K t) := by
  classical
  rw [Construction.family_sq _ _ _ hK.le, tickets, Finset.sum_sigma]
  apply sum_congr rfl
  intro s hs
  change (gen D I) ^ (2 * n - s) * (gen D J) ^ (2 * n + s) * Flat.B K s = _
  apply expand_level
  intro h hh
  have hs' := mem_range.mp hs
  exact Flat.B_coeff_zero (by omega)

private theorem ticket_injective {m n K D : ℕ} {I J : Finset (Fin m)}
    (hd : Disjoint I J) (hK : K < n) (hD : 4 * n < D)
    {t t' : Ticket m} (ht : t ∈ tickets I J n K D) (ht' : t' ∈ tickets I J n K D)
    (he : rowKey D t.2 = rowKey D t'.2) : t = t' := by
  obtain ⟨s,r⟩ := t
  obtain ⟨s',r'⟩ := t'
  obtain ⟨hs,hr⟩ := mem_tickets.mp ht
  obtain ⟨hs',hr'⟩ := mem_tickets.mp ht'
  dsimp at hs hs' hr hr' he
  obtain ⟨h₁,h₂⟩ := rowKey_determines_level (by omega) hd (by omega) (by omega) hD hr hr' he
  subst s'
  subst r'
  rfl

private theorem coeff_on_ticket {m n K D : ℕ} {I J : Finset (Fin m)}
    (hd : Disjoint I J) (hK : K < n) (hD : 4 * n < D)
    {t : Ticket m} (ht : t ∈ tickets I J n K D) :
    ((Construction.family Flat.P (gen D I) (gen D J) n K) ^ 2).coeff (rowKey D t.2) =
    weight I J K t := by
  classical
  rw [square_expansion I J hK hD, Polynomial.finsetSum_coeff, sum_eq_single_of_mem t ht]
  · exact Polynomial.coeff_monomial_same _ _
  · intro u hu hne
    exact Polynomial.coeff_monomial_of_ne _ (fun h => hne (ticket_injective hd hK hD hu ht h.symm))

/-- Every coefficient of F² is bounded by the factorial height at the last level. -/
theorem coeff_cap {m n K D : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4 * n < D) (x : ℕ) :
    ((Construction.family Flat.P (gen D I) (gen D J) n K) ^ 2).coeff x ≤
      Estimate.height n (2 * K) := by
  classical
  by_cases hx : ∃ t ∈ tickets I J n K D, rowKey D t.2 = x
  · obtain ⟨t,ht,rfl⟩ := hx
    rw [coeff_on_ticket hd hK hD ht]
    obtain ⟨hs,hr⟩ := mem_tickets.mp ht
    obtain ⟨ha,hb,_⟩ := mem_rows.mp hr
    have hleft : (Nat.multinomial I t.2.1.1 : ℝ) ≤ ((2 * n - t.1).factorial : ℝ) := by
      exact_mod_cast ((Finset.mem_piAntidiag.mp ha).1 ▸ Digits.multinomial_le_fact I t.2.1.1)
    have hright : (Nat.multinomial J t.2.1.2 : ℝ) ≤ ((2 * n + t.1).factorial : ℝ) := by
      exact_mod_cast ((Finset.mem_piAntidiag.mp hb).1 ▸ Digits.multinomial_le_fact J t.2.1.2)
    calc
      weight I J K t ≤ (Nat.multinomial I t.2.1.1 : ℝ) * Nat.multinomial J t.2.1.2 := by
        unfold weight
        exact mul_le_of_le_one_right (by positivity) (Flat.B_coeff_le_one ..)
      _ ≤ Estimate.height n t.1 := mul_le_mul hleft hright (by positivity) (by positivity)
      _ ≤ _ := Estimate.height_mono hs (by omega)
  · have hz : ((Construction.family Flat.P (gen D I) (gen D J) n K) ^ 2).coeff x = 0 := by
      rw [square_expansion I J hK hD, Polynomial.finsetSum_coeff]
      exact Finset.sum_eq_zero fun t ht => Polynomial.coeff_monomial_of_ne _
        (fun e => hx ⟨t,ht,e.symm⟩)
    rw [hz]
    exact (Estimate.height_pos ..).le

/-- Every low digit in a good block, including its right endpoint, gives the same
coefficient. In the piecewise linear convolution the plateau thus has length s. -/
theorem coeff_eq_good {m n K D s : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4 * n < D) (hs : s ≤ K)
    {a b : Fin m → ℕ} (ha : a ∈ goodVectors I (2 * n - s)) (hb : b ∈ goodVectors J (2 * n + s))
    (h : ℕ) (hh : h ≤ s) :
    ((Construction.family Flat.P (gen D I) (gen D J) n K) ^ 2).coeff (key D a b h) =
      Estimate.height n s := by
  classical
  obtain ⟨ha₁,ha₂⟩ := goodVectors_spec ha
  obtain ⟨hb₁,hb₂⟩ := goodVectors_spec hb
  let t : Ticket m := ⟨s, ((a,b),h)⟩
  have ht : t ∈ tickets I J n K D :=
    mem_tickets.mpr ⟨by change s ≤ 2 * K; omega, mem_rows.mpr ⟨ha₁,hb₁,by change h < D; omega⟩⟩
  change ((Construction.family Flat.P (gen D I) (gen D J) n K) ^ 2).coeff (rowKey D t.2) = _
  rw [coeff_on_ticket hd hK hD ht]
  have hB : (Flat.B K s).coeff h = 1 := by
    rw [Flat.B_flat hs, Polynomial.finsetSum_coeff]
    simp [Polynomial.coeff_X_pow, hh]
  simp only [weight, t, Estimate.height, Digits.multinomial_of_distinct I a (fun i _ => ha₂ i),
    Digits.multinomial_of_distinct J b (fun i _ => hb₂ i),
    (Finset.mem_piAntidiag.mp ha₁).1, (Finset.mem_piAntidiag.mp hb₁).1, hB, mul_one]

end Autoconvolutions.Blocks
