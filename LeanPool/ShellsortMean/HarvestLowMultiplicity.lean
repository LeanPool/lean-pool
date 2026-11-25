/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, diagnostics, and proof consolidation. -/

module

public import LeanPool.ShellsortMean.HarvestMenuSieve

/-! Counting low modes over a gap menu before taking a worst grid.
For a fixed reduced denominator d, its possible original grid tags fit
in B slots, for all original moduli h ≤ B together. -/
@[expose] public noncomputable section
namespace Shellsort.Actual214
open Finset RoughGapDenominatorAverage RoughGapEndpoint

private def pack (p : Fraction) : ℕ × ℕ :=
  let u := reduced p
  (u.2 - 1, u.1 + u.2 * (mult p - 1))

private theorem pack_facts (p : Fraction) (ltp : p.1 < p.2) :
    0 < (reduced p).2 ∧ (pack p).2 < p.2 ∧
    (pack p).2 / (reduced p).2 + 1 = mult p ∧
    (pack p).2 % (reduced p).2 = (reduced p).1 := by
  have g : 0 < mult p := Nat.gcd_pos_of_pos_right _ (by omega)
  have pr : (reduced p).1 < (reduced p).2 :=
    (Nat.div_lt_div_right g.ne' (Nat.gcd_dvd_right ..)).mpr ltp
  have dp : 0 < (reduced p).2 := by omega
  have hd : (reduced p).2 * mult p = p.2 := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have gs : mult p - 1 + 1 = mult p := by omega
  refine ⟨dp, ?_, ?_, ?_⟩
  · change (reduced p).1 + (reduced p).2 * (mult p - 1) < p.2
    calc
      _ < (reduced p).2 + (reduced p).2 * (mult p - 1) := Nat.add_lt_add_right pr _
      _ = (reduced p).2 * (mult p - 1 + 1) := by ring
      _ = p.2 := by rw [gs, hd]
  · dsimp only [pack]
    rw [Nat.add_mul_div_left _ _ dp, Nat.div_eq_of_lt pr, zero_add]
    exact gs
  · dsimp only [pack]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt pr]

/-- Any collection of genuine fraction tags, with original modulus ≤ B and
reduced denominator ≤ D, has size at most B D. -/
theorem low_tag_count {B D : ℕ} (S : Finset Fraction)
    (size : ∀ p ∈ S, p.1 < p.2 ∧ p.2 ≤ B ∧ (reduced p).2 ≤ D) :
    S.card ≤ D * B := by
  have h : S.card ≤ ((range D) ×ˢ (range B)).card := by
    apply card_le_card_of_injOn pack
    · intro p hp
      obtain ⟨ltp, hb, hd⟩ := size p hp
      obtain ⟨dpos, bounded, _, _⟩ := pack_facts p ltp
      exact mem_product.mpr ⟨mem_range.mpr (by change (reduced p).2 - 1 < D; omega),
        mem_range.mpr (bounded.trans_le hb)⟩
    · intro p hp q hq e
      obtain ⟨pd, _, pc, pr⟩ := pack_facts p (size p hp).1
      obtain ⟨qd, _, qc, qr⟩ := pack_facts q (size q hq).1
      have d0 : (reduced p).2 - 1 = (reduced q).2 - 1 := congrArg Prod.fst e
      have d : (reduced p).2 = (reduced q).2 := by omega
      have t : (pack p).2 = (pack q).2 := congrArg Prod.snd e
      rw [t, d] at pc pr
      have g : mult p = mult q := pc.symm.trans qc
      have a : (reduced p).1 = (reduced q).1 := pr.symm.trans qr
      apply Prod.ext
      · calc
          p.1 = (reduced p).1 * mult p := (Nat.div_mul_cancel (Nat.gcd_dvd_left ..)).symm
          _ = (reduced q).1 * mult q := by rw [g, a]
          _ = q.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
      · calc
          p.2 = (reduced p).2 * mult p := (Nat.div_mul_cancel (Nat.gcd_dvd_right ..)).symm
          _ = (reduced q).2 * mult q := by rw [g, d]
          _ = q.2 := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  simpa using h

theorem low_menu_count {B : ℕ} (G : Finset ℕ) (D : ℕ)
    (bounded : ∀ h ∈ G, h ≤ B) :
    (∑ h ∈ G, (lowGrid h D).card) ≤ D * B := by
  classical
  let U (h : ℕ) := (lowGrid h D).image (fun a => (a, h))
  have dis : Set.PairwiseDisjoint (↑G) U := by
    intro h _ k _ ne
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨a, _, rfl⟩ := mem_image.mp hp
    obtain ⟨b, _, e⟩ := mem_image.mp hq
    exact ne (congrArg Prod.snd e).symm
  have bound := low_tag_count (B := B) (D := D) (G.biUnion U) (by
    intro p hp
    obtain ⟨h, hg, hh⟩ := mem_biUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hh
    obtain ⟨ar, _, dl⟩ := mem_filter.mp ha
    exact ⟨mem_range.mp ar, bounded h hg, by simpa [reduced, mult, Nat.gcd_comm] using dl⟩)
  have cards (h : ℕ) : (U h).card = (lowGrid h D).card :=
    card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq)
  simpa only [card_biUnion dis, cards] using bound

/-- On the same state after both retained passes the total low energy,
summed over the whole admissible menu, pays D squared. -/
theorem low_menu_energy {n c g₁ g₂ D B : ℕ}
    (p : RankPlacement n) (T : ℕ) (hT : T ≤ n) (h₂ : 0 < g₂) (hle : g₂ ≤ g₁)
    (G : Finset ℕ) (menu : ∀ h ∈ G, h ∈ window c (Nat.gcd g₁ g₂))
    (bounded : ∀ h ∈ G, h ≤ B) :
    (∑ h ∈ G, ∑ a ∈ lowGrid h D, energy 0 (fun i : Fin n ↦
      (slotError (gapSort (gapSort p g₁) g₂) T i : ℂ)) (a, h)) ≤
      (2 * (g₁ : ℝ) * D ^ 2 * B) * (∑ i, |(slotError p T i : ℝ)|) := by
  let mass : ℝ := ∑ i, |(slotError p T i : ℝ)|
  have mp : 0 ≤ mass := by dsimp [mass]; positivity
  let K := 2 * (g₁ : ℝ) * D * mass
  have kp : 0 ≤ K := by dsimp [K]; positivity
  have each (h : ℕ) (hg : h ∈ G) (a : ℕ) (ha : a ∈ lowGrid h D) :
      energy 0 (fun i : Fin n ↦ (slotError (gapSort (gapSort p g₁) g₂) T i : ℂ)) (a, h) ≤ K := by
    obtain ⟨ar, ap, dl⟩ := mem_filter.mp ha
    have lt := mem_range.mp ar
    have hp : 0 < h := by omega
    have gp := Nat.gcd_pos_of_pos_left a hp
    have rr := (Nat.div_lt_div_right gp.ne' (Nat.gcd_dvd_left h a)).mpr lt
    have apos := Nat.div_pos (Nat.gcd_le_right h ap) gp
    have dp : 1 < h / Nat.gcd h a := by omega
    have prim := (negGridRoot_primitive hp).pow_div_gcd a gp.ne'
    rw [physical_energy_eq_grid]
    apply (menu_mode_after_retained p T hT h₂ hle (menu h hg)
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left h a)) dp _ (prim.norm'_eq_one (by omega)) prim).trans
    change 2 * (g₁ : ℝ) * (h / Nat.gcd h a : ℕ) * mass ≤ 2 * (g₁ : ℝ) * D * mass
    gcongr
  have countR : (∑ h ∈ G, ((lowGrid h D).card : ℝ)) ≤ (D : ℝ) * B := by
    exact_mod_cast low_menu_count G D bounded
  calc
    _ ≤ ∑ h ∈ G, ∑ _a ∈ lowGrid h D, K :=
      sum_le_sum fun h hg => sum_le_sum fun a ha => each h hg a ha
    _ = (∑ h ∈ G, ((lowGrid h D).card : ℝ)) * K := by
      simp only [sum_const, nsmul_eq_mul, sum_mul]
    _ ≤ ((D : ℝ) * B) * K := mul_le_mul_of_nonneg_right countR kp
    _ = _ := by dsimp [K, mass]; ring

end Shellsort.Actual214
