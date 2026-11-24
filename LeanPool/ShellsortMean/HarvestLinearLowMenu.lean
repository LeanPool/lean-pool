/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.HarvestPrimitiveSegment
public import LeanPool.ShellsortMean.HarvestLowMultiplicity

/-! Reassemble an entire primitive packet once for each of its original grids. -/
@[expose] public noncomputable section
namespace Shellsort.Actual214
open Finset RoughGapEndpoint RoughGapDenominatorAverage HarvestPrimitiveSegment

private def den (h a : ℕ) := h / h.gcd a
private def num (h a : ℕ) := a / h.gcd a
private def packSet (d : ℕ) := (range d).filter (fun a => a.Coprime d)

private theorem rep_facts {h D a : ℕ} (ha : a ∈ lowGrid h D) :
    1 < den h a ∧ den h a ≤ D ∧ den h a ∣ h ∧ num h a ∈ packSet (den h a) := by
  obtain ⟨ha, ap, dl⟩ := mem_filter.mp ha
  have al := mem_range.mp ha
  have gp := Nat.gcd_pos_of_pos_left a (by omega : 0 < h)
  have an := Nat.div_pos (Nat.gcd_le_right h ap) gp
  have ad := (Nat.div_lt_div_right gp.ne' (Nat.gcd_dvd_left h a)).mpr al
  exact ⟨by unfold den; omega, dl, Nat.div_dvd_of_dvd (Nat.gcd_dvd_left ..),
    mem_filter.mpr ⟨mem_range.mpr ad, by
      simpa only [num, den, Nat.gcd_comm h a] using Nat.coprime_div_gcd_div_gcd
        (m := a) (n := h) (by simpa [Nat.gcd_comm] using gp)⟩⟩

private theorem reduced_energy {n h D a : ℕ} (p : RankPlacement n) (T : ℕ) (ha : a ∈ lowGrid h D) :
    energy 0 (fun i : Fin n => (slotError p T i : ℂ)) (a, h) =
    ‖amplitude p T ((negGridRoot (den h a)) ^ (num h a))‖ ^ 2 := by
  rw [←physical_energy_eq_grid]
  have hp : 0 < h := by have := mem_range.mp (mem_filter.mp ha).1; omega
  have gp := Nat.gcd_pos_of_pos_left a hp
  have nz : (h.gcd a : ℂ) ≠ 0 := by exact_mod_cast gp.ne'
  have hr : (den h a : ℂ) * (h.gcd a : ℂ) = h := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left h a)
  have ar : (num h a : ℂ) * (h.gcd a : ℂ) = a := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right h a)
  have term (z : ℂ) : z * a / h = z * (num h a) / (den h a) := by
    rw [←ar, ←hr, ←mul_assoc, mul_div_mul_right _ _ nz]
  simp only [energy, term]
private theorem grid_packet {n h D d : ℕ} (p : RankPlacement n) (T : ℕ) :
    (∑ a ∈ (lowGrid h D).filter (fun a => den h a = d),
      energy 0 (fun i : Fin n => (slotError p T i : ℂ)) (a, h)) ≤
    ∑ u ∈ packSet d, ‖amplitude p T ((negGridRoot d) ^ u)‖ ^ 2 := by
  let S := (lowGrid h D).filter (fun a => den h a = d)
  let f (u : ℕ) := ‖amplitude p T ((negGridRoot d) ^ u)‖ ^ 2
  have subs : S.image (num h) ⊆ packSet d := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hu
    obtain ⟨hl, he⟩ := mem_filter.mp ha
    exact he ▸ (rep_facts hl).2.2.2
  have inj (a : ℕ) (ha : a ∈ S) (b : ℕ) (hb : b ∈ S) (eq : num h a = num h b) : a = b := by
    obtain ⟨hal, ad⟩ := mem_filter.mp ha
    obtain ⟨_, bd⟩ := mem_filter.mp hb
    have aa : d * h.gcd a = h := ad ▸ Nat.div_mul_cancel (Nat.gcd_dvd_left h a)
    have bb : d * h.gcd b = h := bd ▸ Nat.div_mul_cancel (Nat.gcd_dvd_left h b)
    have same := Nat.eq_of_mul_eq_mul_left (show 0 < d by have := (rep_facts hal).1; omega)
      (aa.trans bb.symm)
    calc
      a = num h a * h.gcd a := (Nat.div_mul_cancel (Nat.gcd_dvd_right ..)).symm
      _ = num h b * h.gcd b := by rw [eq, same]
      _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  calc
    _ = ∑ a ∈ S, f (num h a) := sum_congr rfl (fun a ha => by
      obtain ⟨hl, he⟩ := mem_filter.mp ha
      simpa only [f, ←he] using reduced_energy p T hl)
    _ = ∑ u ∈ S.image (num h), f u := (sum_image (fun a ha b hb eq => inj a ha b hb eq)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg subs (fun _ _ _ => sq_nonneg _)

private theorem menu_mult {d B : ℕ} (hd : 0 < d) (G : Finset ℕ)
    (bound : ∀ h ∈ G, h ≤ B) :
    (G.filter (fun h => 0 < h ∧ d ∣ h)).card ≤ B / d := by
  rw [←card_range (B / d)]
  apply card_le_card_of_injOn (fun h => h / d - 1)
  · intro h hh
    obtain ⟨hh, hp, hdiv⟩ := mem_filter.mp hh
    have pos := Nat.div_pos (Nat.le_of_dvd hp hdiv) hd
    have up := Nat.div_le_div_right (bound h hh) (c := d)
    apply mem_range.mpr
    change h / d - 1 < B / d
    omega
  · intro h hh k hk e
    obtain ⟨_, hp, dh⟩ := mem_filter.mp hh
    obtain ⟨_, kp, dk⟩ := mem_filter.mp hk
    have hq := Nat.div_pos (Nat.le_of_dvd hp dh) hd
    have kq := Nat.div_pos (Nat.le_of_dvd kp dk) hd
    have eq : h / d = k / d := by dsimp at e; omega
    calc
      h = (h / d) * d := (Nat.div_mul_cancel dh).symm
      _ = k := by rw [eq, Nat.div_mul_cancel dk]

/-- Sum over original grid tags, regrouping by denominator d. A full packet
is paid at most floor(B/d) times. -/
theorem linear_low_menu {n c g₁ g₂ D B : ℕ}
    (p : RankPlacement n) (T : ℕ) (hT : T ≤ n) (hg : 0 < g₂) (hle : g₂ ≤ g₁)
    (G : Finset ℕ) (menu : ∀ h ∈ G, h ∈ window c (Nat.gcd g₁ g₂))
    (bound : ∀ h ∈ G, h ≤ B) :
    (∑ h ∈ G, ∑ a ∈ lowGrid h D, energy 0 (fun i : Fin n =>
      (slotError (gapSort (gapSort p g₁) g₂) T i : ℂ)) (a, h)) ≤
      ((B : ℝ) * g₁ * D) * ∑ i, |(slotError p T i : ℝ)| := by
  let z := gapSort (gapSort p g₁) g₂
  let E (h a : ℕ) := energy 0 (fun i : Fin n => (slotError z T i : ℂ)) (a, h)
  let s := ∑ i, |(slotError p T i : ℝ)|
  have ps : 0 ≤ s := by dsimp [s]; positivity
  let V (h d : ℕ) := ∑ a ∈ (lowGrid h D).filter (fun a => den h a = d), E h a
  have split (h : ℕ) : (∑ a ∈ lowGrid h D, E h a) = ∑ d ∈ Ioc 0 D, V h d :=
    (sum_fiberwise_of_maps_to (g := den h) (t := Ioc 0 D) (s := lowGrid h D)
      (fun a ha => mem_Ioc.mpr ⟨by have := (rep_facts ha).1; omega, (rep_facts ha).2.1⟩) (E h)).symm
  have packet (h : ℕ) (hh : h ∈ G) (d : ℕ) :
      V h d ≤ if 0 < h ∧ d ∣ h then (g₁ : ℝ) * d * s else 0 := by
    by_cases he : ((lowGrid h D).filter (fun a => den h a = d)).Nonempty
    · obtain ⟨a, ha⟩ := he
      obtain ⟨hl, eq⟩ := mem_filter.mp ha
      obtain ⟨gt, _, dvdh, _⟩ := rep_facts hl
      rw [eq] at gt dvdh
      have pos : 0 < h := by have := mem_range.mp (mem_filter.mp hl).1; omega
      simp only [show 0 < h ∧ d ∣ h from ⟨pos, dvdh⟩]
      exact (grid_packet (h := h) (D := D) (d := d) z T).trans
        (primitive_after_retained p T hT hg hle (by omega) (retained_breaks_divisor (menu h hh)
          dvdh gt))
    · simp only [V, not_nonempty_iff_eq_empty.mp he, sum_empty]
      split <;> positivity
  have one (d : ℕ) (hd : d ∈ Ioc 0 D) : (∑ h ∈ G, V h d) ≤ (B : ℝ) * g₁ * s := by
    apply (sum_le_sum (fun h hh => packet h hh d)).trans
    rw [←sum_filter, sum_const, nsmul_eq_mul]
    have c := menu_mult (mem_Ioc.mp hd).1 G bound
    have budget := (Nat.mul_le_mul_right d c).trans (Nat.div_mul_le_self B d)
    have cr : (((G.filter (fun h => 0 < h ∧ d ∣ h)).card : ℝ) * d) ≤ B := by exact_mod_cast budget
    calc
      _ = (((G.filter (fun h => 0 < h ∧ d ∣ h)).card : ℝ) * d) * (g₁ * s) := by ring
      _ ≤ (B : ℝ) * (g₁ * s) := mul_le_mul_of_nonneg_right cr (by positivity)
      _ = _ := by ring
  change (∑ h ∈ G, ∑ a ∈ lowGrid h D, E h a) ≤ ((B : ℝ) * g₁ * D) * s
  simp_rw [split]
  rw [sum_comm]
  apply (sum_le_sum (fun d hd => one d hd)).trans
  simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- The physical two-pass state, actual window, and actual uniform mean. -/
theorem actual_low_linear_mean {n D : ℕ} (p : RankPlacement n) (T : ℕ) (hT : T ≤ n)
    (j : ℕ) (hc : 9400 ≤ gap j) :
    let c := gap j
    let g₁ := gap (j + 2)
    let g₂ := gap (j + 1)
    let G := window c (Nat.gcd g₁ g₂)
    (∑ h ∈ G, ∑ a ∈ lowGrid h D, energy 0 (fun i : Fin n =>
      (slotError (gapSort (gapSort p g₁) g₂) T i : ℂ)) (a, h)) / (G.card : ℝ) ≤
        (2 * 18800 * (g₁ : ℝ) * D) * ∑ i, |(slotError p T i : ℝ)| := by
  intro c g₁ g₂ G
  have hp : (c : ℝ) ≠ 0 := by exact_mod_cast (gap_pos j).ne'
  have hle : g₂ ≤ g₁ := by
    change gap (j + 1) ≤ nextGap (gap (j + 1))
    have := (scaled_next_bounds (gap (j + 1))).1
    omega
  have elems : ∀ h ∈ G, h ≤ 2 * c := by
    intro h hh
    have hi := (mem_Icc.mp (mem_filter.mp hh).1).2
    omega
  have bound := linear_low_menu (c := c) (D := D) p T hT (gap_pos (j + 1)) hle G (fun _ hh => hh)
    elems
  have atom : (1 : ℝ) / G.card ≤ 18800 / (c : ℝ) := actual_atom_le j hc
  have one := mul_le_mul_of_nonneg_left bound (show 0 ≤ (1 : ℝ) / G.card by positivity)
  have two := mul_le_mul_of_nonneg_right atom
    (show (0 : ℝ) ≤ (↑(2 * c) * (g₁ : ℝ) * D) * (∑ i, |(slotError p T i : ℝ)|) by positivity)
  rw [div_eq_inv_mul]
  simpa only [one_div] using (one.trans two).trans_eq (by push_cast; field_simp)

theorem linear_budget :
    let D : ℕ := 2 ^ 79
    let J : ℕ := 2 ^ 15
    let A : ℕ := 2 ^ 115
    let B : ℕ := 2 ^ 16
    18 * 18800 * D + J * 2 ^ 15 < 2 ^ 98 ∧
    A * A * B * B + 2 ^ (47 + 97 + 1) * A * B ≤ 2 ^ 47 * A * A ∧
    4 * A * B * 2 ^ 12 ≤ 2 ^ 145 ∧ 4 * A * 2 ^ 49 ≤ 2 ^ 166 ∧
    (1 + 2 ^ 145) + 33 * (1 + 2 ^ 166) < (2 : ℕ) ^ 172 := by decide



end Shellsort.Actual214
