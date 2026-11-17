/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Inverting a monotone convex function

Deterministic one-dimensional sublevel geometry for the reverse Gaussian-law
characterization. Only finite continuous functions occur. No stochastic inequality
is used here.
-/

@[expose] public section

open Set
open scoped Topology

namespace EhrhardGaussian.EhrhardType

/-- A nonconstant monotone function has a strictly increasing pair. -/
theorem exists_increasing_pair {h : ℝ → ℝ} (hh : Monotone h)
    (hn : ¬ ∀ x, h x = h 0) : ∃ x y, x < y ∧ h x < h y := by
  push Not at hn
  obtain ⟨x, hx⟩ := hn
  rcases lt_trichotomy x 0 with hx0 | rfl | h0x
  · exact ⟨x, 0, hx0, lt_of_le_of_ne (hh hx0.le) hx⟩
  · exact (hx rfl).elim
  · exact ⟨0, x, h0x, lt_of_le_of_ne (hh h0x.le) hx.symm⟩

/-- A nonconstant monotone convex function is unbounded above. -/
theorem exists_lt_monotone_convex {h : ℝ → ℝ} (hh : Monotone h)
    (hc : ConvexOn ℝ univ h) (hn : ¬ ∀ x, h x = h 0) (M : ℝ) :
    ∃ z, M < h z := by
  obtain ⟨x, y, hxy, hhxy⟩ := exists_increasing_pair hh hn
  let m := (h y - h x) / (y - x)
  have hm : 0 < m := div_pos (sub_pos.mpr hhxy) (sub_pos.mpr hxy)
  let z := max (y + 1) (x + (M - h x + 1) / m)
  have hyz : y < z := lt_of_lt_of_le (by linarith : y < y + 1) (le_max_left _ _)
  have hxz : 0 < z - x := sub_pos.mpr (hxy.trans hyz)
  have hs : m ≤ (h z - h x) / (z - x) :=
    hc.secant_mono_aux2 (mem_univ _) (mem_univ _) hxy hyz
  have hs' := (le_div_iff₀ hxz).mp hs
  have hz : (M - h x + 1) / m ≤ z - x := by
    have := le_max_right (y + 1) (x + (M - h x + 1) / m)
    change x + (M - h x + 1) / m ≤ z at this
    linarith only [this]
  have hmul := (div_le_iff₀ hm).mp hz
  exact ⟨z, by nlinarith only [hs', hmul]⟩

/-- A nonempty open lower sublevel of a continuous monotone function is a strict half-line. -/
theorem sublevel_eq_Iio_sSup {h : ℝ → ℝ} (hh : Monotone h) (hc : Continuous h)
    {t : ℝ} (hne : {x | h x < t}.Nonempty) (hbound : ∃ z, t < h z) :
    {x | h x < t} = Iio (sSup {x | h x < t}) := by
  obtain ⟨z, hz⟩ := hbound
  have hbd : BddAbove {x | h x < t} := by
    refine ⟨z, ?_⟩
    intro x hx
    by_contra hnot
    exact (hz.trans_le (hh (le_of_not_ge hnot))).not_ge hx.le
  ext x
  constructor
  · intro hx
    have hopen : IsOpen {x | h x < t} := isOpen_lt hc continuous_const
    obtain ⟨l, u, hxu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hx)
    obtain ⟨y, hxy, hyu⟩ := exists_between hxu.2
    have hy : y ∈ {x | h x < t} := hsub ⟨hxu.1.trans hxy, hyu⟩
    exact hxy.trans_le (le_csSup hbd hy)
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (lt_csSup_iff hbd hne).mp hx
    exact (hh hxy.le).trans_lt hy

/-- Concavity of the finite sublevel cutoff on its nonempty-sublevel domain. -/
theorem concaveOn_sublevelSup {h : ℝ → ℝ} (hh : Monotone h)
    (hc : ConvexOn ℝ univ h) (hn : ¬ ∀ x, h x = h 0) :
    ConcaveOn ℝ {t | ∃ x, h x < t} (fun t => sSup {x | h x < t}) := by
  have hcont : Continuous h := continuousOn_univ.mp (hc.continuousOn isOpen_univ)
  have hsub : ∀ t, (∃ x, h x < t) → {x | h x < t} = Iio (sSup {x | h x < t}) :=
    fun t ht => sublevel_eq_Iio_sSup hh hcont ht (exists_lt_monotone_convex hh hc hn t)
  have hdom : Convex ℝ {t | ∃ x, h x < t} := by
    apply convex_iff_ordConnected.mpr
    constructor
    intro a ha b _ t ht
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, hx.trans_le ht.1⟩
  refine ⟨hdom, ?_⟩
  intro s hs t ht a b ha hb hab
  change a * sSup {x | h x < s} + b * sSup {x | h x < t} ≤
    sSup {x | h x < a * s + b * t}
  apply le_of_forall_pos_le_add
  intro ε hε
  let u := sSup {x | h x < s} - ε
  let v := sSup {x | h x < t} - ε
  have hu : h u < s := by
    have hu : u ∈ Iio (sSup {x | h x < s}) := by dsimp [u]; exact sub_lt_self _ hε
    rw [← hsub s hs] at hu
    exact hu
  have hv : h v < t := by
    have hv : v ∈ Iio (sSup {x | h x < t}) := by dsimp [v]; exact sub_lt_self _ hε
    rw [← hsub t ht] at hv
    exact hv
  have hstrict : a * h u + b * h v < a * s + b * t := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith only [hab, ha0]
      simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hv
    · exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hu (lt_of_le_of_ne ha (Ne.symm ha0)))
        (mul_le_mul_of_nonneg_left hv.le hb)
  have hmem : h (a * u + b * v) < a * s + b * t :=
    (hc.2 (mem_univ u) (mem_univ v) ha hb hab).trans_lt hstrict
  have hlt : a * u + b * v < sSup {x | h x < a * s + b * t} := by
    have hset := hsub (a * s + b * t) (hdom hs ht ha hb hab)
    change a * u + b * v ∈ Iio (sSup {x | h x < a * s + b * t})
    rw [← hset]
    exact hmem
  dsimp [u, v] at hlt
  have heq : a * (sSup {x | h x < s} - ε) + b * (sSup {x | h x < t} - ε) =
      a * sSup {x | h x < s} + b * sSup {x | h x < t} - ε := by
    calc
      _ = a * sSup {x | h x < s} + b * sSup {x | h x < t} - (a + b) * ε := by ring
      _ = _ := by rw [hab, one_mul]
  rw [heq] at hlt
  linarith only [hlt]

end EhrhardGaussian.EhrhardType
