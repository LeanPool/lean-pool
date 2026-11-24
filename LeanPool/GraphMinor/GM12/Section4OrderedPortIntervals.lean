/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Ordered intervals for circle ports

The ports for XII (4.5), page 253, occur in blocks around the
vertices. Several ports may start from the same circle center.
A small positive perturbation, increasing with the port index,
puts them in strict order while retaining their assigned open
neighborhoods. Shrinking to small intervals then leaves room for
the general-position chord choices.
-/

public section

namespace GraphMinor.GM12

open Set Metric Topology

/-- Split ordered, possibly equal, center parameters into strictly
ordered port parameters in prescribed open neighborhoods. This
chooses the order within the vertex blocks in XII (4.5), page 253. -/
theorem exists_strictMono_ports_in_open {n : ℕ} (c : Fin n → ℝ)
    (hc : Monotone c) (U : Fin n → Set ℝ) (hU : ∀ i, IsOpen (U i))
    (hcU : ∀ i, c i ∈ U i) :
    ∃ p : Fin n → ℝ, StrictMono p ∧ ∀ i, p i ∈ U i := by
  let A : Set ℝ := ⋂ i, (fun r : ℝ => c i + r * ((i : ℝ) + 1)) ⁻¹' U i
  have hA : IsOpen A := isOpen_iInter_of_finite fun i => (hU i).preimage (by fun_prop)
  have hzero : (0 : ℝ) ∈ A := by simpa [A] using hcU
  obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.mp hA 0 hzero
  let ε := r / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεA : ε ∈ A := hrA (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp [ε]; linarith)
  refine ⟨fun i => c i + ε * ((i : ℝ) + 1), ?_, ?_⟩
  · intro i j hij
    apply add_lt_add_of_le_of_lt (hc hij.le)
    apply mul_lt_mul_of_pos_left _ hε
    have hval : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  · intro i
    exact mem_iInter.mp hεA i

/-- Thicken a finite strictly ordered family of port parameters
to disjoint ordered intervals inside the assigned open sets.
These intervals leave room for the chord perturbations in XII
(4.5), page 253. -/
theorem exists_ordered_intervals_in_open {n : ℕ} (p : Fin n → ℝ)
    (hp : StrictMono p) (U : Fin n → Set ℝ) (hU : ∀ i, IsOpen (U i))
    (hpU : ∀ i, p i ∈ U i) :
    ∃ u v : Fin n → ℝ,
      (∀ i, u i < p i ∧ p i < v i ∧ Ioo (u i) (v i) ⊆ U i) ∧
      ∀ i j, i < j → v i < u j := by
  classical
  have hrad : ∀ i, ∃ r : ℝ, 0 < r ∧ ball (p i) r ⊆ U i := by
    intro i
    exact Metric.isOpen_iff.mp (hU i) (p i) (hpU i)
  choose r hr hrU using hrad
  let A : Set ℝ := (⋂ i, Iio (r i)) ∩
    (⋂ i, ⋂ j, if i < j then Iio ((p j - p i) / 3) else univ)
  have hA : IsOpen A := by
    apply IsOpen.inter (isOpen_iInter_of_finite fun _ => isOpen_Iio)
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    split_ifs <;> first | exact isOpen_Iio | exact isOpen_univ
  have hzero : (0 : ℝ) ∈ A := by
    refine ⟨mem_iInter.mpr hr, mem_iInter.mpr fun i => mem_iInter.mpr fun j => ?_⟩
    split_ifs with hij
    · change 0 < (p j - p i) / 3
      have h := hp hij
      linarith
    · exact mem_univ _
  obtain ⟨s, hs, hsA⟩ := Metric.isOpen_iff.mp hA 0 hzero
  let ε := s / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεA : ε ∈ A := hsA (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp [ε]; linarith)
  refine ⟨fun i => p i - ε, fun i => p i + ε, ?_, ?_⟩
  · intro i
    refine ⟨by linarith, by linarith, ?_⟩
    intro x hx
    apply hrU i
    rw [mem_ball, Real.dist_eq, abs_lt]
    have hεr : ε < r i := mem_iInter.mp hεA.1 i
    constructor <;> linarith [hx.1, hx.2]
  · intro i j hij
    have hsmall : ε < (p j - p i) / 3 := by
      have h := mem_iInter.mp (mem_iInter.mp hεA.2 i) j
      simpa [hij] using h
    linarith

/-- Choose strictly ordered, nonempty intervals for all ports,
allowing their assigned centers to coincide within vertex blocks.
This is the interval choice for XII (4.5), page 253. -/
theorem exists_ordered_port_intervals {n : ℕ} (c : Fin n → ℝ)
    (hc : Monotone c) (U : Fin n → Set ℝ) (hU : ∀ i, IsOpen (U i))
    (hcU : ∀ i, c i ∈ U i) :
    ∃ u v : Fin n → ℝ,
      (∀ i, u i < v i ∧ Ioo (u i) (v i) ⊆ U i) ∧
      ∀ i j, i < j → v i < u j := by
  obtain ⟨p, hp, hpU⟩ := exists_strictMono_ports_in_open c hc U hU hcU
  obtain ⟨u, v, huv, horder⟩ := exists_ordered_intervals_in_open p hp U hU hpU
  exact ⟨u, v, fun i => ⟨(huv i).1.trans (huv i).2.1, (huv i).2.2⟩, horder⟩

end GraphMinor.GM12
