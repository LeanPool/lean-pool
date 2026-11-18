/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/RecoverySetup.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.Endpoints

/-!
# Recovery Setup
-/


@[expose] public section

namespace OAI

open Set Filter Topology
namespace TuringRigidity

/-- Local separation and oracle-program data used to recover a real from the branch
construction. -/
structure RecoveryData (F : ℝ → Oracle) (t u v : ℝ) where
  /-- The positive radius bounding the rational-span displacements allowed in the local
  program equations. -/
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  /-- The negative lower endpoint of the recovery interval. -/
  lo : ℝ
  /-- The positive upper endpoint of the recovery interval. -/
  hi : ℝ
  lo_gt : -radius < lo
  lo_neg : lo < 0
  hi_pos : 0 < hi
  hi_lt : hi < radius
  /-- The positive rational step size, smaller than the radius and the endpoint gap. -/
  delta : ℚ
  delta_pos : 0 < delta
  delta_lt : (delta : ℝ) < radius
  delta_gap : 3*(delta : ℝ) < hi-lo
  /-- The bit index separating the two endpoint regions. -/
  bit : ℕ
  /-- The index of the forward oracle program in the local addition computation. -/
  forward : ℕ
  /-- The index of the backward oracle program recovering the shifted input. -/
  backward : ℕ
  left : ∀ s ∈ rationalSpan t, s ∈ Icc lo (lo+(delta : ℝ)) →
    F (u+s) bit ≠ F (u+hi) bit
  right : ∀ s ∈ rationalSpan t, s ∈ Icc (hi-(delta : ℝ)) hi →
    F (u+s) bit = F (u+hi) bit
  forward_correct : ∀ s ∈ rationalSpan t, ∀ a ∈ rationalSpan t,
    |s| < radius → |a| < radius →
      OracleCode.eval (oracleFunction (join (F (u+s)) (F (v-u+a))))
        (codeEnumeration forward) = oracleFunction (F (v+s+a))
  backward_correct : ∀ s ∈ rationalSpan t, |s| < radius →
    OracleCode.eval (oracleFunction (join (F (v+s)) (F (u-v))))
      (codeEnumeration backward) = oracleFunction (F (u+s))

theorem recovery_data_exists (F : ℝ → Oracle) (hF : Measurable F)
    (hfiber : ∀ B, {x | F x = B}.Countable)
    (hadd : ∀ x y, Reduces (F (x + y)) (join (F x) (F y))) (t : ℝ) :
    ∃ G : Set (ℝ × ℝ), G ∈ residual (ℝ × ℝ) ∧
      ∀ p ∈ G, Nonempty (RecoveryData F t p.1 p.2) := by
  obtain ⟨D,hD,hFD⟩ := measurable_continuousOn_residual F hF
  obtain ⟨e,E,hE,he,hspec⟩ := addition_program_continuous_restriction F hF hadd
  refine ⟨goodPairs t D E,goodPairs_residual t D E hD hE,?_⟩
  rintro ⟨u,v⟩ hgood
  obtain ⟨p,q,ρ,hρ,hρ1,hp,hq⟩ := fixed_local_programs F t u v D E e he hgood hspec
  obtain ⟨lo,hi,j,δ,hloρ,hlo,hhi,hhiρ,hδ,hδρ,hgap,hleft,hright⟩ :=
    exists_endpoint_bands F hfiber D hD hFD t u ρ hρ (fun s hs => (hgood s hs).1)
  exact ⟨{
    radius := ρ, radius_pos := hρ, radius_lt_one := hρ1,
    lo := lo, hi := hi, lo_gt := hloρ, lo_neg := hlo, hi_pos := hhi, hi_lt := hhiρ,
    delta := δ, delta_pos := hδ, delta_lt := hδρ, delta_gap := hgap,
    bit := j, forward := p, backward := q,
    left := hleft, right := hright, forward_correct := hp, backward_correct := hq }⟩

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

/-- Test whether the selected bit agrees with its value at the upper recovery endpoint. -/
def test (d : RecoveryData F t u v) (s : ℝ) : Bool :=
  decide (F (u+s) d.bit = F (u+d.hi) d.bit)

theorem bounded (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    state d.test (d.delta : ℝ) t n ∈ Icc d.lo d.hi := by
  apply state_mem_Icc_on_span d.test d.delta t d.lo d.hi
    (by exact_mod_cast d.delta_pos) ht0 ht1 d.lo_neg.le d.hi_pos.le
  · intro s hs hb
    simp [test, d.left s hs hb]
  · intro s hs hb
    simp [test, d.right s hs hb]

theorem abs_state_lt (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    |state d.test (d.delta : ℝ) t n| < d.radius := by
  obtain ⟨hl,hu⟩ := d.bounded ht0 ht1 n
  exact abs_lt.mpr ⟨d.lo_gt.trans_le hl, hu.trans_lt d.hi_lt⟩

theorem frequency_bound (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (n : ℕ) (hn : 0 < n) :
    |t - (∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k) / (n : ℝ)| <
      1 / ((n : ℝ) * (d.delta : ℝ)) := by
  exact frequency_error d.test (d.delta : ℝ) t n
    (by exact_mod_cast d.delta_pos) hn ((d.abs_state_lt ht0 ht1 n).trans d.radius_lt_one)

theorem cut_search (d : RecoveryData F t u v) (ht : Irrational t) (ht0 : 0 < t)
    (ht1 : t < 1) (q : ℚ) :
    (q : ℝ) < t ↔ ∃ n : ℕ, 0 < n ∧ (q : ℝ) <
      (∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k) / (n : ℝ) -
        1 / ((n : ℝ) * (d.delta : ℝ)) := by
  exact irrational_cut_iff_search t (d.delta : ℝ)
    (fun n => (∑ k ∈ Finset.range n, branch d.test (d.delta : ℝ) t k) / (n : ℝ))
    ht (by exact_mod_cast d.delta_pos) (fun n hn => d.frequency_bound ht0 ht1 n hn) q
end RecoveryData

end TuringRigidity

end OAI
