/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.NoDrop
public import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Finite-prefix approximation of Borel events

Every Borel event in Cantor space can be approximated in fair-coin measure by
a Boolean table on a fixed finite prefix.  The depth and the table are chosen
once, independently of any later affine block.
-/

@[expose] public section

namespace Klr.PoolApproximation

open MeasureTheory
open scoped ENNReal symmDiff

/-- The first `d` bits, viewed as a member of a finite type. -/
def bits (d : ℕ) (X : Cantor) : Fin d → Bool := fun i => X i.val

/-- Evaluate a finite table on an input sequence. -/
def eval {E : Type*} {d : ℕ} (table : (Fin d → Bool) → E) (X : Cantor) : E :=
  table (bits d X)

/-- A finite Boolean table describes a finite union of prefix cylinders. -/
def event {d : ℕ} (table : (Fin d → Bool) → Bool) : Set Cantor :=
  {X | eval table X = true}

/-- Read a shallower table from a longer prefix. -/
def liftTable {E : Type*} {d e : ℕ} (h : d ≤ e)
    (table : (Fin d → Bool) → E) : (Fin e → Bool) → E :=
  fun u => table (fun i => u (Fin.castLE h i))

@[simp] theorem eval_liftTable {E : Type*} {d e : ℕ} (h : d ≤ e)
    (table : (Fin d → Bool) → E) (X : Cantor) :
    eval (liftTable h table) X = eval table X := rfl

@[simp] theorem event_liftTable {d e : ℕ} (h : d ≤ e)
    (table : (Fin d → Bool) → Bool) : event (liftTable h table) = event table := rfl

theorem measurable_prefix (d : ℕ) : Measurable (bits d) :=
  Measurable.of_eval fun i => measurable_pi_apply i.val

theorem measurable_eval {E : Type*} [MeasurableSpace E] {d : ℕ}
    (table : (Fin d → Bool) → E) : Measurable (eval table) :=
  (measurable_of_finite table).comp (measurable_prefix d)

theorem measurableSet_event {d : ℕ} (table : (Fin d → Bool) → Bool) :
    MeasurableSet (event table) :=
  (measurable_eval table) (measurableSet_singleton true)

/-- The algebra of events determined by a finite initial segment. -/
def prefixEvents : Set (Set Cantor) :=
  {s | ∃ (d : ℕ) (table : (Fin d → Bool) → Bool), s = event table}

theorem empty_mem_prefixEvents : ∅ ∈ prefixEvents := by
  refine ⟨0, fun _ => false, ?_⟩
  ext X
  simp [event, eval]

theorem univ_mem_prefixEvents : Set.univ ∈ prefixEvents := by
  refine ⟨0, fun _ => true, ?_⟩
  ext X
  simp [event, eval]

theorem isSetRing_prefixEvents : IsSetRing prefixEvents where
  empty_mem := empty_mem_prefixEvents
  union_mem := by
    rintro s t ⟨d, a, rfl⟩ ⟨e, b, rfl⟩
    refine ⟨max d e, fun u =>
      liftTable (Nat.le_max_left d e) a u || liftTable (Nat.le_max_right d e) b u, ?_⟩
    ext X
    change (a (bits d X) = true ∨ b (bits e X) = true) ↔
      (a (bits d X) || b (bits e X)) = true
    simp
  sdiff_mem := by
    rintro s t ⟨d, a, rfl⟩ ⟨e, b, rfl⟩
    refine ⟨max d e, fun u =>
      liftTable (Nat.le_max_left d e) a u && !(liftTable (Nat.le_max_right d e) b u), ?_⟩
    ext X
    change (a (bits d X) = true ∧ ¬ b (bits e X) = true) ↔
      (a (bits d X) && !(b (bits e X))) = true
    simp

theorem cylinder_mem_prefixEvents (s : List Bool) : cylinder s ∈ prefixEvents := by
  classical
  refine ⟨s.length, fun u => decide (∀ i : Fin s.length, u i = s.getD i.val false), ?_⟩
  ext X
  change (∀ i < s.length, X i = s.getD i false) ↔
    decide (∀ i : Fin s.length, X i.val = s.getD i.val false) = true
  exact ⟨fun h => decide_eq_true (fun i => h i.val i.isLt),
    fun h i hi => of_decide_eq_true h ⟨i, hi⟩⟩

theorem measurableSpace_eq_generateFrom_prefixEvents :
    (inferInstance : MeasurableSpace Cantor) =
      MeasurableSpace.generateFrom prefixEvents := by
  apply le_antisymm
  · rw [measurableSpace_eq_generateFrom_cylinders]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨s, rfl⟩
    exact cylinder_mem_prefixEvents s
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨d, table, rfl⟩
    exact measurableSet_event table

/-- A Borel event admits a finite Boolean prefix approximation with any positive error. -/
theorem exists_event_symmDiff_lt {H : Set Cantor} (hH : MeasurableSet H)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (d : ℕ) (table : (Fin d → Bool) → Bool), fairCoin (event table ∆ H) < ε := by
  have hcover : ∃ D : Set (Set Cantor),
      D.Countable ∧ D ⊆ prefixEvents ∧ fairCoin (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · simpa using univ_mem_prefixEvents
    · simp
  obtain ⟨s, ⟨d, table, rfl⟩, hs⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing isSetRing_prefixEvents hcover
      measurableSpace_eq_generateFrom_prefixEvents hH hε
  exact ⟨d, table, hs⟩

/-- The same approximation with a real-valued error bound. -/
theorem exists_event_measureReal_symmDiff_lt {H : Set Cantor} (hH : MeasurableSet H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (table : (Fin d → Bool) → Bool), fairCoin.real (event table ∆ H) < ε := by
  obtain ⟨d, table, ht⟩ := exists_event_symmDiff_lt hH (ENNReal.ofReal_pos.mpr hε)
  refine ⟨d, table, ?_⟩
  exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr ht |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

end Klr.PoolApproximation
