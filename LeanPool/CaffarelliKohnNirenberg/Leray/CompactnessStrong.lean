/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Tactic.Positivity

/-!
# Compactness Strong

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter

namespace CKN.Leray

/-- If a sequence admits arbitrarily accurate uniform approximations by
sequences that are Cauchy, then it converges in a complete normed space. This
is the final Cauchy step for the finite ball-average approximations in
lem:compactness. -/
theorem exists_limit_of_cauchy_uniform_approximations
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (P : ℕ → ℕ → E)
    (hP : ∀ m, CauchySeq (fun n => P m n))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ m, ∀ n, dist (f n) (P m n) < ε) :
    ∃ g : E, Tendsto f atTop (nhds g) := by
  have hf : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := happrox (ε / 3) (by positivity)
    have hPm := Metric.cauchySeq_iff.mp (hP m)
    obtain ⟨N, hN⟩ := hPm (ε / 3) (by positivity)
    refine ⟨N, fun n hn p hp => ?_⟩
    have hright : dist (P m p) (f p) < ε / 3 := by
      simpa [dist_comm] using hm p
    calc
      dist (f n) (f p) ≤
          dist (f n) (P m n) +
            (dist (P m n) (P m p) + dist (P m p) (f p)) := by
        calc
          dist (f n) (f p) ≤ dist (f n) (P m n) + dist (P m n) (f p) :=
            dist_triangle _ _ _
          _ ≤ _ := by gcongr; exact dist_triangle _ _ _
      _ < ε / 3 + (ε / 3 + ε / 3) :=
        add_lt_add (hm n) (add_lt_add (hN n hn p hp) hright)
      _ = ε := by ring
  exact ⟨Filter.atTop.limUnder f, hf.tendsto_limUnder⟩

/-- If every requested accuracy admits a Cauchy approximating sequence, then
the original sequence is Cauchy. This is the radius-by-radius form used when
each finite ball cover has its own finite index type. -/
theorem cauchySeq_of_approximating_cauchy_sequences
    {E : Type*} [PseudoMetricSpace E]
    (f : ℕ → E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ → E,
      CauchySeq p ∧ ∀ n, dist (f n) (p n) < ε) :
    CauchySeq f := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨p, hp, happ⟩ := happrox (ε / 3) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hp) (ε / 3) (by positivity)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hright : dist (p m) (f m) < ε / 3 := by
    simpa [dist_comm] using happ m
  calc
    dist (f n) (f m) ≤ dist (f n) (p n) +
        (dist (p n) (p m) + dist (p m) (f m)) := by
      calc
        dist (f n) (f m) ≤ dist (f n) (p n) + dist (p n) (f m) := dist_triangle _ _ _
        _ ≤ _ := by gcongr; exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) :=
      add_lt_add (happ n) (add_lt_add (hN n hn m hm) hright)
    _ = ε := by ring

end CKN.Leray
