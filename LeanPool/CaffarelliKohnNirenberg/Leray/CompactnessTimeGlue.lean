/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessExhaustion
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessModulus
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessUniform
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Compactness Time Glue

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter Set Topology

namespace CKN.Leray

/-- The compact time interval indexed by a rational window. -/
abbrev RationalTimeSlice {I : Set ℝ} (p : RationalCompactTimeWindow I) :=
  {t : ℝ // t ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)}

/-- Weak limits selected on rational compact windows agree on overlaps and
give an every-time weak limit with continuous scalar pairings. -/
theorem exists_all_time_weak_limit_from_rational_windows
    {I : Set ℝ} (hI : IsOpen I)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → ℝ → E)
    (v : ∀ p : RationalCompactTimeWindow I, RationalTimeSlice p → E)
    (hweak : ∀ p t x, Tendsto (fun n => inner ℝ (f n t.1) x) atTop
      (nhds (inner ℝ (v p t) x)))
    (hcontinuous : ∀ p x, Continuous (fun t : RationalTimeSlice p => inner ℝ (v p t) x)) :
    ∃ V : I → E,
      (∀ t x, Tendsto (fun n => inner ℝ (f n t.1) x) atTop
        (nhds (inner ℝ (V t) x))) ∧
      ∀ x, Continuous (fun t => inner ℝ (V t) x) := by
  classical
  let pOf (t : I) : RationalCompactTimeWindow I :=
    Classical.choose (exists_rational_compact_time_window_around hI t.property)
  have hpOpen (t : I) :
      t.1 ∈ Ioo ((pOf t).1.1 : ℝ) ((pOf t).1.2 : ℝ) :=
    Classical.choose_spec (exists_rational_compact_time_window_around hI t.property)
  have hpClosed (t : I) :
      t.1 ∈ Icc ((pOf t).1.1 : ℝ) ((pOf t).1.2 : ℝ) :=
    ⟨(hpOpen t).1.le, (hpOpen t).2.le⟩
  let V : I → E := fun t => v (pOf t) ⟨t.1, hpClosed t⟩
  have hcompat (p q : RationalCompactTimeWindow I) (t : ℝ)
      (htp : t ∈ Icc (p.1.1 : ℝ) p.1.2)
      (htq : t ∈ Icc (q.1.1 : ℝ) q.1.2) :
      v p ⟨t, htp⟩ = v q ⟨t, htq⟩ := by
    apply ext_inner_right ℝ
    intro x
    exact tendsto_nhds_unique (hweak p ⟨t, htp⟩ x)
      (hweak q ⟨t, htq⟩ x)
  refine ⟨V, ?_, ?_⟩
  · intro t x
    exact hweak (pOf t) ⟨t.1, hpClosed t⟩ x
  · intro x
    rw [continuous_iff_continuousAt]
    intro t₀
    obtain ⟨p, htp⟩ := exists_rational_compact_time_window_around hI t₀.property
    let tp : RationalTimeSlice p := ⟨t₀.1, ⟨htp.1.le, htp.2.le⟩⟩
    have hlocal := (hcontinuous p x).continuousAt (x := tp)
    rw [Metric.continuousAt_iff] at hlocal ⊢
    intro ε hε
    obtain ⟨δ₂, hδ₂, hδ₂bound⟩ := hlocal ε hε
    let δ₁ : ℝ := min (t₀.1 - (p.1.1 : ℝ)) ((p.1.2 : ℝ) - t₀.1)
    have hδ₁ : 0 < δ₁ := by
      dsimp [δ₁]
      exact lt_min (sub_pos.mpr htp.1) (sub_pos.mpr htp.2)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
    have htReal : dist t.1 t₀.1 < δ₁ :=
      lt_of_lt_of_le ht (min_le_left _ _)
    have htAbs : |t.1 - t₀.1| < δ₁ := by
      simpa [Real.dist_eq] using htReal
    have htIn : t.1 ∈ Icc (p.1.1 : ℝ) p.1.2 := by
      obtain ⟨hleft, hright⟩ := abs_lt.mp htAbs
      constructor <;> dsimp [δ₁] at hleft hright ⊢ <;>
        have hminLeft := min_le_left (t₀.1 - (p.1.1 : ℝ)) ((p.1.2 : ℝ) - t₀.1) <;>
        have hminRight := min_le_right (t₀.1 - (p.1.1 : ℝ)) ((p.1.2 : ℝ) - t₀.1) <;>
        linarith only [hleft, hright, hminLeft, hminRight]
    have hVt : V t = v p ⟨t.1, htIn⟩ :=
      hcompat (pOf t) p t.1 (hpClosed t) htIn
    have hVt₀ : V t₀ = v p tp :=
      hcompat (pOf t₀) p t₀.1 (hpClosed t₀) tp.property
    have htSubtype : dist (⟨t.1, htIn⟩ : RationalTimeSlice p) tp < δ₂ := by
      change dist t.1 t₀.1 < δ₂
      exact lt_of_lt_of_le ht (min_le_right _ _)
    simpa only [hVt, hVt₀] using hδ₂bound htSubtype

/-- A single subsequence works for countably many Hilbert-valued slice
families on all times of an open interval. -/
theorem exists_common_subsequence_all_time_weak_limit
    {I : Set ℝ} (hI : IsOpen I)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E]
    (f : ℕ → ℕ → ℝ → E) (ψ : ℕ → E) (hψ : DenseRange ψ)
    (C : ℕ → RationalCompactTimeWindow I → ℝ)
    (hC : ∀ j p, 0 ≤ C j p)
    (hbound : ∀ n j p t, t ∈ Icc (p.1.1 : ℝ) p.1.2 →
      ‖f n j t‖ ≤ C j p)
    (hmod : ∀ j (p : RationalCompactTimeWindow I) m,
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n (s t : RationalTimeSlice p),
          |inner ℝ (f n j t.1) (ψ m) -
            inner ℝ (f n j s.1) (ψ m)| ≤
              A * dist t s + B * (dist t s) ^ θ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ V : ℕ → I → E,
      (∀ j t x, Tendsto (fun n => inner ℝ (f (σ n) j t.1) x) atTop
        (nhds (inner ℝ (V j t) x))) ∧
      (∀ j x, Continuous (fun t => inner ℝ (V j t) x)) ∧
      ∀ j (p : RationalCompactTimeWindow I) x ε, 0 < ε →
        ∀ᶠ n in atTop, ∀ t : RationalTimeSlice p,
          dist (inner ℝ (f (σ n) j t.1) x)
            (inner ℝ (V j ⟨t.1, p.property.2 t.property⟩) x) < ε := by
  classical
  let ι := ℕ × RationalCompactTimeWindow I
  let T : ι → Type := fun i => RationalTimeSlice i.2
  let E' : ι → Type _ := fun _ => E
  let : Countable ι := inferInstance
  let : ∀ i : ι, PseudoMetricSpace (T i) := fun _ => inferInstance
  let : ∀ i : ι, CompactSpace (T i) := fun i => by
    dsimp [T]
    exact isCompact_iff_compactSpace.mp isCompact_Icc
  let : ∀ i : ι, CompactlyCoherentSpace (T i) := fun _ => inferInstance
  let : ∀ i : ι, NormedAddCommGroup (E' i) := fun _ => inferInstance
  let : ∀ i : ι, InnerProductSpace ℝ (E' i) := fun _ => inferInstance
  let : ∀ i : ι, CompleteSpace (E' i) := fun _ => inferInstance
  let u : ℕ → ∀ i : ι, T i → E' i := fun n i t => f n i.1 t.1
  let ψ' : ∀ i : ι, ℕ → E' i := fun _ => ψ
  let C' : ι → ℝ := fun i => C i.1 i.2
  have huBound : ∀ n i t, ‖u n i t‖ ≤ C' i := by
    intro n i t
    exact hbound n i.1 i.2 t.1 t.property
  have hmod' : ∀ i m, ∃ A B θ : ℝ,
      0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, |inner ℝ (u n i t) (ψ' i m) -
        inner ℝ (u n i s) (ψ' i m)| ≤
          A * dist t s + B * (dist t s) ^ θ := by
    intro i m
    simpa only [u, ψ', T] using hmod i.1 i.2 m
  obtain ⟨F, hF, σ, hσ, v, hv, hcontinuous, hvbound, L, hL, hLconv⟩ :=
    exists_common_subsequence_weak_pairings_of_two_term_moduli
      T E' u ψ' (fun _ => hψ) C' (fun i => hC i.1 i.2) huBound hmod'
  let V : ℕ → I → E := fun j =>
    Classical.choose (exists_all_time_weak_limit_from_rational_windows
      hI (fun n t => f (σ n) j t) (fun p t => v (j,p) t)
      (fun p t x => hv (j,p) t x)
      (fun p x => hcontinuous (j,p) x))
  have hVspec (j : ℕ) :=
    Classical.choose_spec (exists_all_time_weak_limit_from_rational_windows
      hI (fun n t => f (σ n) j t) (fun p t => v (j,p) t)
      (fun p t x => hv (j,p) t x)
      (fun p x => hcontinuous (j,p) x))
  refine ⟨σ, hσ, V, (fun j t x => (hVspec j).1 t x),
    (fun j x => (hVspec j).2 x), ?_⟩
  intro j p x ε hε
  let i : ι := (j,p)
  have hUniform := eventually_uniform_pairing_convergence_of_dense_tests
    (fun n t => u (σ n) i t) (v i) (ψ' i) (hψ)
    (C' i) (hC j p) (fun n t => huBound (σ n) i t)
    (hvbound i) (fun n m => F (σ n) i m) (L i)
    (fun n m t => hF (σ n) i m t) (hL i) (hLconv i)
    x ε hε
  filter_upwards [hUniform] with n hn t
  have hEq : V j ⟨t.1, p.property.2 t.property⟩ = v i t := by
    apply ext_inner_right ℝ
    intro y
    exact tendsto_nhds_unique
      ((hVspec j).1 ⟨t.1, p.property.2 t.property⟩ y)
      (hv i t y)
  simpa only [u, i, hEq] using hn t

/-- Uniform convergence on rational compact windows extends to every
compact time set inside the open domain. -/
theorem eventually_uniform_on_compact_of_rational_windows
    {I J : Set ℝ} (hI : IsOpen I) (hJ : IsCompact J) (hJI : J ⊆ I)
    (a : ℕ → I → ℝ) (b : I → ℝ)
    (hwindow : ∀ p : RationalCompactTimeWindow I, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t : RationalTimeSlice p,
        dist (a n ⟨t.1, p.property.2 t.property⟩)
          (b ⟨t.1, p.property.2 t.property⟩) < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t, (ht : t ∈ J) →
      dist (a n ⟨t, hJI ht⟩) (b ⟨t, hJI ht⟩) < ε := by
  classical
  intro ε hε
  have hcover : J ⊆ ⋃ p : RationalCompactTimeWindow I,
      Ioo (p.1.1 : ℝ) p.1.2 := by
    intro t ht
    obtain ⟨p, hp⟩ := exists_rational_compact_time_window_around hI (hJI ht)
    exact Set.mem_iUnion.mpr ⟨p, hp⟩
  obtain ⟨P, hP⟩ := hJ.elim_finite_subcover
    (fun p : RationalCompactTimeWindow I => Ioo (p.1.1 : ℝ) p.1.2)
    (fun _ => isOpen_Ioo) hcover
  have hAll : ∀ᶠ n in atTop, ∀ p ∈ P, ∀ t : RationalTimeSlice p,
      dist (a n ⟨t.1, p.property.2 t.property⟩)
        (b ⟨t.1, p.property.2 t.property⟩) < ε := by
    exact (eventually_all_finset P).2 (fun p hp => hwindow p ε hε)
  filter_upwards [hAll] with n hn t ht
  rcases Set.mem_iUnion₂.mp (hP ht) with ⟨p, hp, htp⟩
  let tp : RationalTimeSlice p := ⟨t, ⟨htp.1.le, htp.2.le⟩⟩
  simpa only [tp] using hn p hp tp

end CKN.Leray
