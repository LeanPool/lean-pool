/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Algebra.CharZero.Infinite

public import Mathlib.Analysis.Convex.Topology
public import LeanPool.ApollonianSuperharmonic.P3544T1BoundaryCarrier

-- [TABLET NODE: P3597T1GenericRayStability]

/-!
# P3597T1GenericRayStability

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private theorem genericRayDirection {n : Nat} (p : P3381T1PolygonBoundary n) :
    (∀ x : Real × Real, (∀ i, p.vertex i ≠ x) → ∃ d : Real × Real,
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) ∧
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0)) := by
  intro x hx
  let W : Fin (n + 3) × Bool → Real × Real := fun j =>
    if j.2 then p.vertex j.1 - x else p.vertex (j.1 + 1) - p.vertex j.1
  let S : Finset Real := Finset.univ.image fun j => (W j).2 / (W j).1
  have hcard : S.card < ENat.card Real := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.natCast_lt_top _
  obtain ⟨q, hq⟩ := Finset.exists_notMem_of_card_lt_enatCard hcard
  refine ⟨(1, q), ?_, ?_⟩
  · intro i
    let w := p.vertex i - x
    have hw : w ≠ 0 := sub_ne_zero.mpr (hx i)
    have hnot : q ≠ w.2 / w.1 := by
      intro he
      apply hq
      apply Finset.mem_image.mpr
      refine ⟨(i, true), Finset.mem_univ _, ?_⟩
      simp [W, w, he]
    intro hz
    have hz' : w.2 - q * w.1 = 0 := by simpa [w] using hz
    by_cases hzero : w.1 = 0
    · simp only [hzero, mul_zero, sub_zero] at hz'
      exact hw (Prod.ext hzero hz')
    · apply hnot
      apply (eq_div_iff hzero).2
      nlinarith [hz']
  · intro i
    let w := p.vertex (i + 1) - p.vertex i
    have hi : i + 1 ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_add, Fin.val_one] at hv
      have hm : 2 ≤ n + 3 := by omega
      by_cases hs : i.val + 1 < n + 3
      · rw [Nat.mod_eq_of_lt hs] at hv
        omega
      · have hi' : i.val + 1 = n + 3 := by omega
        rw [hi'] at hv
        simp at hv
        omega
    have hw : w ≠ 0 := by
      intro hz
      have hv : p.vertex (i + 1) = p.vertex i := sub_eq_zero.mp hz
      exact hi (p.injective hv)
    have hnot : q ≠ w.2 / w.1 := by
      intro he
      apply hq
      apply Finset.mem_image.mpr
      refine ⟨(i, false), Finset.mem_univ _, ?_⟩
      simp [W, w, he]
    intro hz
    have hz' : w.2 - q * w.1 = 0 := by simpa [w] using hz
    by_cases hzero : w.1 = 0
    · simp only [hzero, mul_zero, sub_zero] at hz'
      exact hw (Prod.ext hzero hz')
    · apply hnot
      apply (eq_div_iff hzero).2
      nlinarith [hz']

namespace RayCrossingStability

private noncomputable def det (v w : Real × Real) := v.1 * w.2 - v.2 * w.1

private theorem params : ∀ (y a d' e : Real × Real), det d' e ≠ 0 →
      y + (det (a - y) e / det d' e) • d' =
        a + (det (a - y) d' / det d' e) • e ∧
      (∀ t u : Real, y + t • d' = a + u • e →
        t = det (a - y) e / det d' e ∧ u = det (a - y) d' / det d' e) := by
  classical
  let det (v w : Real × Real) := v.1 * w.2 - v.2 * w.1
  change (∀ (y a d' e : Real × Real), det d' e ≠ 0 →
      y + (det (a - y) e / det d' e) • d' =
        a + (det (a - y) d' / det d' e) • e ∧
      (∀ t u : Real, y + t • d' = a + u • e →
        t = det (a - y) e / det d' e ∧ u = det (a - y) d' / det d' e))
  intro y a d' e hD
  constructor
  · have hDn : d'.1 * e.2 - d'.2 * e.1 ≠ 0 := by
      simpa only [det] using hD
    apply Prod.ext
    · change y.1 + (det (a - y) e / det d' e) * d'.1 =
        a.1 + (det (a - y) d' / det d' e) * e.1
      simp only [det, Prod.fst_sub, Prod.snd_sub]
      field_simp (disch := simpa only [mul_comm] using hDn)
      ring
    · change y.2 + (det (a - y) e / det d' e) * d'.2 =
        a.2 + (det (a - y) d' / det d' e) * e.2
      simp only [det, Prod.fst_sub, Prod.snd_sub]
      field_simp (disch := simpa only [mul_comm] using hDn)
      ring
  · intro t u h
    have h1 : y.1 + t * d'.1 = a.1 + u * e.1 := by
      simpa using congrArg Prod.fst h
    have h2 : y.2 + t * d'.2 = a.2 + u * e.2 := by
      simpa using congrArg Prod.snd h
    constructor
    · apply (eq_div_iff hD).2
      dsimp only [det, Prod.fst_sub, Prod.snd_sub]
      linear_combination e.2 * h1 - e.1 * h2
    · apply (eq_div_iff hD).2
      dsimp only [det, Prod.fst_sub, Prod.snd_sub]
      linear_combination d'.2 * h1 - d'.1 * h2

private theorem hitCriterion : ∀ (y a b d' : Real × Real), det d' (b - a) ≠ 0 →
      ((∃ t : Real, 0 < t ∧ y + t • d' ∈ segment Real a b) ↔
      0 < det (a - y) (b - a) / det d' (b - a) ∧
        0 ≤ det (a - y) d' / det d' (b - a) ∧
        det (a - y) d' / det d' (b - a) ≤ 1) := by
  classical
  let det (v w : Real × Real) := v.1 * w.2 - v.2 * w.1
  have params : ∀ (y a d' e : Real × Real), det d' e ≠ 0 →
      y + (det (a - y) e / det d' e) • d' =
        a + (det (a - y) d' / det d' e) • e ∧
      (∀ t u : Real, y + t • d' = a + u • e →
        t = det (a - y) e / det d' e ∧ u = det (a - y) d' / det d' e) := params
  change (∀ (y a b d' : Real × Real), det d' (b - a) ≠ 0 →
      ((∃ t : Real, 0 < t ∧ y + t • d' ∈ segment Real a b) ↔
      0 < det (a - y) (b - a) / det d' (b - a) ∧
        0 ≤ det (a - y) d' / det d' (b - a) ∧
        det (a - y) d' / det d' (b - a) ≤ 1))
  intro y a b d' hD
  obtain ⟨heq, huniq⟩ := params y a d' (b - a) hD
  constructor
  · rintro ⟨t, ht, hseg⟩
    rw [segment_eq_image'] at hseg
    obtain ⟨u, hu, he⟩ := hseg
    obtain ⟨hT, hU⟩ := huniq t u he.symm
    exact ⟨hT ▸ ht, hU ▸ hu.1, hU ▸ hu.2⟩
  · rintro ⟨ht, hu0, hu1⟩
    refine ⟨_, ht, ?_⟩
    rw [segment_eq_image']
    exact ⟨_, ⟨hu0, hu1⟩, heq.symm⟩

private theorem hsegCompact (n : Nat) (p : P3381T1PolygonBoundary n) : ∀ i : Fin (n + 3),
      IsCompact (segment Real (p.vertex i) (p.vertex (i + 1))) := by
  classical
  intro i
  have hfinite : ({p.vertex i, p.vertex (i + 1)} : Set (Real × Real)).Finite := by
    simp
  rw [← convexHull_pair]
  exact hfinite.isCompact_convexHull Real

private theorem hcarrierCompact (n : Nat) (p : P3381T1PolygonBoundary n) : IsCompact
    (P3544T1BoundaryCarrier p) := by
  classical
  have hsegCompact : ∀ i : Fin (n + 3),
      IsCompact (segment Real (p.vertex i) (p.vertex (i + 1))) := hsegCompact n p
  change IsCompact (⋃ i, segment Real (p.vertex i) (p.vertex (i + 1)))
  exact isCompact_iUnion hsegCompact

private theorem hcarrierOpen (n : Nat) (p : P3381T1PolygonBoundary n) : IsOpen
    (P3544T1BoundaryCarrier p)ᶜ := by
  classical
  have hcarrierCompact : IsCompact (P3544T1BoundaryCarrier p) := hcarrierCompact n p
  exact hcarrierCompact.isClosed.isOpen_compl

private noncomputable def T (n : Nat) (p : P3381T1PolygonBoundary n) (d : Real × Real) : Fin (n
    + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * ((p.vertex (i + 1)).2 - (p.vertex i).2) -
      ((p.vertex i).2 - y.2) * ((p.vertex (i + 1)).1 - (p.vertex i).1)) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹

private noncomputable def U (n : Nat) (p : P3381T1PolygonBoundary n) (d : Real × Real) : Fin (n
    + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * d.2 - ((p.vertex i).2 - y.2) * d.1) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹

private noncomputable def G (n : Nat) (p : P3381T1PolygonBoundary n) (d : Real × Real) : Fin (n
    + 3) → (Real × Real) → Real := fun i y =>
    d.1 * ((p.vertex i).2 - y.2) - d.2 * ((p.vertex i).1 - y.1)

private noncomputable def H (n : Nat) (p : P3381T1PolygonBoundary n) (d : Real × Real) : Fin (n
    + 3) → (Real × Real) → Prop := fun i y =>
    ∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))

private theorem hcriterion (n : Nat) (p : P3381T1PolygonBoundary n) (d : Real × Real) (hs : ∀
    i, d.1 * (p.vertex (i + 1) - p.vertex i).2 - d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0) : ∀
    i y, (H n p d) i y ↔
      0 < (T n p d) i y ∧ 0 ≤ (U n p d) i y ∧ (U n p d) i y ≤ 1 := by
  classical
  let det (v w : Real × Real) := v.1 * w.2 - v.2 * w.1
  have hitCriterion : ∀ (y a b d' : Real × Real), det d' (b - a) ≠ 0 →
      ((∃ t : Real, 0 < t ∧ y + t • d' ∈ segment Real a b) ↔
      0 < det (a - y) (b - a) / det d' (b - a) ∧
        0 ≤ det (a - y) d' / det d' (b - a) ∧
        det (a - y) d' / det d' (b - a) ≤ 1) := hitCriterion
  let T : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * ((p.vertex (i + 1)).2 - (p.vertex i).2) -
      ((p.vertex i).2 - y.2) * ((p.vertex (i + 1)).1 - (p.vertex i).1)) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹
  let U : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * d.2 - ((p.vertex i).2 - y.2) * d.1) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹
  let H : Fin (n + 3) → (Real × Real) → Prop := fun i y =>
    ∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))
  change (∀ i y, H i y ↔
      0 < T i y ∧ 0 ≤ U i y ∧ U i y ≤ 1)
  intro i y
  have hD : det d (p.vertex (i + 1) - p.vertex i) ≠ 0 := by
    simpa [det] using hs i
  have hh := hitCriterion y (p.vertex i) (p.vertex (i + 1)) d hD
  simpa [H, T, U, det, Prod.fst_sub, Prod.snd_sub, div_eq_mul_inv] using hh

private theorem hVi (n : Nat) (p : P3381T1PolygonBoundary n) (x : Real × Real) (d : Real ×
    Real) (hx : x ∉ P3544T1BoundaryCarrier p) (hg : ∀ i, d.1 * (p.vertex i - x).2 - d.2 *
    (p.vertex i - x).1 ≠ 0) (hs : ∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 - d.2 * (p.vertex
    (i + 1) - p.vertex i).1 ≠ 0) : ∀ i : Fin (n + 3), ∃ V : Set (Real × Real),
      IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V,
        (G n p d) i y ≠ 0 ∧ ((H n p d) i y ↔ (H n p d) i x) := by
  classical
  let det (v w : Real × Real) := v.1 * w.2 - v.2 * w.1
  have params : ∀ (y a d' e : Real × Real), det d' e ≠ 0 →
      y + (det (a - y) e / det d' e) • d' =
        a + (det (a - y) d' / det d' e) • e ∧
      (∀ t u : Real, y + t • d' = a + u • e →
        t = det (a - y) e / det d' e ∧ u = det (a - y) d' / det d' e) := params
  let T : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * ((p.vertex (i + 1)).2 - (p.vertex i).2) -
      ((p.vertex i).2 - y.2) * ((p.vertex (i + 1)).1 - (p.vertex i).1)) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹
  let U : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * d.2 - ((p.vertex i).2 - y.2) * d.1) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹
  let G : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    d.1 * ((p.vertex i).2 - y.2) - d.2 * ((p.vertex i).1 - y.1)
  let H : Fin (n + 3) → (Real × Real) → Prop := fun i y =>
    ∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))
  have hcriterion : ∀ i y, H i y ↔
      0 < T i y ∧ 0 ≤ U i y ∧ U i y ≤ 1 := hcriterion n p d hs
  change (∀ i : Fin (n + 3), ∃ V : Set (Real × Real),
      IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V,
        G i y ≠ 0 ∧ (H i y ↔ H i x))
  intro i
  have hD : det d (p.vertex (i + 1) - p.vertex i) ≠ 0 := by
    simpa [det] using hs i
  have hparams := params x (p.vertex i) d (p.vertex (i + 1) - p.vertex i) hD
  have hTform : T i x =
      det (p.vertex i - x) (p.vertex (i + 1) - p.vertex i) /
        det d (p.vertex (i + 1) - p.vertex i) := by
    simp [T, det, Prod.fst_sub, Prod.snd_sub, div_eq_mul_inv]
  have hUform : U i x =
      det (p.vertex i - x) d / det d (p.vertex (i + 1) - p.vertex i) := by
    simp [U, det, Prod.fst_sub, Prod.snd_sub, div_eq_mul_inv]
  have hparams' : x + T i x • d = p.vertex i + U i x •
      (p.vertex (i + 1) - p.vertex i) := by
    simpa only [hTform, hUform] using hparams.1
  have hU0 : U i x ≠ 0 := by
    intro hu
    have hpoint : x + T i x • d = p.vertex i := by
      simpa [hu] using hparams'
    have h1 : (p.vertex i - x).1 = T i x * d.1 := by
      have hh := congrArg Prod.fst hpoint
      dsimp [smul_eq_mul] at hh
      change (p.vertex i).1 - x.1 = T i x * d.1
      linarith
    have h2 : (p.vertex i - x).2 = T i x * d.2 := by
      have hh := congrArg Prod.snd hpoint
      dsimp [smul_eq_mul] at hh
      change (p.vertex i).2 - x.2 = T i x * d.2
      linarith
    have hz : d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 = 0 := by
      rw [h1, h2]
      ring
    exact (hg i) hz
  have hU1 : U i x ≠ 1 := by
    intro hu
    have hpoint : x + T i x • d = p.vertex (i + 1) := by
      calc
        x + T i x • d = p.vertex i + U i x •
            (p.vertex (i + 1) - p.vertex i) := hparams'
        _ = p.vertex (i + 1) := by simp [hu, sub_eq_add_neg, add_comm]
    have h1 : (p.vertex (i + 1) - x).1 = T i x * d.1 := by
      have hh := congrArg Prod.fst hpoint
      dsimp [smul_eq_mul] at hh
      change (p.vertex (i + 1)).1 - x.1 = T i x * d.1
      linarith
    have h2 : (p.vertex (i + 1) - x).2 = T i x * d.2 := by
      have hh := congrArg Prod.snd hpoint
      dsimp [smul_eq_mul] at hh
      change (p.vertex (i + 1)).2 - x.2 = T i x * d.2
      linarith
    have hz : d.1 * (p.vertex (i + 1) - x).2 -
        d.2 * (p.vertex (i + 1) - x).1 = 0 := by
      rw [h1, h2]
      ring
    exact (hg (i + 1)) hz
  have hT0 : 0 < U i x ∧ U i x < 1 → T i x ≠ 0 := by
    rintro ⟨hu0, hu1⟩ ht
    have hpoint : x = p.vertex i + U i x •
        (p.vertex (i + 1) - p.vertex i) := by
      have hh : x + T i x • d = p.vertex i + U i x •
          (p.vertex (i + 1) - p.vertex i) := hparams'
      simpa [ht] using hh
    have hxseg : x ∈ segment Real (p.vertex i) (p.vertex (i + 1)) := by
      rw [segment_eq_image']
      refine ⟨U i x, ⟨le_of_lt hu0, le_of_lt hu1⟩, ?_⟩
      exact hpoint.symm
    apply hx
    change x ∈ ⋃ j, segment Real (p.vertex j) (p.vertex (j + 1))
    exact Set.mem_iUnion.mpr ⟨i, hxseg⟩
  have hTcont : Continuous (T i) := by
    change Continuous (fun y : Real × Real =>
      (((p.vertex i).1 - y.1) * ((p.vertex (i + 1)).2 - (p.vertex i).2) -
        ((p.vertex i).2 - y.2) * ((p.vertex (i + 1)).1 - (p.vertex i).1)) *
        (det d (p.vertex (i + 1) - p.vertex i))⁻¹)
    fun_prop
  have hUcont : Continuous (U i) := by
    change Continuous (fun y : Real × Real =>
      (((p.vertex i).1 - y.1) * d.2 - ((p.vertex i).2 - y.2) * d.1) *
        (det d (p.vertex (i + 1) - p.vertex i))⁻¹)
    fun_prop
  have hGcont : Continuous (G i) := by
    change Continuous (fun y : Real × Real =>
      d.1 * ((p.vertex i).2 - y.2) - d.2 * ((p.vertex i).1 - y.1))
    fun_prop
  have hGopen : IsOpen {y | G i y ≠ 0} := isOpen_ne.preimage hGcont
  by_cases hneg : U i x < 0
  · let V : Set (Real × Real) := {y | U i y < 0} ∩ {y | G i y ≠ 0}
    refine ⟨V, ?_, ?_, ?_⟩
    · exact (isOpen_lt hUcont continuous_const).inter hGopen
    · simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨hneg, hg i⟩
    · intro y hy
      simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq] at hy
      refine ⟨hy.2, ?_⟩
      have hNoX : ¬ H i x := by
        intro hh
        have hh' := (hcriterion i x).mp hh
        rcases hh' with ⟨_, hu, _⟩
        exact (not_le_of_gt hneg) hu
      have hNoY : ¬ H i y := by
        intro hh
        have hh' := (hcriterion i y).mp hh
        rcases hh' with ⟨_, hu, _⟩
        exact (not_le_of_gt hy.1) hu
      exact ⟨fun hh => (hNoY hh).elim, fun hh => (hNoX hh).elim⟩
  · by_cases hhigh : 1 < U i x
    · let V : Set (Real × Real) := {y | 1 < U i y} ∩ {y | G i y ≠ 0}
      refine ⟨V, ?_, ?_, ?_⟩
      · exact (isOpen_lt continuous_const hUcont).inter hGopen
      · simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨hhigh, hg i⟩
      · intro y hy
        simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq] at hy
        refine ⟨hy.2, ?_⟩
        have hNoX : ¬ H i x := by
          intro hh
          have hh' := (hcriterion i x).mp hh
          rcases hh' with ⟨_, _, hu⟩
          exact (not_le_of_gt hhigh) hu
        have hNoY : ¬ H i y := by
          intro hh
          have hh' := (hcriterion i y).mp hh
          rcases hh' with ⟨_, _, hu⟩
          exact (not_le_of_gt hy.1) hu
        exact ⟨fun hh => (hNoY hh).elim, fun hh => (hNoX hh).elim⟩
    · have hlow : 0 < U i x := by
        rcases lt_or_eq_of_le (le_of_not_gt hneg) with h | h
        · exact h
        · exact False.elim (hU0 h.symm)
      have hupper : U i x < 1 := by
        rcases lt_or_eq_of_le (le_of_not_gt hhigh) with h | h
        · exact h
        · exact False.elim (hU1 h)
      have hTnonzero : T i x ≠ 0 := hT0 ⟨hlow, hupper⟩
      by_cases htpos : 0 < T i x
      · let V : Set (Real × Real) :=
          {y | 0 < U i y} ∩ {y | U i y < 1} ∩
          {y | 0 < T i y} ∩ {y | G i y ≠ 0}
        refine ⟨V, ?_, ?_, ?_⟩
        · exact (((isOpen_lt continuous_const hUcont).inter
            (isOpen_lt hUcont continuous_const)).inter
            (isOpen_lt continuous_const hTcont)).inter hGopen
        · simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq]
          exact ⟨⟨⟨hlow, hupper⟩, htpos⟩, hg i⟩
        · intro y hy
          simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq] at hy
          rcases hy with ⟨⟨⟨hu0, hu1⟩, htposY⟩, hgy⟩
          refine ⟨hgy, ?_⟩
          constructor
          · intro _
            exact (hcriterion i x).mpr ⟨htpos, le_of_lt hlow, le_of_lt hupper⟩
          · intro _
            exact (hcriterion i y).mpr ⟨htposY, le_of_lt hu0, le_of_lt hu1⟩
      · have htneg : T i x < 0 := by
          rcases lt_or_eq_of_le (le_of_not_gt htpos) with h | h
          · exact h
          · exact False.elim (hTnonzero h)
        let V : Set (Real × Real) :=
          {y | 0 < U i y} ∩ {y | U i y < 1} ∩
          {y | T i y < 0} ∩ {y | G i y ≠ 0}
        refine ⟨V, ?_, ?_, ?_⟩
        · exact (((isOpen_lt continuous_const hUcont).inter
            (isOpen_lt hUcont continuous_const)).inter
            (isOpen_lt hTcont continuous_const)).inter hGopen
        · simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq]
          exact ⟨⟨⟨hlow, hupper⟩, htneg⟩, hg i⟩
        · intro y hy
          simp only [V, Set.mem_inter_iff, Set.mem_ofPred_eq] at hy
          rcases hy with ⟨⟨⟨hu0, hu1⟩, htnegY⟩, hgy⟩
          refine ⟨hgy, ?_⟩
          constructor
          · intro hh
            have hh' := (hcriterion i y).mp hh
            linarith [hh'.1]
          · intro hh
            have hh' := (hcriterion i x).mp hh
            linarith [hh'.1]

end RayCrossingStability

private theorem localRayCrossingStability {n : Nat} (p : P3381T1PolygonBoundary n) :
    (∀ x d : Real × Real, x ∉ P3544T1BoundaryCarrier p →
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) →
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0) →
      ∃ r : Real, 0 < r ∧ ∀ y ∈ Metric.ball x r,
        y ∉ P3544T1BoundaryCarrier p ∧
        (∀ i, d.1 * (p.vertex i - y).2 - d.2 * (p.vertex i - y).1 ≠ 0) ∧
        (∀ i, (∃ t : Real, 0 < t ∧
          y + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))) ↔
          (∃ t : Real, 0 < t ∧
            x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))))) := by
  intro x d hx hg hs
  let det (v w : Real × Real) := v.1 * w.2 - v.2 * w.1
  have params : ∀ (y a d' e : Real × Real), det d' e ≠ 0 →
      y + (det (a - y) e / det d' e) • d' =
        a + (det (a - y) d' / det d' e) • e ∧
      (∀ t u : Real, y + t • d' = a + u • e →
        t = det (a - y) e / det d' e ∧ u = det (a - y) d' / det d' e) := RayCrossingStability.params
  have hitCriterion : ∀ (y a b d' : Real × Real), det d' (b - a) ≠ 0 →
      ((∃ t : Real, 0 < t ∧ y + t • d' ∈ segment Real a b) ↔
      0 < det (a - y) (b - a) / det d' (b - a) ∧
        0 ≤ det (a - y) d' / det d' (b - a) ∧
        det (a - y) d' / det d' (b - a) ≤ 1) := RayCrossingStability.hitCriterion
  have hsegCompact : ∀ i : Fin (n + 3),
      IsCompact (segment Real (p.vertex i) (p.vertex (i + 1))) :=
          RayCrossingStability.hsegCompact n p
  have hcarrierCompact : IsCompact (P3544T1BoundaryCarrier p) :=
      RayCrossingStability.hcarrierCompact n p
  have hcarrierOpen : IsOpen (P3544T1BoundaryCarrier p)ᶜ := RayCrossingStability.hcarrierOpen n p
  let T : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * ((p.vertex (i + 1)).2 - (p.vertex i).2) -
      ((p.vertex i).2 - y.2) * ((p.vertex (i + 1)).1 - (p.vertex i).1)) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹
  let U : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    (((p.vertex i).1 - y.1) * d.2 - ((p.vertex i).2 - y.2) * d.1) *
      (det d (p.vertex (i + 1) - p.vertex i))⁻¹
  let G : Fin (n + 3) → (Real × Real) → Real := fun i y =>
    d.1 * ((p.vertex i).2 - y.2) - d.2 * ((p.vertex i).1 - y.1)
  let H : Fin (n + 3) → (Real × Real) → Prop := fun i y =>
    ∃ t : Real, 0 < t ∧ y + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))
  have hcriterion : ∀ i y, H i y ↔
      0 < T i y ∧ 0 ≤ U i y ∧ U i y ≤ 1 := RayCrossingStability.hcriterion n p d hs
  have hVi : ∀ i : Fin (n + 3), ∃ V : Set (Real × Real),
      IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V,
        G i y ≠ 0 ∧ (H i y ↔ H i x) := RayCrossingStability.hVi n p x d hx hg hs
  choose V hVopen hxV hVstable using hVi
  have hVopen : IsOpen (⋂ i, V i) := isOpen_iInter_of_finite hVopen
  have hxV : x ∈ ⋂ i, V i := Set.mem_iInter.mpr hxV
  have hOpen : IsOpen ((P3544T1BoundaryCarrier p)ᶜ ∩ ⋂ i, V i) :=
    hcarrierOpen.inter hVopen
  have hxOpen : x ∈ (P3544T1BoundaryCarrier p)ᶜ ∩ ⋂ i, V i := ⟨hx, hxV⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOpen x hxOpen
  refine ⟨r, hr, ?_⟩
  intro y hy
  have hyOpen := hball hy
  refine ⟨hyOpen.1, ?_, ?_⟩
  · intro i
    exact hVstable i y (Set.mem_iInter.mp hyOpen.2 i) |>.1
  · intro i
    exact (hVstable i y (Set.mem_iInter.mp hyOpen.2 i)).2

private theorem rayIntersectionParameters {n : Nat} (p : P3381T1PolygonBoundary n) :
    (∀ (x d : Real × Real) (i : Fin (n + 3)),
      let a := p.vertex i
      let e := p.vertex (i + 1) - a
      let D := d.1 * e.2 - d.2 * e.1
      D ≠ 0 →
      let t := ((a - x).1 * e.2 - (a - x).2 * e.1) / D
      let u := ((a - x).1 * d.2 - (a - x).2 * d.1) / D
      x + t • d = a + u • e ∧
      (∀ t' u' : Real, x + t' • d = a + u' • e → t' = t ∧ u' = u) ∧
      ((∃ t' : Real, 0 < t' ∧
        x + t' • d ∈ segment Real a (p.vertex (i + 1))) ↔
        0 < t ∧ 0 ≤ u ∧ u ≤ 1)) := by
  intro x d i
  dsimp
  intro hD
  let a := p.vertex i
  let e := p.vertex (i + 1) - a
  let D := d.1 * e.2 - d.2 * e.1
  let t := ((a - x).1 * e.2 - (a - x).2 * e.1) / D
  let u := ((a - x).1 * d.2 - (a - x).2 * d.1) / D
  let det (v w : Real × Real) := v.1 * w.2 - v.2 * w.1
  have hDet : det d e ≠ 0 := by
    simpa [det, e, a, Prod.fst_sub, Prod.snd_sub] using hD
  have hparams :
      x + (det (a - x) e / det d e) • d =
        a + (det (a - x) d / det d e) • e ∧
      (∀ t' u' : Real, x + t' • d = a + u' • e →
        t' = det (a - x) e / det d e ∧ u' = det (a - x) d / det d e) := by
    constructor
    · have hDn : d.1 * e.2 - d.2 * e.1 ≠ 0 := by
        simpa only [det] using hDet
      apply Prod.ext
      · change x.1 + (det (a - x) e / det d e) * d.1 =
          a.1 + (det (a - x) d / det d e) * e.1
        simp only [det, Prod.fst_sub, Prod.snd_sub]
        field_simp (disch := simpa only [mul_comm] using hDn)
        ring
      · change x.2 + (det (a - x) e / det d e) * d.2 =
          a.2 + (det (a - x) d / det d e) * e.2
        simp only [det, Prod.fst_sub, Prod.snd_sub]
        field_simp (disch := simpa only [mul_comm] using hDn)
        ring
    · intro t' u' h
      have h1 : x.1 + t' * d.1 = a.1 + u' * e.1 := by
        simpa using congrArg Prod.fst h
      have h2 : x.2 + t' * d.2 = a.2 + u' * e.2 := by
        simpa using congrArg Prod.snd h
      constructor
      · apply (eq_div_iff hDet).2
        dsimp only [det, Prod.fst_sub, Prod.snd_sub]
        linear_combination e.2 * h1 - e.1 * h2
      · apply (eq_div_iff hDet).2
        dsimp only [det, Prod.fst_sub, Prod.snd_sub]
        linear_combination d.2 * h1 - d.1 * h2
  have heq : x + t • d = a + u • e := by
    simpa [det, t, u, D] using hparams.1
  have huniq : ∀ t' u' : Real, x + t' • d = a + u' • e →
      t' = t ∧ u' = u := by
    intro t' u' h
    obtain ⟨ht, hu⟩ := hparams.2 t' u' h
    exact ⟨by simpa [det, t, D] using ht, by simpa [det, u, D] using hu⟩
  refine ⟨heq, huniq, ?_⟩
  constructor
  · rintro ⟨t', ht', hseg⟩
    rw [segment_eq_image'] at hseg
    obtain ⟨u', hu', he⟩ := hseg
    obtain ⟨hT, hU⟩ := huniq t' u' he.symm
    rw [hT] at ht'
    rw [hU] at hu'
    exact ⟨by simpa [det, t, D, a, e] using ht',
      by simpa [det, u, D, a, e] using hu'.1,
      by simpa [det, u, D, a, e] using hu'.2⟩
  · rintro ⟨ht, hu0, hu1⟩
    refine ⟨t, ht, ?_⟩
    rw [segment_eq_image']
    exact ⟨u, ⟨hu0, hu1⟩, heq.symm⟩

theorem P3597T1GenericRayStability {n : Nat} (p : P3381T1PolygonBoundary n) :
    (∀ x : Real × Real, (∀ i, p.vertex i ≠ x) → ∃ d : Real × Real,
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) ∧
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0)) ∧
    (∀ x d : Real × Real, x ∉ P3544T1BoundaryCarrier p →
      (∀ i, d.1 * (p.vertex i - x).2 - d.2 * (p.vertex i - x).1 ≠ 0) →
      (∀ i, d.1 * (p.vertex (i + 1) - p.vertex i).2 -
        d.2 * (p.vertex (i + 1) - p.vertex i).1 ≠ 0) →
      ∃ r : Real, 0 < r ∧ ∀ y ∈ Metric.ball x r,
        y ∉ P3544T1BoundaryCarrier p ∧
        (∀ i, d.1 * (p.vertex i - y).2 - d.2 * (p.vertex i - y).1 ≠ 0) ∧
        (∀ i, (∃ t : Real, 0 < t ∧
          y + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))) ↔
          (∃ t : Real, 0 < t ∧
            x + t • d ∈ segment Real (p.vertex i) (p.vertex (i + 1))))) ∧
    (∀ (x d : Real × Real) (i : Fin (n + 3)),
      let a := p.vertex i
      let e := p.vertex (i + 1) - a
      let D := d.1 * e.2 - d.2 * e.1
      D ≠ 0 →
      let t := ((a - x).1 * e.2 - (a - x).2 * e.1) / D
      let u := ((a - x).1 * d.2 - (a - x).2 * d.1) / D
      x + t • d = a + u • e ∧
      (∀ t' u' : Real, x + t' • d = a + u' • e → t' = t ∧ u' = u) ∧
      ((∃ t' : Real, 0 < t' ∧
        x + t' • d ∈ segment Real a (p.vertex (i + 1))) ↔
        0 < t ∧ 0 ≤ u ∧ u ≤ 1)) := by
  exact ⟨genericRayDirection p, localRayCrossingStability p, rayIntersectionParameters p⟩

end ApollonianSuperharmonic

end
