/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.DiameterTwo

/-!
# ClusterTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# 2-connected components of a lattice site set, and their diameter

> A *2-connected component* (or *2-cluster*) of `B*_{m-h}` is a maximal subset
> `A ⊆ B*_{m-h}` such that any two cubes in `A` can be connected by a chain of
> successive cubes `□, □' ∈ A` with `dist(□,□') ≤ 1`.  For `z ∈ 3^{m-h}ℤ^d ∩ □_m`
> we denote by `B*_{m-h}(z;2)` the 2-connected component containing `z + □_{m-h}`
> if `B*(z + □_{m-h})` occurs, and the empty set otherwise.

In lattice coordinates that is exactly the predicate `IsLatticePath₂` of
`LatticeTwo.lean`, so a 2-cluster is a connected component of the site set for
distance-two chains.

## Faithfulness of the transcription

* The chain condition of the source ranges over cubes `□, □' ∈ A`, i.e. the
  intermediate cubes must themselves be bad; `Connected₂ S u v` accordingly asks
  the whole chain to lie inside the site set `S`.  The printed form is nominally
  stronger — the chain inside the cluster `A` itself — and one direction is
  recorded here: `connected₂_of_mem_cluster₂` joins any two sites of a 2-cluster
  by a chain inside `S`.
* "Maximal subset" is implemented by `cluster₂`, whose membership criterion
  `mem_cluster₂_iff` reads `v ∈ cluster₂ S u ↔ u ∈ S ∧ Connected₂ S u v`: the
  cluster collects *every* site of `S` joined to `u`, and
  `connected₂_of_mem_cluster₂` is its 2-connectedness.
* The "empty set otherwise" clause is `cluster₂_nonempty_iff`: the 2-cluster is
  nonempty exactly when the base site lies in the site set.
* `latDiam` is the sup-metric diameter of the *centres* of the cubes of a
  cluster, in units of the cube side; `closedLatDiam = latDiam + 1` on a
  nonempty cluster is the sup-metric diameter of the union of the corresponding
  *closed* cubes, again in units of the cube side (a nonempty cluster of `n`
  cubes whose centres span `latDiam` reaches from one cube's near face to the
  other's far face).  The bad-cluster node uses `closedLatDiam`, the larger and
  hence the faithful reading of the printed `diam`.

## Main definitions

* `Connected₂`, `cluster₂`: the 2-connected relation and the 2-cluster.
* `latDiam`, `closedLatDiam`: the lattice diameters.

## Main results

* `Connected₂.refl`, `.symm`, `.trans`: `Connected₂` is an equivalence on `S`.
* `mem_cluster₂_iff`, `cluster₂_subset`, `self_mem_cluster₂`,
  `cluster₂_nonempty_iff`, `connected₂_of_mem_cluster₂`:
  the characterizations of the 2-cluster.
* `exists_crossingEvent₂At_of_le_latDiam`: the deterministic step "a 2-cluster of
  lattice diameter `≥ 3^{k+1}/2` contains a distance-two crossing of the annulus
  `□_{k+1} \ □_k` based at one of its own sites".

## References

* ABK26, `l.percolation.bad.clusters`, (`e.bad.cluster.def`)
  (`e.diameter.bound.bad.clusters`).
-/

namespace Algsuperdiff.Section3.Provider.Percolation

variable {d : ℕ}

/-! ### The 2-connected relation -/

/-- The whole chain is required to lie in `S`, as in the source ("a chain of
successive cubes `□, □' ∈ A`"). -/
def Connected₂ (S : Finset (Fin d → ℤ)) (u v : Fin d → ℤ) : Prop :=
  ∃ (N : ℕ) (x : ℕ → Fin d → ℤ), x 0 = u ∧ x N = v ∧ IsLatticePath₂ x N ∧
    ∀ i, i ≤ N → x i ∈ S

theorem Connected₂.refl {S : Finset (Fin d → ℤ)} {u : Fin d → ℤ} (hu : u ∈ S) :
    Connected₂ S u u :=
  ⟨0, fun _ => u, rfl, rfl, fun i hi => absurd hi (by omega), fun _ _ => hu⟩


theorem Connected₂.mem_right {S : Finset (Fin d → ℤ)} {u v : Fin d → ℤ}
    (h : Connected₂ S u v) : v ∈ S := by
  obtain ⟨N, x, -, hxN, -, hxS⟩ := h
  rw [← hxN]
  exact hxS N (le_refl N)

theorem Connected₂.symm {S : Finset (Fin d → ℤ)} {u v : Fin d → ℤ}
    (h : Connected₂ S u v) : Connected₂ S v u := by
  obtain ⟨N, x, hx0, hxN, hxp, hxS⟩ := h
  refine ⟨N, fun i => x (N - i), by simpa using hxN, by simpa using hx0, ?_, ?_⟩
  · intro i hi
    have hstep : N - i = (N - (i + 1)) + 1 := by omega
    have := hxp (N - (i + 1)) (by omega)
    rw [latDist_comm]
    show latDist (x (N - (i + 1))) (x (N - i)) ≤ 2
    rw [hstep]
    exact this
  · intro i hi
    exact hxS (N - i) (by omega)

theorem Connected₂.trans {S : Finset (Fin d → ℤ)} {u v w : Fin d → ℤ}
    (h₁ : Connected₂ S u v) (h₂ : Connected₂ S v w) : Connected₂ S u w := by
  classical
  obtain ⟨N, x, hx0, hxN, hxp, hxS⟩ := h₁
  obtain ⟨M, y, hy0, hyM, hyp, hyS⟩ := h₂
  refine ⟨N + M, fun i => if i ≤ N then x i else y (i - N), ?_, ?_, ?_, ?_⟩
  · show (if (0 : ℕ) ≤ N then x 0 else y (0 - N)) = u
    rw [ite_eq_left (Nat.zero_le N)]; exact hx0
  · show (if N + M ≤ N then x (N + M) else y (N + M - N)) = w
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · rw [ite_eq_left (by omega), Nat.add_zero, hxN, ← hyM, hy0]
    · rw [ite_eq_right (by omega), show N + M - N = M from by omega]
      exact hyM
  · intro i hi
    show latDist (if i ≤ N then x i else y (i - N))
      (if i + 1 ≤ N then x (i + 1) else y (i + 1 - N)) ≤ 2
    by_cases h1 : i + 1 ≤ N
    · rw [ite_eq_left (by omega), ite_eq_left h1]
      exact hxp i (by omega)
    · by_cases h2 : i ≤ N
      · have hiN : i = N := by omega
        subst hiN
        rw [ite_eq_left (le_refl i), ite_eq_right (by omega), show i + 1 - i = 1 from by omega, hxN,
          ← hy0]
        exact hyp 0 (by omega)
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          show i + 1 - N = (i - N) + 1 from by omega]
        exact hyp (i - N) (by omega)
  · intro i hi
    show (if i ≤ N then x i else y (i - N)) ∈ S
    by_cases h1 : i ≤ N
    · rw [ite_eq_left h1]; exact hxS i h1
    · rw [ite_eq_right h1]; exact hyS (i - N) (by omega)

/-! ### The 2-cluster -/

/-- ABK26 `e.bad.cluster.def`: the 2-connected component of the site set `S`
containing `u` if `u ∈ S`, and the empty set otherwise. -/
noncomputable def cluster₂ (S : Finset (Fin d → ℤ)) (u : Fin d → ℤ) :
    Finset (Fin d → ℤ) :=
  if u ∈ S then @Finset.filter _ (fun v => Connected₂ S u v) (Classical.decPred _) S
  else ∅

theorem mem_cluster₂_iff {S : Finset (Fin d → ℤ)} {u v : Fin d → ℤ} :
    v ∈ cluster₂ S u ↔ u ∈ S ∧ Connected₂ S u v := by
  classical
  unfold cluster₂
  by_cases hu : u ∈ S
  · rw [ite_eq_left hu, Finset.mem_filter]
    constructor
    · rintro ⟨-, hconn⟩; exact ⟨hu, hconn⟩
    · rintro ⟨-, hconn⟩; exact ⟨hconn.mem_right, hconn⟩
  · rw [ite_eq_right hu]
    simp [hu]

/-- The 2-cluster is a subset of the site set: the source's `A ⊆ B*_{m-h}`. -/
theorem cluster₂_subset (S : Finset (Fin d → ℤ)) (u : Fin d → ℤ) :
    cluster₂ S u ⊆ S := fun _ hv => (mem_cluster₂_iff.mp hv).2.mem_right

/-- The 2-cluster of a site of `S` contains that site. -/
theorem self_mem_cluster₂ {S : Finset (Fin d → ℤ)} {u : Fin d → ℤ} (hu : u ∈ S) :
    u ∈ cluster₂ S u := mem_cluster₂_iff.mpr ⟨hu, Connected₂.refl hu⟩


theorem cluster₂_nonempty_iff {S : Finset (Fin d → ℤ)} {u : Fin d → ℤ} :
    (cluster₂ S u).Nonempty ↔ u ∈ S := by
  constructor
  · rintro ⟨v, hv⟩
    exact (mem_cluster₂_iff.mp hv).1
  · intro hu
    exact ⟨u, self_mem_cluster₂ hu⟩

/-- **First half of maximality.**  Any two sites of a 2-cluster are joined by a
chain of successive sites of `S` at lattice sup distance at most two. -/
theorem connected₂_of_mem_cluster₂ {S : Finset (Fin d → ℤ)} {u v w : Fin d → ℤ}
    (hv : v ∈ cluster₂ S u) (hw : w ∈ cluster₂ S u) : Connected₂ S v w :=
  ((mem_cluster₂_iff.mp hv).2).symm.trans (mem_cluster₂_iff.mp hw).2


/-! ### Lattice diameters -/

/-- The sup-metric diameter of a finite set of lattice sites, in units of the
lattice spacing: the largest sup distance between two of its sites. -/
def latDiam (A : Finset (Fin d → ℤ)) : ℕ := A.sup fun u => A.sup fun v => latDist u v

theorem latDist_le_latDiam {A : Finset (Fin d → ℤ)} {u v : Fin d → ℤ}
    (hu : u ∈ A) (hv : v ∈ A) : latDist u v ≤ latDiam A :=
  le_trans (Finset.le_sup (f := fun w => latDist u w) hv)
    (Finset.le_sup (f := fun w => A.sup fun w' => latDist w w') hu)

/-- A positive lower bound on the lattice diameter is attained by a pair of
sites. -/
theorem exists_le_latDist_of_le_latDiam {A : Finset (Fin d → ℤ)} {D : ℕ}
    (hD : 0 < D) (h : D ≤ latDiam A) : ∃ u ∈ A, ∃ v ∈ A, D ≤ latDist u v := by
  have hbot : (⊥ : ℕ) < D := by simpa using hD
  obtain ⟨u, hu, hu'⟩ := (Finset.le_sup_iff hbot).mp h
  obtain ⟨v, hv, hv'⟩ := (Finset.le_sup_iff hbot).mp hu'
  exact ⟨u, hu, v, hv, hv'⟩

/-- The sup-metric diameter, in units of the cube side, of the union of the
*closed* unit cubes centred at the sites of `A`.  On a nonempty `A` this is
`latDiam A + 1`; the empty set has diameter `0`.

This is the reading of the printed `diam(B*_{m-h}(z;2))` used by the bad-cluster
node: it is the larger of the two candidate readings (the other being the
centre-to-centre `latDiam`), so bounding the probability that it is large is the
stronger statement. -/
def closedLatDiam (A : Finset (Fin d → ℤ)) : ℕ := if A.Nonempty then latDiam A + 1 else 0


theorem closedLatDiam_eq_of_nonempty {A : Finset (Fin d → ℤ)} (hA : A.Nonempty) :
    closedLatDiam A = latDiam A + 1 := ite_eq_left hA

/-! ### From a large 2-cluster to a distance-two crossing -/

/-- **The deterministic step of `e.diameter.bound.bad.clusters`.**

If the 2-cluster of `u` has lattice diameter `D` with `3 ^ (k+1) ≤ 2 D`, and
every site of the site set carries the bad event `⋃_L B_L`, then one of the sites
of that 2-cluster is the base of a distance-two crossing of its own annulus
`□_{k+1} \ □_k`, i.e. of the event `crossingEvent₂At B k`.

This is the "follows from `e.diameter.bound` (rescaled)" of the source proof,
made explicit at the ruled adjacency: the chain joining the two extreme sites
of the cluster is a distance-two path, which the distance-two abstract layer of
`DiameterTwo.lean` — and not the proved distance-one layer — covers. -/
theorem exists_crossingEvent₂At_of_le_latDiam {Ω : Type*}
    {B : ℕ → (Fin d → ℤ) → Set Ω} {ω : Ω} {S : Finset (Fin d → ℤ)}
    {u : Fin d → ℤ} {k : ℕ}
    (hbad : ∀ y ∈ S, ω ∈ ⋃ L : ℕ, B L y)
    (hdiam : 3 ^ (k + 1) ≤ 2 * latDiam (cluster₂ S u)) :
    ∃ w ∈ cluster₂ S u, ω ∈ crossingEvent₂At B k w := by
  have hpow : 0 < (3 : ℕ) ^ (k + 1) := three_pow_pos (k + 1)
  have hpos : 0 < latDiam (cluster₂ S u) := by omega
  obtain ⟨v, hv, v', hv', hdist⟩ :=
    exists_le_latDist_of_le_latDiam hpos (le_refl (latDiam (cluster₂ S u)))
  obtain ⟨N, x, hx0, hxN, hxp, hxS⟩ := connected₂_of_mem_cluster₂ hv hv'
  refine ⟨v, hv, v, N, x, self_mem_cubeAt k v, hx0, hxp, ?_, ?_⟩
  · intro hmem
    have hlt : 2 * latDist v (x N) < 3 ^ (k + 1) := mem_cubeAt_iff.mp hmem
    rw [hxN] at hlt
    omega
  · intro i hi
    exact hbad (x i) (hxS i hi)

end Algsuperdiff.Section3.Provider.Percolation
