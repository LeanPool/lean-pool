/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Lattice
public import Mathlib.Order.Lattice.Nat

/-!
# LatticeTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Distance-two lattice paths: geometry and separated selection

ABK26's abstract percolation machinery (`l.percolation.bound.general`) steps
along paths whose consecutive sites are at lattice distance at most one.  The
bad-cluster lemma `l.percolation.bad.clusters` however joins base cubes `□, □'`
with `dist(□,□') ≤ 1`, i.e. **lattice sup distance at most two** in units of
the cube side `3^{m-h}`.  A 2-adjacent chain is *not* a 1-adjacent lattice
path, so the abstract layer as proved does not literally cover 2-clusters.

This module is the first half of that re-run: the purely combinatorial geometry
of distance-two paths.  It is a parallel layer under new names; no proved
declaration is modified.

## Where the step size enters

Exactly three places, and each costs only a dimension-only factor:

* **Truncation.**  A distance-two path truncated at its first exit from `z +
  □_n` is confined to `2 · latDist z (x i) ≤ 3 ^ n + 3` (the distance-one layer
  has `3 ^ n + 1`).
* **Shell selection.**  The distance to the starting site now jumps by up to
  two per step, so a first passage of the level `m * s` proves in `[m*s, m*s +
  1]` rather than exactly on `m * s`; consecutive selected sites are therefore
  `s - 1`-separated instead of `s`-separated.  Taking the step `s = 3 ^ (k+1) +
  5` restores the separation `3 ^ (k+1) + 4` needed below.
* **Range of independence.**  The wider localisation boxes need the wider site
  separation `3 ^ (k+1) + 4` (against `3 ^ (k+1) + 2`) to keep the boxes at sup
  distance more than `3 ^ k`; `three_pow_lt_latDist_of_mem_locBox₂` supplies it.

The number `3 ^ (h - 3)` of selected sites — the quantity that drives the whole
induction — is **unchanged**, because the arithmetic
`2 · 3 ^ (h-3) · (3 ^ (k+1) + 5) ≤ 3 ^ (k+h)` still holds.  This is why the
gate constant of the distance-two layer is the same `16 d exp(40 (1-b)^{-1})` as
the distance-one one.

## Main definitions

* `IsLatticePath₂`: the distance-two path predicate.
* `locBox₂`: the localisation box of a truncated distance-two path.

## Main results

* `exists_truncated_path₂`: truncation at the first exit from a cube.
* `card_locBox₂_le`: `#(locBox₂ n z) ≤ 3 ^ (d * (n + 2))`.
* `three_pow_lt_latDist_of_mem_locBox₂`: the independence range.
* `exists_separated_subpaths₂`: the separated-subpath extraction, with the same
  count `3 ^ (h - 3)` as the distance-one layer.

## References

* ABK26, `l.percolation.bad.clusters`, (the 2-connected component) and
  `l.percolation.bound.general`, (the abstract layer).
-/

namespace Algsuperdiff.Section3.Provider.Percolation

variable {d : ℕ}

/-! ### Distance-two paths -/

/-- The distance-two path predicate: consecutive sites are at sup distance at most
two. -/
def IsLatticePath₂ (x : ℕ → Fin d → ℤ) (N : ℕ) : Prop :=
  ∀ i, i < N → latDist (x i) (x (i + 1)) ≤ 2


/-- A distance-two path may be shortened. -/
theorem IsLatticePath₂.mono {x : ℕ → Fin d → ℤ} {N M : ℕ} (h : IsLatticePath₂ x N)
    (hMN : M ≤ N) : IsLatticePath₂ x M := fun i hi => h i (lt_of_lt_of_le hi hMN)

/-- A distance-two path may be restarted at any of its sites. -/
theorem IsLatticePath₂.shift {x : ℕ → Fin d → ℤ} {N : ℕ} (h : IsLatticePath₂ x N)
    (a M : ℕ) (hle : a + M ≤ N) : IsLatticePath₂ (fun t => x (a + t)) M := by
  intro i hi
  have hlt : a + i < N := by omega
  simpa [Nat.add_assoc] using h (a + i) hlt

/-- Along a distance-two path the sup distance to the starting site grows by at
most two per step. -/
theorem IsLatticePath₂.latDist_start_succ_le {x : ℕ → Fin d → ℤ} {N : ℕ}
    (h : IsLatticePath₂ x N) {i : ℕ} (hi : i < N) :
    latDist (x 0) (x (i + 1)) ≤ latDist (x 0) (x i) + 2 :=
  le_trans (latDist_triangle _ _ _) (Nat.add_le_add_left (h i hi) _)

/-! ### Truncation at the first exit from a cube -/

/-- Truncation of a distance-two path at its first exit from `z + □_n`: from a
path started at `z` and ending outside `z + □_n` we extract an initial segment
which still ends outside `z + □_n` and all of whose sites satisfy
`2 * latDist z (x i) ≤ 3 ^ n + 3`.

The distance-one layer confines the truncated path to `3 ^ n + 1`; the extra `2`
is the single place where the step size enters the localisation. -/
theorem exists_truncated_path₂ {x : ℕ → Fin d → ℤ} {N n : ℕ} {z : Fin d → ℤ}
    (h0 : x 0 = z) (hpath : IsLatticePath₂ x N) (hout : x N ∉ cubeAt n z) :
    ∃ M, M ≤ N ∧ x M ∉ cubeAt n z ∧ ∀ i, i ≤ M → 2 * latDist z (x i) ≤ 3 ^ n + 3 := by
  obtain ⟨M, hMN, hMout, hin⟩ := exists_first_exit hout
  refine ⟨M, hMN, hMout, fun i hi => ?_⟩
  have hpos := three_pow_pos n
  rcases lt_or_eq_of_le hi with hlt | rfl
  · have hmem := hin i hlt
    rw [mem_cubeAt_iff] at hmem
    omega
  · rcases Nat.eq_zero_or_pos i with rfl | hposi
    · rw [h0, latDist_self]
      omega
    · obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
      have hprev : x p ∈ cubeAt n z := hin p (by omega)
      rw [mem_cubeAt_iff] at hprev
      have hstep : latDist (x 0) (x (p + 1)) ≤ latDist (x 0) (x p) + 2 :=
        hpath.latDist_start_succ_le (lt_of_lt_of_le (by omega) hMN)
      rw [h0] at hstep
      omega

/-! ### The localisation box of a distance-two path -/

/-- Half-width, rounded up, of the distance-two localisation box at scale `n`. -/
def locRadius₂ (n : ℕ) : ℕ := (3 ^ n + 3) / 2

theorem two_mul_locRadius₂ (n : ℕ) : 2 * locRadius₂ n = 3 ^ n + 3 := by
  have hodd : (3 : ℕ) ^ n % 2 = 1 := by simp [Nat.pow_mod]
  rw [locRadius₂]
  omega

/-- The finite set of lattice sites `y` with `2 * latDist z y ≤ 3 ^ n + 3`: the
region in which a distance-two path started at `z` and truncated at its first
exit from `z + □_n` is confined. -/
def locBox₂ (n : ℕ) (z : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun j => Finset.Icc (z j - (locRadius₂ n : ℤ)) (z j + (locRadius₂ n : ℤ))

theorem mem_locBox₂_iff {n : ℕ} {z y : Fin d → ℤ} :
    y ∈ locBox₂ n z ↔ 2 * latDist z y ≤ 3 ^ n + 3 := by
  classical
  have hr := two_mul_locRadius₂ (n := n)
  rw [locBox₂, Fintype.mem_piFinset]
  constructor
  · intro hy
    have hsup : latDist z y ≤ locRadius₂ n :=
      Finset.sup_le fun j _ => by have := Finset.mem_Icc.mp (hy j); omega
    omega
  · intro hy j
    have hj : (z j - y j).natAbs ≤ latDist z y := coord_le_latDist z y j
    rw [Finset.mem_Icc]
    omega

theorem mem_locBox₂_of_two_mul_latDist_le {n : ℕ} {z y : Fin d → ℤ}
    (h : 2 * latDist z y ≤ 3 ^ n + 3) : y ∈ locBox₂ n z :=
  mem_locBox₂_iff.mpr h

/-- Distance-two localisation boxes of two sites at sup distance at least `3 ^
(k + 1) + 4` are at sup distance strictly greater than `3 ^ k`.  This is the
separation required by the finite-range independence hypothesis of ABK26; the
distance-one layer needs only `3 ^ (k + 1) + 2`. -/
theorem three_pow_lt_latDist_of_mem_locBox₂ {k : ℕ} {a b u v : Fin d → ℤ}
    (hab : 3 ^ (k + 1) + 4 ≤ latDist a b) (hu : u ∈ locBox₂ k a) (hv : v ∈ locBox₂ k b) :
    3 ^ k < latDist u v := by
  have hu' : 2 * latDist a u ≤ 3 ^ k + 3 := mem_locBox₂_iff.mp hu
  have hv' : 2 * latDist b v ≤ 3 ^ k + 3 := mem_locBox₂_iff.mp hv
  have htri : latDist a b ≤ latDist a u + (latDist u v + latDist v b) :=
    le_trans (latDist_triangle a u b) (Nat.add_le_add (le_refl _) (latDist_triangle u v b))
  have hvb : latDist v b = latDist b v := latDist_comm v b
  have hsucc : (3 : ℕ) ^ (k + 1) = 3 ^ k * 3 := by rw [pow_succ]
  omega

/-- A crude count of the distance-two localisation box: one factor `3 ^ d` more
than the distance-one `card_locBox_le`. -/
theorem card_locBox₂_le (n : ℕ) (z : Fin d → ℤ) :
    (locBox₂ n z).card ≤ 3 ^ (d * (n + 2)) := by
  classical
  have hr := two_mul_locRadius₂ (n := n)
  have hpos := three_pow_pos n
  have hcard : (locBox₂ n z).card = (3 ^ n + 4) ^ d := by
    rw [locBox₂, Fintype.card_piFinset]
    have hfac : ∀ j : Fin d,
        (Finset.Icc (z j - (locRadius₂ n : ℤ)) (z j + (locRadius₂ n : ℤ))).card
          = 3 ^ n + 4 := by
      intro j
      rw [Int.card_Icc]
      omega
    rw [Finset.prod_congr rfl fun j _ => hfac j, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hcard]
  calc (3 ^ n + 4) ^ d ≤ (3 ^ (n + 2)) ^ d := by
        refine Nat.pow_le_pow_left ?_ d
        have hsucc : (3 : ℕ) ^ (n + 2) = 3 ^ n * 3 * 3 := by rw [pow_succ, pow_succ]
        omega
    _ = 3 ^ (d * (n + 2)) := by rw [← pow_mul, Nat.mul_comm]

/-! ### Shell selection along a distance-two path -/

/-- **Shell selection for distance-two paths.**  Along a distance-two path whose
final site is at sup distance at least `M * s` from the starting site there are
indices `i 0 ≤ ⋯ ≤ i M` (bounded by the length of the path) with `i 0 = 0` such
that `x (i m)` lies in the shell `[m * s, m * s + 1]` around `x 0`. -/
theorem exists_shell_indices₂ {x : ℕ → Fin d → ℤ} {N s M : ℕ}
    (hpath : IsLatticePath₂ x N) (hreach : M * s ≤ latDist (x 0) (x N)) :
    ∃ i : ℕ → ℕ, i 0 = 0 ∧ (∀ m, m ≤ M → i m ≤ N) ∧
      (∀ m m', m ≤ m' → m' ≤ M → i m ≤ i m') ∧
      (∀ m, m ≤ M → m * s ≤ latDist (x 0) (x (i m)) ∧
        latDist (x 0) (x (i m)) ≤ m * s + 1) := by
  classical
  have hmemN : ∀ m, m ≤ M → N ∈ {j | m * s ≤ latDist (x 0) (x j)} := fun m hm =>
    le_trans (Nat.mul_le_mul hm (le_refl s)) hreach
  have hne : ∀ m, m ≤ M → ({j | m * s ≤ latDist (x 0) (x j)} : Set ℕ).Nonempty :=
    fun m hm => ⟨N, hmemN m hm⟩
  refine ⟨fun m => sInf {j | m * s ≤ latDist (x 0) (x j)}, ?_, ?_, ?_, ?_⟩
  · have hzero : (0 : ℕ) ∈ {j | 0 * s ≤ latDist (x 0) (x j)} := by
      simp only [Set.mem_ofPred_eq, Nat.zero_mul]
      exact Nat.zero_le _
    exact Nat.le_zero.mp (Nat.sInf_le hzero)
  · exact fun m hm => Nat.sInf_le (hmemN m hm)
  · intro m m' hmm' hm'
    refine Nat.sInf_le ?_
    have hmem := Nat.sInf_mem (hne m' hm')
    simp only [Set.mem_ofPred_eq] at hmem ⊢
    exact le_trans (Nat.mul_le_mul hmm' (le_refl s)) hmem
  · intro m hm
    change m * s ≤ latDist (x 0) (x (sInf {j | m * s ≤ latDist (x 0) (x j)})) ∧
      latDist (x 0) (x (sInf {j | m * s ≤ latDist (x 0) (x j)})) ≤ m * s + 1
    have hlow : m * s ≤ latDist (x 0) (x (sInf {j | m * s ≤ latDist (x 0) (x j)})) :=
      Nat.sInf_mem (hne m hm)
    have hleN : sInf {j | m * s ≤ latDist (x 0) (x j)} ≤ N := Nat.sInf_le (hmemN m hm)
    refine ⟨hlow, ?_⟩
    rcases Nat.eq_zero_or_pos (sInf {j | m * s ≤ latDist (x 0) (x j)}) with hz | hpos
    · rw [hz] at hlow ⊢
      rw [latDist_self] at hlow ⊢
      omega
    · obtain ⟨q, hq⟩ : ∃ q, sInf {j | m * s ≤ latDist (x 0) (x j)} = q + 1 :=
        ⟨sInf {j | m * s ≤ latDist (x 0) (x j)} - 1, by omega⟩
      have hqnot : ¬ m * s ≤ latDist (x 0) (x q) := fun hcon => by
        have := Nat.sInf_le (show q ∈ {j | m * s ≤ latDist (x 0) (x j)} from hcon)
        omega
      have hstep : latDist (x 0) (x (q + 1)) ≤ latDist (x 0) (x q) + 2 :=
        hpath.latDist_start_succ_le (by omega : q < N)
      rw [hq]
      omega

/-- Distinct shell-selected sites of a distance-two path are at sup distance at
least `s - 1`, stated in the addition-free form `s ≤ latDist + 1`. -/
theorem latDist_shell_separated₂ {x : ℕ → Fin d → ℤ} {i : ℕ → ℕ} {s M : ℕ}
    (hval : ∀ m, m ≤ M → m * s ≤ latDist (x 0) (x (i m)) ∧
      latDist (x 0) (x (i m)) ≤ m * s + 1)
    {m m' : ℕ} (hm : m ≤ M) (hm' : m' ≤ M) (hmm' : m ≠ m') :
    s ≤ latDist (x (i m)) (x (i m')) + 1 := by
  have key : ∀ a b, a ≤ M → b ≤ M → a < b → s ≤ latDist (x (i a)) (x (i b)) + 1 := by
    intro a b ha hb hab
    have htri : latDist (x 0) (x (i b))
        ≤ latDist (x 0) (x (i a)) + latDist (x (i a)) (x (i b)) :=
      latDist_triangle _ _ _
    have hva := hval a ha
    have hvb := hval b hb
    have hstep : (a + 1) * s ≤ b * s := Nat.mul_le_mul hab (le_refl s)
    rw [Nat.succ_mul] at hstep
    omega
  rcases Nat.lt_or_ge m m' with hlt | hge
  · exact key m m' hm hm' hlt
  · rw [latDist_comm]
    exact key m' m hm' hm (by omega)

/-- **The separated-subpath extraction for distance-two paths.**

Let `x` be a distance-two path started at `z` which ends outside `z + □_{k+h}`,
with `h ≥ 3`, and suppose a property `P` holds at every site of the path.  Then
there are `3 ^ (h - 3)` sites of the path — the *same count* as in the
distance-one layer — all lying in `locBox₂ (k + h) z`, pairwise at sup distance
at least `3 ^ (k + 1) + 4`, each of them the starting site of a distance-two
subpath which leaves its own `□_k`-cube and along which `P` still holds. -/
theorem exists_separated_subpaths₂ {x : ℕ → Fin d → ℤ} {N k h : ℕ} {z : Fin d → ℤ}
    {P : (Fin d → ℤ) → Prop}
    (hh : 3 ≤ h) (h0 : x 0 = z) (hpath : IsLatticePath₂ x N)
    (hout : x N ∉ cubeAt (k + h) z) (hP : ∀ i, i ≤ N → P (x i)) :
    ∃ y : ℕ → Fin d → ℤ,
      (∀ m, m < 3 ^ (h - 3) → y m ∈ locBox₂ (k + h) z) ∧
      (∀ m m', m < 3 ^ (h - 3) → m' < 3 ^ (h - 3) → m ≠ m' →
        3 ^ (k + 1) + 4 ≤ latDist (y m) (y m')) ∧
      (∀ m, m < 3 ^ (h - 3) → ∃ (N' : ℕ) (x' : ℕ → Fin d → ℤ),
        x' 0 = y m ∧ IsLatticePath₂ x' N' ∧ x' N' ∉ cubeAt k (y m) ∧
          ∀ t, t ≤ N' → P (x' t)) := by
  classical
  obtain ⟨M₀, hM₀N, hM₀out, hM₀loc⟩ := exists_truncated_path₂ h0 hpath hout
  have harith : 2 * (3 ^ (h - 3) * (3 ^ (k + 1) + 5)) ≤ 3 ^ (k + h) := by
    have h1 : (3 : ℕ) ^ (k + 1) + 5 ≤ 3 ^ (k + 2) := by
      have e : (3 : ℕ) ^ (k + 2) = 3 ^ (k + 1) * 3 := by rw [pow_succ]
      have p : 3 ≤ (3 : ℕ) ^ (k + 1) := by
        have hp1 : (3 : ℕ) ^ 1 ≤ 3 ^ (k + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        simpa using hp1
      omega
    have h2 : (3 : ℕ) ^ (h - 3) * 3 ^ (k + 2) = 3 ^ (k + h - 1) := by
      rw [← pow_add, show h - 3 + (k + 2) = k + h - 1 from by omega]
    have h3 : (3 : ℕ) ^ (k + h - 1) * 3 = 3 ^ (k + h) := by
      rw [← pow_succ, show k + h - 1 + 1 = k + h from by omega]
    have hp : 0 < (3 : ℕ) ^ (k + h - 1) := three_pow_pos (k + h - 1)
    calc 2 * (3 ^ (h - 3) * (3 ^ (k + 1) + 5))
        ≤ 2 * (3 ^ (h - 3) * 3 ^ (k + 2)) :=
          Nat.mul_le_mul (le_refl 2) (Nat.mul_le_mul (le_refl (3 ^ (h - 3))) h1)
      _ = 2 * 3 ^ (k + h - 1) := by rw [h2]
      _ ≤ 3 ^ (k + h) := by omega
  have hreach : 3 ^ (h - 3) * (3 ^ (k + 1) + 5) ≤ latDist (x 0) (x M₀) := by
    have hge : 3 ^ (k + h) ≤ 2 * latDist z (x M₀) := by
      by_contra hcon
      exact hM₀out (mem_cubeAt_iff.mpr (by omega))
    rw [h0]
    omega
  obtain ⟨i, _, hiN, himono, hival⟩ := exists_shell_indices₂ (hpath.mono hM₀N) hreach
  refine ⟨fun m => x (i m), ?_, ?_, ?_⟩
  · intro m hm
    exact mem_locBox₂_of_two_mul_latDist_le (hM₀loc (i m) (hiN m (by omega)))
  · intro m m' hm hm' hmm'
    change 3 ^ (k + 1) + 4 ≤ latDist (x (i m)) (x (i m'))
    have := latDist_shell_separated₂ hival (M := 3 ^ (h - 3)) (by omega) (by omega) hmm'
    omega
  · intro m hm
    have hmM : m ≤ 3 ^ (h - 3) := by omega
    have hm1M : m + 1 ≤ 3 ^ (h - 3) := by omega
    have hle : i m ≤ i (m + 1) := himono m (m + 1) (by omega) hm1M
    have hi1 : i (m + 1) ≤ M₀ := hiN (m + 1) hm1M
    have hend : i m + (i (m + 1) - i m) = i (m + 1) := by omega
    refine ⟨i (m + 1) - i m, fun t => x (i m + t), by simp, ?_, ?_, ?_⟩
    · refine (hpath.mono hM₀N).shift (i m) (i (m + 1) - i m) ?_
      rw [hend]
      exact hi1
    · change x (i m + (i (m + 1) - i m)) ∉ cubeAt k (x (i m))
      rw [hend]
      intro hcon
      rw [mem_cubeAt_iff] at hcon
      have hsep : 3 ^ (k + 1) + 5 ≤ latDist (x (i m)) (x (i (m + 1))) + 1 :=
        latDist_shell_separated₂ hival hmM hm1M (by omega)
      have hmono : (3 : ℕ) ^ k ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · intro t ht
      exact hP (i m + t) (by omega)

end Algsuperdiff.Section3.Provider.Percolation
