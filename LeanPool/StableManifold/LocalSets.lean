/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.LocalSetDefinitions
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Local stable and unstable sets of a fixed point

For a map `f : X → X` of a topological space, a point `p` and a set `U`:

* `Function.localStableSet f p U`: the points whose forward orbit stays in `U` and tends to `p`
  (the local stable set of `f|_U`);
* `Function.globalStableSet f p`: the points whose forward orbit tends to `p`;
* `Function.localUnstableSet f p U`: the points having a backward orbit (`f (y (n + 1)) = y n`) in
  `U` that tends to `p` (the local stable set of `f⁻¹|_U` when `f` is invertible; the definition
  does not need an inverse).

The two local sets are defined in `StableManifold.Defs`, with the other definitions in the
statement of the stable manifold theorem; the global stable set is defined here.

Elementary facts:

* `Function.eventually_iterate_mem_localStableSet`, `Function.eventually_mem_localUnstableSet`:
  an orbit tending to `p` eventually lies in the local stable set of every neighborhood of `p`,
  and a backward orbit tending to `p` eventually lies in the local unstable set;
* `Function.localStableSet_symm_eq_localUnstableSet`: unstable for `e` is stable for `e⁻¹`;
* `Function.setOf_forall_iterate_symm_mem_eq`: the points whose `e⁻¹`-orbit stays in `U` are the
  points with a backward `e`-orbit in `U`;
* `Function.localStableSet_congr`, `Function.localUnstableSet_congr`: the local sets of `f|_U`
  depend only on `f|_U`;
* `Function.localStableSet_conj`, `Function.localUnstableSet_conj`: conjugating `f` by a
  homeomorphism `e` carries the local sets along `e` (the first is used with a translation, to
  move the fixed point to `0`).

## Proofs

* `eventually_iterate_mem_localStableSet`: `f^[m] x ∈ U` for `m ≥ N`; for `n ≥ N`, the orbit
  `k ↦ f^[k] (f^[n] x) = f^[k + n] x` (`Function.iterate_add_apply`) stays in `U` and tends to
  `p` (`Filter.tendsto_add_atTop_iff_nat`).
* `eventually_mem_localUnstableSet`: `y m ∈ U` for `m ≥ N`; for `n ≥ N`, `k ↦ y (k + n)` is a
  backward orbit of `y n` in `U` tending to `p`.
* `localStableSet_symm_eq_localUnstableSet`: the orbit `n ↦ e.symm^[n] x` of a point of the
  local stable set of `e.symm` is a backward `e`-orbit, as `U ⊆ e.target`
  (`OpenPartialHomeomorph.right_inv`); conversely, a backward `e`-orbit `y` in `U ⊆ e.source`
  has `e.symm (y n) = y (n + 1)` (`OpenPartialHomeomorph.left_inv`), so `y n = e.symm^[n] (y 0)`
  by induction. The second equation is the first one for `e.symm`.
* `setOf_forall_iterate_symm_mem_eq`: the same two facts, without the limits.
* `localStableSet_congr`: along an `f`-orbit in `U`, `f^[n] x = g^[n] x` by induction on `n`
  (`Function.iterate_succ_apply'`); symmetrically for `g`. `localUnstableSet_congr`: a backward
  orbit `y` in `U` has `f (y (n + 1)) = g (y (n + 1))`.
* `localStableSet_conj`: `(e ∘ f ∘ e.symm)^[n] (e x) = e (f^[n] x)`
  (`Function.Semiconj.iterate_right`), `e y ∈ e '' U ↔ y ∈ U`, and `e`, `e.symm` are continuous.
  `localUnstableSet_conj`: `e` maps a backward `f`-orbit in `U` to a backward orbit in `e '' U`,
  and `e.symm` maps back; continuity of both carries the limits.
-/

@[expose] public section

open Filter Topology Set

namespace Function

variable {X : Type*} [TopologicalSpace X]

/-- The **global stable set** of `f` at `p`: the points whose forward orbit tends to `p`. -/
def globalStableSet (f : X → X) (p : X) : Set X :=
  {x | Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- A point of the local stable set lies in `U`. -/
theorem mem_of_mem_localStableSet {f : X → X} {p : X} {U : Set X} {x : X}
    (h : x ∈ localStableSet f p U) : x ∈ U := by
  simpa using h.1 0

/-- A point of the local unstable set lies in `U`. -/
theorem mem_of_mem_localUnstableSet {f : X → X} {p : X} {U : Set X} {x : X}
    (h : x ∈ localUnstableSet f p U) : x ∈ U := by
  obtain ⟨y, rfl, hy, -⟩ := h
  exact (hy 0).1

/-- The local stable set lies in the global stable set. -/
theorem localStableSet_subset_globalStableSet (f : X → X) (p : X) (U : Set X) :
    localStableSet f p U ⊆ globalStableSet f p :=
  fun _ hx ↦ hx.2

/-- **An orbit tending to `p` eventually lies in the local stable set** of any neighborhood `U`
of `p`: the tail of the orbit stays in `U`.

Proof: `fⁿ(x) ∈ U` for `n ≥ N`; then `f^[k] (f^[n] x) = f^[k + n] x ∈ U` and tends to `p`. -/
theorem eventually_iterate_mem_localStableSet {f : X → X} {p : X} {U : Set X} (hU : U ∈ 𝓝 p)
    {x : X} (hx : Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)) :
    ∀ᶠ n in atTop, f^[n] x ∈ localStableSet f p U := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hx hU)
  refine eventually_atTop.2 ⟨N, fun n hn ↦ ⟨fun k ↦ ?_, ?_⟩⟩
  · rw [← iterate_add_apply]
    exact hN _ (by omega)
  · simp_rw [← iterate_add_apply]
    exact (tendsto_add_atTop_iff_nat n).2 hx

/-- **A backward orbit tending to `p` eventually lies in the local unstable set** of any
neighborhood `U` of `p`: if `f (y (n + 1)) = y n` for all `n` and `y n → p`, then `y n` lies in
`localUnstableSet f p U` for all large `n` (with the backward orbit `k ↦ y (n + k)`). -/
theorem eventually_mem_localUnstableSet {f : X → X} {p : X} {U : Set X} (hU : U ∈ 𝓝 p)
    {y : ℕ → X} (hy : ∀ n, f (y (n + 1)) = y n) (ht : Tendsto y atTop (𝓝 p)) :
    ∀ᶠ n in atTop, y n ∈ localUnstableSet f p U := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht hU)
  refine eventually_atTop.2 ⟨N, fun n hn ↦ ⟨fun k ↦ y (k + n), by simp,
    fun k ↦ ⟨hN _ (by omega), ?_⟩, (tendsto_add_atTop_iff_nat n).2 ht⟩⟩
  change f (y (k + 1 + n)) = y (k + n)
  rw [Nat.add_right_comm]
  exact hy _

/-- A forward `e⁻¹`-orbit in `U ⊆ e.target` is a backward `e`-orbit. -/
private lemma apply_iterate_symm_succ (e : OpenPartialHomeomorph X X) {U : Set X}
    (hU : U ⊆ e.target) {x : X} (hx : ∀ n, e.symm^[n] x ∈ U) (n : ℕ) :
    e (e.symm^[n + 1] x) = e.symm^[n] x := by
  rw [iterate_succ_apply']
  exact e.right_inv (hU (hx n))

/-- A backward `e`-orbit in `U ⊆ e.source` is the forward `e⁻¹`-orbit of its first point. -/
private lemma iterate_symm_eq_of_backward (e : OpenPartialHomeomorph X X) {U : Set X}
    (hU : U ⊆ e.source) {y : ℕ → X} (hy : ∀ n, y n ∈ U ∧ e (y (n + 1)) = y n) (n : ℕ) :
    e.symm^[n] (y 0) = y n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', ih, ← (hy n).2, e.left_inv (hU (hy (n + 1)).1)]

/-- One half of `localStableSet_symm_eq_localUnstableSet`. -/
private lemma localStableSet_symm_eq_localUnstableSet_aux (e : OpenPartialHomeomorph X X) {p : X}
    {U : Set X} (hU : U ⊆ e.source ∩ e.target) :
    localStableSet e.symm p U = localUnstableSet e p U := by
  ext x
  constructor
  · rintro ⟨hxU, hxt⟩
    exact ⟨fun n ↦ e.symm^[n] x, rfl, fun n ↦ ⟨hxU n,
      apply_iterate_symm_succ e (hU.trans inter_subset_right) hxU n⟩, hxt⟩
  · rintro ⟨y, rfl, hy, hyt⟩
    have hit := iterate_symm_eq_of_backward e (hU.trans inter_subset_left) hy
    exact ⟨fun n ↦ (hit n).symm ▸ (hy n).1, hyt.congr fun n ↦ (hit n).symm⟩

/-- **Unstable for `f` means stable for `f⁻¹`**: for an open partial homeomorphism `e` and a set
`U` inside both its source and its target, the local stable set of `e⁻¹|_U` is the local unstable
set of `e|_U` (a forward `e⁻¹`-orbit in `U` is a backward `e`-orbit, and conversely), and
symmetrically.

Proof: if `y n = e.symm^[n] x ∈ U ⊆ e.target`, then `e (y (n + 1)) = e (e.symm (y n)) = y n`;
conversely, if `e (y (n + 1)) = y n` with `y (n + 1) ∈ U ⊆ e.source`, then
`e.symm (y n) = y (n + 1)`, so `y n = e.symm^[n] x` by induction. -/
theorem localStableSet_symm_eq_localUnstableSet (e : OpenPartialHomeomorph X X) {p : X}
    {U : Set X} (hU : U ⊆ e.source ∩ e.target) :
    localStableSet e.symm p U = localUnstableSet e p U ∧
      localUnstableSet e.symm p U = localStableSet e p U := by
  refine ⟨localStableSet_symm_eq_localUnstableSet_aux e hU, ?_⟩
  have h := localStableSet_symm_eq_localUnstableSet_aux e.symm (p := p)
    (hU.trans (inter_comm _ _).subset)
  rwa [OpenPartialHomeomorph.symm_symm, eq_comm] at h

/-- **A forward `e⁻¹`-orbit is a backward `e`-orbit**: for an open partial homeomorphism `e` and a
set `U` inside both its source and its target, the points whose forward `e⁻¹`-orbit stays in `U`
are the points having a backward `e`-orbit in `U`.

Proof: as for `localStableSet_symm_eq_localUnstableSet`, without the limits: `n ↦ e.symm^[n] x`
is a backward `e`-orbit, and a backward `e`-orbit `y` in `U` is `n ↦ e.symm^[n] (y 0)`. -/
theorem setOf_forall_iterate_symm_mem_eq (e : OpenPartialHomeomorph X X) {U : Set X}
    (hU : U ⊆ e.source ∩ e.target) :
    {x | ∀ n, e.symm^[n] x ∈ U} =
      {x | ∃ y : ℕ → X, y 0 = x ∧ ∀ n, y n ∈ U ∧ e (y (n + 1)) = y n} := by
  ext x
  constructor
  · intro hx
    exact ⟨fun n ↦ e.symm^[n] x, rfl, fun n ↦ ⟨hx n,
      apply_iterate_symm_succ e (hU.trans inter_subset_right) hx n⟩⟩
  · rintro ⟨y, rfl, hy⟩ n
    rw [iterate_symm_eq_of_backward e (hU.trans inter_subset_left) hy n]
    exact (hy n).1

omit [TopologicalSpace X] in
/-- Along an `f`-orbit in `U`, the iterates of `f` and of any `g` equal to `f` on `U` agree. -/
theorem iterate_eq_of_eqOn {f g : X → X} {U : Set X} (h : EqOn f g U) {x : X}
    (hx : ∀ n, f^[n] x ∈ U) (n : ℕ) : f^[n] x = g^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih, h (hx n)]

/-- The local stable set of `f|_U` depends only on the values of `f` on `U`.

Proof: if the `f`-orbit of `x` stays in `U`, then `f^[n] x = g^[n] x` by induction on `n`, so the
`g`-orbit is the same; symmetrically. -/
theorem localStableSet_congr {f g : X → X} {p : X} {U : Set X} (h : EqOn f g U) :
    localStableSet f p U = localStableSet g p U := by
  have key {f g : X → X} (h : EqOn f g U) : localStableSet f p U ⊆ localStableSet g p U := by
    rintro x ⟨hxU, hxt⟩
    have hfg : ∀ n, f^[n] x = g^[n] x := iterate_eq_of_eqOn h hxU
    exact ⟨fun n ↦ hfg n ▸ hxU n, hxt.congr hfg⟩
  exact (key h).antisymm (key h.symm)

/-- The local unstable set of `f|_U` depends only on the values of `f` on `U`.

Proof: a backward orbit `y` in `U` has `f (y (n + 1)) = g (y (n + 1))` since `y (n + 1) ∈ U`. -/
theorem localUnstableSet_congr {f g : X → X} {p : X} {U : Set X} (h : EqOn f g U) :
    localUnstableSet f p U = localUnstableSet g p U := by
  have key {f g : X → X} (h : EqOn f g U) :
      localUnstableSet f p U ⊆ localUnstableSet g p U := by
    rintro x ⟨y, hy0, hy, hyt⟩
    exact ⟨y, hy0, fun n ↦ ⟨(hy n).1, by rw [← h (hy (n + 1)).1, (hy n).2]⟩, hyt⟩
  exact (key h).antisymm (key h.symm)

/-- **Conjugation** carries local stable sets along: for a homeomorphism `e : X ≃ₜ Y`, the local
stable set of `e ∘ f ∘ e⁻¹` at `e p` in `e '' U` is the image by `e` of the local stable set of `f`
at `p` in `U`.

Proof: `(e ∘ f ∘ e.symm)^[n] (e x) = e (f^[n] x)` (`Function.Semiconj.iterate_right`),
`e y ∈ e '' U ↔ y ∈ U`, and `e`, `e.symm` are continuous, so they carry convergent orbits to
convergent orbits. -/
theorem localStableSet_conj {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) (p : X)
    (U : Set X) :
    localStableSet (e ∘ f ∘ e.symm) (e p) (e '' U) = e '' localStableSet f p U := by
  have hit (n : ℕ) (x : X) : (e ∘ f ∘ e.symm)^[n] (e x) = e (f^[n] x) := by
    have hs : Semiconj e f (e ∘ f ∘ e.symm) := fun x ↦ by simp
    exact ((hs.iterate_right n) x).symm
  ext z
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [e.injective.mem_set_image]
  simp only [localStableSet, mem_ofPred_eq, hit, e.injective.mem_set_image]
  refine and_congr Iff.rfl ⟨fun ht ↦ ?_, fun ht ↦ (e.continuous.tendsto p).comp ht⟩
  have := (e.symm.continuous.tendsto (e p)).comp ht
  simpa [Function.comp_def] using this

/-- **Conjugation** carries local unstable sets along: for a homeomorphism `e : X ≃ₜ Y`, the local
unstable set of `e ∘ f ∘ e⁻¹` at `e p` in `e '' U` is the image by `e` of the local unstable set of
`f` at `p` in `U`.

Proof: a backward `f`-orbit `y` in `U` gives the backward orbit `e ∘ y` in `e '' U`, and a backward
`(e ∘ f ∘ e.symm)`-orbit `z` in `e '' U` gives the backward `f`-orbit `e.symm ∘ z` in `U`;
continuity of `e` and `e.symm` carries the limits. -/
theorem localUnstableSet_conj {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) (p : X)
    (U : Set X) :
    localUnstableSet (e ∘ f ∘ e.symm) (e p) (e '' U) = e '' localUnstableSet f p U := by
  ext z
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [e.injective.mem_set_image]
  constructor
  · rintro ⟨w, hw0, hw, hwt⟩
    refine ⟨fun n ↦ e.symm (w n), by simp [hw0], fun n ↦ ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨u, hu, hwu⟩ := (hw n).1
      simpa [← hwu] using hu
    · have h := congrArg e.symm (hw n).2
      simpa using h
    · simpa [Function.comp_def] using (e.symm.continuous.tendsto (e p)).comp hwt
  · rintro ⟨y, hy0, hy, hyt⟩
    refine ⟨fun n ↦ e (y n), by simp [hy0], fun n ↦ ⟨mem_image_of_mem e (hy n).1, ?_⟩,
      (e.continuous.tendsto p).comp hyt⟩
    simp [(hy n).2]

end Function
