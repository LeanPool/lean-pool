/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.Cartographic
public import Mathlib.GroupTheory.Coxeter.Length

/-!
# Orientability in the cartographic group

The even part of the monodromy group of a flag system (`GMap.evenMonodromy`) is the image under
the monodromy homomorphism of the kernel of the length parity of the cartographic group: the
products of an even number of the involutions `adj i`.

A nonempty connected flag system in which no dart is fixed by any `adj i` is orientable exactly
when the even part of its monodromy group is not transitive on flags
(`GMap.isOrientable_iff_not_isPretransitive_evenMonodromy'`); in rank `2` this applies to
connected closed-surface maps (`GMap.isOrientable_iff_not_isPretransitive_evenMonodromy`).

## References

* S. Wilson, *Maniplexes: Part 1: maps, polytopes, symmetry and operators*, Symmetry 4 (2012),
  265–275, §5, p. 270.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv

namespace GMap

variable {n : ℕ} {D : Type*}

/-- The length parity of the cartographic group, read additively in `ZMod 2`. -/
noncomputable def parity (w : cartographicGroup n) : ZMod 2 :=
  Multiplicative.toAdd ((cartographicMatrix n).toCoxeterSystem.lengthParity w)

theorem parity_simple_mul (i : Fin (n + 1)) (w : cartographicGroup n) :
    parity ((cartographicMatrix n).simple i * w) = 1 + parity w := by
  rw [parity, parity, map_mul, toAdd_mul,
    show (cartographicMatrix n).simple i = (cartographicMatrix n).toCoxeterSystem.simple i from rfl,
    CoxeterSystem.lengthParity_simple, toAdd_ofAdd]

theorem parity_one : parity (1 : cartographicGroup n) = 0 := by simp [parity]

theorem mem_ker_lengthParity_iff (w : cartographicGroup n) :
    w ∈ (cartographicMatrix n).toCoxeterSystem.lengthParity.ker ↔ parity w = 0 := by
  rw [MonoidHom.mem_ker, parity, toAdd_eq_zero]

/-- The even part of the monodromy group: the image of the kernel of the length parity. -/
noncomputable def evenMonodromy (G : GMap n D) : Subgroup (Perm D) :=
  (cartographicMatrix n).toCoxeterSystem.lengthParity.ker.map G.monodromyHom

variable (G : GMap n D)

private theorem fin_two_eq_add_one_of_ne {a b : Fin 2} (h : a ≠ b) :
    ((b : ℕ) : ZMod 2) = ((a : ℕ) : ZMod 2) + 1 := by
  revert a b; decide

/-- Along a two-colouring, the colour of the image of a flag changes by the parity. -/
private theorem coloring_monodromyHom (hfix : ∀ i d, G.adj i d ≠ d)
    (C : G.flagGraph.Coloring (Fin 2)) (w : cartographicGroup n) (d : D) :
    ((C (G.monodromyHom w d) : ℕ) : ZMod 2) = ((C d : ℕ) : ZMod 2) + parity w := by
  induction w using (cartographicMatrix n).toCoxeterSystem.simple_induction_left
    generalizing d with
  | one => simp [parity_one]
  | mul_simple_left w i ih =>
    rw [CoxeterMatrix.toCoxeterSystem_simple, map_mul, Perm.mul_apply, monodromyHom_simple,
      parity_simple_mul]
    have hadj : G.flagGraph.Adj (G.monodromyHom w d) (G.adj i (G.monodromyHom w d)) :=
      ⟨(hfix i _).symm, i, rfl⟩
    rw [fin_two_eq_add_one_of_ne (C.valid hadj), ih]
    ring

/-- A nonempty connected flag system without fixed darts is orientable iff the even part of its
monodromy group is not transitive on flags. -/
theorem isOrientable_iff_not_isPretransitive_evenMonodromy' [Nonempty D] (hG : G.IsConnected)
    (hfix : ∀ i d, G.adj i d ≠ d) :
    G.IsOrientable ↔ ¬ MulAction.IsPretransitive G.evenMonodromy D := by
  classical
  obtain ⟨d₀⟩ := ‹Nonempty D›
  set K := (cartographicMatrix n).toCoxeterSystem.lengthParity.ker
  have hconn := (G.isConnected_iff_exists_monodromyHom).1 hG
  constructor
  · rintro ⟨C⟩ ⟨htr⟩
    obtain ⟨⟨g, w, hw, rfl⟩, hg⟩ := htr d₀ (G.adj 0 d₀)
    have h1 := G.coloring_monodromyHom hfix C w d₀
    rw [(mem_ker_lengthParity_iff w).1 hw, add_zero] at h1
    change G.monodromyHom w d₀ = G.adj 0 d₀ at hg
    have hadj : G.flagGraph.Adj d₀ (G.adj 0 d₀) := ⟨(hfix 0 d₀).symm, 0, rfl⟩
    rw [hg, fin_two_eq_add_one_of_ne (C.valid hadj)] at h1
    exact absurd h1 (by simp)
  · intro hnot
    -- the even orbit of `d₀`
    set O : Set D := {d | ∃ w ∈ K, G.monodromyHom w d₀ = d}
    have hpar : ∀ w : cartographicGroup n, w ∉ K → ∀ i,
        (cartographicMatrix n).simple i * w ∈ K := by
      intro w hw i
      rw [mem_ker_lengthParity_iff] at hw ⊢
      rw [parity_simple_mul]
      generalize parity w = x at hw ⊢
      revert x; decide
    have hout : ∀ d i, d ∉ O → G.adj i d ∈ O := by
      intro d i hd
      obtain ⟨w, rfl⟩ := hconn d₀ d
      have hw : w ∉ K := fun hw => hd ⟨w, hw, rfl⟩
      exact ⟨(cartographicMatrix n).simple i * w, hpar w hw i,
        by rw [map_mul, Perm.mul_apply, monodromyHom_simple]⟩
    -- if a flag and a neighbour are both even, the even part is transitive
    have hboth : ∀ d i, d ∈ O → G.adj i d ∈ O → False := by
      rintro d i ⟨w, hw, rfl⟩ ⟨w', hw', hw'eq⟩
      set u := w'⁻¹ * ((cartographicMatrix n).simple i * w)
      have hu : u ∉ K := by
        intro hu
        have : (cartographicMatrix n).simple i * w ∈ K := by
          have := K.mul_mem hw' hu
          rwa [mul_inv_cancel_left] at this
        have h1 := (mem_ker_lengthParity_iff _).1 this
        have h2 := (mem_ker_lengthParity_iff _).1 hw
        rw [parity_simple_mul, h2] at h1
        exact absurd h1 (by decide)
      have hufix : G.monodromyHom u d₀ = d₀ := by
        simp only [u, map_mul, map_inv, Perm.mul_apply, monodromyHom_simple]
        rw [← hw'eq]
        exact perm_inv_apply_self _ _
      have hall : ∀ e, e ∈ O := by
        intro e
        by_contra he
        obtain ⟨v, rfl⟩ := hconn d₀ e
        have hv : v ∉ K := fun hv => he ⟨v, hv, rfl⟩
        refine he ⟨v * u, ?_, by rw [map_mul, Perm.mul_apply, hufix]⟩
        rw [mem_ker_lengthParity_iff]
        have h1 := (mem_ker_lengthParity_iff v).not.1 hv
        have h2 := (mem_ker_lengthParity_iff u).not.1 hu
        simp only [parity, map_mul, toAdd_mul] at h1 h2 ⊢
        generalize Multiplicative.toAdd _ = x at h1 ⊢
        generalize Multiplicative.toAdd _ = y at h2 ⊢
        revert x y; decide
      apply hnot
      refine ⟨fun e e' => ?_⟩
      obtain ⟨a, ha, rfl⟩ := hall e
      obtain ⟨b, hb, rfl⟩ := hall e'
      refine ⟨⟨G.monodromyHom (b * a⁻¹), b * a⁻¹, K.mul_mem hb (K.inv_mem ha), rfl⟩, ?_⟩
      change G.monodromyHom (b * a⁻¹) (G.monodromyHom a d₀) = G.monodromyHom b d₀
      rw [← Perm.mul_apply, ← map_mul, inv_mul_cancel_right]
    refine ⟨SimpleGraph.Coloring.mk (fun d => if d ∈ O then 0 else 1) fun {d e} hde => ?_⟩
    obtain ⟨_, i, rfl⟩ := hde
    by_cases hd : d ∈ O
    · have he : G.adj i d ∉ O := fun he => hboth d i hd he
      simp [hd, he]
    · simp [hd, hout d i hd]

/-- A nonempty connected closed-surface map is orientable iff the even part of its monodromy
group is not transitive on flags. -/
theorem isOrientable_iff_not_isPretransitive_evenMonodromy [Nonempty D] (G : GMap2 D)
    (hG : G.IsConnected) (hS : G.IsClosedSurface) :
    G.IsOrientable ↔ ¬ MulAction.IsPretransitive G.evenMonodromy D :=
  G.isOrientable_iff_not_isPretransitive_evenMonodromy' hG hS.1

end GMap

end LeanPool.PseudolineArrangements
