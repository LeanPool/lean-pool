/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.ValueIdeal
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Data.Finset.Order

/-!
# Direct limits of LG-rings

`GN 2.2` (from `EG`): a filtered colimit of LG-rings is an LG-ring.

## Main results

* `MvPolynomial.representsUnit_of_map_of_valueIdeal_eq_top` : the transfer principle. If `p` comes
  from a polynomial `q` over an LG-ring `A` along a ring map `A → R`, and `q.valueIdeal = ⊤`, then
  `p` represents a unit over `R`. Both examples below are this lemma plus the work of producing
  such a `q`.
* `isLGRing_of_directed_subring` : a ring that is the directed union of a family of LG subrings is
  an LG-ring.
* `isLGRing_directLimit` : **`GN 2.2`**, the direct limit of a directed system of LG-rings is an
  LG-ring.

## Proof idea

Everything rests on the *finitary* form of the LG axiom from `LGRing/ValueIdeal.lean`: `R` is LG
iff `p` represents a unit over `R` whenever the values of `p` generate the unit ideal, and that
hypothesis unwinds to one equation

  `1 = Σⱼ cⱼ · p(tⱼ)`

in finitely many elements of `R`. A finitary condition is exactly what survives passage to a
filtered colimit: the coefficients of `p`, the `cⱼ` and the coordinates of the `tⱼ` are finitely
many elements of `R = colim Gᵢ`, so all of them already live in a single `G_M`; and the equation
between them, being a single equation, already holds in some `G_N` with `M ≤ N`. Then `G_N` is LG,
so the lifted polynomial takes a unit value there, and that unit maps forward to a unit of `R`.

Note where the argument would break with the *definitional* form of the LG axiom: a maximal ideal
of `G_N` need not be the contraction of any maximal ideal of `R` (take `ℤ ⊆ ℚ`), so there is no way
to feed the residue fields of `R` back into the residue fields of the components. Passing through
the value ideal removes maximal ideals from the argument entirely, which is the whole point.

## References

* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Example 2.2.
* [EG] Estes, Guralnick, *Module equivalences: local to global when primitive polynomials represent
  units*, Journal of Algebra **77** (1982), 138–157.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {A : Type u} [CommRing A] {R : Type v} [CommRing R] {n k : ℕ}

/-- A ring map carries a linear combination of values of `q` to the corresponding combination of
values of the reduced polynomial `map φ q`. This is the only computation the two examples share:
in `isLGRing_of_directed_subring` it is used with an injective `φ`, and in `isLGRing_directLimit`
with the structure map of a component. -/
theorem map_sum_mul_aeval (φ : A →+* R) (q : MvPolynomial (Fin n) A) (c : Fin k → A)
    (t : Fin k → Fin n → A) :
    φ (∑ j, c j * aeval (t j) q)
      = ∑ j, φ (c j) * aeval (fun x ↦ φ (t j x)) (MvPolynomial.map φ q) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, aeval_map_comm φ φ (by ext x; simp) (t j) q]

/-- **Transfer along a ring map out of an LG-ring.** If `p` is the reduction of a polynomial `q`
over an LG-ring `A`, and the values of `q` already generate the unit ideal of `A`, then `p`
represents a unit over `R`.

Only the *hypothesis* of the LG axiom has to be checked over `A`; the conclusion transports for
free, since ring maps preserve units. -/
theorem representsUnit_of_map_of_valueIdeal_eq_top (φ : A →+* R) (hA : IsLGRing A)
    {q : MvPolynomial (Fin n) A} {p : MvPolynomial (Fin n) R} (hq : MvPolynomial.map φ q = p)
    (htop : q.valueIdeal = ⊤) : p.RepresentsUnit R := by
  obtain ⟨s, hs⟩ := (isLGRing_iff_forall_valueIdeal_eq_top A).mp hA n q htop
  refine ⟨fun x ↦ φ (s x), ?_⟩
  rw [← hq, aeval_map_comm φ φ (by ext x; simp) s q]
  exact hs.map φ

end MvPolynomial

/-! ### Directed unions -/

/-- **A directed union of LG subrings is an LG-ring.**

Given `1 = Σⱼ cⱼ · p(tⱼ)`, the coefficients of `p` together with the `cⱼ` and the coordinates of
the `tⱼ` form a finite subset of `R`, so directedness places all of them inside a single `S z`.
There the equation holds verbatim — `S z → R` is injective — so the lifted polynomial has value
ideal `⊤`, and `S z` being LG finishes it. -/
theorem isLGRing_of_directed_subring {R : Type u} [CommRing R] {ι : Type v} [Nonempty ι]
    (S : ι → Subring R) (hdir : Directed (· ≤ ·) S) (hcov : ∀ x : R, ∃ i, x ∈ S i)
    (hLG : ∀ i, IsLGRing (S i)) : IsLGRing R := by
  classical
  rw [isLGRing_iff_forall_valueIdeal_eq_top]
  intro n p htop
  obtain ⟨k, c, t, hsum⟩ := MvPolynomial.exists_sum_mul_aeval_eq_one htop
  choose idx hidx using hcov
  set F : Finset R := p.coeffs ∪ Finset.image c Finset.univ ∪
    Finset.image (fun a : Fin k × Fin n ↦ t a.1 a.2) Finset.univ with hF
  obtain ⟨z, hz⟩ := hdir.finset_le (F.image idx)
  have hmem : ∀ x ∈ F, x ∈ S z := fun x hx ↦
    hz (idx x) (Finset.mem_image_of_mem idx hx) (hidx x)
  have hcoeff : ∀ x ∈ (p.coeffs : Set R), x ∈ S z := fun x hx ↦
    hmem x (Finset.mem_union_left _ (Finset.mem_union_left _ (by exact_mod_cast hx)))
  have hc : ∀ j, c j ∈ S z := fun j ↦
    hmem _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem c (Finset.mem_univ j))))
  have ht : ∀ j x, t j x ∈ S z := fun j x ↦
    hmem _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(j, x), Finset.mem_univ _, rfl⟩))
  obtain ⟨q, hq⟩ : p ∈ Set.range (MvPolynomial.map (S z).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    exact fun x hx ↦ ⟨⟨x, hcoeff x hx⟩, rfl⟩
  refine MvPolynomial.representsUnit_of_map_of_valueIdeal_eq_top (S z).subtype (hLG z) hq
    (MvPolynomial.valueIdeal_eq_top_of_sum_mul_aeval_eq_one (fun j ↦ ⟨c j, hc j⟩)
      (fun j x ↦ ⟨t j x, ht j x⟩) ?_)
  have key := MvPolynomial.map_sum_mul_aeval (S z).subtype q (fun j ↦ (⟨c j, hc j⟩ : S z))
    (fun j x ↦ (⟨t j x, ht j x⟩ : S z))
  rw [hq] at key
  exact Subtype.coe_injective (key.trans hsum)

/-! ### Direct limits -/

/-- **`GN 2.2`: a direct limit of LG-rings is an LG-ring.**

The finitely many elements of `colim Gᵢ` appearing in `1 = Σⱼ cⱼ · p(tⱼ)` all come from a single
component `G_M` (`Ring.DirectLimit.exists_of`, plus directedness of `ι` to merge the finitely many
indices), which lets `p` be lifted to `q` over `G_M`. The lifted equation need not hold in `G_M`
itself — only its image in the colimit is known to be `1` — but the discrepancy dies somewhere
along the system (`Ring.DirectLimit.of.zero_exact`), so it does hold in `G_N` for some `N ≥ M`.
Then `G_N` is LG and `MvPolynomial.representsUnit_of_map_of_valueIdeal_eq_top` applies to
`of G _ N`. -/
theorem isLGRing_directLimit {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type u) [∀ i, CommRing (G i)] (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h ↦ f i j h] (hLG : ∀ i, IsLGRing (G i)) :
    IsLGRing (Ring.DirectLimit G (f · · ·)) := by
  classical
  rw [isLGRing_iff_forall_valueIdeal_eq_top]
  intro n p htop
  obtain ⟨k, c, t, hsum⟩ := MvPolynomial.exists_sum_mul_aeval_eq_one htop
  choose idx elt helt using fun z : Ring.DirectLimit G (f · · ·) ↦
    Ring.DirectLimit.exists_of (G := G) (f := (f · · ·)) z
  set F : Finset (Ring.DirectLimit G (f · · ·)) := p.coeffs ∪ Finset.image c Finset.univ ∪
    Finset.image (fun a : Fin k × Fin n ↦ t a.1 a.2) Finset.univ with hF
  obtain ⟨M, hM⟩ := (F.image idx).exists_le
  have hrange : ∀ x ∈ F, ∃ y : G M, Ring.DirectLimit.of G (f · · ·) M y = x := fun x hx ↦
    ⟨f (idx x) M (hM _ (Finset.mem_image_of_mem idx hx)) (elt x),
      (Ring.DirectLimit.of_f _ _).trans (helt x)⟩
  choose lift hlift using hrange
  obtain ⟨q, hq⟩ :
      p ∈ Set.range (MvPolynomial.map (Ring.DirectLimit.of G (f · · ·) M)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    exact fun x hx ↦ ⟨lift x (Finset.mem_union_left _
      (Finset.mem_union_left _ (by exact_mod_cast hx))), hlift x _⟩
  set c' : Fin k → G M := fun j ↦ lift (c j) (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem c (Finset.mem_univ j)))) with hc'
  set t' : Fin k → Fin n → G M := fun j x ↦ lift (t j x)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(j, x), Finset.mem_univ _, rfl⟩)) with ht'
  -- the lifted equation holds in the colimit …
  have hM0 : Ring.DirectLimit.of G (f · · ·) M
      ((∑ j, c' j * MvPolynomial.aeval (t' j) q) - 1) = 0 := by
    rw [map_sub, map_one, MvPolynomial.map_sum_mul_aeval, hq, sub_eq_zero]
    simp only [hc', ht', hlift]
    exact hsum
  -- … hence already in some component `G N`
  obtain ⟨N, hMN, hN⟩ := Ring.DirectLimit.of.zero_exact (f' := f) hM0
  refine MvPolynomial.representsUnit_of_map_of_valueIdeal_eq_top
    (Ring.DirectLimit.of G (f · · ·) N) (hLG N) (q := MvPolynomial.map (f M N hMN) q) ?_
    (MvPolynomial.valueIdeal_eq_top_of_sum_mul_aeval_eq_one (fun j ↦ f M N hMN (c' j))
      (fun j x ↦ f M N hMN (t' j x)) ?_)
  · rw [MvPolynomial.map_map, ← hq]
    exact congrArg (MvPolynomial.map · q) (RingHom.ext fun x ↦ Ring.DirectLimit.of_f _ _)
  · rw [← MvPolynomial.map_sum_mul_aeval, ← sub_eq_zero, ← map_one (f M N hMN), ← map_sub]
    exact hN
