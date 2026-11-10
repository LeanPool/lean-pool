/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Additions to the `IsAdic` API

Consequences of `IsAdic I` for a topological ring: the topology is linear, and elements
of `I` are topologically nilpotent. These are the `IsAdic` counterparts of
`Ideal.isLinearTopology` and `WithIdeal.isTopologicallyNilpotent_of_mem`. Being adic
transfers between cofinal ideals (`IsAdic.of_le_of_pow_le`, `IsAdic.of_pow`).
-/

@[expose] public section

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R}

/-- A ring with the `I`-adic topology is linearly topologized. -/
theorem IsAdic.isLinearTopology (hI : IsAdic I) : IsLinearTopology R R :=
  IsLinearTopology.mk_of_hasBasis _ hI.hasBasis_nhds_zero

/-- A ring with an adic topology is nonarchimedean. -/
theorem IsAdic.nonarchimedeanRing (hI : IsAdic I) : NonarchimedeanRing R := by
  simp only [IsAdic] at hI
  subst hI
  exact I.nonarchimedean

/-- In a ring with the `I`-adic topology, the powers of `I` are open. -/
theorem IsAdic.isOpen_pow (hI : IsAdic I) (n : ℕ) :
    IsOpen ((I ^ n : Ideal R) : Set R) := by
  simp only [IsAdic] at hI
  subst hI
  let : TopologicalSpace R := I.adicTopology
  exact (I.openAddSubgroup n).isOpen'

/-- In a ring with the `I`-adic topology, the powers of `I` are closed. -/
theorem IsAdic.isClosed_pow (hI : IsAdic I) (n : ℕ) :
    IsClosed ((I ^ n : Ideal R) : Set R) := by
  have hopen := hI.isOpen_pow n
  simp only [IsAdic] at hI
  subst hI
  let : TopologicalSpace R := I.adicTopology
  have : NonarchimedeanRing R := I.nonarchimedean
  exact AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen

/-- In a ring with the `I`-adic topology, elements of `I` are topologically nilpotent. -/
theorem IsAdic.isTopologicallyNilpotent_of_mem (hI : IsAdic I) {a : R} (ha : a ∈ I) :
    IsTopologicallyNilpotent a := by
  suffices ∀ m : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → a ^ n ∈ I ^ m by
    simpa [IsTopologicallyNilpotent, hI.hasBasis_nhds_zero.tendsto_right_iff]
  exact fun m ↦ ⟨m, fun n hn ↦ Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha _)⟩

open Filter Topology in
/-- In an `I`-adic ring, a family lying in growing powers of `I` (the exponents tending to
`∞`) tends to `0`. -/
theorem IsAdic.tendsto_zero_of_mem_pow (hI : IsAdic I) {γ : Type*} {l : Filter γ}
    {g : γ → R} {e : γ → ℕ} (hg : ∀ i, g i ∈ I ^ e i) (he : Tendsto e l atTop) :
    Tendsto g l (𝓝 0) := by
  rw [hI.hasBasis_nhds_zero.tendsto_right_iff]
  intro k _
  filter_upwards [he.eventually_ge_atTop k] with i hi
  exact Ideal.pow_le_pow_right hi (hg i)

/-- Being adic transfers between ideals squeezed between powers of each other: if `I ≤ J` and
`J ^ e ≤ I`, the `I`-adic topology is also the `J`-adic one. -/
theorem IsAdic.of_le_of_pow_le (hI : IsAdic I) {J : Ideal R} {e : ℕ} (hIJ : I ≤ J)
    (hJI : J ^ e ≤ I) : IsAdic J := by
  have := hI.nonarchimedeanRing
  rw [isAdic_iff] at hI ⊢
  refine ⟨fun n ↦ Submodule.isOpen_mono (Ideal.pow_right_mono hIJ n) (hI.1 n), fun s hs ↦ ?_⟩
  obtain ⟨n, hn⟩ := hI.2 s hs
  refine ⟨e * n, Set.Subset.trans ?_ hn⟩
  rw [pow_mul]
  exact Ideal.pow_right_mono hJI n

/-- The `J ^ e`-adic topology is the `J`-adic one (the filtrations are cofinal). -/
theorem IsAdic.of_pow {J : Ideal R} {e : ℕ} (he : 0 < e) (h : IsAdic (J ^ e)) : IsAdic J :=
  h.of_le_of_pow_le (Ideal.pow_le_self he.ne') le_rfl

end
