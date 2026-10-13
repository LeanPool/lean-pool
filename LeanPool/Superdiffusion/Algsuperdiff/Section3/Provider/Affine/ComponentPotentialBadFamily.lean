/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.ComponentPotential
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.GlobalSuperposition

/-!
# ComponentPotentialBadFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Zero-trace potential for an actual bad-family component

This file specializes the generic finite-root-mesh potential theorem to one
component of the Section 3 bad family.  All window hypotheses are discharged
by `badComponents_window_badFamily`, and the standing nonzero-dimension
instance is derived internally from the model.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport Set
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-- One actual bad component supplies a public zero-trace potential field.
The `[NeZero d]` instance used by the finite Kuhn analysis is derived from the
model's standing dimension assumption and is not a theorem binder. -/
theorem potentialZeroTraceFieldOn_globalCompetitorSlope_sub_badComponent
    {M : ABKModel d} {m : ℤ} {E b : ℝ} {k₀ : ℕ}
    {omega : Cutoff.CutoffSample d} (hb0 : 0 < b) (hb : b ≤ 1 / 8)
    (hk₀ : 3 ≤ k₀) (hne : (hsepSet M m E b omega).Nonempty)
    {C : Set (TriadicCube d)}
    (hCmem : C ∈ badComponents
      (badFamily M m (whitneyScale M m E b k₀ omega) omega))
    (p : Vec d) :
    HCPolySupport.Book.Ch01.PotentialZeroTraceFieldOn
      (openCubeSet (originCube d m))
      (fun x => globalCompetitorSlope m
        (simplexScale m (whitneyScale M m E b k₀ omega)
          (componentWindowLayer m (whitneyScale M m E b k₀ omega) C)) C p x - p) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let hn : ℕ → ℕ := whitneyScale M m E b k₀ omega
  let I : Set (TriadicCube d) := badFamily M m hn omega
  have hwindow := badComponents_window_badFamily hb0 hb hk₀ hne C hCmem
  let N : Finset (TriadicCube d) := hwindow.1.toFinset
  have hmono : Monotone hn := by
    change Monotone (whitneyScaleSeq b (hsep M m E b omega) k₀)
    exact whitneyScaleSeq_mono hb0.le (by linarith) _ _
  have hCsub : C ⊆ whitneyPartition m hn :=
    (badComponents_subset hCmem).trans fun _ hQ => hQ.1
  have hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn := by
    intro Q hQ
    exact (Set.Finite.mem_toFinset hwindow.1).mp hQ |>.1
  have hN : ∀ Q ∈ whitneyPartition m hn,
      (∃ R ∈ C, CubeTouch Q R) → Q ∈ N := by
    intro Q hQ hex
    exact (Set.Finite.mem_toFinset hwindow.1).mpr ⟨hQ, hex⟩
  have hNlayer : ∀ Q ∈ N, ∀ n : ℕ, Q ∈ whitneyLayer m hn n →
      n = componentWindowLayer m hn C ∨ n = componentWindowLayer m hn C + 1 := by
    intro Q hQ n hQn
    have hQwindow : Q ∈ whitneyNeighborhood m hn C :=
      (Set.Finite.mem_toFinset hwindow.1).mp hQ
    rcases hwindow.2 Q hQwindow with hQj | hQj
    · exact Or.inl (whitneyLayer_index_unique hmono hQn hQj)
    · exact Or.inr (whitneyLayer_index_unique hmono hQn hQj)
  have hs : ∀ Q ∈ N,
      simplexScale m hn (componentWindowLayer m hn C) ≤ Q.scale :=
    simplexScale_le_scale_of_mem_window (step_of_monotone hmono) hNsub hNlayer
  simpa only [hn] using
    potentialZeroTraceFieldOn_globalCompetitorSlope_sub
      (simplexScale_le_self m hn (componentWindowLayer m hn C))
      hCsub hNsub hN hs p

end

end Algsuperdiff.Section3.Provider.Affine
