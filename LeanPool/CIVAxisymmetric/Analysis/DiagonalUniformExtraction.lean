/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Diagonal extraction for uniform convergence with values in a uniform space

A countable family of sets `S j` and a sequence `f : ℕ → X → α` are given, together with the
ability to refine any subsequence into a further subsequence that converges uniformly on a
prescribed `S j`.  A single subsequence then converges uniformly on every `S j`, with one limit
function shared by all of them.

The limit is recovered as the pointwise limit of the diagonal subsequence, which is where the
Hausdorff hypothesis on the target enters: the uniform limits produced on the separate sets `S j`
agree wherever they overlap because each of them is the pointwise limit of the same sequence.

The target is any Hausdorff uniform space, so the statement applies to real-valued families, to
families of continuous linear maps, and to tuples of both — the combination needed to extract a
`C¹` limit of a sequence of functions together with its derivative along one subsequence.
-/

public section

open Filter Topology

namespace CIV

/-- Diagonal extraction over a countable family of sets, for values in a Hausdorff uniform
space: if from every subsequence one can extract a further subsequence converging uniformly on
`S j`, then a single subsequence converges uniformly on every `S j`, with one limit function. -/
theorem exists_subseq_tendstoUniformlyOn_forall_of_subseq {X α : Type*} [UniformSpace α]
    [T2Space α] [Nonempty α] (S : ℕ → Set X) (f : ℕ → X → α)
    (hstep : ∀ (j : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : X → α,
        TendstoUniformlyOn (fun n => f (g (g' n))) w atTop (S j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : X → α,
      ∀ j, TendstoUniformlyOn (fun n => f (φ n)) w atTop (S j) := by
  classical
  have hstep' : ∀ (j : ℕ) (g : {h : ℕ → ℕ // StrictMono h}),
      ∃ g' : {h : ℕ → ℕ // StrictMono h}, ∃ w : X → α,
        TendstoUniformlyOn (fun n => f (g.1 (g'.1 n))) w atTop (S j) := by
    intro j g
    obtain ⟨g', hg', w, hw⟩ := hstep j g.1 g.2
    exact ⟨⟨g', hg'⟩, w, hw⟩
  choose rho w hw using hstep'
  obtain ⟨Psi, hPsisucc⟩ :
      ∃ P : ℕ → {h : ℕ → ℕ // StrictMono h},
        ∀ k, (P (k + 1)).1 = (P k).1 ∘ (rho k (P k)).1 :=
    ⟨fun j => Nat.rec (motive := fun _ => {h : ℕ → ℕ // StrictMono h})
      ⟨fun n => n, strictMono_id⟩
      (fun k p => ⟨p.1 ∘ (rho k p).1, p.2.comp (rho k p).2⟩) j, fun _ => rfl⟩
  have hconv : ∀ j,
      TendstoUniformlyOn (fun n => f ((Psi (j + 1)).1 n)) (w j (Psi j)) atTop (S j) := by
    intro j
    have h := hw j (Psi j)
    have heq : (fun n => f ((Psi (j + 1)).1 n))
        = fun n => f ((Psi j).1 ((rho j (Psi j)).1 n)) := by
      funext n
      rw [hPsisucc j]
      rfl
    rw [heq]
    exact h
  have hnest : ∀ j m, j ≤ m → ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ n, (Psi (m + 1)).1 n = (Psi (j + 1)).1 (κ n) := by
    intro j m hjm
    induction m, hjm using Nat.le_induction with
    | base => exact ⟨fun n => n, strictMono_id, fun _ => rfl⟩
    | succ m hm ih =>
        obtain ⟨κ, hκ, hκeq⟩ := ih
        refine ⟨fun n => κ ((rho (m + 1) (Psi (m + 1))).1 n),
          hκ.comp (rho (m + 1) (Psi (m + 1))).2, fun n => ?_⟩
        rw [hPsisucc (m + 1)]
        exact hκeq _
  have hφmono : StrictMono (fun n => (Psi (n + 1)).1 n) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have h1 : (Psi (n + 1 + 1)).1 (n + 1)
        = (Psi (n + 1)).1 ((rho (n + 1) (Psi (n + 1))).1 (n + 1)) := by
      rw [hPsisucc (n + 1)]
      rfl
    have h2 : n + 1 ≤ (rho (n + 1) (Psi (n + 1))).1 (n + 1) :=
      (rho (n + 1) (Psi (n + 1))).2.le_apply
    have h3 : (Psi (n + 1)).1 (n + 1)
        ≤ (Psi (n + 1)).1 ((rho (n + 1) (Psi (n + 1))).1 (n + 1)) := (Psi (n + 1)).2.monotone h2
    have h4 : (Psi (n + 1)).1 n < (Psi (n + 1)).1 (n + 1) :=
      (Psi (n + 1)).2 (Nat.lt_succ_self n)
    show (Psi (n + 1)).1 n < (Psi (n + 1 + 1)).1 (n + 1)
    rw [h1]
    exact lt_of_lt_of_le h4 h3
  refine ⟨fun n => (Psi (n + 1)).1 n, hφmono,
    fun x => limUnder atTop fun n => f ((Psi (n + 1)).1 n) x, fun j => ?_⟩
  have hmain : TendstoUniformlyOn (fun n => f ((Psi (n + 1)).1 n)) (w j (Psi j)) atTop (S j) := by
    intro u hu
    have h := hconv j u hu
    rw [eventually_atTop] at h ⊢
    obtain ⟨N, hN⟩ := h
    refine ⟨max N j, fun n hn => ?_⟩
    obtain ⟨κ, hκ, hκeq⟩ := hnest j n (le_trans (le_max_right N j) hn)
    have hκn : n ≤ κ n := hκ.le_apply
    have hNn : N ≤ κ n := le_trans (le_trans (le_max_left N j) hn) hκn
    have hstepN := hN (κ n) hNn
    intro x hx
    have h2 := hstepN x hx
    show (w j (Psi j) x, f ((Psi (n + 1)).1 n) x) ∈ u
    rw [hκeq n]
    exact h2
  refine hmain.congr_right fun x hx => ?_
  have hpt : Tendsto (fun n => f ((Psi (n + 1)).1 n) x) atTop (𝓝 (w j (Psi j) x)) :=
    hmain.tendsto_at hx
  exact hpt.limUnder_eq.symm

end CIV
