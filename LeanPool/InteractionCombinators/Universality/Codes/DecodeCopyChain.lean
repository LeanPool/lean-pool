/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Codes.DecodeCopy

/-!
# The chain `C_{p_{i,j}}` → `C_2` → `D` of Fig. 10 (pages 89 and 90)

In Fig. 10 (page 89, the translation `⟨α_k⟩`) the code `!Γ` reaches the decoder `D` only after
two copiers. `C_{p_{i,j}}` in `Γ_{i,j}` makes a copy, and `C_2` in `⟨α_k⟩` copies that copy again.

These two lemmas were first proved in the review of issue #105 (`DecodeCopyReview.lean`).

Contents, in the order of the file:

1. Auxiliary lemma: `copy_of_copy`, a copy of a copy is still of the form
   `(code k π).bind (var ∘ f)` with `f` injective on the names of the code.
2. Main result: `copier_decoder_copy`, which chains `C_2` (`copier_package`) with
   `code_decoder_copy`, with every hypothesis taken from the first copier.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Auxiliary lemma: a copy of a copy
-- ============================================================================================

/-- A copy of a copy is a copy (page 89, Fig. 10: `!Γ` passes through `C_{p_{i,j}}`, then `C_2`).
Renaming `t` by `f`, injective on the names of `t`, and then by `g`, injective on the names of the
renamed tree, is renaming `t` by `g ∘ f`, which is injective on the names of `t`. -/
theorem copy_of_copy
    -- the tree
    (t : Term sig ℕ)
    -- the two renamings, `f` applied first
    (f g : ℕ → ℕ)
    -- `f` is injective on the names of the tree
    (hf : Set.InjOn f {x | x ∈ t.vars})
    -- `g` is injective on the names of the renamed tree
    (hg : Set.InjOn g {x | x ∈ (t.bind fun x => var (f x)).vars}) :
    -- renaming by `f`, then by `g`, is renaming by `g ∘ f`,
    ((t.bind fun x => var (f x)).bind fun x => var (g x)) = t.bind (fun x => var (g (f x))) ∧
      -- and `g ∘ f` is injective on the names of the tree
      Set.InjOn (fun x => g (f x)) {x | x ∈ t.vars} := by
  refine ⟨?_, fun x hx y hy h => hf hx hy (hg ?_ ?_ h)⟩
  · rw [Term.bind_bind]
    exact Term.bind_congr fun x _ => by rw [Term.bind_var]
  · change f x ∈ (t.bind fun x => var (f x)).vars
    rw [INet.Comb.vars_bind_var]; exact Multiset.mem_map_of_mem f hx
  · change f y ∈ (t.bind fun x => var (f x)).vars
    rw [INet.Comb.vars_bind_var]; exact Multiset.mem_map_of_mem f hy

-- ============================================================================================
-- 2. Main result: a copy of the code through `C_2` and the decoder
-- ============================================================================================

/-- **The translation `⟨α_k⟩` of Fig. 10 (page 89) against a copy of `!Γ`, then the extraction of
page 90.** A copy `(code k π).bind (var ∘ f)`, as `copier_code` leaves it (`f` injective on the
names of the code), meets the copier `C_2` whose first auxiliary port carries the decoder `D`
(free port `w`, loop `k₀, k₀ + 1`) and whose second carries `u` (the extra port of `⟨α_k⟩`). This
reduces, in any context `Δ`, to a net that is `Equiv` to the package `π` renamed by some injective
`g` on `w`, next to a new copy of the code on `u`. The only hypotheses are those of
`copier_code`, together with `f` and linearity. -/
theorem copier_decoder_copy
    -- the package: every name occurs twice
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    -- the first new name of the code: every name of the package is below `k`
    (k : ℕ)
    (hb : π.Below k)
    -- the renaming of the copy of the code, injective on the names of the code
    (f : ℕ → ℕ)
    (hf : Set.InjOn f {x | x ∈ (code k π).vars})
    -- the free port `w` of the decoder and the first name `k₀` of its loop
    (w k₀ : ℕ)
    -- the tree on the second auxiliary port of `C_2`
    (u : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the copy of the code on the root of `C_2`, and `Δ`
    (hlin : Net.Linear
      (s(copier [decoder w k₀, u], (code k π).bind (fun x => var (f x))) ::ₘ Δ)) :
    -- there are two renamings `g`, `g'` and a net `M` such that
    ∃ (g g' : ℕ → ℕ) (M : CNet),
      -- `g` is injective on the names of the code,
      Set.InjOn g {x | x ∈ (code k π).vars} ∧
      -- `g'` is injective on the names of the code,
      Set.InjOn g' {x | x ∈ (code k π).vars} ∧
      -- the net reduces, up to wires, to `M`,
      StepsE system
        (s(copier [decoder w k₀, u], (code k π).bind (fun x => var (f x))) ::ₘ Δ) M ∧
      -- and `M` is the same graph as: the package renamed by `g` on `w`, the code renamed by
      -- `g'` on `u`, and `Δ`
      Equiv M (s(var w, π.bind (fun x => var (g x))) ::ₘ
        s(u, (code k π).bind (fun x => var (g' x))) ::ₘ Δ) := by
  set C := (code k π).bind (fun x => var (f x)) with hC
  have hCp : C.IsPackage := IsPackage.bind_var (code_isPackage k π hπ hb) f hf
  have hCd : DupFree C := DupFree.bind_var (code_dupFree k π) f
  obtain ⟨fs, N, hlen, hinj, hS, hE⟩ := copier_package C hCp hCd [decoder w k₀, u] Δ hlin
  obtain ⟨g₁, g₂, rfl⟩ := List.length_eq_two.1 hlen
  obtain ⟨e₁, i₁⟩ := copy_of_copy (code k π) f g₁ hf (hinj g₁ (by simp))
  obtain ⟨e₂, i₂⟩ := copy_of_copy (code k π) f g₂ hf (hinj g₂ (by simp))
  set N₁ : CNet := s((code k π).bind (fun x => var (g₁ (f x))), decoder w k₀) ::ₘ
    (s(u, (code k π).bind (fun x => var (g₂ (f x)))) ::ₘ Δ) with hN₁
  have hE₁ : Equiv N N₁ := by
    have e : ((List.zipWith (fun u g => s(u, C.bind (fun x => var (g x)))) [decoder w k₀, u]
        [g₁, g₂] : CNet) + Δ) = N₁ := by
      simp only [List.zipWith_cons_cons, List.zipWith_nil_left, ← Multiset.cons_coe,
        Multiset.coe_nil, Multiset.cons_add, zero_add, hN₁, hC, e₁, e₂, Sym2.eq_swap]
    exact e ▸ hE
  have hlinN : N.Linear := StepsE.linear system_wellFormed.linear hS hlin
  have hlin₁ : N₁.Linear := hE₁.linear hlinN
  obtain ⟨M, hS₁, hEM⟩ := code_decoder_copy π hπ k hb (fun x => g₁ (f x)) i₁ w k₀ _ hlin₁
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv hE₁ hS₁
  exact ⟨_, _, M', i₁, i₂, hS.trans hS', hE'.trans hEM⟩

end INet.Comb
