/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Codes.Decode

/-!
# Lafont, "Interaction Combinators" (1997): the decoder on a renamed copy of the code

Pages 89 and 90, Fig. 9 and Fig. 10. In Fig. 10 the decoder `D` never meets `code k π` itself, but
a copy of it left by the copier `C_n` (`copier_code`): `(code k π).bind fun x => var (f x)`, with
`f` injective on the names of the code. Such a copy is in general not of the form `code k' π'`:
`decomp` numbers the cut names in a fixed order, and `f` need not keep it. It is still the same
graph as a code, and the decoder still extracts the package.

Contents, in the order of the file:

1. Definition: `Decomp.rename`, a decomposition with every name renamed.
2. Auxiliary lemmas, the equivariance of the decomposition: `decomp_bind_var` (decomposing `t`
   renamed by `g` from `K` is decomposing `t` from `k` and renaming everything by `g`, when `g`
   sends `k + i` to `K + i`; the cut names come only from the counter), and its two cases
   `decomp_bind_var_below` (renaming the names of `π` keeps the cut names) and `decomp_shift`
   (moving the start from `k` to `K ≥ k` shifts the cut names by `K - k`); `bind_var_mux`,
   `bind_var_muxStar`; and the consequence on the code, `code_bind_var`.
3. Auxiliary lemmas, renaming the internal wires from the renamed net:
   `count_add_count_le_count_map`, `count_le_count_map`, and `Net.equiv_bind_var_of_linear` (a
   renaming whose result is linear and which keeps the free ports is a renaming of internal
   wires, `Net.equiv_bind_var`).
4. Main result: `code_decoder_copy`, Fig. 9 on a renamed copy of the code, as Fig. 10 needs.
-/

@[expose] public section

namespace INet.Comb

open Term Decomp

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- A decomposition with every name renamed by `g`, and next unused name `k'`. -/
def Decomp.rename
    -- the renaming, and the new next unused name
    (g : ℕ → ℕ)
    (k' : ℕ)
    -- the decomposition
    (D : Decomp) :
    Decomp :=
  ⟨D.τ.bind (fun x => var (g x)),
    D.cells.map
      (fun c => (g c.1, c.2.1.bind (fun x => var (g x)), c.2.2.bind (fun x => var (g x)))),
    k'⟩

-- ============================================================================================
-- 2. Auxiliary lemmas: equivariance of the decomposition
-- ============================================================================================

/-- The decomposition of page 88 is equivariant: the cut names come only from the counter. If `g`
sends `k + i` to `K + i` for every `i`, then decomposing `t` renamed by `g` with new names from `K`
is decomposing `t` with new names from `k` and renaming `τ`, the cut names and the auxiliary trees
by `g`; the next unused name moves by the same amount. No hypothesis on the names of `t`. -/
theorem decomp_bind_var
    -- the tree
    (t : Term sig ℕ)
    -- the renaming, which sends the block of new names from `k` to the block from `K`
    (g : ℕ → ℕ)
    (k K : ℕ)
    (hg : ∀ i, g (k + i) = K + i) :
    -- decomposing the renamed tree from `K` is renaming the decomposition from `k`
    decomp K (t.bind fun x => var (g x))
      = (decomp k t).rename g (K + ((decomp k t).k - k)) := by
  induction t using Comb.induction generalizing k K with
  | var x => simp [decomp_var, Decomp.rename]
  | era => simp [decomp_mkEra, Decomp.rename]
  | con a b iha ihb =>
    have hA := (decomp_ports a (k + 2)).2.2
    have hB := (decomp_ports b (decomp (k + 2) a).k).2.2
    rw [bind_mkCon, decomp_mkCon, decomp_mkCon,
      iha (k + 2) (K + 2) (fun i => by rw [add_assoc, hg, add_assoc])]
    simp only [Decomp.rename]
    rw [ihb (decomp (k + 2) a).k (K + 2 + ((decomp (k + 2) a).k - (k + 2)))
      (fun i => by
        rw [show (decomp (k + 2) a).k + i = k + ((decomp (k + 2) a).k - k + i) by omega, hg]
        omega)]
    simp only [Decomp.rename, bind_mkCon, List.map_append, Decomp.mk.injEq, true_and]
    omega
  | dup a b iha ihb =>
    have hA := (decomp_ports a (k + 3)).2.2
    have hB := (decomp_ports b (decomp (k + 3) a).k).2.2
    have h0 : g k = K := by simpa using hg 0
    rw [bind_mkDup, decomp_mkDup, decomp_mkDup,
      iha (k + 3) (K + 3) (fun i => by rw [add_assoc, hg, add_assoc])]
    simp only [Decomp.rename]
    rw [ihb (decomp (k + 3) a).k (K + 3 + ((decomp (k + 3) a).k - (k + 3)))
      (fun i => by
        rw [show (decomp (k + 3) a).k + i = k + ((decomp (k + 3) a).k - k + i) by omega, hg]
        omega)]
    simp only [Decomp.rename, bind_var, h0, List.map_cons, List.map_append, Decomp.mk.injEq,
      true_and]
    omega

/-- Renaming the names of a tree (page 88): if the names of `t` are below `k`, decomposing `t`
renamed by `g` from `k` renames `τ` and the auxiliary trees of the cells by `g` on the names of `t`,
and keeps the cut names and the next unused name. -/
theorem decomp_bind_var_below
    -- the tree and the renaming
    (t : Term sig ℕ)
    (g : ℕ → ℕ)
    -- the names of the tree are below `k`
    (k : ℕ)
    (hb : t.Below k) :
    -- decomposing the renamed tree renames the decomposition by `g` below `k` only
    decomp k (t.bind fun x => var (g x))
      = (decomp k t).rename (fun x => if x < k then g x else x) (decomp k t).k := by
  have e : (t.bind fun x => var (g x)) = t.bind fun x => var (if x < k then g x else x) :=
    Term.bind_congr fun x hx => by simp [hb x hx]
  rw [e, decomp_bind_var t _ k k (fun i => by simp)]
  have := (decomp_ports t k).2.2
  congr 1
  omega

/-- Changing the start (page 88): if the names of `t` are below `k ≤ K`, decomposing `t` from `K`
shifts every cut name, and the next unused name, by `K - k`, and keeps the names of `t`. -/
theorem decomp_shift
    -- the tree, with its names below `k`
    (t : Term sig ℕ)
    (k K : ℕ)
    (hkK : k ≤ K)
    (hb : t.Below k) :
    -- decomposing from `K` shifts the names from `k` by `K - k`
    decomp K t
      = (decomp k t).rename (fun x => if x < k then x else x + (K - k))
          ((decomp k t).k + (K - k)) := by
  have e : t = t.bind fun x => var (if x < k then x else x + (K - k)) := by
    conv_lhs => rw [← Term.bind_var_self t]
    exact Term.bind_congr fun x hx => by simp [hb x hx]
  conv_lhs => rw [e]
  rw [decomp_bind_var t _ k K (fun i => by simp; omega)]
  have := (decomp_ports t k).2.2
  congr 1
  omega

/-- Renaming the auxiliary trees of `M_n` renames `M_n`. -/
theorem bind_var_mux
    -- the renaming
    (g : ℕ → ℕ) :
    -- for all auxiliary trees `ts`
    ∀ ts : List (Term sig ℕ),
      (mux ts).bind (fun x => var (g x)) = mux (ts.map fun t => t.bind fun x => var (g x))
  | [] => by simp [mux]
  | [t] => rfl
  | t :: t' :: ts => by
    rw [mux, bind_mkCon, bind_var_mux g (t' :: ts)]
    rfl

/-- Renaming the auxiliary trees of `M_n*` renames `M_n*`. -/
theorem bind_var_muxStar
    -- the renaming
    (g : ℕ → ℕ) :
    -- for all auxiliary trees `us`
    ∀ us : List (Term sig ℕ),
      (muxStar us).bind (fun x => var (g x)) = muxStar (us.map fun t => t.bind fun x => var (g x))
  | [] => by simp [muxStar]
  | [u] => rfl
  | u :: u' :: us => by
    rw [muxStar, bind_mkCon, bind_var_muxStar g (u' :: us)]
    rfl

/-- The code is equivariant (Fig. 8, page 88): if `g` sends `k + i` to `K + i` for every `i`, the
code of `t` renamed by `g`, with new names from `K`, is the code of `t` with new names from `k`,
renamed by `g`. -/
theorem code_bind_var
    -- the tree
    (t : Term sig ℕ)
    -- the renaming, which sends the block of new names from `k` to the block from `K`
    (g : ℕ → ℕ)
    (k K : ℕ)
    (hg : ∀ i, g (k + i) = K + i) :
    -- the code of the renamed tree from `K` is the renamed code from `k`
    code K (t.bind fun x => var (g x)) = (code k t).bind fun x => var (g x) := by
  rw [code, code, decomp_bind_var t g k K hg]
  simp only [Decomp.code, Decomp.rename, bind_var_mux, bind_var_muxStar, List.map_cons,
    List.map_nil, List.map_map]
  rfl

-- ============================================================================================
-- 3. Auxiliary lemmas: renaming the internal wires, from the renamed net
-- ============================================================================================

/-- Two names with the same image occur in the renamed multiset at least as often as together. -/
theorem count_add_count_le_count_map
    -- the multiset and the renaming
    (s : Multiset ℕ)
    (f : ℕ → ℕ)
    -- two distinct names with the same image
    (x y : ℕ)
    (hxy : x ≠ y)
    (h : f x = f y) :
    s.count x + s.count y ≤ (s.map f).count (f x) := by
  have hle : Multiset.replicate (s.count x) x + Multiset.replicate (s.count y) y ≤ s := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    split_ifs <;> subst_vars <;> omega
  have := Multiset.count_le_of_le (f x) (Multiset.map_le_map (f := f) hle)
  simpa [Multiset.map_add, Multiset.map_replicate, Multiset.count_replicate, h] using this

/-- A name occurs in the renamed multiset at least as often as in the multiset. -/
theorem count_le_count_map
    -- the multiset, the renaming and the name
    (s : Multiset ℕ)
    (f : ℕ → ℕ)
    (x : ℕ) :
    s.count x ≤ (s.map f).count (f x) := by
  have hle : Multiset.replicate (s.count x) x ≤ s := Multiset.le_count_iff_replicate_le.1 le_rfl
  have := Multiset.count_le_of_le (f x) (Multiset.map_le_map (f := f) hle)
  simpa [Multiset.map_replicate, Multiset.count_replicate] using this

/-- **Renaming the internal wires, from the renamed net.** If renaming the names of `N` by `f`
gives a linear net, and `f` keeps the free ports of `N`, then `N` is linear, `f` keeps its names
distinct, and the renamed net is the same graph (`Net.equiv_bind_var`; page 70: the names of the
internal wires do not matter). Two distinct names with the same image would give that image at
least twice, so both would be free ports, which `f` keeps. -/
theorem Net.equiv_bind_var_of_linear
    -- the net
    {N : CNet}
    -- the renaming: the renamed net is linear, and the free ports of `N` are kept
    (f : ℕ → ℕ)
    (hlin : Net.Linear (N.bind fun x => var (f x)))
    (hfree : ∀ x, N.vars.count x = 1 → f x = x) :
    -- the renamed net is the same graph as `N`
    Equiv N (N.bind fun x => var (f x)) := by
  have hv := Net.vars_bind_var (S := sig) f N
  have hL : N.Linear := fun x => by
    have h1 := count_le_count_map N.vars f x
    have h2 := hlin (f x)
    rw [hv] at h2
    omega
  refine Net.equiv_bind_var hL f (fun x hx y hy hxy => ?_) hfree
  by_contra hne
  have hx : x ∈ N.vars := hx
  have hy : y ∈ N.vars := hy
  have h1 := count_add_count_le_count_map N.vars f x y hne hxy
  have h2 := hlin (f x)
  rw [hv] at h2
  have cx := Multiset.one_le_count_iff_mem.2 hx
  have cy := Multiset.one_le_count_iff_mem.2 hy
  have ex := hfree x (by omega)
  have ey := hfree y (by omega)
  exact hne (ex.symm.trans (hxy.trans ey))

-- ============================================================================================
-- 4. Main result: Fig. 9 on a renamed copy of the code
-- ============================================================================================

/-- Fig. 9 on a renamed copy of the code, as Fig. 10 needs (pages 89 and 90). In Fig. 10 the
decoder `D` meets a copy of `!π` left by the copier (`copier_code`): the code `code k π` renamed by
a function `f` injective on its names. Plugged into the decoder with free port `w` and loop
`k₀, k₀ + 1`, with any context `Δ`, the copy reduces, by interactions up to wires, to a net that is
`Equiv` to the package `π` renamed by `f` on `w`.

Proof: the copy is the same graph as `code K π''`, where `π''` is `π` renamed by `f` and `K` is
above every name of the net (`code_bind_var`, `Net.equiv_bind_var_of_linear`); there the loop of
the decoder is moved to the next name unused by that code, and `code_decoder_package` applies. -/
theorem code_decoder_copy
    -- the package, with its names below `k`, where its code starts numbering
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    (k : ℕ)
    (hb : π.Below k)
    -- the renaming of the copy, injective on the names of the code
    (f : ℕ → ℕ)
    (hf : Set.InjOn f {x | x ∈ (code k π).vars})
    -- the free port `w` of the decoder and its loop `k₀, k₀ + 1`
    (w k₀ : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the copy of the code on the decoder, and `Δ`
    (hlin : Net.Linear (s((code k π).bind (fun x => var (f x)), decoder w k₀) ::ₘ Δ)) :
    -- there is a net `M` such that
    ∃ M,
      -- the net reduces, up to wires, to `M`,
      StepsE system (s((code k π).bind (fun x => var (f x)), decoder w k₀) ::ₘ Δ) M ∧
      -- and `M` is the same graph as: the package renamed by `f` on `w`; and `Δ`
      Equiv M (s(var w, π.bind (fun x => var (f x))) ::ₘ Δ) := by
  set C := (code k π).bind (fun x => var (f x)) with hC
  set N : CNet := s(C, decoder w k₀) ::ₘ Δ with hN
  -- a block of names above every name of the net
  set K := (Net.vars N).sup + 1 with hK
  have hKN : ∀ x ∈ Net.vars N, x < K := fun x hx => by have := Multiset.le_sup hx; omega
  have hNv : Net.vars N = C.vars + (decoder w k₀).vars + Net.vars Δ := by
    simp only [hN, Net.vars_cons, eqVars_mk]
  have hCv : C.vars = (code k π).vars.map f := vars_bind_var f _
  have hcode := vars_code k π
  have hπc : π.vars ≤ (code k π).vars := by
    rw [hcode, add_assoc]; exact Multiset.le_add_right _ _
  have hfπ : ∀ x ∈ π.vars, f x < K := fun x hx => hKN _ (by
    rw [hNv, hCv]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl
      (Multiset.mem_map_of_mem f (Multiset.mem_of_le hπc hx))))))
  have hwK : w < K := hKN _ (by rw [hNv, vars_decoder]; simp)
  have hΔK : ∀ x ∈ Net.vars Δ, x < K := fun x hx => hKN _ (by rw [hNv]; simp [hx])
  -- `π` renamed by `f`, and the renaming that sends the cut names from `k` to `K`
  set h : ℕ → ℕ := fun x => if x < k then f x else K + (x - k) with hh
  have hhk : ∀ i, h (k + i) = K + i := fun i => by simp [hh]
  set π'' := π.bind fun x => var (f x) with hπ''
  have eπ : π'' = π.bind fun x => var (h x) :=
    Term.bind_congr fun x hx => by simp [hh, hb x hx]
  have hcodeK : code K π'' = (code k π).bind fun x => var (h x) := by
    rw [eπ, code_bind_var π h k K hhk]
  set Ω := (decomp k π).k - k with hΩ
  have hK₀ : (decomp K π'').k = K + Ω := by
    rw [eπ, decomp_bind_var π h k K hhk]; rfl
  -- the renaming back to the copy, the loop of the decoder included
  set σ : ℕ → ℕ := fun y => if K ≤ y ∧ y < K + Ω then f (y - K + k) else
    if y = K + Ω then k₀ else if y = K + Ω + 1 then k₀ + 1 else y with hσ
  have hσlow : ∀ y, y < K → σ y = y := fun y hy => by
    simp only [hσ]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have hσ1 : σ (K + Ω) = k₀ := by simp [hσ]
  have hσ2 : σ (K + Ω + 1) = k₀ + 1 := by simp [hσ]
  have hσmid : ∀ y, K ≤ y → y < K + Ω → σ y = f (y - K + k) := fun y h1 h2 => by
    simp only [hσ]
    rw [ite_eq_left ⟨h1, h2⟩]
  set N' : CNet := s(code K π'', decoder w (K + Ω)) ::ₘ Δ with hN'
  have hΔσ : Net.bind (fun y => var (σ y)) Δ = Δ :=
    (Net.bind_congr fun x hx => congrArg var (hσlow x (hΔK x hx))).trans (Net.bind_var_self Δ)
  have hdec : (decoder w (K + Ω)).bind (fun y => var (σ y)) = decoder w k₀ := by
    simp only [decoder, muxStar, bind_mkCon, bind_mkDup, bind_var, hσ1, hσ2, hσlow w hwK]
  have hcσ : (code K π'').bind (fun y => var (σ y)) = C := by
    rw [hcodeK, Term.bind_bind, hC]
    refine Term.bind_congr fun x hx => ?_
    rw [bind_var]
    congr 1
    rw [hcode] at hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · rcases Multiset.mem_add.1 hx with hx | hx
      · have hxk := hb x hx
        simp only [hh, ite_eq_left hxk]
        exact hσlow _ (hfπ x hx)
      · obtain ⟨-, hr, -⟩ := decomp_ports π k
        have := hr x hx
        simp only [hh, ite_eq_right (show ¬ x < k by omega)]
        rw [hσmid _ (by omega) (by omega)]
        congr 1; omega
    · obtain ⟨-, hr, -⟩ := decomp_ports π k
      have := hr x hx
      simp only [hh, ite_eq_right (show ¬ x < k by omega)]
      rw [hσmid _ (by omega) (by omega)]
      congr 1; omega
  have hbind : Net.bind (fun y => var (σ y)) N' = N := by
    have e : Net.bind (fun y => var (σ y)) N' = s((code K π'').bind (fun y => var (σ y)),
        (decoder w (K + Ω)).bind (fun y => var (σ y))) ::ₘ Net.bind (fun y => var (σ y)) Δ := by
      rw [hN', Net.bind, Multiset.map_cons]; rfl
    rw [e, hcσ, hdec, hΔσ]
  -- the free ports of `N'` are below `K`: the names from `K` occur twice
  have hfree : ∀ y, (Net.vars N').count y = 1 → σ y = y := by
    intro y hy
    by_cases hyK : y < K
    · exact hσlow y hyK
    exfalso
    have hπ0 : π''.vars.count y = 0 := Multiset.count_eq_zero.2 fun hm => by
      rw [hπ'', vars_bind_var] at hm
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hm
      exact hyK (hfπ x hx)
    have hΔ0 : (Net.vars Δ).count y = 0 :=
      Multiset.count_eq_zero.2 fun hm => hyK (hΔK y hm)
    simp only [hN', Net.vars_cons, eqVars_mk, vars_code, vars_decoder, Multiset.count_add,
      hπ0, hΔ0, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hy
    split_ifs at hy <;> omega
  have E : Equiv N' N := hbind ▸ Net.equiv_bind_var_of_linear σ (hbind ▸ hlin) hfree
  -- Fig. 9 on `code K π''`
  have hπ''p : π''.IsPackage :=
    IsPackage.bind_var hπ f (hf.mono fun x hx => Multiset.mem_of_le hπc hx)
  have hle : Net.vars (s(var w, π'') ::ₘ Δ) ≤ Net.vars N := by
    rw [hNv, Net.vars_cons, eqVars_mk, vars_var]
    refine add_le_add (add_comm ({w} : Multiset ℕ) _ ▸ add_le_add ?_ ?_) le_rfl
    · rw [hπ'', vars_bind_var, hCv]; exact Multiset.map_le_map hπc
    · rw [vars_decoder]; simp
  have hlin' : Net.Linear (s(var w, π'') ::ₘ Δ) := fun y =>
    (Multiset.count_le_of_le y hle).trans (hlin y)
  have hbK : Net.Below K (s(var w, π'') ::ₘ Δ) := fun x hx => hKN x (Multiset.mem_of_le hle hx)
  obtain ⟨M, hS, hEM⟩ := code_decoder_package π'' hπ''p K w (K + Ω) Δ hlin' hbK hK₀.le
  obtain ⟨M', hS', hE'⟩ := stepsE_of_equiv E.symm hS
  exact ⟨M', hS', hE'.trans hEM⟩

end INet.Comb
