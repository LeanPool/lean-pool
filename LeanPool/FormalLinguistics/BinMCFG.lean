/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.MCFG

/-!
  MCFG / LCFRS Binarization (Rank-≤-2 Normal Form)
  Every finite Linear Non-Erasing MCFG `G` of arbitrary rank is computably
  transformed into a weakly equivalent Linear Non-Erasing MCFG `binarizeMCFG G`
  whose every rule has at most 2 RHS nonterminals (`r.rhs.length ≤ 2`).
-/

@[expose] public section

namespace FormalLinguistics

/-- Nonterminals of the binarized MCFG:
    `orig A` represents `A`;
    `join Bs` (used for `Bs.length ≥ 2`) represents the flattened concatenation of the tuples of `Bs`. -/
inductive BinMCFGNT (N : Type) where
  | orig : N → BinMCFGNT N
  | join : List N → BinMCFGNT N
  deriving DecidableEq, Repr

namespace BinMCFG

variable {N T : Type}

/-- Number of components in the concatenated tuples for a list of nonterminals. -/
def sumDim (dim : N → Nat) : List N → Nat
  | [] => 0
  | B :: Bs => dim B + sumDim dim Bs

/-- Arity of an original nonterminal or of the tuple joining a suffix of a rule. -/
def binDim (dim : N → Nat) : BinMCFGNT N → Nat
  | BinMCFGNT.orig A => dim A
  | BinMCFGNT.join Bs => max 1 (sumDim dim Bs)

theorem sumDim_pos_of_cons {dim : N → Nat} (hpos : ∀ A, 1 ≤ dim A) (B : N) (Bs : List N) :
    1 ≤ sumDim dim (B :: Bs) := by
  have := hpos B
  simp [sumDim]; omega

theorem binDim_join_cons {dim : N → Nat} (hpos : ∀ A, 1 ≤ dim A) (B : N) (Bs : List N) :
    binDim dim (BinMCFGNT.join (B :: Bs)) = sumDim dim (B :: Bs) := by
  have h1 := sumDim_pos_of_cons hpos B Bs
  simp [binDim]; omega

theorem binDim_pos {dim : N → Nat} (hpos : ∀ A, 1 ≤ dim A) (A : BinMCFGNT N) :
    1 ≤ binDim dim A := by
  cases A with
  | orig X => exact hpos X
  | join Bs => simp [binDim]; omega

/-- Cumulative dimension offset of index `i` inside `Bs`. -/
def offset (dim : N → Nat) (Bs : List N) (i : Nat) : Nat :=
  sumDim dim (Bs.take i)

theorem offset_lt_sumDim {dim : N → Nat} {Bs : List N} {i j : Nat} {B : N}
    (hget : Bs[i]? = some B) (hj : j < dim B) :
    offset dim Bs i + j < sumDim dim Bs := by
  induction Bs generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp at hget; subst hget
      simp [offset, sumDim]; omega
    | succ i' =>
      have h' : tl[i']? = some B := by simpa using hget
      have ih' := ih h'
      simp only [offset, List.take_succ_cons, sumDim] at ih' ⊢
      omega

theorem offset_injective {dim : N → Nat} {Bs : List N} {i1 i2 j1 j2 : Nat} {B1 B2 : N}
    (h1 : Bs[i1]? = some B1) (hj1 : j1 < dim B1)
    (h2 : Bs[i2]? = some B2) (hj2 : j2 < dim B2)
    (heq : offset dim Bs i1 + j1 = offset dim Bs i2 + j2) :
    i1 = i2 ∧ j1 = j2 := by
  induction Bs generalizing i1 i2 with
  | nil => simp at h1
  | cons hd tl ih =>
    cases i1 with
    | zero =>
      simp at h1; subst h1
      cases i2 with
      | zero =>
        simp [offset, sumDim] at heq
        exact ⟨rfl, heq⟩
      | succ i2' =>
        simp [offset, sumDim] at heq
        omega
    | succ i1' =>
      cases i2 with
      | zero =>
        simp at h2; subst h2
        simp [offset, sumDim] at heq
        omega
      | succ i2' =>
        simp only [offset, List.take_succ_cons, sumDim] at heq
        have h1' : tl[i1']? = some B1 := by simpa using h1
        have h2' : tl[i2']? = some B2 := by simpa using h2
        have ⟨hi, hj⟩ := ih h1' h2' (by simp only [offset]; omega)
        exact ⟨by omega, hj⟩

theorem offset_surjective {dim : N → Nat} {Bs : List N} {k : Nat}
    (hk : k < sumDim dim Bs) :
    ∃ i B j, Bs[i]? = some B ∧ j < dim B ∧ offset dim Bs i + j = k := by
  induction Bs generalizing k with
  | nil => simp [sumDim] at hk
  | cons hd tl ih =>
    simp only [sumDim] at hk
    by_cases hlt : k < dim hd
    · exact ⟨0, hd, k, rfl, hlt, by simp [offset, sumDim]⟩
    · obtain ⟨i, B, j, hget, hj, heq⟩ := ih (k := k - dim hd) (by omega)
      refine ⟨i + 1, B, j, by simpa using hget, hj, ?_⟩
      simp only [offset, List.take_succ_cons, sumDim] at heq ⊢
      omega

/-- Remap variables `(0, j) ↦ (0, j)` and `(i + 1, j) ↦ (1, offset dim tailBs i + j)`. -/
def remapAtom (dim : N → Nat) (tailBs : List N) : MCFGAtom T → MCFGAtom T
  | MCFGAtom.tm a => MCFGAtom.tm a
  | MCFGAtom.var 0 j => MCFGAtom.var 0 j
  | MCFGAtom.var (i + 1) j => MCFGAtom.var 1 (offset dim tailBs i + j)

/-- Reindex rule templates after packing the tail arguments into one tuple. -/
def remapYield (dim : N → Nat) (tailBs : List N) (y : List (List (MCFGAtom T))) :
    List (List (MCFGAtom T)) :=
  y.map fun comp => comp.map (remapAtom dim tailBs)

/-- Identity tuple-concatenation rule joining two nonterminals of dimensions `d1` and `d2`. -/
def joinYield (d1 d2 : Nat) : List (List (MCFGAtom T)) :=
  ((List.range d1).map fun j => [MCFGAtom.var 0 j]) ++
  ((List.range d2).map fun j => [MCFGAtom.var 1 j])

/-- Generate all rank-2 join rules for a tail of length ≥ 2. -/
def tailJoinRules (dim : N → Nat) : List N → List (MCFGRule (BinMCFGNT N) T)
  | [] => []
  | [_] => []
  | [X, Y] =>
    [{ lhs := BinMCFGNT.join [X, Y]
       rhs := [BinMCFGNT.orig X, BinMCFGNT.orig Y]
       yield := joinYield (dim X) (dim Y) }]
  | X :: Y :: Z :: rest =>
    { lhs := BinMCFGNT.join (X :: Y :: Z :: rest)
      rhs := [BinMCFGNT.orig X, BinMCFGNT.join (Y :: Z :: rest)]
      yield := joinYield (dim X) (sumDim dim (Y :: Z :: rest)) } ::
    tailJoinRules dim (Y :: Z :: rest)

/-- Replace a production with rules of rank at most two, joining its tail arguments. -/
def binarizeRule (dim : N → Nat) (r : MCFGRule N T) : List (MCFGRule (BinMCFGNT N) T) :=
  match r.rhs with
  | [] => [{ lhs := BinMCFGNT.orig r.lhs, rhs := [], yield := r.yield }]
  | [B0] => [{ lhs := BinMCFGNT.orig r.lhs, rhs := [BinMCFGNT.orig B0], yield := r.yield }]
  | [B0, B1] =>
    [{ lhs := BinMCFGNT.orig r.lhs, rhs := [BinMCFGNT.orig B0, BinMCFGNT.orig B1], yield := r.yield }]
  | B0 :: B1 :: B2 :: rest =>
    { lhs := BinMCFGNT.orig r.lhs
      rhs := [BinMCFGNT.orig B0, BinMCFGNT.join (B1 :: B2 :: rest)]
      yield := remapYield dim (B1 :: B2 :: rest) r.yield } ::
    tailJoinRules dim (B1 :: B2 :: rest)

/-! ### Well-Formedness & Rank-≤-2 Proofs -/

theorem range_var0_props (d : Nat) :
    let vs : List (List (MCFGAtom T)) := (List.range d).map fun j => [MCFGAtom.var 0 j]
    vs.length = d ∧
    (vs.flatMap fun c => c.filterMap fun | MCFGAtom.tm _ => none | MCFGAtom.var i j => some (i, j)).Nodup ∧
    (∀ i j, (i, j) ∈ (vs.flatMap fun c => c.filterMap fun | MCFGAtom.tm _ => none | MCFGAtom.var i j => some (i, j)) ↔
      i = 0 ∧ j < d) := by
  induction d with
  | zero =>
    refine ⟨rfl, List.nodup_nil, ?_⟩
    intro i j; simp
  | succ d ih =>
    obtain ⟨hlen, hnd, hmem⟩ := ih
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine ⟨by simp [hlen], ?_, ?_⟩
    · rw [List.flatMap_append, List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      intro heq; subst heq
      have := (hmem 0 d).mp ha; omega
    · intro i j
      rw [List.flatMap_append, List.mem_append, hmem i j]
      simp only [List.flatMap_cons, List.flatMap_nil, List.filterMap_cons, List.filterMap_nil,
        List.append_nil, List.mem_singleton, Prod.mk.injEq]
      omega

theorem range_var1_props (d : Nat) :
    let vs : List (List (MCFGAtom T)) := (List.range d).map fun j => [MCFGAtom.var 1 j]
    vs.length = d ∧
    (vs.flatMap fun c => c.filterMap fun | MCFGAtom.tm _ => none | MCFGAtom.var i j => some (i, j)).Nodup ∧
    (∀ i j, (i, j) ∈ (vs.flatMap fun c => c.filterMap fun | MCFGAtom.tm _ => none | MCFGAtom.var i j => some (i, j)) ↔
      i = 1 ∧ j < d) := by
  induction d with
  | zero =>
    refine ⟨rfl, List.nodup_nil, ?_⟩
    intro i j; simp
  | succ d ih =>
    obtain ⟨hlen, hnd, hmem⟩ := ih
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine ⟨by simp [hlen], ?_, ?_⟩
    · rw [List.flatMap_append, List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha b hb
      simp at hb; subst hb
      intro heq; subst heq
      have := (hmem 1 d).mp ha; omega
    · intro i j
      rw [List.flatMap_append, List.mem_append, hmem i j]
      simp only [List.flatMap_cons, List.flatMap_nil, List.filterMap_cons, List.filterMap_nil,
        List.append_nil, List.mem_singleton, Prod.mk.injEq]
      omega

theorem joinRule_wf {dim : N → Nat} {A B C : BinMCFGNT N}
    (hA : binDim dim A = binDim dim B + binDim dim C) :
    MCFGRule.WellFormed (binDim dim)
      ({ lhs := A, rhs := [B, C], yield := joinYield (T := T) (binDim dim B) (binDim dim C) } :
        MCFGRule (BinMCFGNT N) T) := by
  obtain ⟨hl0, hnd0, hm0⟩ := range_var0_props (T := T) (binDim dim B)
  obtain ⟨hl1, hnd1, hm1⟩ := range_var1_props (T := T) (binDim dim C)
  refine ⟨?_, ?_, ?_⟩
  · simp [joinYield, hA]
  · unfold MCFGRule.isLinear MCFGRule.varOccurrences
    simp only [joinYield, List.flatMap_append]
    rw [List.nodup_append]
    refine ⟨hnd0, hnd1, ?_⟩
    intro ⟨i1, j1⟩ h1 ⟨i2, j2⟩ h2 heq
    have := (hm0 i1 j1).mp h1
    have := (hm1 i2 j2).mp h2
    simp at heq; omega
  · intro i j
    unfold MCFGRule.varOccurrences
    simp only [joinYield, List.flatMap_append, List.mem_append]
    constructor
    · rintro (h0 | h1)
      · obtain ⟨rfl, hj⟩ := (hm0 i j).mp h0; exact ⟨B, rfl, hj⟩
      · obtain ⟨rfl, hj⟩ := (hm1 i j).mp h1; exact ⟨C, rfl, hj⟩
    · rintro ⟨X, hget, hj⟩
      cases i with
      | zero => simp at hget; subst hget; left; exact (hm0 0 j).mpr ⟨rfl, hj⟩
      | succ i' =>
        cases i' with
        | zero => simp at hget; subst hget; right; exact (hm1 1 j).mpr ⟨rfl, hj⟩
        | succ _ => simp at hget

theorem tailJoinRules_wf {dim : N → Nat} (hpos : ∀ A, 1 ≤ dim A) :
    ∀ Bs r, r ∈ tailJoinRules (T := T) dim Bs →
      r.WellFormed (binDim dim) ∧ r.rhs.length ≤ 2 := by
  intro Bs
  match Bs with
  | [] => intro _ h; simp [tailJoinRules] at h
  | [_] => intro _ h; simp [tailJoinRules] at h
  | [X, Y] =>
    intro r h
    simp [tailJoinRules] at h; subst h
    refine ⟨?_, by simp⟩
    have hA : binDim dim (BinMCFGNT.join [X, Y]) =
        binDim dim (BinMCFGNT.orig X) + binDim dim (BinMCFGNT.orig Y) := by
      rw [binDim_join_cons hpos]; simp [binDim, sumDim]
    simpa [binDim] using joinRule_wf (T := T) hA
  | X :: Y :: Z :: rest =>
    intro r h
    simp only [tailJoinRules, List.mem_cons] at h
    rcases h with rfl | ht
    · refine ⟨?_, by simp⟩
      have hA : binDim dim (BinMCFGNT.join (X :: Y :: Z :: rest)) =
          binDim dim (BinMCFGNT.orig X) + binDim dim (BinMCFGNT.join (Y :: Z :: rest)) := by
        rw [binDim_join_cons hpos, binDim_join_cons hpos]; simp [binDim, sumDim]
      have hstep := joinRule_wf (T := T) hA
      rw [binDim_join_cons hpos] at hstep
      simpa [binDim] using hstep
    · exact tailJoinRules_wf hpos (Y :: Z :: rest) r ht

/-- Mapping helper: `varOccurrences` of a remapped rule equals mapping `(0,j)↦(0,j), (i+1,j)↦(1,offset+j)`. -/
def remapCoord (dim : N → Nat) (tailBs : List N) : Nat × Nat → Nat × Nat
  | (0, j) => (0, j)
  | (i + 1, j) => (1, offset dim tailBs i + j)

theorem varOccurrences_remapYield (dim : N → Nat) (tailBs : List N)
    (lhs : BinMCFGNT N) (rhs : List (BinMCFGNT N)) (y : List (List (MCFGAtom T))) :
    MCFGRule.varOccurrences { lhs := lhs, rhs := rhs, yield := remapYield dim tailBs y } =
      (y.flatMap fun comp => comp.filterMap fun
        | MCFGAtom.tm _ => none
        | MCFGAtom.var i j => some (i, j)).map (remapCoord dim tailBs) := by
  simp only [MCFGRule.varOccurrences, remapYield]
  induction y with
  | nil => rfl
  | cons comp rest ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    rw [ih]
    congr 1
    induction comp with
    | nil => rfl
    | cons a t iha =>
      cases a with
      | tm x => simp [remapAtom, iha]
      | var i j =>
        cases i <;> simp [remapAtom, remapCoord, iha]

theorem binarizeRule_wf {dim : N → Nat} (hpos : ∀ A, 1 ≤ dim A)
    {r : MCFGRule N T} (hwf : r.WellFormed dim) :
    ∀ r', r' ∈ binarizeRule dim r → r'.WellFormed (binDim dim) ∧ r'.rhs.length ≤ 2 := by
  obtain ⟨hlen, hlin, hne⟩ := hwf
  intro r' hr'
  unfold binarizeRule at hr'
  match hrhs : r.rhs with
  | [] =>
    simp [hrhs] at hr'; subst hr'
    refine ⟨⟨by simpa [binDim] using hlen, hlin, ?_⟩, by simp⟩
    intro i j
    have := hne i j
    simp [hrhs] at this ⊢
    exact this
  | [B0] =>
    simp [hrhs] at hr'; subst hr'
    refine ⟨⟨by simpa [binDim] using hlen, hlin, ?_⟩, by simp⟩
    intro i j
    change (i, j) ∈ r.varOccurrences ↔ _
    rw [hne i j]
    simp only [hrhs]
    constructor
    · rintro ⟨B, hget, hj⟩
      cases i with
      | zero => simp at hget; subst hget; exact ⟨BinMCFGNT.orig B0, rfl, hj⟩
      | succ _ => simp at hget
    · rintro ⟨B', hget, hj⟩
      cases i with
      | zero => simp at hget; subst hget; exact ⟨B0, rfl, hj⟩
      | succ _ => simp at hget
  | [B0, B1] =>
    simp [hrhs] at hr'; subst hr'
    refine ⟨⟨by simpa [binDim] using hlen, hlin, ?_⟩, by simp⟩
    intro i j
    change (i, j) ∈ r.varOccurrences ↔ _
    rw [hne i j]
    simp only [hrhs]
    constructor
    · rintro ⟨B, hget, hj⟩
      cases i with
      | zero => simp at hget; subst hget; exact ⟨BinMCFGNT.orig B0, rfl, hj⟩
      | succ i' =>
        cases i' with
        | zero => simp at hget; subst hget; exact ⟨BinMCFGNT.orig B1, rfl, hj⟩
        | succ _ => simp at hget
    · rintro ⟨B', hget, hj⟩
      cases i with
      | zero => simp at hget; subst hget; exact ⟨B0, rfl, hj⟩
      | succ i' =>
        cases i' with
        | zero => simp at hget; subst hget; exact ⟨B1, rfl, hj⟩
        | succ _ => simp at hget
  | B0 :: B1 :: B2 :: rest =>
    simp only [hrhs, List.mem_cons] at hr'
    rcases hr' with rfl | htail
    · let tailBs := B1 :: B2 :: rest
      refine ⟨⟨by simp [remapYield, binDim, hlen], ?_, ?_⟩, by simp⟩
      · -- Linearity: remapCoord is injective on r.varOccurrences!
        unfold MCFGRule.isLinear
        rw [varOccurrences_remapYield]
        have hinj : ∀ p1 p2, p1 ∈ r.varOccurrences → p2 ∈ r.varOccurrences →
            remapCoord dim tailBs p1 = remapCoord dim tailBs p2 → p1 = p2 := by
          rintro ⟨i1, j1⟩ ⟨i2, j2⟩ hp1 hp2 heq
          obtain ⟨X1, hX1, hj1⟩ := (hne i1 j1).mp hp1
          obtain ⟨X2, hX2, hj2⟩ := (hne i2 j2).mp hp2
          rw [hrhs] at hX1 hX2
          cases i1 with
          | zero =>
            cases i2 with
            | zero => simp [remapCoord] at heq; exact Prod.ext rfl heq
            | succ _ => simp [remapCoord] at heq
          | succ i1' =>
            cases i2 with
            | zero => simp [remapCoord] at heq
            | succ i2' =>
              simp only [remapCoord, Prod.mk.injEq, true_and] at heq
              have h1' : tailBs[i1']? = some X1 := by simpa [tailBs] using hX1
              have h2' : tailBs[i2']? = some X2 := by simpa [tailBs] using hX2
              obtain ⟨hi, hj⟩ := offset_injective h1' hj1 h2' hj2 heq
              exact Prod.ext (by omega) hj
        -- Nodup of map under injection on list elements
        have hnd_map : ∀ {α β : Type} {f : α → β} {l : List α},
            l.Nodup → (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) → (l.map f).Nodup := by
          intro α β f l hnd hi
          induction l with
          | nil => exact List.nodup_nil
          | cons a t iht =>
            rw [List.nodup_cons] at hnd
            rw [List.map_cons, List.nodup_cons]
            refine ⟨?_, iht hnd.2 (fun x y hx hy => hi x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy))⟩
            intro hm
            obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
            have heq := hi b a (List.mem_cons_of_mem _ hb) (List.mem_cons_self ..) hfb
            exact hnd.1 (heq ▸ hb)
        exact hnd_map hlin hinj
      · -- Non-erasing bijection
        intro i j
        rw [varOccurrences_remapYield, List.mem_map]
        constructor
        · rintro ⟨⟨i0, j0⟩, hmem, heq⟩
          obtain ⟨X, hX, hj0⟩ := (hne i0 j0).mp hmem
          rw [hrhs] at hX
          cases i0 with
          | zero =>
            simp [remapCoord] at heq; obtain ⟨rfl, rfl⟩ := heq
            simp at hX; subst hX
            exact ⟨BinMCFGNT.orig B0, rfl, hj0⟩
          | succ i0' =>
            simp [remapCoord] at heq; obtain ⟨rfl, rfl⟩ := heq
            have hX' : tailBs[i0']? = some X := by simpa [tailBs] using hX
            refine ⟨BinMCFGNT.join tailBs, rfl, ?_⟩
            rw [binDim_join_cons hpos]
            exact offset_lt_sumDim hX' hj0
        · rintro ⟨B', hget, hj⟩
          cases i with
          | zero =>
            simp at hget; subst hget
            exact ⟨(0, j), (hne 0 j).mpr ⟨B0, by simp [hrhs], hj⟩, rfl⟩
          | succ i' =>
            cases i' with
            | zero =>
              simp at hget; subst hget
              rw [binDim_join_cons hpos] at hj
              obtain ⟨i0, X, j0, hX, hj0, hoff⟩ := offset_surjective hj
              refine ⟨(i0 + 1, j0), (hne (i0 + 1) j0).mpr ⟨X, ?_, hj0⟩, ?_⟩
              · rw [hrhs]; simpa [tailBs] using hX
              · simp [remapCoord, hoff]
            | succ _ => simp at hget
    · exact tailJoinRules_wf hpos (B1 :: B2 :: rest) r' htail

/-- Construct the binarized (rank-≤-2) Linear Non-Erasing MCFG from `G`. -/
def binarizeMCFG (G : MCFG N T) : MCFG (BinMCFGNT N) T where
  start := BinMCFGNT.orig G.start
  dim := binDim G.dim
  dim_pos := binDim_pos G.dim_pos
  dim_start := G.dim_start
  rules := G.rules.flatMap (binarizeRule G.dim)
  rules_wf := by
    intro r' hr'
    obtain ⟨r, hr, hbin⟩ := List.mem_flatMap.mp hr'
    exact (binarizeRule_wf G.dim_pos (G.rules_wf r hr) r' hbin).1

theorem binarizeMCFG_rank_le_two (G : MCFG N T) :
    ∀ r', r' ∈ (binarizeMCFG G).rules → r'.rhs.length ≤ 2 := by
  intro r' hr'
  obtain ⟨r, hr, hbin⟩ := List.mem_flatMap.mp hr'
  exact (binarizeRule_wf G.dim_pos (G.rules_wf r hr) r' hbin).2

/-! ### Semantic Equivalence (`(binarizeMCFG G).Lang ↔ G.Lang`) -/

/-- Flattened lookup lemma: indexing `args.flatten` at `offset G.dim Bs i + j` recovers `args[i][j]`. -/
theorem flatten_getElem?_offset {G : MCFG N T} {Bs : List N} {args : List (List (List T))} :
    MCFG.YieldList G Bs args →
    ∀ i j B, Bs[i]? = some B → j < G.dim B →
      args.flatten[offset G.dim Bs i + j]? =
        match args[i]? with
        | some tup => tup[j]?
        | none => none
  | MCFG.YieldList.nil, _, _, _, hget, _ => by simp at hget
  | MCFG.YieldList.cons (B := hd) (Bs := tl) (tup := tup) hy hrest, i, j, B, hget, hj => by
    have htup_len : tup.length = G.dim hd := hy.length_eq
    cases i with
    | zero =>
      simp at hget; subst hget
      have hlt : j < tup.length := by omega
      simp only [List.flatten_cons, offset, List.take_zero, sumDim, Nat.zero_add,
        List.getElem?_cons_zero, List.getElem?_append_left hlt]
    | succ i' =>
      have h' : tl[i']? = some B := by simpa using hget
      have ih' := flatten_getElem?_offset hrest i' j B h' hj
      simp only [List.flatten_cons, offset, List.take_succ_cons, sumDim, List.getElem?_cons_succ]
      rw [Nat.add_assoc, ← htup_len, List.getElem?_append_right (Nat.le_add_right _ _)]
      simpa [offset, Nat.add_sub_cancel_left] using ih'

theorem evalComp_remap {G : MCFG N T} {tailBs : List N}
    {tup0 : List (List T)} {tailArgs : List (List (List T))}
    (hyl : MCFG.YieldList G tailBs tailArgs)
    (comp : List (MCFGAtom T))
    (hwf : ∀ i j, MCFGAtom.var (i + 1) j ∈ comp → ∃ B, tailBs[i]? = some B ∧ j < G.dim B) :
    MCFG.evalComp [tup0, tailArgs.flatten] (comp.map (remapAtom G.dim tailBs)) =
      MCFG.evalComp (tup0 :: tailArgs) comp := by
  induction comp with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun i j hm => hwf i j (List.mem_cons_of_mem _ hm))
    cases a with
    | tm x => simp [remapAtom, MCFG.evalComp, ih']
    | var i j =>
      cases i with
      | zero => simp [remapAtom, MCFG.evalComp, ih']
      | succ i' =>
        obtain ⟨B, hB, hj⟩ := hwf i' j (List.mem_cons_self ..)
        have hfl := flatten_getElem?_offset hyl i' j B hB hj
        simp only [List.map_cons, remapAtom, MCFG.evalComp, List.getElem?_cons_succ,
          List.getElem?_cons_zero, hfl, ih']
        cases tailArgs[i']? <;> rfl

theorem evalYield_joinYield (tup1 tup2 : List (List T)) :
    MCFG.evalYield [tup1, tup2] (joinYield tup1.length tup2.length) = tup1 ++ tup2 := by
  unfold joinYield MCFG.evalYield
  rw [List.map_append]
  congr 1
  · have h0 : ∀ (pre mid : List (List T)),
        (List.range mid.length).map (fun k => MCFG.evalComp [pre ++ mid, tup2] [MCFGAtom.var 0 (pre.length + k)]) = mid := by
      intro pre mid
      induction mid generalizing pre with
      | nil => rfl
      | cons a tl ih =>
        have hr : List.range (tl.length + 1) = 0 :: (List.range tl.length).map Nat.succ :=
          List.range_succ_eq_map (n := tl.length)
        simp only [List.length_cons, hr, List.map_cons, List.map_map]
        have hh : MCFG.evalComp [pre ++ a :: tl, tup2] [MCFGAtom.var 0 (pre.length + 0)] = a := by
          simp [MCFG.evalComp]
        rw [hh]; congr 1
        have htl := ih (pre ++ [a])
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append] at htl
        refine Eq.trans ?_ htl
        apply List.map_congr_left
        intro k _
        have hidx : pre.length + k.succ = pre.length + 1 + k := by omega
        simp [Function.comp, hidx]
    have h0' := h0 [] tup1
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at h0'
    rw [List.map_map]; exact h0'
  · have h1 : ∀ (pre mid : List (List T)),
        (List.range mid.length).map (fun k => MCFG.evalComp [tup1, pre ++ mid] [MCFGAtom.var 1 (pre.length + k)]) = mid := by
      intro pre mid
      induction mid generalizing pre with
      | nil => rfl
      | cons a tl ih =>
        have hr : List.range (tl.length + 1) = 0 :: (List.range tl.length).map Nat.succ :=
          List.range_succ_eq_map (n := tl.length)
        simp only [List.length_cons, hr, List.map_cons, List.map_map]
        have hh : MCFG.evalComp [tup1, pre ++ a :: tl] [MCFGAtom.var 1 (pre.length + 0)] = a := by
          simp [MCFG.evalComp]
        rw [hh]; congr 1
        have htl := ih (pre ++ [a])
        simp only [List.length_append, List.length_singleton, List.append_assoc,
          List.singleton_append] at htl
        refine Eq.trans ?_ htl
        apply List.map_congr_left
        intro k _
        have hidx : pre.length + k.succ = pre.length + 1 + k := by omega
        simp [Function.comp, hidx]
    have h1' := h1 [] tup2
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at h1'
    rw [List.map_map]; exact h1'

/-- Interpret a binarized nonterminal by a yield or a concatenation of yields in the original
grammar. -/
def binInterp (G : MCFG N T) : BinMCFGNT N → List (List T) → Prop
  | BinMCFGNT.orig A, tup => MCFG.Yield G A tup
  | BinMCFGNT.join Bs, tup => ∃ args, MCFG.YieldList G Bs args ∧ tup = args.flatten

/-- Relate a list of binarized nonterminals to tuples interpreted in the original grammar. -/
inductive BinInterpList (G : MCFG N T) : List (BinMCFGNT N) → List (List (List T)) → Prop where
  | nil : BinInterpList G [] []
  | cons {A : BinMCFGNT N} {As : List (BinMCFGNT N)}
      {tup : List (List T)} {tups : List (List (List T))} :
      binInterp G A tup → BinInterpList G As tups → BinInterpList G (A :: As) (tup :: tups)

theorem tailJoinRules_sound {dim : N → Nat} {Bs : List N} {r' : MCFGRule (BinMCFGNT N) T}
    (h : r' ∈ tailJoinRules dim Bs) :
    (∃ X Y, r' = { lhs := BinMCFGNT.join [X, Y], rhs := [BinMCFGNT.orig X, BinMCFGNT.orig Y],
                   yield := joinYield (dim X) (dim Y) }) ∨
    (∃ X Y Z rest, r' = { lhs := BinMCFGNT.join (X :: Y :: Z :: rest),
                          rhs := [BinMCFGNT.orig X, BinMCFGNT.join (Y :: Z :: rest)],
                          yield := joinYield (dim X) (sumDim dim (Y :: Z :: rest)) }) := by
  match Bs with
  | [] => simp [tailJoinRules] at h
  | [_] => simp [tailJoinRules] at h
  | [X, Y] =>
    simp [tailJoinRules] at h; subst h
    left; exact ⟨X, Y, rfl⟩
  | X :: Y :: Z :: rest =>
    simp only [tailJoinRules, List.mem_cons] at h
    rcases h with rfl | ht
    · right; exact ⟨X, Y, Z, rest, rfl⟩
    · exact tailJoinRules_sound ht

theorem flatten_length_eq_sumDim {G : MCFG N T} {Bs : List N} {args : List (List (List T))} :
    MCFG.YieldList G Bs args → args.flatten.length = sumDim G.dim Bs
  | MCFG.YieldList.nil => rfl
  | MCFG.YieldList.cons hy hrest => by
    simp [List.flatten_cons, sumDim, hy.length_eq, flatten_length_eq_sumDim hrest]

mutual
  theorem binarizeMCFG_sound {G : MCFG N T} {A : BinMCFGNT N} {tup : List (List T)} :
      MCFG.Yield (binarizeMCFG G) A tup → binInterp G A tup
    | MCFG.Yield.rule hr' hargs_raw => by
      have hargs := binarizeMCFG_sound_list hargs_raw
      obtain ⟨r, hr, hbin⟩ := List.mem_flatMap.mp hr'
      unfold binarizeRule at hbin
      match hrhs : r.rhs with
      | [] =>
        simp [hrhs] at hbin; subst hbin
        cases hargs
        have hyl : MCFG.YieldList G r.rhs [] := by rw [hrhs]; exact MCFG.YieldList.nil
        exact MCFG.Yield.rule hr hyl
      | [B0] =>
        simp [hrhs] at hbin; subst hbin
        cases hargs with
        | @cons _ _ tup0 _ h0 hnil =>
          cases hnil
          have hyl : MCFG.YieldList G r.rhs [tup0] := by
            rw [hrhs]; exact MCFG.YieldList.cons h0 MCFG.YieldList.nil
          exact MCFG.Yield.rule hr hyl
      | [B0, B1] =>
        simp [hrhs] at hbin; subst hbin
        cases hargs with
        | @cons _ _ tup0 _ h0 hrest =>
          cases hrest with
          | @cons _ _ tup1 _ h1 hnil =>
            cases hnil
            have hyl : MCFG.YieldList G r.rhs [tup0, tup1] := by
              rw [hrhs]; exact MCFG.YieldList.cons h0 (MCFG.YieldList.cons h1 MCFG.YieldList.nil)
            exact MCFG.Yield.rule hr hyl
      | B0 :: B1 :: B2 :: rest =>
        simp only [hrhs, List.mem_cons] at hbin
        rcases hbin with rfl | htail
        · cases hargs with
          | @cons _ _ tup0 _ h0 hrest =>
            cases hrest with
            | cons h1 hnil =>
              cases hnil
              obtain ⟨tailArgs, htailY, rfl⟩ := h1
              have hne := (G.rules_wf r hr).2.2
              have hev : MCFG.evalYield [tup0, tailArgs.flatten] (remapYield G.dim (B1 :: B2 :: rest) r.yield) =
                  MCFG.evalYield (tup0 :: tailArgs) r.yield := by
                unfold MCFG.evalYield remapYield
                rw [List.map_map]
                apply List.map_congr_left
                intro comp hcomp
                apply evalComp_remap htailY comp
                intro i j hm
                have hvar : (i + 1, j) ∈ r.varOccurrences := by
                  simp only [MCFGRule.varOccurrences, List.mem_flatMap, List.mem_filterMap]
                  exact ⟨comp, hcomp, MCFGAtom.var (i + 1) j, hm, rfl⟩
                obtain ⟨B, hB, hj⟩ := (hne (i + 1) j).mp hvar
                rw [hrhs] at hB
                exact ⟨B, by simpa using hB, hj⟩
              rw [hev]
              have hyl : MCFG.YieldList G r.rhs (tup0 :: tailArgs) := by
                rw [hrhs]; exact MCFG.YieldList.cons h0 htailY
              exact MCFG.Yield.rule hr hyl
        · rcases tailJoinRules_sound htail with ⟨X, Y, rfl⟩ | ⟨X, Y, Z, more, rfl⟩
          · cases hargs with
            | @cons _ _ tupX _ hX hrest =>
              cases hrest with
              | @cons _ _ tupY _ hY hnil =>
                cases hnil
                refine ⟨[tupX, tupY], MCFG.YieldList.cons hX (MCFG.YieldList.cons hY MCFG.YieldList.nil), ?_⟩
                rw [← hX.length_eq, ← hY.length_eq, evalYield_joinYield]
                simp
          · cases hargs with
            | @cons _ _ tupX _ hX hrest =>
              cases hrest with
              | cons hRest hnil =>
                cases hnil
                obtain ⟨tailArgs, htailY, rfl⟩ := hRest
                refine ⟨tupX :: tailArgs, MCFG.YieldList.cons hX htailY, ?_⟩
                rw [← hX.length_eq, ← flatten_length_eq_sumDim htailY, evalYield_joinYield]
                simp

  theorem binarizeMCFG_sound_list {G : MCFG N T} {As : List (BinMCFGNT N)}
      {args : List (List (List T))} :
      MCFG.YieldList (binarizeMCFG G) As args → BinInterpList G As args
    | MCFG.YieldList.nil => BinInterpList.nil
    | MCFG.YieldList.cons hy hrest =>
      BinInterpList.cons (binarizeMCFG_sound hy) (binarizeMCFG_sound_list hrest)
end

/-- Helper predicate for completeness: `YieldList` where every element has already been lifted to `binarizeMCFG`. -/
inductive BinYieldList (G : MCFG N T) : List N → List (List (List T)) → Prop where
  | nil : BinYieldList G [] []
  | cons {B : N} {Bs : List N} {tup : List (List T)} {tups : List (List (List T))} :
      MCFG.Yield (binarizeMCFG G) (BinMCFGNT.orig B) tup →
      MCFG.Yield G B tup →
      BinYieldList G Bs tups →
      BinYieldList G (B :: Bs) (tup :: tups)

theorem binYieldList_to_orig {G : MCFG N T} {Bs : List N} {args : List (List (List T))} :
    BinYieldList G Bs args → MCFG.YieldList G Bs args
  | BinYieldList.nil => MCFG.YieldList.nil
  | BinYieldList.cons _ hy hrest => MCFG.YieldList.cons hy (binYieldList_to_orig hrest)

theorem binYieldList_join {G : MCFG N T} :
    ∀ Bs args,
      (∀ r', r' ∈ tailJoinRules G.dim Bs → r' ∈ (binarizeMCFG G).rules) →
      BinYieldList G Bs args →
      Bs.length ≥ 2 →
      MCFG.Yield (binarizeMCFG G) (BinMCFGNT.join Bs) args.flatten := by
  intro Bs
  match Bs with
  | [] => intro _ _ _ hlen; simp at hlen
  | [_] => intro _ _ _ hlen; simp at hlen
  | [X, Y] =>
    intro args hrules hyl _
    cases hyl with
    | cons hXb hX hrest =>
      cases hrest with
      | cons hYb hY hnil =>
        cases hnil
        have hr : { lhs := BinMCFGNT.join [X, Y], rhs := [BinMCFGNT.orig X, BinMCFGNT.orig Y],
                    yield := joinYield (T := T) (G.dim X) (G.dim Y) } ∈ (binarizeMCFG G).rules :=
          hrules _ (by simp [tailJoinRules])
        have hy := MCFG.Yield.rule hr (MCFG.YieldList.cons hXb (MCFG.YieldList.cons hYb MCFG.YieldList.nil))
        rw [← hX.length_eq, ← hY.length_eq, evalYield_joinYield] at hy
        simpa using hy
  | X :: Y :: Z :: rest =>
    intro args hrules hyl _
    cases hyl with
    | cons hXb hX hrest =>
      have htail := binYieldList_join (Y :: Z :: rest) _
        (fun r' hm => hrules r' (by simp [tailJoinRules, hm])) hrest (by simp)
      have hr : { lhs := BinMCFGNT.join (X :: Y :: Z :: rest),
                  rhs := [BinMCFGNT.orig X, BinMCFGNT.join (Y :: Z :: rest)],
                  yield := joinYield (T := T) (G.dim X) (sumDim G.dim (Y :: Z :: rest)) } ∈
          (binarizeMCFG G).rules :=
        hrules _ (by simp [tailJoinRules])
      have hy := MCFG.Yield.rule hr (MCFG.YieldList.cons hXb (MCFG.YieldList.cons htail MCFG.YieldList.nil))
      have hfl_len := flatten_length_eq_sumDim (binYieldList_to_orig hrest)
      rw [← hX.length_eq, ← hfl_len, evalYield_joinYield] at hy
      simpa using hy

mutual
  theorem binarizeMCFG_complete {G : MCFG N T} {A : N} {tup : List (List T)} :
      MCFG.Yield G A tup → MCFG.Yield (binarizeMCFG G) (BinMCFGNT.orig A) tup
    | MCFG.Yield.rule (r := r) hr hargs_raw => by
      have hargs := binarizeMCFG_complete_list hargs_raw
      match hrhs : r.rhs with
      | [] =>
        rw [hrhs] at hargs
        cases hargs
        have hr' : { lhs := BinMCFGNT.orig r.lhs, rhs := [], yield := r.yield } ∈ (binarizeMCFG G).rules :=
          List.mem_flatMap.mpr ⟨r, hr, by simp [binarizeRule, hrhs]⟩
        exact MCFG.Yield.rule hr' MCFG.YieldList.nil
      | [B0] =>
        rw [hrhs] at hargs
        cases hargs with
        | cons h0b _ hnil =>
          cases hnil
          have hr' : { lhs := BinMCFGNT.orig r.lhs, rhs := [BinMCFGNT.orig B0], yield := r.yield } ∈
              (binarizeMCFG G).rules :=
            List.mem_flatMap.mpr ⟨r, hr, by simp [binarizeRule, hrhs]⟩
          exact MCFG.Yield.rule hr' (MCFG.YieldList.cons h0b MCFG.YieldList.nil)
      | [B0, B1] =>
        rw [hrhs] at hargs
        cases hargs with
        | cons h0b _ hrest =>
          cases hrest with
          | cons h1b _ hnil =>
            cases hnil
            have hr' : { lhs := BinMCFGNT.orig r.lhs, rhs := [BinMCFGNT.orig B0, BinMCFGNT.orig B1],
                         yield := r.yield } ∈ (binarizeMCFG G).rules :=
              List.mem_flatMap.mpr ⟨r, hr, by simp [binarizeRule, hrhs]⟩
            exact MCFG.Yield.rule hr' (MCFG.YieldList.cons h0b (MCFG.YieldList.cons h1b MCFG.YieldList.nil))
      | B0 :: B1 :: B2 :: rest =>
        rw [hrhs] at hargs
        cases hargs with
        | @cons _ _ tup0 tailArgs h0b _ hrest =>
          have htail_rules : ∀ r', r' ∈ tailJoinRules G.dim (B1 :: B2 :: rest) →
              r' ∈ (binarizeMCFG G).rules := fun r' hm =>
            List.mem_flatMap.mpr ⟨r, hr, by simp [binarizeRule, hrhs, hm]⟩
          have hjoin := binYieldList_join (B1 :: B2 :: rest) tailArgs htail_rules hrest (by simp)
          have hr' : { lhs := BinMCFGNT.orig r.lhs,
                       rhs := [BinMCFGNT.orig B0, BinMCFGNT.join (B1 :: B2 :: rest)],
                       yield := remapYield G.dim (B1 :: B2 :: rest) r.yield } ∈ (binarizeMCFG G).rules :=
            List.mem_flatMap.mpr ⟨r, hr, by simp [binarizeRule, hrhs]⟩
          have hy := MCFG.Yield.rule hr' (MCFG.YieldList.cons h0b (MCFG.YieldList.cons hjoin MCFG.YieldList.nil))
          have hne := (G.rules_wf r hr).2.2
          have hev : MCFG.evalYield [tup0, tailArgs.flatten] (remapYield G.dim (B1 :: B2 :: rest) r.yield) =
              MCFG.evalYield (tup0 :: tailArgs) r.yield := by
            unfold MCFG.evalYield remapYield
            rw [List.map_map]
            apply List.map_congr_left
            intro comp hcomp
            apply evalComp_remap (binYieldList_to_orig hrest) comp
            intro i j hm
            have hvar : (i + 1, j) ∈ r.varOccurrences := by
              simp only [MCFGRule.varOccurrences, List.mem_flatMap, List.mem_filterMap]
              exact ⟨comp, hcomp, MCFGAtom.var (i + 1) j, hm, rfl⟩
            obtain ⟨B, hB, hj⟩ := (hne (i + 1) j).mp hvar
            rw [hrhs] at hB
            exact ⟨B, by simpa using hB, hj⟩
          rw [hev] at hy
          exact hy

  theorem binarizeMCFG_complete_list {G : MCFG N T} {Bs : List N} {args : List (List (List T))} :
      MCFG.YieldList G Bs args → BinYieldList G Bs args
    | MCFG.YieldList.nil => BinYieldList.nil
    | MCFG.YieldList.cons hy hrest =>
      BinYieldList.cons (binarizeMCFG_complete hy) hy (binarizeMCFG_complete_list hrest)
end

/-- MCFG Binarization Theorem: every Linear Non-Erasing MCFG has a weakly equivalent
    rank-≤-2 Linear Non-Erasing MCFG. -/
theorem binarizeMCFG_lang (G : MCFG N T) (w : List T) :
    (binarizeMCFG G).Lang w ↔ G.Lang w :=
  ⟨binarizeMCFG_sound, binarizeMCFG_complete⟩

end BinMCFG
end FormalLinguistics
