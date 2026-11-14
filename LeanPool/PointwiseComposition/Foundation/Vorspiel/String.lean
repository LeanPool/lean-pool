/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace String

/-- The vec To Str construction in `String`. -/
def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0, _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))

end String

end

end PointwiseComposition
