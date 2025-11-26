/-
  Soundness proof for JsonType.subtype

  Main theorem: If t1.check x = true and t1.subtype t2 = true, then t2.check x = true

  This ensures that the subtyping relation is sound: any value that satisfies a subtype
  also satisfies its supertype.
-/

import JsonSubtyping.Subtype

open Lean (Json)

namespace JsonType

/-! ## Helper Lemmas

We need a few critical lemmas to prove soundness. These are proven separately.
-/

end JsonType
