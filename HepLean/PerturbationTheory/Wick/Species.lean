/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Function.Basic
import HepLean.Meta.Informal.Basic
import HepLean.Meta.Notes.Basic
/-!

# Wick Species

Note: There is very likely a much better name for what we here call a Wick Species.

A Wick Species is a structure containing the basic information needed to write wick contractions
for a theory, and calculate their corresponding Feynman diagrams.

-/

/-! TODO: There should be some sort of notion of a group action on a Wick Species. -/
namespace Wick

note "
<h2>Wick Species</h2>

To do perturbation theory for a quantum field theory, we need a quantum field theory, or
at least enough data from a quantum field theory to write down necessary constructions.
The first bit of data we need is a type of fields `𝓯`. We also need to know what fields
are dual to what other fields, for example in a complex scalar theory `φ` is dual to `φ†`.
We can encode this information in an involution `ξ : 𝓯 → 𝓯`.
<br><br>
...
<br><br>
This necessary information to do perturbation theory is encoded in a `Wick Species`, which
we define as:
"

/-- The basic structure needed to write down Wick contractions for a theory and
  calculate the corresponding Feynman diagrams.

  WARNING: This definition is not yet complete. -/
@[note_attr]
structure Species where
  /-- The color of Field operators which appear in a theory.
    One may wish to call these `half-edges`, however we restrict this terminology
    to Feynman diagrams. -/
  𝓯 : Type
  /-- The map taking a field operator to its dual operator. -/
  ξ : 𝓯 → 𝓯
  /-- The condition that `ξ` is an involution. -/
  ξ_involutive : Function.Involutive ξ
  /-- The color of interaction terms which appear in a theory.
    One may wish to call these `vertices`, however we restrict this terminology
    to Feynman diagrams. -/
  𝓘 : Type
  /-- The fields associated to each interaction term. -/
  𝓘Fields : 𝓘 → Σ n, Fin n → 𝓯

namespace Species

variable (S : Species)

informal_definition 𝓕 where
  math :≈ "The orbits of the involution `ξ`.
    May have to define a multiplicative action of ℤ₂ on `𝓯`, and
    take the orbits of this."
  physics :≈ "The different types of fields present in a theory."
  deps :≈ [``Species]

end Species

end Wick
