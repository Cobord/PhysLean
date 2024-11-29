/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
import HepLean.Meta.Informal
/-!

# Operator algebra

Currently this file is only for an example of Wick strings, correpsonding to a
theory with two complex scalar fields. The concepts will however generalize.

This file is currently a stub.

We will formally define the operator ring, in terms of the fields present in the theory.

## Futher reading

- https://physics.stackexchange.com/questions/258718/ and links therein
- Ryan Thorngren (https://physics.stackexchange.com/users/10336/ryan-thorngren), Fermions,
  different species and (anti-)commutation rules, URL (version: 2019-02-20) :
  https://physics.stackexchange.com/q/461929
-/

namespace TwoComplexScalar
open CategoryTheory
open FeynmanDiagram
open PreFeynmanRule

informal_definition WickAlgebra where
  math :≈ "
    Modifications of this may be needed.
    A structure with the following data:
    - A ℤ₂-graded algebra A.
    - A map from `ψ : 𝓔 × SpaceTime → A` where 𝓔 are field colors.
    - A map `ψ₊ :  𝓔 × SpaceTime → A`.
    - A map `ψ₋ :  𝓔 × SpaceTime → A`.
    Subject to the conditions:
    - The sum of `ψ0` and `ψ1` is `ψ`.
    - Two fields super-commute if there colors are not dual to each other.
    - The super-commutator of two fields is always in the
      center of the algebra. "
  ref :≈ "https://physics.stackexchange.com/questions/24157/"

informal_definition WickMonomial where
  math :≈ "The type of elements of the Wick algebra which is a product of fields."
  deps :≈ [``WickAlgebra]

namespace WickMonomial

informal_definition toWickAlgebra where
  math :≈ "A function from WickMonomial to WickAlgebra which takes a monomial and
    returns the product of the fields in the monomial."
  deps :≈ [``WickAlgebra, ``WickMonomial]

informal_definition timeOrdering where
  math :≈ "A function from WickMonomial to WickAlgebra which takes a monomial and
    returns the monomial with the fields time ordered, with the correct sign
    determined by the Koszul sign factor."
  deps :≈ [``WickAlgebra, ``WickMonomial]

informal_definition normalOrdering where
  math :≈ "A function from WickMonomial to WickAlgebra which takes a monomial and
    returns the element in `WickAlgebra` defined as follows
    - The ψ₊ fields are move to the right.
    - The ψ₋ fields are moved to the left.
    - Othewise the order of the fields is preserved."
  ref :≈ "https://www.imperial.ac.uk/media/imperial-college/research-centres-and-groups/theoretical-physics/msc/current/qft/handouts/qftwickstheorem.pdf"
  deps :≈ [``WickAlgebra, ``WickMonomial]

end WickMonomial

informal_definition contraction where
  math :≈ "Given two `i j : 𝓔 × SpaceTime`, the element of WickAlgebra
    defined by subtracting the normal ordering of `ψ i ψ j` from the time-ordering of
    `ψ i ψ j`."
  deps :≈ [``WickAlgebra, ``WickMonomial]

end TwoComplexScalar
