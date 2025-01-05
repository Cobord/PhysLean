/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Involutions
/-!

# Cardinality of full contractions

-/

namespace Wick
namespace Contractions

open HepLean.Fin
open Nat

/-- There are `(φs.length - 1)‼` full contractions of a list `φs` with an even number of fields. -/
lemma card_of_full_contractions_even {φs : List 𝓕} (he : Even φs.length) :
    Fintype.card {c : Contractions φs // IsFull c} = (φs.length - 1)‼ := by
  rw [Fintype.card_congr (isFullInvolutionEquiv (φs := φs))]
  exact involutionNoFixed_card_even φs.length he

/-- There are no full contractions of a list with an odd number of fields. -/
lemma card_of_full_contractions_odd {φs : List 𝓕} (ho : Odd φs.length) :
    Fintype.card {c : Contractions φs // IsFull c} = 0 := by
  rw [Fintype.card_eq_zero_iff, isEmpty_subtype]
  intro c
  simp only [IsFull]
  by_contra hn
  have hc := uncontracted_length_even_iff c
  rw [hn] at hc
  simp only [List.length_nil, even_zero, iff_true] at hc
  rw [← Nat.not_odd_iff_even] at hc
  exact hc ho

end Contractions

end Wick
