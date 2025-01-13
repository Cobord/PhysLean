/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

## Informal definitions and lemmas

This file contains the necessary structures that must be imported into a file
for it to contain informal definitions and lemmas.

Everything else about informal definitions and lemmas are in the `Informal.Post` module.

-/
open Lean Elab System

/-! TODO: Can likely make this a bona-fide command. -/

/-- The structure representing an informal definition. -/
structure InformalDefinition where
  /-- The name of the informal definition. This is autogenerated. -/
  name : Name
  /-- The mathematical description of the definition. -/
  math : String
  /-- The physics description of the definition. -/
  physics : String
  /-- References. -/
  ref : String
  /-- The names of top-level commands we expect this definition to depend on. -/
  dependencies : List Name

/-- The structure representing an informal proof. -/
structure InformalLemma where
  /-- The name of the informal lemma. This is autogenerated. -/
  name : Name
  /-- The mathematical description of the lemma. -/
  math : String
  /-- The physics description of the lemma. -/
  physics : String
  /-- A description of the proof. -/
  proof : String
  /-- References. -/
  ref : String
  /-- The names of top-level commands we expect this lemma to depend on. -/
  dependencies : List Name

namespace Informal

/-- The Parser.Category we will use for assignments. -/
declare_syntax_cat informalAssignment

/-- The syntax describing an informal assignment of `ident` to a string. -/
syntax (name := informalAssignment) ident ":≈" str : informalAssignment

/-- The syntax describing an informal assignment of `ident` to a list. -/
syntax (name := informalAssignmentDeps) ident ":≈" "[" sepBy(term, ",") "]" : informalAssignment

/-!

## Syntax

-/
/-- The syntax for the command informal_definition. -/
syntax (name := informal_definition) "informal_definition " ident
  " where " (colGt informalAssignment)* : command

/-- An informal definition is a definition which is not type checked, and is written
  as a string literal. It can be used to plan out sections for future formalization, or to
  include results which the formalization is not immediately known.
  Each informal definition must included a
  `math :≈ "..."`
  entry, but can also include the following entries
  `physics :≈ "..."`, `ref :≈ "..."`, and `deps :≈ [...]`. -/
macro "informal_definition " name:ident " where " assignments:informalAssignment* : command => do
  let mut math_def? : Option (TSyntax `term) := none
  let mut physics_def? : Option (TSyntax `term) := none
  let mut ref_def? : Option (TSyntax `term) := none
  let mut dep_def? : Option (TSyntax `term) := none
  for assignment in assignments do
    match assignment with
    | `(informalAssignment| physics :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for physics"
      physics_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| math :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for math"
      math_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| ref :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for ref"
      ref_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignmentDeps| deps :≈ [$deps,*]) =>
      dep_def? := some (← `([$deps,*]))
    | _ => Macro.throwError "invalid assignment syntax in informal_definition"
  unless math_def?.isSome do
    Macro.throwError "A 'math' assignments is required"
  `(
/-- An informal definition. -/
def $name : InformalDefinition := {
  name := $(Lean.quote name.getId),
  physics := $(physics_def?.getD (← `("No physics description provided"))),
  math := $(math_def?.getD (panic! "math not assigned")),
  ref := $(ref_def?.getD (← `("No references provided"))),
  dependencies := $(dep_def?.getD (← `([])))
    })

/-- The syntax for the command informal_definition. -/
syntax (name := informal_definition_note) "informal_definition_note " ident
  " where " (colGt informalAssignment)* : command

/-- An informal definition is a definition which is not type checked, and is written
  as a string literal. It can be used to plan out sections for future formalization, or to
  include results which the formalization is not immediately known.
  Each informal definition must included a
  `math :≈ "..."`
  entry, but can also include the following entries
  `physics :≈ "..."`, `ref :≈ "..."`, and `deps :≈ [...]`. -/
macro "informal_definition_note " name:ident " where " assignments:informalAssignment* :
    command => do
  let mut math_def? : Option (TSyntax `term) := none
  let mut physics_def? : Option (TSyntax `term) := none
  let mut ref_def? : Option (TSyntax `term) := none
  let mut dep_def? : Option (TSyntax `term) := none
  for assignment in assignments do
    match assignment with
    | `(informalAssignment| physics :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for physics"
      physics_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| math :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for math"
      math_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| ref :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for ref"
      ref_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignmentDeps| deps :≈ [$deps,*]) =>
      dep_def? := some (← `([$deps,*]))
    | _ => Macro.throwError "invalid assignment syntax in informal_definition"
  unless math_def?.isSome do
    Macro.throwError "A 'math' assignments is required"
  `(
/-- An informal definition. -/
@[note_attr_informal]
def $name : InformalDefinition := {
  name := $(Lean.quote name.getId),
  physics := $(physics_def?.getD (← `("No physics description provided"))),
  math := $(math_def?.getD (panic! "math not assigned")),
  ref := $(ref_def?.getD (← `("No references provided"))),
  dependencies := $(dep_def?.getD (← `([])))
    })

/-- The syntax for the command `informal_lemma`. -/
syntax (name := informal_lemma) "informal_lemma " ident " where "
  (colGt informalAssignment)* : command

/-- An informal lemma is a lemma which is not type checked, and is written
  as a string literal. It can be used to plan out sections for future formalization, or to
  include results which the formalization is not immediately known.
  Every informal lemma must included a
  `math :≈ "..."`
  entry, but can also include the following entries
  `physics :≈ "..."`, `proof :≈ "..."`, `ref :≈ "..."`, and `deps :≈ [...]`. -/
macro "informal_lemma " name:ident " where " assignments:informalAssignment* : command => do
  let mut math_def? : Option (TSyntax `term) := none
  let mut physics_def? : Option (TSyntax `term) := none
  let mut proof_def? : Option (TSyntax `term) := none
  let mut ref_def? : Option (TSyntax `term) := none
  let mut dep_def? : Option (TSyntax `term) := none
  for assignment in assignments do
    match assignment with
    | `(informalAssignment| physics :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for physics"
      physics_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| math :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for math"
      math_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| proof :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for proof"
      proof_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| ref :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for ref"
      ref_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignmentDeps| deps :≈ [$deps,*]) =>
      dep_def? := some (← `([$deps,*]))
    | _ => Macro.throwError "invalid assignment syntax"
  unless math_def?.isSome do
    Macro.throwError "A 'math' assignments is required"
  `(
/-- An informal lemma. -/
def $name : InformalLemma := {
  name := $(Lean.quote name.getId),
  physics := $(physics_def?.getD (← `("No physics description provided"))),
  math := $(math_def?.getD (panic! "math not assigned")),
  proof := $(proof_def?.getD (← `("No proof description provided"))),
  ref := $(ref_def?.getD (← `("No references provided"))),
  dependencies := $(dep_def?.getD (← `([])))
    })

/-- The syntax for the command `informal_lemma`. -/
syntax (name := informal_lemma_note) "informal_lemma_note " ident " where "
  (colGt informalAssignment)* : command

/-- An informal lemma is a lemma which is not type checked, and is written
  as a string literal. It can be used to plan out sections for future formalization, or to
  include results which the formalization is not immediately known.
  Every informal lemma must included a
  `math :≈ "..."`
  entry, but can also include the following entries
  `physics :≈ "..."`, `proof :≈ "..."`, `ref :≈ "..."`, and `deps :≈ [...]`. -/
macro "informal_lemma_note " name:ident " where " assignments:informalAssignment* : command => do
  let mut math_def? : Option (TSyntax `term) := none
  let mut physics_def? : Option (TSyntax `term) := none
  let mut proof_def? : Option (TSyntax `term) := none
  let mut ref_def? : Option (TSyntax `term) := none
  let mut dep_def? : Option (TSyntax `term) := none
  for assignment in assignments do
    match assignment with
    | `(informalAssignment| physics :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for physics"
      physics_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| math :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for math"
      math_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| proof :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for proof"
      proof_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignment| ref :≈ $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for ref"
      ref_def? := some (← `($(Lean.quote strVal)))
    | `(informalAssignmentDeps| deps :≈ [$deps,*]) =>
      dep_def? := some (← `([$deps,*]))
    | _ => Macro.throwError "invalid assignment syntax"
  unless math_def?.isSome do
    Macro.throwError "A 'math' assignments is required"
  `(
/-- An informal lemma. -/
@[note_attr_informal]
def $name : InformalLemma := {
  name := $(Lean.quote name.getId),
  physics := $(physics_def?.getD (← `("No physics description provided"))),
  math := $(math_def?.getD (panic! "math not assigned")),
  proof := $(proof_def?.getD (← `("No proof description provided"))),
  ref := $(ref_def?.getD (← `("No references provided"))),
  dependencies := $(dep_def?.getD (← `([])))
    })

end Informal
