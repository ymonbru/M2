import Mathlib
import Batteries

namespace Batteries.CodeAction

open Lean Meta Elab Tactic Server RequestM CodeAction

@[tactic_code_action Lean.Parser.Tactic.dsimp]
def Suffices : TacticCodeAction := fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]

  let eager := {
    title := s!"Clic"
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let tacPos := doc.meta.text.utf8PosToLspPos info.stx.getPos?.get!
      let endPos := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!

      let goal := info.goalsAfter[0]!
      --let goal := info.goalsBefore[0]!

      -- here ctx is the context before applying the tactic not the tactic
      let goalFmt ← ctx.runMetaM  {} <| goal.withContext do ppExpr (← goal.getType)


      return { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier
          { range := ⟨tacPos, endPos⟩, newText := s!"suffices {goalFmt} by dsimp;assumption" }
      }
  }]

@[simps]
def foo : ℕ × ℤ := (4, 2)

example : foo.1 = 5 := by
  dsimp
  -- i would like :
  --suffices 4 = 5 by dsimp;assumption
  sorry
