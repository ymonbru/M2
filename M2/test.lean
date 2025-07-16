import Batteries
import Mathlib
import Batteries.Lean.Position
import Batteries.CodeAction.Attr
import Lean.Server.CodeActions.Provider
import Lean.Elab.Tactic.Basic

open Lean Meta Elab Tactic Server RequestM CodeAction

namespace Batteries.CodeAction

#check Lean.Elab.TacticInfo.goalsBefore

/-@[tactic_code_action Lean.Parser.Tactic.simp]
def Test : TacticCodeAction := fun _ _ _ stk node => do
  --let .node (.ofTacticInfo info) _ := node | return #[]
  --unless info.goalsBefore.isEmpty do return #[]
  let  _ :: (seq, i) :: _ := stk | return #[]

  let some stop := seq.getTailPos? | return #[]
  let some prev := (seq.setArgs seq.getArgs[:i]).getTailPos? | return #[]
  let doc ← readDoc
  let eager := {
    title := "Je suis la"
    kind? := "quickfix"
    isPreferred? := true
    edit? := some <|.ofTextEdit doc.versionedIdentifier {
      range := doc.meta.text.utf8RangeToLspRange ⟨prev, stop⟩
      newText := "\n  skip"
    }
  }
  pure #[{ eager }]-/
@[tactic_code_action Lean.Parser.Tactic.dsimp]
def createCalc : TacticCodeAction := fun _params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  if info.goalsAfter.isEmpty then return #[]-- si simp termine le but alors stop
  let eager := {
    title := s!"Clique ici!"
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let tacPos := doc.meta.text.utf8PosToLspPos info.stx.getPos?.get!
      let endPos := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!


      let goal := info.goalsBefore[0]!

      let goalFmt ← ctx.runMetaM {} <| goal.withContext do ppExpr (← goal.getType)
      return { eager with
        edit? := some <|.ofTextEdit doc.versionedIdentifier
          { range := ⟨tacPos, endPos⟩, newText := s!"suffices {goalFmt} by simpa" }
      }
  }]

@[simps!]
def foo : ℕ × ℤ := (4, 2)


example : foo.1 = 5 := by
  suffices foo.1 = 5 by simpa

  sorry
