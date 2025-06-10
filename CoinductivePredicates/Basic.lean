/- import Std.Tactic.OpenPrivate -/
import Lean
import CoinductivePredicates.Parser
import CoinductivePredicates.Utils
import CoinductivePredicates.Binders
import CoinductivePredicates.Hacks

open Lean Meta Elab.Command
open Lean.Parser.Command (ctor)
open Elab (Modifiers elabModifiers)
open Elab.Term (BinderView)
open Parser.Term (namedArgument)
open PrettyPrinter (delab)
open Lean.Parser.Command

initialize registerTraceClass `Elab.coinductive

namespace Coind

/-- Generates the underlaying inveriant for the GUB -/
def generateInvariant (topView : CoinductiveView) (argArr : Array Ident) : CommandElabM Ident := do
  let id := topView.shortDeclName ++ `Invariant

  let v : Array (TSyntax ``ctor) ← topView.ctors.mapM $ handleCtor id

  let invariant ← `(command|
    inductive $(mkIdent id)
      $(←topView.binders.mapM binderViewtoBracketedBinder)*
      ($(topView.shortDeclName |> mkIdent) : $(topView.type))
      : $(topView.type) where $v*
  )

  trace[Elab.coinductive] invariant
  Elab.Command.elabCommand invariant

  return mkIdent id

  where
    handleCtor idNm view : CommandElabM (TSyntax ``ctor) := do
      let .some type := view.type? | throwErrorAt view.ref "Expected ret type" -- TODO: is this the case

      let ⟨args, out⟩ := typeToArgArr type
      let ⟨arr, id⟩ := appsToArgArr out

      -- Make sure name is correct
      match termToName id with
      | .some idNm => if idNm.isSuffixOf view.declName
                      then throwErrorAt id "Expected {topView.shortDeclName}"
      | _          =>      throwErrorAt id "Expected {topView.shortDeclName}"

      let arr := arr.toList.insertIdx topView.binders.size $ mkIdent topView.shortDeclName

      let out := Lean.Syntax.mkApp (mkIdent idNm) arr.toArray
      let out ← argArrToType args out

      let binders ← view.binders.mapM binderViewtoBracketedBinder

      let nm := view.declName.replacePrefix topView.declName .anonymous
      -- TODO: modifiers
      `(ctor| | $(mkIdent nm):ident $binders:bracketedBinder* : $out )

/-- Generate the full condition -/
def generateIs
    (invId : Ident)
    (id : Ident)
    (type : Term)
    (argArr : Array Ident)
    (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder)
    (relBinderNames : Array Ident)
    : CommandElabM Ident := do
  let stx ← `(command|
    abbrev $id $binders* (R : $type) : Prop :=
      ∀ { $argArr* }, R $argArr* → $invId $relBinderNames* R $argArr*)

  trace[Elab.coinductive] stx
  Elab.Command.elabCommand stx

  return id

/-- Generate the coind -/
def generatePred
    (condId : Ident)
    (id : Ident)
    (type : Term)
    (argIds : Array Ident)
    (binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder)
    (relBinderNames : Array Ident)
    : CommandElabM Unit := do
  let stx ← `(
    def $id $binders* : $type :=
      fun $argIds* => ∃ R, @$condId $relBinderNames:ident* R ∧ R $argIds* )

  trace[Elab.coinductive] stx
  Elab.Command.elabCommand stx

open Macro in
@[command_elab Parser.declaration]
def elabData : CommandElab := fun stx => do
  let view ← CoinductiveView.ofStx stx

  let ⟨tyArr, out⟩ := typeToArgArr view.type 
  let tyArr := tyArr.toArray
  -- List of unique names for the ids
  let argIds := (← tyArr.mapM (fun _ => Elab.Term.mkFreshBinderName)).map mkIdent

  let .node _ ``Parser.Term.prop _ := out.raw | throwErrorAt out "Expected return type to be a Prop"

  let relBinderNames := view.binders.map Lake.BinderSyntaxView.id
  let binders ← view.binders.mapM binderViewtoBracketedBinder
  let type := view.type

  let isId   := view.shortDeclName ++ `Is |> mkIdent
  let predId := view.shortDeclName |> mkIdent

  let id ← generateInvariant view argIds
  let id ← generateIs   id isId   type argIds binders relBinderNames
  let _  ← generatePred id predId type argIds binders relBinderNames

