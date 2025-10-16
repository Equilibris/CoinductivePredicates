import Lean
import Lake.Util.Binder

open Lean
open Parser
open Parser.Command
open Elab (expandDeclId liftMacroM Modifiers elabModifiers)
open Elab.Command (CommandElabM checkValidCtorModifier getLevelNames)
open Lake (BinderSyntaxView expandBinders)

namespace Parser

/-- Base parser for syntax, taken from syntax for `inductive` -/
def coind : Parser :=
  leading_parser "coinductive " >> declId
                     >> Command.declSig
                     >> Lean.Parser.optional (symbol " :=" <|> " where")
                     >> many ctor
                     /- >> optDeriving -/

@[command_parser]
def declaration : Parser := leading_parser declModifiers false >> coind
end Parser

structure CoinductiveView.CtorView where
  ref       : Syntax
  modifiers : Modifiers
  declName  : Name
  binders   : Array BinderSyntaxView
  type?     : Option Term
  deriving Inhabited

structure CoinductiveView : Type where
  ref             : TSyntax ``Parser.declaration
  declId          : TSyntax ``Parser.Command.declId
  modifiers       : Modifiers
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Array BinderSyntaxView
  type            : Term
  ctors           : Array CoinductiveView.CtorView
  /- derivingClasses : Array Lean.Elab.DerivingClassView -/
  /- computedFields  : Array Lean.Elab.Command.ComputedFieldView -/
  deriving Inhabited

namespace CoinductiveView

def CtorView.ofStx (declName : Name) (modifiers : Modifiers) (ref : Syntax) : CommandElabM CtorView := do
  let mut ctorModifiers ← elabModifiers ⟨ref[2]⟩
  if let some leadingDocComment := ref[0].getOptional? then
    if ctorModifiers.docString?.isSome then
      logErrorAt leadingDocComment "duplicate doc string"
    ctorModifiers := { ctorModifiers with docString? := .some ⟨⟨leadingDocComment⟩, true⟩ }
  if ctorModifiers.isPrivate && modifiers.isPrivate then
    throwError "invalid 'private' constructor in a 'private' inductive datatype"
  if ctorModifiers.isProtected && modifiers.isPrivate then
    throwError "invalid 'protected' constructor in a 'private' inductive datatype"

  checkValidCtorModifier ctorModifiers
  let ctorName := ref.getIdAt 3
  let ctorName := declName ++ ctorName
  let ctorName ← withRef ref[3] $ Elab.applyVisibility ctorModifiers ctorName
  let (binders, type?) := Elab.expandOptDeclSig ref[4]
  -- TODO
  /- addDocString' ctorName ctorModifiers.docString? -/

  -- TODO: Check this is correctly updated
  Elab.addDeclarationRangesFromSyntax ctorName ref ref[3]

  let binders ← liftMacroM $ expandBinders binders.getArgs

  return { ref, modifiers := ctorModifiers, declName := ctorName, binders, type? := type?.map (⟨·⟩) }

/- open private toBinderViews from Lean.Elab.Binders in -/
def ofStx (stx : Syntax) : CommandElabM CoinductiveView := do
  let modifiers ← elabModifiers ⟨stx[0]⟩
  let decl := stx[1]
  let (binders, type) := Elab.expandDeclSig decl[2]!

  let binders ← liftMacroM $ expandBinders binders.getArgs

  let currNamespace ← getCurrNamespace
  let currLevelNames ← getLevelNames
  let declId : TSyntax ``Command.declId := ⟨decl[1]⟩
  let {
    shortName := shortDeclName,
    declName,
    levelNames,
    docString? := _
  } ← Elab.Command.liftTermElabM $ expandDeclId currNamespace currLevelNames declId modifiers

  let ctors ← decl[4].getArgs.mapM $ CtorView.ofStx declName modifiers

  Elab.addDeclarationRangesFromSyntax declName decl

  let out := {
    ref := ⟨decl⟩

    declName
    shortDeclName

    levelNames
    type := ⟨type⟩

    binders
    ctors

    declId
    modifiers
  }

  -- TODO: Here a check should be done to ensure that the ret-type is Prop

  return out

end CoinductiveView
