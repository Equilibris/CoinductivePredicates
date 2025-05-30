/- import Std.Tactic.OpenPrivate -/
import Lean
import CoinductivePredicates.Parser
import CoinductivePredicates.Utils
import CoinductivePredicates.Binders
import CoinductivePredicates.Hacks

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)
open Elab.Term (BinderView)
open Parser.Term (namedArgument)
open PrettyPrinter (delab)
open Lean.Parser.Command

namespace Coind

/-- Generates the underlaying inveriant for the GUB -/
def generateIs
    (topView : CoinductiveView)
    (argArr : Array Ident)
    (tyArr : Array Term)
    : CommandElabM Unit := do
  let id := topView.shortDeclName ++ `Invariant

  let isTy ← `($(mkIdent id)
    $(topView.binders.map (⟨·.id⟩))*
    $(mkIdent topView.shortDeclName)
    $argArr*)

  let v : Array (TSyntax ``ctor) ← topView.ctors.mapM $ handleCtor isTy

  let x ← argArr.zip tyArr |>.mapM (fun ⟨id, v⟩ => `(bb| ($id : $v) ))

  let invariant ← `(command|
    inductive $(mkIdent id)
      $(←topView.binders.mapM binderViewtoBracketedBinder)*
      ($(topView.shortDeclName |> mkIdent) : $(topView.type))
      $x* : Prop where $v*
  )
  let stx ← `(command|
    abbrev $(topView.shortDeclName ++ `Is |> mkIdent) $(←topView.binders.mapM binderViewtoBracketedBinder)* (R : $(topView.type)) : Prop :=
      ∀ { $argArr* }, R $argArr* → $(mkIdent id) $(topView.binders.map (⟨·.id⟩))* R $argArr*)

  Elab.Command.elabCommand invariant
  Elab.Command.elabCommand stx

  where
    correctorIterator (loc : Term)
      | ⟨.ident _ _ nm _⟩ :: tla, binderV :: tlb => do
        let nmx := binderV.id.getId
        if nm == nmx then correctorIterator loc tla tlb
        else throwErrorAt loc s!"Expected {binderV.id}"
      | loc :: _, binderV :: _ => throwErrorAt loc s!"Expected {binderV.id}"
      | rest, [] =>
        pure rest
      | [], _ => throwErrorAt loc "Insufficent arguments"

    handleRetty appl arr id := do
      let .ident _ _ nm _ := id.raw  | throwErrorAt id s!"Expected return type to be {topView.declId}" 
      if nm != topView.shortDeclName then throwErrorAt id s!"Expected return type to be {topView.declId}"

      correctorIterator appl arr.toList topView.binders.toList

    -- Removal array × Equational array
    equationalTransformer (loc : Term) : List Term → List Ident → CommandElabM ((List (Ident × Ident)) × (List Term))
      | [], [] => return Prod.mk [] []
      | x@⟨.ident _ _ _ _⟩ :: tla, hdb :: tlb => do
        let ⟨rem, eq⟩ ← equationalTransformer loc tla tlb
        return ⟨(Prod.mk ⟨x.raw⟩ hdb) :: rem, eq⟩
      | hda :: tla, hdb :: tlb => do
        let ⟨rem, eq⟩ ← equationalTransformer loc tla tlb
        return ⟨rem, (←`($hda = $hdb)) :: eq⟩
      | [], _ | _, [] => throwErrorAt loc "Incorrect number of arguments"

    handleCtor isTy view := do
      let nm := view.declName.replacePrefix topView.declName .anonymous

      let .some type := view.type? | throwErrorAt view.ref "An coinductive predicate without a retty could better be expressed inductively" -- TODO: is this the case
      let ⟨args, out⟩ := typeToArgArr type

      let ⟨arr, id⟩ := appsToArgArr out
      let arr ← handleRetty out arr id

      let ⟨eqRpl, eqs⟩ ← equationalTransformer out arr argArr.toList

      let binders := view.binders.filter fun x => eqRpl.find? (fun v => x.id.getId == v.fst.getId) |>.isNone
      let binders ← binders.mapM binderViewtoBracketedBinder

      let out ← (eqs.toArray ++ args).reverse.foldlM (fun acc curr => `($curr → $acc)) isTy
      let out ← `(ctor| | $(mkIdent nm):ident $binders* : $out)

      let out ← eqRpl.foldlM (fun term ⟨src, rpl⟩ =>
        let src := src.getId
        term.replaceM (fun
          | .ident _ _ nm _ =>
            if nm == src then return some rpl
            else return none
          | _ => return none)) out.raw

      return ⟨out⟩

def preprocessView (view : CoinductiveView) (argArr : Array Term) (out : Term) : CommandElabM CoinductiveView := do
  let .node _ ``Parser.Term.prop _ := out.raw | throwErrorAt out "Expected return type to be a Prop"
  throwError "lol"

open Macro in
@[command_elab Parser.declaration]
def elabData : CommandElab := fun stx => do
  let view ← CoinductiveView.ofStx stx

  let ⟨tyArr, out⟩ := typeToArgArr view.type
  let argArr := (← tyArr.mapM (fun _ => Elab.Term.mkFreshBinderName)).map mkIdent

  /- let view ← preprocessView view argArr out -/
  let .node _ ``Parser.Term.prop _ := out.raw | throwErrorAt out "Expected return type to be a Prop"

  generateIs view argArr tyArr
  let stx ← `(
    def $(view.shortDeclName |> mkIdent) $(←view.binders.mapM binderViewtoBracketedBinder)* : $(view.type) :=
      fun $argArr* => ∃ R, @$(view.shortDeclName ++ `Is |> mkIdent) $(view.binders.map (⟨·.id⟩)):ident* R ∧ R $argArr* )
  Elab.Command.elabCommand stx
end Coind

