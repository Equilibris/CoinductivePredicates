/- import Std.Tactic.OpenPrivate -/
import Lean

open Lean (Syntax TSyntax Term)
open Lean.Parser.Term (arrow app)

namespace Coind

/-- Transforms: a -> b -> c to ⟨#[a, b], c⟩ -/
def typeToArgArr (type : Term) : List Term × Term := go type.raw
  where go
    | Syntax.node _ ``arrow #[hd, _, tail] => Prod.map (⟨hd⟩ :: ·) id $ go tail
    | rest => ⟨[], ⟨rest⟩⟩

def argArrToType [Monad m] [Lean.MonadQuotation m] (args : List Term) (base : Term) : m Term :=
  args.reverse.foldlM (fun acc curr => `($curr → $acc)) base

def appsToArgArr (type : Term) : Array Term × Term :=
  match type.raw with
  | Syntax.node _ ``app #[v, cont] => ⟨cont.getArgs.map (⟨·⟩), ⟨v⟩⟩
  | rest => ⟨#[], ⟨rest⟩⟩

def termToName : Term → Option Lean.Name
  | ⟨.ident _ _ n _ ⟩ => .some n
  | _ => .none

