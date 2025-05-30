/- import Std.Tactic.OpenPrivate -/
import Lean

open Lean (Syntax TSyntax Term)
open Lean.Parser.Term (arrow app)

namespace Coind

partial def typeToArgArr
    (type : Term)
    : Array Term × Term := Prod.map List.toArray id $ go type.raw
  where go
    | Syntax.node _ ``arrow #[hd, _, tail] => Prod.map (⟨hd⟩ :: ·) id $ go tail
    | rest => ⟨[], ⟨rest⟩⟩

def appsToArgArr (type : Term) : Array Term × Term :=
  match type.raw with
  | Syntax.node _ ``app #[v, cont] => ⟨cont.getArgs.map (⟨·⟩), ⟨v⟩⟩
  | rest => ⟨#[], ⟨rest⟩⟩
