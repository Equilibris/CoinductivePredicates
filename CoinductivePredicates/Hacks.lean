/- import Std.Tactic.OpenPrivate -/
import Lean
import CoinductivePredicates.Parser

open Lean (TSyntax)
open Lean.Parser (Parser)
open Lean.Parser.Term (bracketedBinder matchAlts)

namespace Coind

abbrev bb            : Parser := bracketedBinder
abbrev matchAltExprs : Parser := matchAlts

/- Since `bb` and `matchAltExprs` are aliases for `bracketedBinder`, resp. `matchAlts`,
we can safely coerce syntax of these categories  -/
instance : Coe (TSyntax ``bb) (TSyntax ``bracketedBinder)      where coe x := ⟨x.raw⟩
instance : Coe (TSyntax ``matchAltExprs) (TSyntax ``matchAlts) where coe x := ⟨x.raw⟩

