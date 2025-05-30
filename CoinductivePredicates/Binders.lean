/- import Std.Tactic.OpenPrivate -/
import Lean
import CoinductivePredicates.Parser
import CoinductivePredicates.Hacks

open Lean (TSyntax)
open Lean.Parser.Term (bracketedBinder)
open Lean.Elab.Command (CommandElabM)

namespace Coind

def binderViewtoBracketedBinder
    (v : Lake.BinderSyntaxView)
    : CommandElabM $ TSyntax ``bracketedBinder := do
  match v.info with
  | .default =>        `(bb|( $(⟨v.id⟩):ident : $(⟨v.type⟩) ))
  | .implicit =>       `(bb|{ $(⟨v.id⟩):ident : $(⟨v.type⟩) })
  | .strictImplicit => `(bb|⦃ $(⟨v.id⟩):ident : $(⟨v.type⟩) ⦄)
  | .instImplicit =>   `(bb|[ $(⟨v.id⟩):ident : $(⟨v.type⟩) ])
