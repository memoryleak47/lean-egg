import Egg.Core.Config
import Egg.Core.Explanation
open Lean Meta

namespace Egg.Explanation

-- Note: Since we don't know lambda expressions' binder types, we pass fresh mvars instead. These
--       are assigned in `Explanation.proof`.
--
-- Note: If universe level erasure is active, we don't know constant expressions' universe level
--       parameters. We can figure out how many there need to be though and instantiate them with
--       fresh universe level mvars.
def Expression.toExpr (cfg : Config) : Expression → MetaM Expr
  | bvar idx          => return .bvar idx
  | fvar id           => return .fvar id
  | mvar id           => return .mvar id
  | sort lvl          => return .sort lvl
  | const name lvls   => mkConst name lvls.toList cfg.eraseULvls
  | app fn arg        => return .app (← toExpr cfg fn) (← toExpr cfg arg)
  | lam body          => return .lam .anonymous (← mkFreshExprMVar none) (← toExpr cfg body) .default
  | .forall type body => return .forallE .anonymous (← toExpr cfg type) (← toExpr cfg body) .default
  | lit l             => return .lit l
where
  mkConst (name : Name) (lvls : List Level) (erasedULvls : Bool) : MetaM Expr := do
    if erasedULvls
    then mkConstWithFreshMVarLevels name
    else return .const name lvls

-- BUG: `isDefEq` doesn't unify level mvars.
def proof (expl : Explanation) (cgr : Congr) (rws : Rewrites) (cfg : Config) : MetaM Expr := do
  withTraceNode `egg.reconstruction (fun _ => return "Reconstruction") do
    let mut current ← expl.start.toExpr cfg
    unless ← isDefEq cgr.lhs current do
      throwError s!"{errorPrefix} initial expression is not defeq to lhs of proof goal"
    let mut proof ← mkEqRefl current
    for step in expl.steps, idx in [:expl.steps.size] do
      let next ← step.dst.toExpr cfg
      let stepEq ← do
        withTraceNode `egg.reconstruction (fun _ => return m!"Step {idx}") do
          trace[egg.reconstruction] m!"Current: {current}"
          trace[egg.reconstruction] m!"Next:    {next}"
          proofStep current next step.toInfo
      proof ← mkEqTrans proof stepEq
      current := next
    match cgr.rel with
    | .eq  => return proof
    | .iff => mkIffOfEq proof
where
  errorPrefix := "'egg' tactic failed to reconstruct proof:"

  proofStep (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Expr := do
    let eqAtRw ← proofStepAtRwPos current next rwInfo
    let motive ← mkMotive current rwInfo.pos
    mkEqNDRec motive (← mkEqRefl current) eqAtRw

  proofStepAtRwPos (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Expr := do
    viewSubexpr (p := rwInfo.pos) (root := next) fun _ rhs => do
      viewSubexpr (p := rwInfo.pos) (root := current) fun _ lhs => do
        let some rw := rws.find? rwInfo.src | throwError s!"{errorPrefix} unknown rewrite"
        let freshRw ← (← rw.fresh).forDir rwInfo.dir
        withTraceNode `egg.reconstruction (fun _ => return m!"Rewrite {rwInfo.src.description}") do
          trace[egg.reconstruction] m!"Type: {freshRw.lhs} = {freshRw.rhs}"
          trace[egg.reconstruction] m!"Proof: {freshRw.proof}"
          trace[egg.reconstruction] m!"Holes: {freshRw.holes.map (Expr.mvar ·)}"
        withTraceNode `egg.reconstruction (fun _ => return m!"Unification at {rwInfo.pos}") do
          withTraceNode `egg.reconstruction (fun _ => return "LHS") (collapsed := false) do
            trace[egg.reconstruction] lhs
            trace[egg.reconstruction] freshRw.lhs
          withTraceNode `egg.reconstruction (fun _ => return "RHS") (collapsed := false) do
            trace[egg.reconstruction] rhs
            trace[egg.reconstruction] freshRw.rhs
        unless ← isDefEq lhs freshRw.lhs <&&> isDefEq rhs freshRw.rhs do
          throwError s!"{errorPrefix} unification failure"
        match freshRw.rel with
        | .eq  => return freshRw.proof
        | .iff => mkPropExt freshRw.proof

  mkMotive (lhs : Expr) (pos : SubExpr.Pos) : MetaM Expr :=
    viewSubexpr (p := pos) (root := lhs) fun _ target => do
      withLocalDecl .anonymous .default (← inferType target) fun fvar => do
        let rhs ← replaceSubexpr (fun _ => return fvar) pos lhs
        mkLambdaFVars #[fvar] (← mkEq lhs rhs)