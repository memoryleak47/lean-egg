import Lean
import Std.Lean.HashSet

def List.replicateM [Monad m] (count : Nat) (f : m α) : m (List α) := do
  let mut result := []
  for _ in [0:count] do
    result := result.concat (← f)
  return result

namespace Lean

-- Note: The `_uniq` prefix comes from the `MonadNameGenerator`.

def FVarId.uniqueIdx! : FVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique fvar-id"

def FVarId.fromUniqueIdx (idx : Nat) : FVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

def MVarId.uniqueIdx! : MVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique mvar-id"

def MVarId.fromUniqueIdx (idx : Nat) : MVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

def LMVarId.uniqueIdx! : LMVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique level mvar-id"

def LMVarId.fromUniqueIdx (idx : Nat) : LMVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

def Level.levelMVars : Level → HashSet LMVarId
    | mvar id                => {id}
    | zero | param _         => ∅
    | succ l                 => l.levelMVars
    | max l₁ l₂ | imax l₁ l₂ => l₁.levelMVars.merge l₂.levelMVars

def Expr.levelMVars : Expr → HashSet LMVarId
  | sort lvl => lvl.levelMVars
  | const _ lvls => lvls.foldl (·.merge ·.levelMVars) ∅
  | bvar _ | fvar _ | mvar _ | lit _ => ∅
  | mdata _ e | proj _ _ e => e.levelMVars
  | app e₁ e₂ | lam _ e₁ e₂ _ | forallE _ e₁ e₂ _ => e₁.levelMVars.merge e₂.levelMVars
  | letE _ e₁ e₂ e₃ _ => e₁.levelMVars.merge e₂.levelMVars |>.merge e₃.levelMVars

deriving instance BEq, Hashable for SubExpr.Pos

def HashMap.insertIfNew [BEq α] [BEq β] [Hashable α] [Hashable β]
    (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  if m.contains a then m else m.insert a b
