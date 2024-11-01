import Egg

-- Checks that we rerun with shapes when proof reconstruction fails if `egg.retryWithShapes = true`.
-- Without rerunning with shapes, the first fails during proof reconstruction with the explanation
-- shown when setting `exitPoint := some .beforeProof`.

/--
error: egg failed to build proof: unification failure for LHS of rewrite #0:
  Nat.add
vs
  ?m.279
in
  Nat.add
and
  ()
-/
#guard_msgs in
set_option egg.retryWithShapes false in
example (h : ∀ u : Unit, u = .unit) : Nat.add = Nat.mul := by
  egg [h]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.retryWithShapes true in
example (h : ∀ u : Unit, u = .unit) : Nat.add = Nat.mul := by
  egg [h]