import Egg

set_option trace.egg true in
variable (h : ∀ (p : Nat → Nat) (x : Nat), p x = p (x + 0)) in
example (f : Nat → Nat) : f x = f (x + 0) := by
  egg [h]

set_option trace.egg true in
variable (h : ∀ (p : Nat → Nat) (x : Nat), p x = p (x.add .zero)) in
example (f : Nat → Nat → Nat) : (f 1) x = (f 1) (x + 0) := by
  egg [h]





set_option egg.genTcProjRws false in
set_option trace.egg true in
variable (h : ∀ (p : Nat → Nat) (x : Nat), (p x) + 1 = (p (x + 0)) + 1) in
example (f : Nat → Nat → Nat) : (f x 1) + 1 = (f (x + 0) 1) + 1 := by
  egg [h]


example (p q : Nat → Prop) : ((∀ x, p x) ∧ (∀ x, q x)) ↔ ∀ x, p x ∧ q x := by
  egg [forall_and]

example (p q : Nat → Nat → Prop) : ((∀ x, p 1 x) ∧ (∀ x, q 1 x)) ↔ ∀ x, p 1 x ∧ q 1 x := by
  egg [forall_and]

example (p q : Nat → Nat → Prop) : ((∀ x, p x 1) ∧ (∀ x, q x 1)) ↔ ∀ x, p x 1 ∧ q x 1 := by
  egg [forall_and]




-- CRASH: When turning on proof erasure.
set_option egg.eraseProofs false in
theorem Array.get_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i.1 ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  sorry -- egg [set, Array.getElem_eq_data_get, List.get_set_ne _ h]

-- The universe mvars (or universe params if you make this a theorem instead of an example) are
-- different for the respective `α`s, so this doesn't hold by reflexivity. But `simp` can somehow
-- prove this.
example : (∀ α (l : List α), l.length = l.length) ↔ (∀ α (l : List α), l.length = l.length) := by
  set_option trace.egg true in egg

-- For rewrites involving dependent arguments, we can easily get an incorrect motive. E.g. when
-- rewriting the condition in ite without chaning the type class instance:
set_option trace.egg true in
example : (if 0 = 0 then 0 else 1) = 0 := by
  have h1 : (0 = 0) = True := eq_self 0
  have h2 : 0 = 0 := rfl
  egg [h1, h2, ite_congr, if_true]

-- For typeclass arguments we might be able to work around this by the following:
-- When a rewrite is applied to a term containing a typeclass argument (which we might be able to
-- track via e-class analysis), export that term, check if it's type correct, and if not,
-- try to resynthesize any contained typeclass instances. If this works reintroduce the typecorrect
-- term into the egraph.
-- How do we prove that this new term is equivalent to the old one though? Changing typeclass
-- instances isn't generally defeq.

-- Could it be that it is usually the case that if it makes sense to rewrite a dependent argument
-- by itself then its only dependents will be typeclass arguments (because otherwise the result
-- would need to involve a cast or something like that)?

-- Simp only somehow knows how to handle this:
set_option pp.explicit true in
theorem t : (if 0 = 0 then 0 else 1) = 0 := by
  have : (0 = 0) = True := eq_self 0
  simp only [this]
  sorry

-- Where does it pull `ite_congr` from? Does it have something to do with the `congr` attribute?
#print t
#check ite_congr
