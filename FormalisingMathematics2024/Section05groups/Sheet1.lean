/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Groups

## How to use Lean's groups

In previous courses I have made groups from scratch, but it's kind of irritating
to do (because all the lemma names like `mul_one` are already taken) and I'm
not entirely sure that most students want to know how to make their own
groups, rings, whatever: what's the point if these things are there already?

So in this sheet I explain how to use Lean's groups.

-/

-- let G be a group
variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
/-  Let's see what just happened.
    The tactic state now looks like this:

    G : Type
    inst✝ : Group G
    g : G
    ⊢ g⁻¹ * g = 1

    So G is what most mathematicians would call a "set", and what in this course
    we call a "type" (they're the same thing as far as you're concerned), and
    `g : G` just mean "g is an element of G". The remaining thing is this
    `inst✝` thing, and that means "G has a multiplication `*`, an identity `1`,
    an inverse function `⁻¹`, and satisfies all the group axioms; furthermore
    all of this will be taken care of by "instances", which are a part
    of Lean's "type class inference system". The type class inference system
    is the system which deals with stuff in square brackets. You don't have
    to worry about it right now -- all that matters is that you have access
    to all the group axioms. This one is called `inv_mul_self g`.
-/
  inv_mul_self g

-- Why don't you use `exact?` to see the names of the other axioms
-- of a group? Note that when `exact?` has run, you can click on
-- the output (the blue output in the infoview) and replace `exact?`
-- with the name of the axiom it found. Note also that you can instead *guess*
-- the names of the axioms. For example what do you think the proof of `1 * a = a` is called?
example (a b c : G) : a * b * c = a * (b * c) := by
  rw[← mul_assoc]

-- can be found with `library_search` if you didn't know the answer already
example (a : G) : a * 1 = a := by
  rw[mul_one]

-- Can you guess the last two?
example (a : G) : 1 * a = a := by
  rw[one_mul]

example (a : G) : a * a⁻¹ = 1 := by
  rw[mul_inv_self]

-- As well as the axioms, Lean has many other standard facts which are true
-- in all groups. See if you can prove these from the axioms, or find them
-- in the library.
-- let a,b,c be elements of G in the below.
variable (a b c : G)

example : a⁻¹ * (a * b) = b := by
  rw[← mul_assoc, inv_mul_self, one_mul]

example : a * (a⁻¹ * b) = b := by
  rw[← mul_assoc, mul_inv_self, one_mul]


example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  -- hint for this one if you're doing it from first principles: `b * (a * c) = (b * a) * c`
  calc b = b * 1 := by rw[mul_one]
    _ = b * (a * c) := by rw[h2]
    _ = (b * a) * c := by rw[mul_assoc]
    _ = 1 * c := by rw[h1]
    _ = c := by rw[one_mul]

example : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  · intro h
    calc a⁻¹ = a⁻¹ * 1 := by rw[mul_one]
      _ = a⁻¹ * (a * b) := by rw[h]
      _ = (a⁻¹ * a) * b := by rw[mul_assoc]
      _ = 1 * b := by rw[inv_mul_self]
      _ = b := by rw[one_mul]
  · intro h
    calc a * b = a * a⁻¹ := by rw[h]
      _ = 1 := by rw[mul_inv_self]

example : (1 : G)⁻¹ = 1 := by
  apply inv_eq_iff_mul_eq_one.mpr
  exact one_mul 1

example : a⁻¹⁻¹ = a := by
  apply inv_eq_iff_mul_eq_one.mpr
  exact inv_mul_self a

theorem inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_iff_mul_eq_one.mpr
  calc (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by simp[mul_assoc]
    _ = a * 1 * a⁻¹ := by rw[mul_inv_self]
    _ = a * a⁻¹ := by rw[mul_one]
    _ = 1 := by rw[mul_inv_self]

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? There's also a `group`
tactic which does the same thing for groups. This tactic would have solved
many of the examples above.  NB the way it works is that it just uses
Lean's simplifier but armed with all the examples above; a theorem of Knuth and Bendix
says that these examples and the axioms of a group give a "confluent rewrite system"
which can solve any identity in group theory. If you like you can
try and prove the next example manually by rewriting with the lemmas above
(if you know their names, which you can find out with `exact?` or by
educated guessing).

-/
example : (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by group

-- Try this trickier problem: if g^2=1 for all g in G, then G is abelian
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  have j : ∀ g : G, g⁻¹ = g := by
    intro g
    apply inv_eq_iff_mul_eq_one.mpr
    rw[h g]
  intro g h
  calc g * h = g⁻¹ * h⁻¹ := by rw[j g, j h]
    _ = (h * g)⁻¹ := by rw[inv_mul]
    _ = h * g := by rw[j (h * g)]
