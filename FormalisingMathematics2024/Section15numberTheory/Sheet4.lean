/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

section Section15Sheet4
/-

# Prove that for all positive integers n we have that
# 169 | 3³ⁿ⁺³-26n-27

This is the fourth question in Sierpinski's book "250 elementary problems
in number theory".

Proof: note that n=0 also works :-) In general use induction on n.

Base case n=0 works fine.

Inductive step: we assume `169 ∣ 3³ⁿ⁺³-26d-27`
So it divides 27 times this
which is `3³⁽ᵈ⁺¹⁾⁺³-26*27*d-27*27`
and we want it to divide `3³⁽ᵈ⁺¹⁾⁺³-26(d+1)-27`

so we're done if it divides the difference, which is
`-26d-26-27+26*27d+27*27`
which is `26*26n+26*26 = 13*13*something`
-/

-- The statement has subtraction in, so we use integers.
example (n : ℕ) (hn : 0 < n) : -- remark; not going to use hn
    (169 : ℤ) ∣ 3 ^ (3 * n + 3) - 26 * n - 27 := by
  clear hn
  induction n with
  | zero =>
    simp
    norm_num
  | succ d ih =>
    rw[pow_add 3 (3 * Nat.succ d) 3, mul_comm, Nat.succ_eq_add_one, mul_add, mul_one]
    have ih2 : (169 : ℤ) ∣ 3 ^ 3 * (3 ^ (3 * d + 3) - 26 * d - 27) := by
      apply dvd_mul.mpr
      use 1 , 169
      constructor
      norm_num
      constructor
      exact ih
      norm_num
    have h : (169 : ℤ) ∣ 676 * (d + 1) := ⟨4 * (d + 1), by ring⟩   -- 676(d+1) = 169·4(d+1)

    convert dvd_add ih2 h using 1
    push_cast
    ring




end Section15Sheet4
