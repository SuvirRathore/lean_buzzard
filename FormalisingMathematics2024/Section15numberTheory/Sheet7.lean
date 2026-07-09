/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

section Section15Sheet7

/-

# Prove that for every positive integer n the number 3 × (1⁵ +2⁵ +...+n⁵)
# is divisible by 1³+2³+...+n³

This is question 9 in Sierpinski's book

-/

open scoped BigOperators

open Finset

example (n : ℕ) : ∑ i in range n, i ^ 3 ∣ 3 * ∑ i in range n, i ^ 5 := by
  have H3 : ∀ m : ℕ, 4 * ∑ i in range m, (i:ℤ)^3 = ((m:ℤ)^2 - m)^2 := by
    intro m
    induction m with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, mul_add]
      push_cast [ih]
      ring_nf
  have H5 : ∀ m : ℕ, 12 * ∑ i in range m, (i:ℤ)^5 = ((m:ℤ)^2 - m)^2 * (2*(m:ℤ)^2 - 2*m - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ d ih =>
      rw [Finset.sum_range_succ, mul_add]
      push_cast [ih]
      ring_nf
  have key : (4 : ℤ ) * (3 * ∑ i in range n, (i:ℤ)^5)
    = 4 * ((∑ i in range n, (i:ℤ)^3) * (2*(n:ℤ)^2 - 2*n - 1)) := by
    have e3 := H3 n
    have e5 := H5 n
    push_cast at e3 e5 ⊢
    linear_combination e5 - (2*(n:ℤ)^2 - 2*n - 1) * e3
  have hZ : 3 * ∑ i in range n, (i:ℤ)^5 = (∑ i in range n, (i:ℤ)^3) * (2*(n:ℤ)^2 - 2*n - 1) := by
    exact mul_left_cancel₀ (by norm_num : (4:ℤ) ≠ 0) key
  have hdvdZ : (∑ i in range n, (i:ℤ)^3) ∣ 3 * ∑ i in range n, (i:ℤ)^5 := by
    exact ⟨2*(n:ℤ)^2 - 2*n - 1, by rw [hZ] ⟩
  exact_mod_cast hdvdZ












end Section15Sheet7
