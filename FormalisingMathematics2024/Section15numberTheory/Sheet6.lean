import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.PrimeNormNum

section Section15Sheet6
/-

# Prove the theorem, due to Kraichik, asserting that 13|2⁷⁰+3⁷⁰

This is the sixth question in Sierpinski's book "250 elementary problems
in number theory".

-/

example : 13 ∣ 2 ^ 70 + 3 ^ 70 := by
  apply (ZMod.nat_cast_zmod_eq_zero_iff_dvd _ 13).mp
  push_cast
  ring_nf
  decide

end Section15Sheet6
