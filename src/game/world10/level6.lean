import game.world10.level5 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 6: `le_antisymm`

In Advanced Addition World you proved

`eq_zero_of_add_right_eq_self (a b : mynat) : a + b = a → b = 0`.

This might be useful in this level.

Another tip: if you want to create a new hypothesis, you can use the `have` tactic.
For example, if you have a hypothesis `hd : a + (c + d) = a` and you want 
a hypothesis `h : c + d = 0` then you can write

`have h := eq_zero_of_add_right_eq_self hd,`

-/

/- Lemma
$\le$ is antisymmetric. In other words, if $a\le b$ and $b\le a$ then $a = b$. 
-/
theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b :=
begin [nat_num_game]
  cases hab with c,
  cases hba with d,
  rw hab_h at hba_h,
  rw add_assoc at hba_h,
  symmetry at hba_h,
  have h := eq_zero_of_add_right_eq_self hba_h,
  have g := add_right_eq_zero h,
  symmetry,
  rw hab_h,
  rw g,
  rw add_zero,
  refl,


end
/-
Congratulations -- you just proved that the natural numbers are a partial order!
-/

instance : partial_order mynat := by structure_helper
end mynat -- hide
