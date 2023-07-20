import game.world9.level1 -- hide
namespace mynat -- hide

/-
# Advanced Multiplication World

## Level 2: `eq_zero_or_eq_zero_of_mul_eq_zero`

A variant on the previous level.
-/

/- Theorem
If $ab = 0$, then at least one of $a$ or $b$ is equal to zero.
-/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :
  a = 0 ∨ b = 0 :=
begin [nat_num_game]
  cases a with n,
  left,
  refl,
  right,
  rw succ_mul at h,
  rw add_left_eq_zero h,
  refl,

end

end mynat -- hide
