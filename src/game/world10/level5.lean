import game.world10.level4 -- hide
namespace mynat -- hide
/- 

# Inequality world. 

## Level 5: `le_trans`

Another straightforward one. 
-/


/- Lemma
≤ is transitive. In other words, if $a\leq b$ and $b\leq c$ then $a\leq c$. 
-/
theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin [nat_num_game]
  cases a with d hd,
  apply zero_le,
  cases hbc with s1,
  cases hab with s2,
  use s2+s1,
  rw hbc_h,
  rw hab_h,
  rw add_assoc,
  refl,

end

/-
Congratulations -- you just got a collectible. You proved that the
natural numbers are a preorder.
-/
instance : preorder mynat := by structure_helper
end mynat -- hide
