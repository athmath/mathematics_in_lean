module
public import MIL.Common
public import Mathlib.Basic.Real.Basic
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]


example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm a]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [mul_assoc a e f]
  rw [h]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  linarith

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ )
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a : ℚ)

#check a
#check (2.5*a)
end

#check 5/2
#eval (5/2)

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw[mul_add]
  rw[add_mul, add_mul]
  rw[← add_assoc]
  rw[add_assoc (a*a)]
  rw[mul_comm b a]
  rw[← two_mul]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw[pow_two, pow_two]
  rw[add_mul]
  rw[mul_sub, mul_sub, mul_comm b a, ← add_assoc]


example (a b c d : ℝ) :  a- b + (c + d) = a -b +c + d := by
  rw[add_assoc]

#check pow_two a
#check mul_sub a b c
