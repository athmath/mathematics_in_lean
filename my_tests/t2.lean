import Mathlib

example (x : ℝ) :
    2*x ≤ x^2 + 1 := by
  nlinarith [sq_nonneg (x - 1)]

example (x y : ℝ)
  (h: x+y=10) :
  x*y ≤ 25 := by
  nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 5), h]

example (x y : ℝ)
    (h: x+y=10) :
    x*y ≤ 25 := by
  calc
    x*y = x*(10-x) := by
      have hy : y = 10 - x := by linarith
      rw [hy]
    _ = 10*x - x^2 := by ring
    _ ≤ 25 := by nlinarith [sq_nonneg (x - 5)]
