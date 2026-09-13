/-!
# Exercises, Lecture 6

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.EN.Exercises

inductive Natural where
  | zero
  | succ (n : Natural)

open Natural

def one : Natural := succ zero
def two : Natural := succ one

def add (m n : Natural) : Natural :=
  match n with
  | zero => m
  | succ n => succ (add m n)

def double (n : Natural) : Natural :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))

-- ============================================================
-- DEFINING MULTIPLICATION
-- ============================================================

-- 1. Define `multiply` by recursion on its second argument.
-- Choose the two lines of the definition from the meaning of multiplication
-- as repeated addition.
def multiply (m n : Natural) : Natural :=
  match n with
  | zero => sorry
  | succ n => sorry

-- 2. After defining `multiply`, these two equalities should close with `rfl`.
theorem multiply_zero_right (m : Natural) :
    multiply m zero = zero := by
  sorry

theorem multiply_succ_right (m n : Natural) :
    multiply m (succ n) = add m (multiply m n) := by
  sorry

-- ============================================================
-- COMPUTATION AND REWRITING
-- ============================================================

-- 3. Prove the following statement.
theorem add_succ_right (m n : Natural) :
    add m (succ n) = succ (add m n) := by
  sorry

-- 4. Given an equality `h : a = b`, rewrite the first argument of the sum
-- and conclude by computation.
theorem rewrite_first_argument
    (a b : Natural)
    (h : a = b) :
    add a zero = b := by
  sorry

-- ============================================================
-- INDUCTION ON ADDITION
-- ============================================================

-- 5. Prove by induction that adding one on the left yields the successor of
-- the given natural number.
theorem add_one_left (n : Natural) :
    add one n = succ n := by
  sorry

-- 6. Prove the analogous result for two by induction.
theorem add_two_left (n : Natural) :
    add two n = succ (succ n) := by
  sorry

-- 7. Prove this particular form of associativity. Choose the induction
-- variable by looking at the additions that must reduce.
theorem add_with_one_assoc (m n : Natural) :
    add (add m one) n = add m (add one n) := by
  sorry

-- 8. Combine addition and double in an induction proof.
theorem double_add_one (n : Natural) :
    double (add one n) = add two (double n) := by
  sorry

-- ============================================================
-- INDUCTION ON MULTIPLICATION AND SIMPLIFICATION
-- ============================================================

-- 9. After completing `multiply`, prove by induction that multiplying one by
-- every natural number gives that natural number.
theorem multiply_one_left (n : Natural) :
    multiply one n = n := by
  sorry

-- 10. Use `simp only` to close the following goal.
example (n : Natural) : add one n = succ n := by
  sorry

end Course.Shared.Lecture06.EN.Exercises
