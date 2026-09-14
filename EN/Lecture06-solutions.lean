/-!
# Solutions, Lecture 6

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.EN.Solutions

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

-- Multiplication repeats `m` as many times as indicated by its second argument.
def multiply (m n : Natural) : Natural :=
  match n with
  | zero => zero
  | succ n => add m (multiply m n)

theorem multiply_zero_right (m : Natural) :
    multiply m zero = zero := by
  rfl

theorem multiply_succ_right (m n : Natural) :
    multiply m (succ n) = add m (multiply m n) := by
  rfl

theorem add_succ_right (m n : Natural) :
    add m (succ n) = succ (add m n) := by
  rfl

theorem rewrite_first_argument
    (a b : Natural)
    (h : a = b) :
    add a zero = b := by
  rw [h]
  rfl

theorem add_one_left (n : Natural) :
    add one n = succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold add
      rw [ih]

end Course.Shared.Lecture06.EN.Solutions
