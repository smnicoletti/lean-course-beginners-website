/-!
# Lecture 6: Inductive Types, Recursion, and Induction

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.EN.Classroom

-- ============================================================
-- FROM ABSTRACT TYPES TO INDUCTIVE TYPES
-- ============================================================

-- In earlier lectures we declared `Thing : Type` without specifying which
-- values belonged to the type or how they were built. An inductive type lists
-- every way of building its values. These ways are called constructors.
inductive TrafficLight where
  | red
  | yellow
  | green

#check TrafficLight
#check TrafficLight.red
#check TrafficLight.yellow
#check TrafficLight.green

-- Pattern matching gives one result for each constructor. This also connects
-- with predicates: `MustStop light` is a proposition depending on `light`.
def MustStop : TrafficLight → Prop
  | .red => True
  | .yellow => True
  | .green => False

-- We prove that every traffic light has one of the declared colours.
-- `cases light` considers every way in which `light` could have been built.
theorem lecture06_traffic_light_has_a_colour (light : TrafficLight) :
    light = .red ∨ light = .yellow ∨ light = .green := by
  cases light with
  | red =>
      apply Or.inl
      rfl
  | yellow =>
      apply Or.inr
      apply Or.inl
      rfl
  | green =>
      apply Or.inr
      apply Or.inr
      rfl

-- ============================================================
-- BUILDING OUR OWN NATURAL NUMBERS
-- ============================================================

-- `zero` builds a natural number without arguments.
-- `succ` builds a new natural number from one already built.
-- There are no other ways to build a value of type `Natural`.
inductive Natural where
  | zero
  | succ (n : Natural)

open Natural

-- We build the first natural numbers without Lean numerals.
def one : Natural := succ zero
def two : Natural := succ one
def three : Natural := succ two

#check zero
#check succ
#check one
#check two
#check three

-- ============================================================
-- RECURSIVE DEFINITIONS
-- ============================================================

-- A recursive definition follows the constructors of its input.
-- Addition recurses on its second argument.
-- Adding zero leaves the first argument unchanged.
-- Adding a successor takes the successor of the preceding sum.
-- An equivalent formulation first displays only the fixed argument:
--
-- def add (m : Natural) : Natural → Natural
--   | zero => m
--   | succ n => succ (add m n)
--
-- Here we name both arguments immediately and use `match n with` to show
-- that recursion takes place on the second argument.
def add (m n : Natural) : Natural :=
  match n with
  | zero => m
  | succ n => succ (add m n)

-- `double` also follows the two constructors of `Natural`.
-- In the second case, the recursive call uses the smaller natural number `n`.
def double (n : Natural) : Natural :=
  match n with
  | zero => zero
  | succ n => succ (succ (double n))

-- We check two concrete computations.
example : add one one = two := by
  rfl

example : double one = two := by
  rfl

-- ============================================================
-- DEFINITIONAL EQUALITY: RFL AND UNFOLD
-- ============================================================

-- These equalities follow directly from the equations used to define `add`
-- and `double`. Lean reduces both sides to the same expression, so `rfl`
-- is sufficient.
theorem lecture06_add_zero_right (m : Natural) :
    add m zero = m := by
  rfl

theorem lecture06_add_succ_right (m n : Natural) :
    add m (succ n) = succ (add m n) := by
  rfl

-- In these names, "right" says that `zero` or `succ n` occurs as the second
-- argument of `add`. That is the argument analysed by `match n with`, so
-- these equalities follow immediately from the definition. The corresponding
-- properties with `zero` or `succ` on the left do not reduce directly. We
-- will prove them later by induction.
theorem lecture06_double_succ (n : Natural) :
    double (succ n) = succ (succ (double n)) := by
  rfl

-- `unfold` explicitly opens a definition in the goal.
-- It helps us see the computation that `rfl` can perform automatically.
example : double one = two := by
  unfold double
  unfold one two
  rfl

-- ============================================================
-- REWRITING WITH AN EQUALITY
-- ============================================================

-- We want to prove `add a zero = b` from the assumption `h : a = b`.
-- `rw [h]` replaces `a` with `b`, then the left side reduces to `b`.
theorem lecture06_rw_forward
    (a b : Natural)
    (h : a = b) :
    add a zero = b := by
  -- Replace `a` with `b`. The goal becomes `add b zero = b`.
  rw [h]
  -- The definition of `add` now reduces the left side to `b`.
  rfl

-- The left arrow uses the equality in the opposite direction.
-- It replaces `b` with `a`.
theorem lecture06_rw_backward
    (a b : Natural)
    (h : a = b) :
    add b zero = a := by
  -- Use `h` backwards and replace `b` with `a`.
  rw [← h]
  -- What remains is `add a zero = a`, which follows by computation.
  rfl

-- ============================================================
-- INDUCTION
-- ============================================================

-- `add m zero = m` reduces because `add` recurses on its second argument.
-- `add zero n = n` cannot reduce while `n` is unknown. We prove this second
-- statement by induction on `n`.
--
-- How do we choose the induction variable?
-- 1. Find the definition that cannot yet reduce the goal. Here it is `add`.
-- 2. Find the argument analysed by the cases of that definition.
--    `add` distinguishes `zero` and `succ n` in its second argument.
-- 3. Induct on the variable in that position. Here it is `n`.
-- In the successor step, the induction hypothesis then concerns the recursive
-- call `add zero n` which appears after opening the definition.
--
-- The base case proves the statement for `zero`.
-- In the inductive step, `ih` assumes the statement for `n`. We prove it for
-- `succ n` and explicitly use `rewrite [ih]`.
theorem lecture06_zero_add (n : Natural) :
    add zero n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Open the successor case. The goal contains `add zero n`.
      unfold add
      -- Replace `add zero n` with `n` using the induction hypothesis.
      rewrite [ih]
      rfl

end Course.Shared.Lecture06.EN.Classroom
