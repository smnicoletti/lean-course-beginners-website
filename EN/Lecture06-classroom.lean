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

-- The computation in this goal is also blocked by the second argument of
-- `add`. We therefore induct on `n`, not on `m`. In the successor step, `ih`
-- concerns exactly the two recursive additions with second argument `n`.
theorem lecture06_succ_add (m n : Natural) :
    add (succ m) n = succ (add m n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Open both additions in the case where their second argument is
      -- `succ n`. The inner goal now concerns the smaller natural number `n`.
      unfold add
      -- `ih` replaces the addition with first argument `succ m` and second
      -- argument `n`.
      rewrite [ih]
      rfl

-- ============================================================
-- ASSOCIATIVITY AND COMMUTATIVITY
-- ============================================================

-- Associativity says that grouping `a` and `b` first, or grouping `b` and `c`
-- first, does not change the result. Since `add` recurses on its second
-- argument, we choose `c`. Induction on `c` lets both outer expressions
-- proceed through the equations of `add`, and `ih` matches the equality left
-- inside.
theorem lecture06_add_assoc (a b c : Natural) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      -- Reduce the outer addition on the left in the `succ c` case.
      rw [lecture06_add_succ_right]
      -- First reduce `add b (succ c)` on the right.
      rw [lecture06_add_succ_right]
      -- Then reduce the resulting outer addition on the right.
      rw [lecture06_add_succ_right]
      -- We have reached the form described by the induction hypothesis.
      rw [ih]

-- Commutativity says that swapping the arguments does not change the sum.
-- The definition does not treat the two arguments symmetrically. In the base
-- case we use `zero_add`, and in the step we also use `succ_add`. We choose
-- `b` because it is the second argument on the left. On the right, `b` is the
-- first argument, and `succ_add` compensates for that asymmetry.
theorem lecture06_add_comm (a b : Natural) :
    add a b = add b a := by
  induction b with
  | zero =>
      rw [lecture06_zero_add]
      rfl
  | succ b ih =>
      -- The left side reduces because `succ b` is the second argument.
      rw [lecture06_add_succ_right]
      -- On the right, `succ b` is the first argument. Use `succ_add` to
      -- move `succ` outside the addition.
      rw [lecture06_succ_add]
      -- Both sides now have the same outer `succ`. Inside remains the case `b`.
      rw [ih]

-- ============================================================
-- THE SIMPLIFIER
-- ============================================================

-- `simp` automatically applies equations oriented towards simpler forms.
-- We start from a proof we understand and compare three levels of control.

-- 1. With `rw`, we choose every rewrite explicitly.
theorem lecture06_zero_add_with_rw (n : Natural) : add zero n = n := by
  rw [lecture06_zero_add]

-- 2. `simp only` uses only the listed rules.
theorem lecture06_zero_add_with_simp_only (n : Natural) : add zero n = n := by
  simp only [lecture06_zero_add]

-- 3. `simp [lemma]` adds the stated rule to the simp set for this command.
theorem lecture06_zero_add_with_simp (n : Natural) : add zero n = n := by
  simp [lecture06_zero_add]

-- We can add lemmas to the simp set only inside a section.
-- Outside the section, the local attribute has no effect.
section LocalSimplification

attribute [local simp] lecture06_zero_add lecture06_succ_add

theorem lecture06_succ_add_with_simp (m n : Natural) :
    add (succ m) n = succ (add m n) := by
  simp

end LocalSimplification

-- `@[simp]` registers a rule for the rest of the module.
-- We use it only for a canonical equation that clearly reduces the term.
@[simp] theorem lecture06_double_zero :
    double zero = zero := by
  rfl

-- We do not register associativity and commutativity as `simp` rules.
-- In `add a b = add b a`, the two sides have the same complexity and the rule
-- only swaps arguments. Associativity only moves parentheses without removing
-- an operation. Neither equality provides a clearly simpler normal form.
-- When needed, we use them explicitly with `rw` in the desired direction.

-- ============================================================
-- FINAL PROOF
-- ============================================================

-- Exercise: the double of a sum is the sum of the doubles.
-- Which variable should we induct on? Which equations are needed?
-- The reduction of `add m n` depends on `n`, so we choose `n`. In the
-- successor step, the induction hypothesis is about `add m n`, which is the
-- recursive call that appears after rewriting the goal.
theorem lecture06_double_add (m n : Natural) :
    double (add m n) = add (double m) (double n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Reduce `add m (succ n)` on the left.
      rw [lecture06_add_succ_right]
      -- Open the double of the successor just obtained.
      rw [lecture06_double_succ]
      -- Open `double (succ n)` on the right too.
      rw [lecture06_double_succ]
      -- The next two rewrites move the two `succ` constructors produced by
      -- the double through the addition.
      rw [lecture06_add_succ_right]
      rw [lecture06_add_succ_right]
      -- Under the two successors remains precisely the inductive case for `n`.
      rw [ih]

-- After understanding the steps, we can abbreviate the same proof.
theorem lecture06_double_add_short (m n : Natural) :
    double (add m n) = add (double m) (double n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [lecture06_add_succ_right, lecture06_double_succ, ih]

end Course.Shared.Lecture06.EN.Classroom
