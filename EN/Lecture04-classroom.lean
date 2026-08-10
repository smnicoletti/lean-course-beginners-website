/-!
# Lecture 4: Classical Logic and Quantifiers

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture04.EN.Classroom

-- ============================================================
-- REDUCTIO AD ABSURDUM: CLASSICAL RULE
-- ============================================================

-- From `¬A → False`, we classically conclude A.
-- Example: if it does not rain, I do not take an umbrella; but I take an
-- umbrella; therefore, classically, it rains.
theorem lecture04_reductio_ad_absurdum
    (Rains TakeUmbrella : Prop)
    (hNotRainsNotUmbrella : ¬Rains → ¬TakeUmbrella)
    (hTakeUmbrella : TakeUmbrella) :
    Rains := by
  apply Classical.byContradiction
  intro hNotRains
  have hNotTakeUmbrella := hNotRainsNotUmbrella hNotRains
  have hContradiction := hNotTakeUmbrella hTakeUmbrella
  exact hContradiction

-- ============================================================
-- THE LANGUAGE OF PREDICATE LOGIC
-- ============================================================

section PredicateLogicLanguage

-- A section keeps these parameters local until the corresponding `end`.
-- Lean adds to each theorem only the parameters actually used in its statement.

-- `variable` introduces local parameters rather than global objects.
-- The temporarily assumed type represents the domain of discourse.
variable (Thing : Type)

-- These parameters receive an interpretation when a theorem is used.
variable (hypatia hannah rome athens : Thing)

-- A predicate takes an object and returns a proposition.
variable (Person City Philosopher Curious : Thing → Prop)

-- A function takes an object and returns an object.
variable (motherOf : Thing → Thing)

-- A relation takes two objects from the domain.
variable (Knows Visits : Thing → Thing → Prop)

#check hypatia
#check Philosopher
#check Philosopher hypatia
#check motherOf
#check motherOf hypatia
#check Curious (motherOf hypatia)
#check Knows hypatia hannah
#check Visits hypatia athens

-- “Every philosopher is curious.”
#check ∀ x : Thing, Philosopher x → Curious x

-- “There is a curious philosopher.”
#check ∃ x : Thing, Philosopher x ∧ Curious x

end PredicateLogicLanguage

-- ============================================================
-- FORMALIZATION EXERCISES
-- ============================================================

section FormalizationExercises

variable (Thing : Type)
variable (Student Reads Understands : Thing → Prop)

-- Formalize:
-- 1. Every student reads.
-- 2. Some student reads.
-- 3. Every student who reads understands.
-- 4. There is a student who reads and understands.

-- SOLUTIONS

#check ∀ x : Thing, Student x → Reads x
#check ∃ x : Thing, Student x ∧ Reads x
#check ∀ x : Thing, Student x → Reads x → Understands x
#check ∃ x : Thing, Student x ∧ Reads x ∧ Understands x

end FormalizationExercises

end Course.Shared.Lecture04.EN.Classroom
