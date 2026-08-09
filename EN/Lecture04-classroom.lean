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

-- We now introduce only the ingredients needed for functions.
variable (motherOf : Thing → Thing)
variable (hypatia : Thing)
variable (Curious : Thing → Prop)
variable (Knows : Thing → Thing → Prop)

-- Formalize:
-- 1. Hypatia's mother is curious.
-- 2. Every student knows their mother.
-- 3. There is a student whose mother reads.

-- SOLUTIONS

#check Curious (motherOf hypatia)
#check ∀ x : Thing, Student x → Knows x (motherOf x)
#check ∃ x : Thing, Student x ∧ Reads (motherOf x)

-- `Person` is introduced only for the following exercises.
variable (Person : Thing → Prop)

-- Using `Knows : Thing → Thing → Prop`, formalize:
-- 1. Every person knows someone.
-- 2. Someone knows every person.
-- 3. Nobody knows every person.

-- SOLUTIONS

#check ∀ x : Thing, Person x →
  ∃ y : Thing, Person y ∧ Knows x y

#check ∃ x : Thing, Person x ∧
  ∀ y : Thing, Person y → Knows x y

#check ¬∃ x : Thing, Person x ∧
  ∀ y : Thing, Person y → Knows x y

end FormalizationExercises

-- ============================================================
-- UNIVERSAL QUANTIFIER: ∀
-- ============================================================

-- Universal introduction, ∀I.
-- The universal goal is opened by introducing a new arbitrary thing `x`.
-- Only the first `intro` applies ∀I; the next two introduce implications.
theorem lecture04_forall_intro
    (Thing : Type)
    (Person Curious : Thing → Prop) :
    ∀ y : Thing, Person y → Curious y → Curious y := by
  intro x
  intro hXPerson
  intro hXCurious
  exact hXCurious

-- Universal elimination, ∀E.
-- Every student reads; Marta is a student; therefore Marta reads.
theorem lecture04_forall_elim
    (Thing : Type)
    (Student Reads : Thing → Prop)
    (marta : Thing)
    (hEveryStudentReads : ∀ x : Thing, Student x → Reads x)
    (hMartaStudent : Student marta) :
    Reads marta := by
  have hIfMartaStudentThenReads := hEveryStudentReads marta
  have hMartaReads := hIfMartaStudentThenReads hMartaStudent
  exact hMartaReads

-- ============================================================
-- EXISTENTIAL QUANTIFIER: ∃
-- ============================================================

-- Existential introduction, ∃I.
-- Choose Marta as the witness and use the assumption that she reads.
theorem lecture04_exists_intro
    (Thing : Type)
    (Reads : Thing → Prop)
    (marta : Thing)
    (hMartaReads : Reads marta) :
    ∃ x : Thing, Reads x := by
  apply Exists.intro marta
  exact hMartaReads

-- Existential elimination, ∃E.
-- Someone filed a report; whenever someone files a report, an investigation
-- starts; therefore an investigation starts.
theorem lecture04_exists_elim
    (Thing : Type)
    (FiledReport : Thing → Prop)
    (InvestigationStarts : Prop)
    (hSomeoneFiledReport : ∃ x : Thing, FiledReport x)
    (hReportStartsInvestigation :
      ∀ x : Thing, FiledReport x → InvestigationStarts) :
    InvestigationStarts := by
  apply Exists.elim hSomeoneFiledReport
  intro y
  intro hYFiledReport
  have hInvestigation := hReportStartsInvestigation y hYFiledReport
  exact hInvestigation

-- A more complex example combining ∃E, ∀E, and ∃I.
-- Someone has an umbrella; everyone with an umbrella stays dry;
-- therefore someone stays dry.
theorem lecture04_exists_elim_combined
    (Thing : Type)
    (HasUmbrella StaysDry : Thing → Prop)
    (hSomeoneHasUmbrella : ∃ x : Thing, HasUmbrella x)
    (hUmbrellaStaysDry : ∀ x : Thing, HasUmbrella x → StaysDry x) :
    ∃ x : Thing, StaysDry x := by
  apply Exists.elim hSomeoneHasUmbrella
  intro x hXHasUmbrella
  apply Exists.intro x
  have hXStaysDry := hUmbrellaStaysDry x hXHasUmbrella
  exact hXStaysDry

end Course.Shared.Lecture04.EN.Classroom
