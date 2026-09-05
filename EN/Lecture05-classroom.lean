/-!
# Lecture 5: Quantifier Rules

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture05.EN.Classroom

section FormalizationExercises

variable (Thing : Type)
variable (Student Reads Understands : Thing → Prop)

-- Review from Lecture 4.
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
theorem lecture05_forall_intro
    (Thing : Type)
    (Person Curious : Thing → Prop) :
    ∀ y : Thing, Person y → Curious y → Curious y := by
  intro x
  intro hXPerson
  intro hXCurious
  exact hXCurious

-- A fact about Hypatia does not establish the same fact for every thing.
-- After `intro x`, `hHypatiaCurious : Curious hypatia` cannot close the goal
-- `Curious x`. If a source proof reuses the name `x`, Lean displays the older
-- local variable as `x✝`; the two local objects remain distinct.

-- Universal elimination, ∀E.
-- Every student reads; Marta is a student; therefore Marta reads.
theorem lecture05_forall_elim
    (Thing : Type)
    (Student Reads : Thing → Prop)
    (marta : Thing)
    (hEveryStudentReads : ∀ x : Thing, Student x → Reads x)
    (hMartaStudent : Student marta) :
    Reads marta := by
  have hIfMartaStudentThenReads := hEveryStudentReads marta
  have hMartaReads := hIfMartaStudentThenReads hMartaStudent
  exact hMartaReads

-- The term used for ∀E may be constructed by a function.
theorem lecture05_forall_elim_function_term
    (Thing : Type)
    (Curious : Thing → Prop)
    (motherOf : Thing → Thing)
    (hypatia : Thing)
    (hEverythingCurious : ∀ x : Thing, Curious x) :
    Curious (motherOf hypatia) := by
  have hHypatiasMotherCurious := hEverythingCurious (motherOf hypatia)
  exact hHypatiasMotherCurious

-- ============================================================
-- EXISTENTIAL QUANTIFIER: ∃
-- ============================================================

-- Existential introduction, ∃I.
-- Choose Marta as the witness and use the assumption that she reads.
theorem lecture05_exists_intro
    (Thing : Type)
    (Reads : Thing → Prop)
    (marta : Thing)
    (hMartaReads : Reads marta) :
    ∃ x : Thing, Reads x := by
  apply Exists.intro marta
  exact hMartaReads

-- The witness used for ∃I may also be a compound term.
theorem lecture05_exists_intro_function_term
    (Thing : Type)
    (Curious : Thing → Prop)
    (motherOf : Thing → Thing)
    (hypatia : Thing)
    (hHypatiasMotherCurious : Curious (motherOf hypatia)) :
    ∃ x : Thing, Curious x := by
  apply Exists.intro (motherOf hypatia)
  exact hHypatiasMotherCurious

-- Existential elimination, ∃E.
-- Someone filed a report; whenever someone files a report, an investigation
-- starts; therefore an investigation starts.
theorem lecture05_exists_elim
    (Thing : Type)
    (FiledReport : Thing → Prop)
    (InvestigationStarts : Prop)
    (hSomeoneFiledReport : ∃ x : Thing, FiledReport x)
    (hReportStartsInvestigation :
      (x : Thing) → FiledReport x → InvestigationStarts) :
    InvestigationStarts := by
  apply Exists.elim hSomeoneFiledReport
  intro y
  intro hYFiledReport
  have hIfYFiledThenInvestigationStarts := hReportStartsInvestigation y
  have hInvestigationStarts :=
    hIfYFiledThenInvestigationStarts hYFiledReport
  exact hInvestigationStarts

-- A more complex example combining ∃E, ∀E, and ∃I.
-- Someone has an umbrella; everyone with an umbrella stays dry;
-- therefore someone stays dry.
theorem lecture05_exists_elim_combined
    (Thing : Type)
    (HasUmbrella StaysDry : Thing → Prop)
    (hSomeoneHasUmbrella : ∃ x : Thing, HasUmbrella x)
    (hUmbrellaStaysDry : ∀ x : Thing, HasUmbrella x → StaysDry x) :
    ∃ x : Thing, StaysDry x := by
  apply Exists.elim hSomeoneHasUmbrella
  intro y
  intro hYHasUmbrella
  apply Exists.intro y
  have hIfYHasUmbrellaThenStaysDry := hUmbrellaStaysDry y
  have hYStaysDry := hIfYHasUmbrellaThenStaysDry hYHasUmbrella
  exact hYStaysDry

-- Combine ∀I, →I, ∀E, and ∧I.
theorem lecture05_forall_conjunction_combined
    (Thing : Type)
    (Student Reads TakesNotes Understands : Thing → Prop)
    (hReadersTakeNotes :
      ∀ x : Thing, Student x → Reads x → TakesNotes x)
    (hReadersUnderstand :
      ∀ x : Thing, Student x → Reads x → Understands x) :
    ∀ x : Thing, Student x → Reads x → TakesNotes x ∧ Understands x := by
  intro x
  intro hXStudent
  intro hXReads
  apply And.intro
  · have hIfXStudentThenReadingImpliesNotes := hReadersTakeNotes x
    have hIfXReadsThenTakesNotes :=
      hIfXStudentThenReadingImpliesNotes hXStudent
    have hXTakesNotes := hIfXReadsThenTakesNotes hXReads
    exact hXTakesNotes
  · have hIfXStudentThenReadingImpliesUnderstanding := hReadersUnderstand x
    have hIfXReadsThenUnderstands :=
      hIfXStudentThenReadingImpliesUnderstanding hXStudent
    have hXUnderstands := hIfXReadsThenUnderstands hXReads
    exact hXUnderstands

-- Combine ∃E, ∨E, ∀E, and ∃I.
theorem lecture05_exists_or_combined
    (Thing : Type)
    (VisitsRome VisitsAthens SeesMuseum : Thing → Prop)
    (hSomeoneVisitsACity : ∃ x : Thing, VisitsRome x ∨ VisitsAthens x)
    (hRomeVisitorsSeeMuseum : ∀ x : Thing, VisitsRome x → SeesMuseum x)
    (hAthensVisitorsSeeMuseum : ∀ x : Thing, VisitsAthens x → SeesMuseum x) :
    ∃ x : Thing, SeesMuseum x := by
  apply Exists.elim hSomeoneVisitsACity
  intro y
  intro hYVisitsRomeOrAthens
  cases hYVisitsRomeOrAthens with
  | inl hYVisitsRome =>
      apply Exists.intro y
      have hIfYVisitsRomeThenSeesMuseum := hRomeVisitorsSeeMuseum y
      have hYSeesMuseum := hIfYVisitsRomeThenSeesMuseum hYVisitsRome
      exact hYSeesMuseum
  | inr hYVisitsAthens =>
      apply Exists.intro y
      have hIfYVisitsAthensThenSeesMuseum := hAthensVisitorsSeeMuseum y
      have hYSeesMuseum := hIfYVisitsAthensThenSeesMuseum hYVisitsAthens
      exact hYSeesMuseum

-- Combine ∃E, ∧E, ∀E, and ¬E.
theorem lecture05_exists_negation_combined
    (Thing : Type)
    (Submitted ReceivedConfirmation : Thing → Prop)
    (hSubmissionGetsConfirmation :
      ∀ x : Thing, Submitted x → ReceivedConfirmation x)
    (hCounterexample :
      ∃ x : Thing, Submitted x ∧ ¬ReceivedConfirmation x) :
    False := by
  apply Exists.elim hCounterexample
  intro y
  intro hYSubmittedAndNoConfirmation
  have hYSubmitted := hYSubmittedAndNoConfirmation.left
  have hYNoConfirmation := hYSubmittedAndNoConfirmation.right
  have hIfYSubmittedThenConfirmation := hSubmissionGetsConfirmation y
  have hYReceivedConfirmation := hIfYSubmittedThenConfirmation hYSubmitted
  have hContradiction := hYNoConfirmation hYReceivedConfirmation
  exact hContradiction

-- Combine nested quantifiers, ∃E, ∃I, and ∧I.
-- Every person knows at least one person. Therefore, for every person, there
-- is someone whom they know and who is a person.
theorem lecture05_nested_quantifiers_combined
    (Thing : Type)
    (Person : Thing → Prop)
    (Knows : Thing → Thing → Prop)
    (hEveryPersonKnowsSomeone :
      ∀ x : Thing, Person x →
        ∃ y : Thing, Person y ∧ Knows x y) :
    ∀ x : Thing, Person x →
      ∃ y : Thing, Knows x y ∧ Person y := by
  intro x
  intro hXPerson
  have hIfXPersonThenKnowsSomeone := hEveryPersonKnowsSomeone x
  have hXKnowsSomeone := hIfXPersonThenKnowsSomeone hXPerson
  apply Exists.elim hXKnowsSomeone
  intro y
  intro hYPersonAndXKnowsY
  apply Exists.intro y
  apply And.intro
  · exact hYPersonAndXKnowsY.right
  · exact hYPersonAndXKnowsY.left

-- Combine ∃E, ∀E, ↔E, and ∃I.
-- Being a square is equivalent to having four equal sides. A square exists;
-- therefore, something has four equal sides.
theorem lecture05_exists_iff_combined
    (Thing : Type)
    (Square HasFourEqualSides : Thing → Prop)
    (hEquivalence :
      ∀ x : Thing, Square x ↔ HasFourEqualSides x)
    (hSquareExists : ∃ x : Thing, Square x) :
    ∃ x : Thing, HasFourEqualSides x := by
  apply Exists.elim hSquareExists
  intro y
  intro hYSquare
  apply Exists.intro y
  have hEquivalenceForY := hEquivalence y
  have hForwardDirection := Iff.mp hEquivalenceForY
  have hYHasFourEqualSides := hForwardDirection hYSquare
  exact hYHasFourEqualSides

end Course.Shared.Lecture05.EN.Classroom
