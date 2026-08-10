/-!
# Solutions, Lecture 4

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Replace each `sorry` with a proposition or proof.
-/

namespace Course.Shared.Lecture04.EN.Solutions

section ReductioAdAbsurdum

example (Study PassExam : Prop)
    (hNotStudyNotPass : ¬Study → ¬PassExam)
    (hPassExam : PassExam) :
    Study := by
  apply Classical.byContradiction
  intro hNonStudy
  have hNotPassExam := hNotStudyNotPass hNonStudy
  exact hNotPassExam hPassExam

end ReductioAdAbsurdum

section FormalizationWithVocabulary

variable (Thing : Type)
variable (Poet Musician Curious Scholar Tired : Thing → Prop)
variable (Writes Plays Listens : Thing → Prop)

-- 1. Every poet writes.
#check ∀ x : Thing, Poet x → Writes x
-- 2. Some musician plays.
#check ∃ x : Thing, Musician x ∧ Plays x
-- 3. Every curious musician listens.
#check ∀ x : Thing, Musician x → Curious x → Listens x
-- 4. There is a poet who writes and listens.
#check ∃ x : Thing, Poet x ∧ Writes x ∧ Listens x
-- 5. Every scholar writes or listens.
#check ∀ x : Thing, Scholar x → Writes x ∨ Listens x
-- 6. No tired musician plays.
#check ∀ x : Thing, Musician x → Tired x → ¬Plays x
-- 7. There is a poet who is not tired.
#check ∃ x : Thing, Poet x ∧ ¬Tired x
-- 8. Every poet writes if and only if they listen.
#check ∀ x : Thing, Poet x → (Writes x ↔ Listens x)

end FormalizationWithVocabulary

section IndependentFormalization

variable (Thing : Type)
variable (Astronomer Observes Cook Experiments Tastes : Thing → Prop)
variable (Athlete Trains Rests Librarian Distracted Catalogs : Thing → Prop)
variable (Painter Exhibits Sells Botanist Classifies Studies : Thing → Prop)
-- 1. Every astronomer observes.
#check ∀ x : Thing, Astronomer x → Observes x
-- 2. Some cook experiments and tastes.
#check ∃ x : Thing, Cook x ∧ Experiments x ∧ Tastes x
-- 3. Every athlete trains or rests.
#check ∀ x : Thing, Athlete x → Trains x ∨ Rests x
-- 4. No distracted librarian catalogs.
#check ∀ x : Thing, Librarian x → Distracted x → ¬Catalogs x
-- 5. There is a painter who exhibits but does not sell.
#check ∃ x : Thing, Painter x ∧ Exhibits x ∧ ¬Sells x
-- 6. Every botanist classifies if and only if they study.
#check ∀ x : Thing, Botanist x → (Classifies x ↔ Studies x)

end IndependentFormalization

end Course.Shared.Lecture04.EN.Solutions
