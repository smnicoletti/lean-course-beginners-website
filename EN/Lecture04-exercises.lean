/-!
# Exercises, Lecture 4

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Replace each `sorry` with a proposition or proof.
-/

namespace Course.Shared.Lecture04.EN.Exercises

section ReductioAdAbsurdum

example (Study PassExam : Prop)
    (hNotStudyNotPass : ¬Study → ¬PassExam)
    (hPassExam : PassExam) :
    Study := by
  sorry

end ReductioAdAbsurdum

section FormalizationWithVocabulary

variable (Thing : Type)
variable (Poet Musician Curious Scholar Tired : Thing → Prop)
variable (Writes Plays Listens : Thing → Prop)

-- 1. Every poet writes.
#check sorry
-- 2. Some musician plays.
#check sorry
-- 3. Every curious musician listens.
#check sorry
-- 4. There is a poet who writes and listens.
#check sorry
-- 5. Every scholar writes or listens.
#check sorry
-- 6. No tired musician plays.
#check sorry
-- 7. There is a poet who is not tired.
#check sorry
-- 8. Every poet writes if and only if they listen.
#check sorry

end FormalizationWithVocabulary

section IndependentFormalization

-- For each statement, declare `Thing`, the required unary predicates, and its
-- formalization with `#check`.
-- 1. Every astronomer observes.
-- 2. Some cook experiments and tastes.
-- 3. Every athlete trains or rests.
-- 4. No distracted librarian catalogs.
-- 5. There is a painter who exhibits but does not sell.
-- 6. Every botanist classifies if and only if they study.

end IndependentFormalization

end Course.Shared.Lecture04.EN.Exercises
