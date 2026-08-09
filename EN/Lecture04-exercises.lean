/-!
# Exercises, Lecture 4

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

In the formalization exercises, replace each `sorry` with a proposition.
In the proof exercises, replace each `sorry` with a proof.
-/

namespace Course.Shared.Lecture04.EN.Exercises

section ReductioAdAbsurdum

-- Prove that I study, assuming that if I do not study then I do not pass the
-- exam, and that I pass the exam. Use reductio ad absurdum.
example (Study PassExam : Prop)
    (hNotStudyNotPass : ¬Study → ¬PassExam)
    (hPassExam : PassExam) :
    Study := by
  sorry

end ReductioAdAbsurdum

-- ============================================================
-- FORMALIZATION WITH A PROVIDED VOCABULARY
-- ============================================================

section FormalizationWithVocabulary

variable (Thing : Type)
variable (Researcher Article Interesting Reviewed : Thing → Prop)
variable (Reads Cites : Thing → Thing → Prop)
variable (favoriteArticle : Thing → Thing)
variable (ada : Thing)

-- 1. Every researcher reads some article.
#check (sorry : Prop)
-- 2. There is an interesting, reviewed article.
#check (sorry : Prop)
-- 3. Ada's favorite article is interesting.
#check (sorry : Prop)
-- 4. Every researcher cites their favorite article.
#check (sorry : Prop)
-- 5. Every researcher reads at least one interesting article.
#check (sorry : Prop)
-- 6. There is an article read by every researcher.
#check (sorry : Prop)

end FormalizationWithVocabulary

-- ============================================================
-- FORMALIZATION FROM NATURAL LANGUAGE ONLY
-- ============================================================

section IndependentFormalization

-- For each statement, declare a domain and the required objects, predicates,
-- relations, or functions; then use `#check` on the formalization.

-- 1. Every museum exhibits some artwork.
-- 2. There is an artwork admired by every visitor.
-- 3. No visitor admires every artwork.
-- 4. The curator of the Uffizi visits Rome.
-- 5. Every visitor admires their favorite artwork.
-- 6. There is a visitor whose favorite artwork is exhibited by the Uffizi.

-- Write the declarations and formalizations here.

end IndependentFormalization

-- ============================================================
-- QUANTIFIER INTRODUCTION AND ELIMINATION
-- ============================================================

section QuantifierRules

-- ∀ introduction: prove that every cat that sleeps, sleeps.
example (Thing : Type) (Cat Sleeps : Thing → Prop) :
    ∀ x : Thing, Cat x → Sleeps x → Sleeps x := by
  sorry

-- ∀ elimination: every library is open and the Central Library is a library.
example (Thing : Type)
    (Library Open : Thing → Prop)
    (centralLibrary : Thing)
    (hEveryLibraryOpen : ∀ x : Thing, Library x → Open x)
    (hCentralLibrary : Library centralLibrary) :
    Open centralLibrary := by
  sorry

-- ∃ introduction: Beatrice bakes bread; prove that someone bakes bread.
example (Thing : Type)
    (BakesBread : Thing → Prop)
    (beatrice : Thing)
    (hBeatriceBakesBread : BakesBread beatrice) :
    ∃ x : Thing, BakesBread x := by
  sorry

-- ∃ elimination: someone pressed the alarm, and pressing it makes the siren
-- sound; prove that the siren sounds.
example (Thing : Type)
    (PressedAlarm : Thing → Prop)
    (SirenSounds : Prop)
    (hSomeonePressedAlarm : ∃ x : Thing, PressedAlarm x)
    (hPressingSoundsSiren : ∀ x : Thing, PressedAlarm x → SirenSounds) :
    SirenSounds := by
  sorry

-- Combine ∃E, ∀E, and ∃I.
example (Thing : Type)
    (HasSeeds PlantsFlowers : Thing → Prop)
    (hSomeoneHasSeeds : ∃ x : Thing, HasSeeds x)
    (hSeedsPlantsFlowers : ∀ x : Thing, HasSeeds x → PlantsFlowers x) :
    ∃ x : Thing, PlantsFlowers x := by
  sorry

end QuantifierRules

end Course.Shared.Lecture04.EN.Exercises
