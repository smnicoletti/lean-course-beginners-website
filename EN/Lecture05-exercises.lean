/-!
# Exercises, Lecture 5

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture05.EN.Exercises

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
#check sorry
-- 2. There is an interesting, reviewed article.
#check sorry
-- 3. Ada's favorite article is interesting.
#check sorry
-- 4. Every researcher cites their favorite article.
#check sorry
-- 5. Every researcher reads at least one interesting article.
#check sorry
-- 6. There is an article read by every researcher.
#check sorry

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

-- ∃ introduction: Elisa bakes bread; prove that someone bakes bread.
example (Thing : Type)
    (BakesBread : Thing → Prop)
    (elisa : Thing)
    (hElisaBakesBread : BakesBread elisa) :
    ∃ x : Thing, BakesBread x := by
  sorry

-- ∃ elimination: someone pressed the alarm, and pressing it makes the siren
-- sound; prove that the siren sounds.
example (Thing : Type)
    (PressedAlarm : Thing → Prop)
    (SirenSounds : Prop)
    (hSomeonePressedAlarm : ∃ x : Thing, PressedAlarm x)
    (hPressingSoundsSiren :
      (x : Thing) → PressedAlarm x → SirenSounds) :
    SirenSounds := by
  sorry

-- Combine ∃E, ∀E, and ∃I.
example (Thing : Type)
    (HasSeeds PlantsFlowers : Thing → Prop)
    (hSomeoneHasSeeds : ∃ x : Thing, HasSeeds x)
    (hSeedsPlantsFlowers : ∀ x : Thing, HasSeeds x → PlantsFlowers x) :
    ∃ x : Thing, PlantsFlowers x := by
  sorry

-- Combine ∀I, ∀E, →I, and ∧I.
-- Every violinist who rehearses is prepared, and every violinist who rehearses
-- is calm. Prove that every violinist who rehearses is prepared and calm.
example (Thing : Type)
    (Violinist Rehearses Prepared Calm : Thing → Prop)
    (hRehearsingPrepared :
      ∀ x : Thing, Violinist x → Rehearses x → Prepared x)
    (hRehearsingCalm :
      ∀ x : Thing, Violinist x → Rehearses x → Calm x) :
    ∀ x : Thing, Violinist x → Rehearses x → Prepared x ∧ Calm x := by
  sorry

-- Combine ∃E, ∨E, ∀E, and ∃I.
-- Someone reaches the shelter on foot or by bicycle. Anyone who reaches it by
-- either route finds shelter. Prove that someone finds shelter.
example (Thing : Type)
    (ArrivesOnFoot ArrivesByBike FindsShelter : Thing → Prop)
    (hSomeoneArrives :
      ∃ x : Thing, ArrivesOnFoot x ∨ ArrivesByBike x)
    (hWalkingFindsShelter :
      ∀ x : Thing, ArrivesOnFoot x → FindsShelter x)
    (hCyclingFindsShelter :
      ∀ x : Thing, ArrivesByBike x → FindsShelter x) :
    ∃ x : Thing, FindsShelter x := by
  sorry

-- Combine ∃E, ∧E, ∀E, and ¬E.
-- Everyone who booked receives a ticket. Someone booked but did not receive a
-- ticket. Prove that the assumptions are contradictory.
example (Thing : Type)
    (Booked ReceivedTicket : Thing → Prop)
    (hBookingReceivesTicket :
      ∀ x : Thing, Booked x → ReceivedTicket x)
    (hCounterexample :
      ∃ x : Thing, Booked x ∧ ¬ReceivedTicket x) :
    False := by
  sorry

end QuantifierRules

end Course.Shared.Lecture05.EN.Exercises
