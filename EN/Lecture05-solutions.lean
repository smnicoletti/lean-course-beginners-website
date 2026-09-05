/-!
# Solutions, Lecture 5

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture05.EN.Solutions

section FormalizationWithVocabulary

variable (Thing : Type)
variable (Researcher Article Interesting Reviewed : Thing → Prop)
variable (Reads Cites : Thing → Thing → Prop)
variable (favoriteArticle : Thing → Thing)
variable (ada : Thing)

#check ∀ x : Thing, Researcher x →
  ∃ y : Thing, Article y ∧ Reads x y
#check ∃ x : Thing, Article x ∧ Interesting x ∧ Reviewed x
#check Interesting (favoriteArticle ada)
#check ∀ x : Thing, Researcher x → Cites x (favoriteArticle x)
#check ∀ x : Thing, Researcher x →
  ∃ y : Thing, Article y ∧ Interesting y ∧ Reads x y
#check ∃ y : Thing, Article y ∧
  ∀ x : Thing, Researcher x → Reads x y

end FormalizationWithVocabulary

section IndependentFormalization

variable (Thing : Type)
variable (Museum Artwork Visitor : Thing → Prop)
variable (Exhibits Admires Visits : Thing → Thing → Prop)
variable (curatorOf favoriteArtwork : Thing → Thing)
variable (uffizi rome : Thing)

#check ∀ x : Thing, Museum x →
  ∃ y : Thing, Artwork y ∧ Exhibits x y
#check ∃ y : Thing, Artwork y ∧
  ∀ x : Thing, Visitor x → Admires x y
#check ¬∃ x : Thing, Visitor x ∧
  ∀ y : Thing, Artwork y → Admires x y
#check Visits (curatorOf uffizi) rome
#check ∀ x : Thing, Visitor x → Admires x (favoriteArtwork x)
#check ∃ x : Thing, Visitor x ∧ Exhibits uffizi (favoriteArtwork x)

end IndependentFormalization

section QuantifierRules

example (Thing : Type) (Cat Sleeps : Thing → Prop) :
    ∀ x : Thing, Cat x → Sleeps x → Sleeps x := by
  intro x
  intro hXCat
  intro hXSleeps
  exact hXSleeps

example (Thing : Type)
    (Library Open : Thing → Prop)
    (centralLibrary : Thing)
    (hEveryLibraryOpen : ∀ x : Thing, Library x → Open x)
    (hCentralLibrary : Library centralLibrary) :
    Open centralLibrary := by
  have hIfCentralLibraryThenOpen := hEveryLibraryOpen centralLibrary
  have hCentralOpen := hIfCentralLibraryThenOpen hCentralLibrary
  exact hCentralOpen

example (Thing : Type)
    (BakesBread : Thing → Prop)
    (elisa : Thing)
    (hElisaBakesBread : BakesBread elisa) :
    ∃ x : Thing, BakesBread x := by
  apply Exists.intro elisa
  exact hElisaBakesBread

example (Thing : Type)
    (PressedAlarm : Thing → Prop)
    (SirenSounds : Prop)
    (hSomeonePressedAlarm : ∃ x : Thing, PressedAlarm x)
    (hPressingSoundsSiren :
      (x : Thing) → PressedAlarm x → SirenSounds) :
    SirenSounds := by
  apply Exists.elim hSomeonePressedAlarm
  intro y
  intro hYPressedAlarm
  have hIfYPressedAlarmThenSirenSounds := hPressingSoundsSiren y
  have hSirenSounds := hIfYPressedAlarmThenSirenSounds hYPressedAlarm
  exact hSirenSounds

example (Thing : Type)
    (HasSeeds PlantsFlowers : Thing → Prop)
    (hSomeoneHasSeeds : ∃ x : Thing, HasSeeds x)
    (hSeedsPlantsFlowers : ∀ x : Thing, HasSeeds x → PlantsFlowers x) :
    ∃ x : Thing, PlantsFlowers x := by
  apply Exists.elim hSomeoneHasSeeds
  intro y
  intro hYHasSeeds
  apply Exists.intro y
  have hIfYHasSeedsThenPlantsFlowers := hSeedsPlantsFlowers y
  have hYPlantsFlowers := hIfYHasSeedsThenPlantsFlowers hYHasSeeds
  exact hYPlantsFlowers

example (Thing : Type)
    (Violinist Rehearses Prepared Calm : Thing → Prop)
    (hRehearsingPrepared :
      ∀ x : Thing, Violinist x → Rehearses x → Prepared x)
    (hRehearsingCalm :
      ∀ x : Thing, Violinist x → Rehearses x → Calm x) :
    ∀ x : Thing, Violinist x → Rehearses x → Prepared x ∧ Calm x := by
  intro x
  intro hXViolinist
  intro hXRehearses
  apply And.intro
  · have hIfXViolinistThenRehearsalImpliesPrepared :=
      hRehearsingPrepared x
    have hIfXRehearsesThenPrepared :=
      hIfXViolinistThenRehearsalImpliesPrepared hXViolinist
    have hXPrepared := hIfXRehearsesThenPrepared hXRehearses
    exact hXPrepared
  · have hIfXViolinistThenRehearsalImpliesCalm :=
      hRehearsingCalm x
    have hIfXRehearsesThenCalm :=
      hIfXViolinistThenRehearsalImpliesCalm hXViolinist
    have hXCalm := hIfXRehearsesThenCalm hXRehearses
    exact hXCalm

example (Thing : Type)
    (ArrivesOnFoot ArrivesByBike FindsShelter : Thing → Prop)
    (hSomeoneArrives :
      ∃ x : Thing, ArrivesOnFoot x ∨ ArrivesByBike x)
    (hWalkingFindsShelter :
      ∀ x : Thing, ArrivesOnFoot x → FindsShelter x)
    (hCyclingFindsShelter :
      ∀ x : Thing, ArrivesByBike x → FindsShelter x) :
    ∃ x : Thing, FindsShelter x := by
  apply Exists.elim hSomeoneArrives
  intro y
  intro hYArrivesOnFootOrByBike
  cases hYArrivesOnFootOrByBike with
  | inl hYArrivesOnFoot =>
      apply Exists.intro y
      have hIfYWalksThenFindsShelter := hWalkingFindsShelter y
      have hYFindsShelter := hIfYWalksThenFindsShelter hYArrivesOnFoot
      exact hYFindsShelter
  | inr hYArrivesByBike =>
      apply Exists.intro y
      have hIfYCyclesThenFindsShelter := hCyclingFindsShelter y
      have hYFindsShelter := hIfYCyclesThenFindsShelter hYArrivesByBike
      exact hYFindsShelter

example (Thing : Type)
    (Booked ReceivedTicket : Thing → Prop)
    (hBookingReceivesTicket :
      ∀ x : Thing, Booked x → ReceivedTicket x)
    (hCounterexample :
      ∃ x : Thing, Booked x ∧ ¬ReceivedTicket x) :
    False := by
  apply Exists.elim hCounterexample
  intro y
  intro hYBookedAndNoTicket
  have hYBooked := hYBookedAndNoTicket.left
  have hYDidNotReceiveTicket := hYBookedAndNoTicket.right
  have hIfYBookedThenReceivesTicket := hBookingReceivesTicket y
  have hYReceivedTicket := hIfYBookedThenReceivesTicket hYBooked
  have hContradiction := hYDidNotReceiveTicket hYReceivedTicket
  exact hContradiction

end QuantifierRules

end Course.Shared.Lecture05.EN.Solutions
