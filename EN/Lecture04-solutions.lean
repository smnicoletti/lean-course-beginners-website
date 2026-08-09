/-!
# Solutions, Lecture 4

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture04.EN.Solutions

section ReductioAdAbsurdum

example (Study PassExam : Prop)
    (hNotStudyNotPass : ¬Study → ¬PassExam)
    (hPassExam : PassExam) : Study := by
  apply Classical.byContradiction
  intro hNotStudy
  have hNotPassExam := hNotStudyNotPass hNotStudy
  have hContradiction := hNotPassExam hPassExam
  exact hContradiction

end ReductioAdAbsurdum

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
    (beatrice : Thing)
    (hBeatriceBakesBread : BakesBread beatrice) :
    ∃ x : Thing, BakesBread x := by
  apply Exists.intro beatrice
  exact hBeatriceBakesBread

example (Thing : Type)
    (PressedAlarm : Thing → Prop)
    (SirenSounds : Prop)
    (hSomeonePressedAlarm : ∃ x : Thing, PressedAlarm x)
    (hPressingSoundsSiren : ∀ x : Thing, PressedAlarm x → SirenSounds) :
    SirenSounds := by
  apply Exists.elim hSomeonePressedAlarm
  intro y
  intro hYPressedAlarm
  have hSiren := hPressingSoundsSiren y hYPressedAlarm
  exact hSiren

example (Thing : Type)
    (HasSeeds PlantsFlowers : Thing → Prop)
    (hSomeoneHasSeeds : ∃ x : Thing, HasSeeds x)
    (hSeedsPlantsFlowers : ∀ x : Thing, HasSeeds x → PlantsFlowers x) :
    ∃ x : Thing, PlantsFlowers x := by
  apply Exists.elim hSomeoneHasSeeds
  intro x
  intro hXHasSeeds
  apply Exists.intro x
  have hXPlantsFlowers := hSeedsPlantsFlowers x hXHasSeeds
  exact hXPlantsFlowers

end QuantifierRules

end Course.Shared.Lecture04.EN.Solutions
