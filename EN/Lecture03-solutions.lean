/-!
# Solutions, Lecture 3

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture03.EN.Solutions

section ImplicationAndConjunction

example (DrinkWine EatPasta : Prop) : DrinkWine ∧ EatPasta → DrinkWine := by
  intro hDrinkWineAndEatPasta
  have hDrinkWine := hDrinkWineAndEatPasta.left
  exact hDrinkWine

example (DrinkWine GetDrunk : Prop)
    (hDrinkWine : DrinkWine) (hWineDrunk : DrinkWine → GetDrunk) :
    GetDrunk := by
  have hGetDrunk := hWineDrunk hDrinkWine
  exact hGetDrunk

example (TakeUmbrella WearCoat : Prop)
    (hTakeUmbrella : TakeUmbrella) (hWearCoat : WearCoat) :
    TakeUmbrella ∧ WearCoat := by
  apply And.intro
  · exact hTakeUmbrella
  · exact hWearCoat

example (TakeUmbrella WearCoat : Prop)
    (hClothing : TakeUmbrella ∧ WearCoat) : WearCoat := by
  have hWearCoat := hClothing.right
  exact hWearCoat

end ImplicationAndConjunction

section Disjunction

example (TravelByBus TravelByTrain : Prop) (hBus : TravelByBus) :
    TravelByBus ∨ TravelByTrain := by
  apply Or.inl
  exact hBus

example (TravelByBus TravelByTrain : Prop) (hTrain : TravelByTrain) :
    TravelByBus ∨ TravelByTrain := by
  apply Or.inr
  exact hTrain

example (TravelByBus TravelByTrain ArriveOnTime : Prop)
    (hChoice : TravelByBus ∨ TravelByTrain)
    (hBusOnTime : TravelByBus → ArriveOnTime)
    (hTrainOnTime : TravelByTrain → ArriveOnTime) : ArriveOnTime := by
  cases hChoice with
  | inl hBus =>
      have hArriveOnTime := hBusOnTime hBus
      exact hArriveOnTime
  | inr hTrain =>
      have hArriveOnTime := hTrainOnTime hTrain
      exact hArriveOnTime

end Disjunction

section NegationTruthAndFalsity

example (DrinkCoffee StayAwake : Prop)
    (hCoffeeAwake : DrinkCoffee → StayAwake) (hNotAwake : ¬StayAwake) :
    ¬DrinkCoffee := by
  intro hDrinkCoffee
  have hStayAwake := hCoffeeAwake hDrinkCoffee
  have hContradiction := hNotAwake hStayAwake
  exact hContradiction

example (ShopOpen : Prop) (hOpen : ShopOpen) (hNotOpen : ¬ShopOpen) :
    False := by
  have hContradiction := hNotOpen hOpen
  exact hContradiction

example : True := by
  exact True.intro

example (WinPrize : Prop) (hContradiction : False) : WinPrize := by
  apply False.elim
  exact hContradiction

end NegationTruthAndFalsity

section Biconditional

example (DoorClosed LightOff : Prop) :
    DoorClosed ∧ LightOff ↔ LightOff ∧ DoorClosed := by
  apply Iff.intro
  · intro hDoorClosedAndLightOff
    apply And.intro
    · exact hDoorClosedAndLightOff.right
    · exact hDoorClosedAndLightOff.left
  · intro hLightOffAndDoorClosed
    apply And.intro
    · exact hLightOffAndDoorClosed.right
    · exact hLightOffAndDoorClosed.left

example (EvenNumber DivisibleByTwo : Prop)
    (hEquivalence : EvenNumber ↔ DivisibleByTwo) (hEven : EvenNumber) :
    DivisibleByTwo := by
  have hDirection := Iff.mp hEquivalence
  have hDivisible := hDirection hEven
  exact hDivisible

example (EvenNumber DivisibleByTwo : Prop)
    (hEquivalence : EvenNumber ↔ DivisibleByTwo)
    (hDivisible : DivisibleByTwo) : EvenNumber := by
  have hDirection := Iff.mpr hEquivalence
  have hEven := hDirection hDivisible
  exact hEven

end Biconditional

section ReductioAdAbsurdum

example (Study PassExam : Prop)
    (hNotStudyNotPass : ¬Study → ¬PassExam) (hPassExam : PassExam) :
    Study := by
  apply Classical.byContradiction
  intro hNotStudy
  have hNotPassExam := hNotStudyNotPass hNotStudy
  have hContradiction := hNotPassExam hPassExam
  exact hContradiction

end ReductioAdAbsurdum

section CompleteArguments

example (Rains Sunny TakeUmbrella WearSunglasses GoOut : Prop)
    (hWeather : Rains ∨ Sunny)
    (hRainsUmbrella : Rains → TakeUmbrella)
    (hSunnySunglasses : Sunny → WearSunglasses)
    (hUmbrellaGoOut : TakeUmbrella → GoOut)
    (hSunglassesGoOut : WearSunglasses → GoOut) : GoOut := by
  cases hWeather with
  | inl hRains =>
      have hTakeUmbrella := hRainsUmbrella hRains
      have hGoOut := hUmbrellaGoOut hTakeUmbrella
      exact hGoOut
  | inr hSunny =>
      have hWearSunglasses := hSunnySunglasses hSunny
      have hGoOut := hSunglassesGoOut hWearSunglasses
      exact hGoOut

end CompleteArguments

end Course.Shared.Lecture03.EN.Solutions
