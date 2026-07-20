/-!
# Exercises, Lecture 3

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Open this file in VSCode and observe how the goal changes after each tactic.
Each `sorry` is a proof to complete with the natural-deduction rules from class.
-/

namespace Course.Shared.Lecture03.EN.Exercises

section ImplicationAndConjunction

-- If I drink wine and eat pasta, then I drink wine.
example (DrinkWine EatPasta : Prop) : DrinkWine ∧ EatPasta → DrinkWine := by
  sorry

-- I drink wine; if I drink wine, I get drunk; therefore I get drunk.
example (DrinkWine GetDrunk : Prop)
    (hDrinkWine : DrinkWine) (hWineDrunk : DrinkWine → GetDrunk) :
    GetDrunk := by
  sorry

-- I take an umbrella and wear a coat.
example (TakeUmbrella WearCoat : Prop)
    (hTakeUmbrella : TakeUmbrella) (hWearCoat : WearCoat) :
    TakeUmbrella ∧ WearCoat := by
  sorry

-- From taking an umbrella and wearing a coat, conclude that I wear a coat.
example (TakeUmbrella WearCoat : Prop)
    (hClothing : TakeUmbrella ∧ WearCoat) : WearCoat := by
  sorry

end ImplicationAndConjunction

section Disjunction

example (TravelByBus TravelByTrain : Prop) (hBus : TravelByBus) :
    TravelByBus ∨ TravelByTrain := by
  sorry

example (TravelByBus TravelByTrain : Prop) (hTrain : TravelByTrain) :
    TravelByBus ∨ TravelByTrain := by
  sorry

-- I travel by bus or train, and either choice gets me there on time.
example (TravelByBus TravelByTrain ArriveOnTime : Prop)
    (hChoice : TravelByBus ∨ TravelByTrain)
    (hBusOnTime : TravelByBus → ArriveOnTime)
    (hTrainOnTime : TravelByTrain → ArriveOnTime) : ArriveOnTime := by
  sorry

end Disjunction

section NegationTruthAndFalsity

-- If coffee keeps me awake, but I am not awake, then I did not drink coffee.
example (DrinkCoffee StayAwake : Prop)
    (hCoffeeAwake : DrinkCoffee → StayAwake) (hNotAwake : ¬StayAwake) :
    ¬DrinkCoffee := by
  sorry

example (ShopOpen : Prop) (hOpen : ShopOpen) (hNotOpen : ¬ShopOpen) :
    False := by
  sorry

example : True := by
  sorry

example (WinPrize : Prop) (hContradiction : False) : WinPrize := by
  sorry

end NegationTruthAndFalsity

section Biconditional

example (DoorClosed LightOff : Prop) :
    DoorClosed ∧ LightOff ↔ LightOff ∧ DoorClosed := by
  sorry

example (EvenNumber DivisibleByTwo : Prop)
    (hEquivalence : EvenNumber ↔ DivisibleByTwo) (hEven : EvenNumber) :
    DivisibleByTwo := by
  sorry

example (EvenNumber DivisibleByTwo : Prop)
    (hEquivalence : EvenNumber ↔ DivisibleByTwo)
    (hDivisible : DivisibleByTwo) : EvenNumber := by
  sorry

end Biconditional

section CompleteArguments

-- Whether it rains or is sunny, the appropriate item lets me go out.
example (Rains Sunny TakeUmbrella WearSunglasses GoOut : Prop)
    (hWeather : Rains ∨ Sunny)
    (hRainsUmbrella : Rains → TakeUmbrella)
    (hSunnySunglasses : Sunny → WearSunglasses)
    (hUmbrellaGoOut : TakeUmbrella → GoOut)
    (hSunglassesGoOut : WearSunglasses → GoOut) : GoOut := by
  sorry

end CompleteArguments

end Course.Shared.Lecture03.EN.Exercises
