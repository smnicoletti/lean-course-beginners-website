/-!
# Soluzioni, Lezione 2

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture02.IT.Solutions

section Implicazione

-- Linguaggio naturale: se abbiamo gia una dimostrazione di `Q`, allora da `P`
-- possiamo concludere `Q`.
example (P Q : Prop) (hQ : Q) : P → Q := by
  intro hP
  exact hQ

-- Linguaggio naturale: se da `P` segue `Q`, e abbiamo `P`, allora abbiamo `Q`.
example (P Q : Prop) : (P → Q) → P → Q := by
  intro hPQ
  intro hP
  have hQ := hPQ hP
  exact hQ

end Implicazione

section Congiunzione

-- Linguaggio naturale: se abbiamo `P` e abbiamo `Q`, allora abbiamo `P ∧ Q`.
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  exact And.intro hP hQ

-- Linguaggio naturale: da `P ∧ Q` possiamo estrarre `P`.
example (P Q : Prop) : P ∧ Q → P := by
  intro hPQ
  exact hPQ.left

-- Linguaggio naturale: da `P ∧ Q` possiamo estrarre `Q`.
example (P Q : Prop) : P ∧ Q → Q := by
  intro hPQ
  exact hPQ.right

-- Linguaggio naturale: se abbiamo `P ∧ Q`, allora possiamo scambiare l'ordine
-- e ottenere `Q ∧ P`.
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro hPQ
  exact And.intro hPQ.right hPQ.left

end Congiunzione

section Disgiunzione

-- Linguaggio naturale: se abbiamo `P`, allora abbiamo `P ∨ Q`.
example (P Q : Prop) : P → P ∨ Q := by
  intro hP
  exact Or.inl hP

-- Linguaggio naturale: se abbiamo `Q`, allora abbiamo `P ∨ Q`.
example (P Q : Prop) : Q → P ∨ Q := by
  intro hQ
  exact Or.inr hQ

-- Linguaggio naturale: se abbiamo `P ∨ Q`, allora possiamo ottenere `Q ∨ P`
-- ragionando per casi.
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro hPOrQ
  cases hPOrQ with
  | inl hP =>
      exact Or.inr hP
  | inr hQ =>
      exact Or.inl hQ

-- Linguaggio naturale: se prendo il bus oppure prendo il treno, e in ciascuno
-- dei due casi arrivo in tempo, allora arrivo in tempo.
example (PrendoBus PrendoTreno ArrivoInTempo : Prop) :
    ((PrendoBus → ArrivoInTempo) ∧
      (PrendoTreno → ArrivoInTempo)) ∧
    (PrendoBus ∨ PrendoTreno) →
    ArrivoInTempo := by
  intro hArgomento
  have hRegole := hArgomento.left
  have hBusOTreno := hArgomento.right
  have hBusTempo := hRegole.left
  have hTrenoTempo := hRegole.right
  cases hBusOTreno with
  | inl hBus =>
      exact hBusTempo hBus
  | inr hTreno =>
      exact hTrenoTempo hTreno

end Disgiunzione

section FalseENegazione

-- Linguaggio naturale: da una contraddizione possiamo concludere qualunque `P`.
example (P : Prop) : False → P := by
  intro hFalse
  exact False.elim hFalse

-- Linguaggio naturale: `P` e `¬P` producono una contraddizione.
example (P : Prop) : P → ¬P → False := by
  intro hP
  intro hNonP
  exact hNonP hP

-- Linguaggio naturale: se da `P` segue `Q`, e `Q` e falso, allora `P` e falso.
example (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hNonQ
  intro hP
  have hQ := hPQ hP
  exact hNonQ hQ

end FalseENegazione

end Course.Shared.Lecture02.IT.Solutions
