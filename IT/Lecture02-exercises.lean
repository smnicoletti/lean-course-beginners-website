/-!
# Esercizi, Lezione 2

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Aprire questo file in VSCode e osservare l'Infoview dopo ogni riga. Ogni
`sorry` indica un buco intenzionale da sostituire con una dimostrazione.
-/

namespace Course.Shared.Lecture02.IT.Exercises

section Implicazione

-- Linguaggio naturale: se abbiamo gia una dimostrazione di `Q`, allora da `P`
-- possiamo concludere `Q`.
example (P Q : Prop) (hQ : Q) : P → Q := by
  sorry

-- Linguaggio naturale: se da `P` segue `Q`, e abbiamo `P`, allora abbiamo `Q`.
example (P Q : Prop) : (P → Q) → P → Q := by
  sorry

end Implicazione

section Congiunzione

-- Linguaggio naturale: se abbiamo `P` e abbiamo `Q`, allora abbiamo `P ∧ Q`.
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  sorry

-- Linguaggio naturale: da `P ∧ Q` possiamo estrarre `P`.
example (P Q : Prop) : P ∧ Q → P := by
  sorry

-- Linguaggio naturale: da `P ∧ Q` possiamo estrarre `Q`.
example (P Q : Prop) : P ∧ Q → Q := by
  sorry

-- Linguaggio naturale: se abbiamo `P ∧ Q`, allora possiamo scambiare l'ordine
-- e ottenere `Q ∧ P`.
example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

end Congiunzione

section Disgiunzione

-- Linguaggio naturale: se abbiamo `P`, allora abbiamo `P ∨ Q`.
example (P Q : Prop) : P → P ∨ Q := by
  sorry

-- Linguaggio naturale: se abbiamo `Q`, allora abbiamo `P ∨ Q`.
example (P Q : Prop) : Q → P ∨ Q := by
  sorry

-- Linguaggio naturale: se abbiamo `P ∨ Q`, allora possiamo ottenere `Q ∨ P`
-- ragionando per casi.
example (P Q : Prop) : P ∨ Q → Q ∨ P := by
  sorry

-- Linguaggio naturale: se prendo il bus oppure prendo il treno, e in ciascuno
-- dei due casi arrivo in tempo, allora arrivo in tempo.
example (PrendoBus PrendoTreno ArrivoInTempo : Prop) :
    ((PrendoBus → ArrivoInTempo) ∧
      (PrendoTreno → ArrivoInTempo)) ∧
    (PrendoBus ∨ PrendoTreno) →
    ArrivoInTempo := by
  sorry

end Disgiunzione

section FalseENegazione

-- Linguaggio naturale: da una contraddizione possiamo concludere qualunque `P`.
example (P : Prop) : False → P := by
  sorry

-- Linguaggio naturale: `P` e `¬P` producono una contraddizione.
example (P : Prop) : P → ¬P → False := by
  sorry

-- Linguaggio naturale: se da `P` segue `Q`, e `Q` e falso, allora `P` e falso.
example (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  sorry

-- Linguaggio naturale: se bevo caffè allora resto sveglio; ma non resto
-- sveglio; dunque non ho bevuto caffè.
example (BevoCaffe Sveglio : Prop) :
    ((BevoCaffe → Sveglio) ∧ ¬Sveglio) → ¬BevoCaffe := by
  sorry

end FalseENegazione

section Bicondizionale

-- Linguaggio naturale: se abbiamo entrambe le direzioni, allora abbiamo un
-- bicondizionale.
example (P Q : Prop) : (P → Q) → (Q → P) → (P ↔ Q) := by
  sorry

-- Linguaggio naturale: da `P ↔ Q` e `P` possiamo ottenere `Q`.
example (P Q : Prop) : (P ↔ Q) → P → Q := by
  sorry

-- Linguaggio naturale: da `P ↔ Q` e `Q` possiamo ottenere `P`.
example (P Q : Prop) : (P ↔ Q) → Q → P := by
  sorry

end Bicondizionale

section Classica

-- La direzione costruttiva della contrapposizione.
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  sorry

-- La direzione inversa della contrapposizione richiede
-- ragionamento classico.
example (P Q : Prop) : (¬Q → ¬P) → P → Q := by
  sorry

-- Dimostrazione classica per assurdo.
example (P : Prop) : (¬P → False) → P := by
  sorry

end Classica

section Argomentazione

-- Linguaggio naturale: se il modulo è completo, e se un modulo completo rende la
-- pratica ricevibile, e se una pratica ricevibile puo essere valutata, allora
-- la pratica puo essere valutata.
example (ModuloCompleto PraticaRicevibile PraticaValutabile : Prop) :
    (ModuloCompleto ∧ (ModuloCompleto → PraticaRicevibile)) ∧
      (PraticaRicevibile → PraticaValutabile) →
    PraticaValutabile := by
  sorry

-- Linguaggio naturale: se la misurazione è precisa oppure la revisione è approvata,
-- e ciascuno dei due casi rende affidabile il risultato, e se un risultato
-- affidabile giustifica la decisione, allora la decisione e giustificata.
example (MisurazionePrecisa RevisioneApprovata RisultatoAffidabile
    DecisioneGiustificata : Prop) :
    ((MisurazionePrecisa ∨ RevisioneApprovata) ∧
      ((MisurazionePrecisa → RisultatoAffidabile) ∧
        (RevisioneApprovata → RisultatoAffidabile))) ∧
    (RisultatoAffidabile → DecisioneGiustificata) →
    DecisioneGiustificata := by
  sorry

end Argomentazione

end Course.Shared.Lecture02.IT.Exercises
