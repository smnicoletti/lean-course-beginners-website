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

-- Linguaggio naturale: se bevo caffè allora resto sveglio; ma non resto
-- sveglio; dunque non ho bevuto caffè.
example (BevoCaffe Sveglio : Prop) :
    ((BevoCaffe → Sveglio) ∧ ¬Sveglio) → ¬BevoCaffe := by
  intro hArgomento
  have hRegola := hArgomento.left
  have hNonSveglio := hArgomento.right
  intro hBevoCaffe
  have hSveglio := hRegola hBevoCaffe
  exact hNonSveglio hSveglio

end FalseENegazione

section Bicondizionale

-- Linguaggio naturale: se abbiamo entrambe le direzioni, allora abbiamo un
-- bicondizionale.
example (P Q : Prop) : (P → Q) → (Q → P) → (P ↔ Q) := by
  intro hPQ
  intro hQP
  exact Iff.intro hPQ hQP

-- Linguaggio naturale: da `P ↔ Q` e `P` possiamo ottenere `Q`.
example (P Q : Prop) : (P ↔ Q) → P → Q := by
  intro hIff
  intro hP
  exact Iff.mp hIff hP

-- Linguaggio naturale: da `P ↔ Q` e `Q` possiamo ottenere `P`.
example (P Q : Prop) : (P ↔ Q) → Q → P := by
  intro hIff
  intro hQ
  exact Iff.mpr hIff hQ

end Bicondizionale

section Classica

-- La direzione costruttiva della contrapposizione.
example (P Q : Prop) : (P → Q) → (¬Q → ¬P) := by
  intro hPQ
  intro hNonQ
  intro hP
  have hQ := hPQ hP
  exact hNonQ hQ

-- La direzione inversa della contrapposizione richiede
-- ragionamento classico.
example (P Q : Prop) : (¬Q → ¬P) → P → Q := by
  intro hContrapp
  intro hP
  cases Classical.em Q with
  | inl hQ =>
      exact hQ
  | inr hNonQ =>
      have hNonP := hContrapp hNonQ
      exfalso
      exact hNonP hP

-- Dimostrazione classica per assurdo.
example (P : Prop) : (¬P → False) → P := by
  intro hContraddizione
  exact Classical.byContradiction hContraddizione

end Classica

section Argomentazione

-- Linguaggio naturale: se il modulo è completo, e se un modulo completo rende la
-- pratica ricevibile, e se una pratica ricevibile puo essere valutata, allora
-- la pratica puo essere valutata.
example (ModuloCompleto PraticaRicevibile PraticaValutabile : Prop) :
    (ModuloCompleto ∧ (ModuloCompleto → PraticaRicevibile)) ∧
      (PraticaRicevibile → PraticaValutabile) →
    PraticaValutabile := by
  intro hArgomento
  have hPrimoPasso := hArgomento.left
  have hModuloCompleto := hPrimoPasso.left
  have hModuloPratica := hPrimoPasso.right
  have hPraticaValutabile := hArgomento.right
  have hPraticaRicevibile := hModuloPratica hModuloCompleto
  have hValutabile := hPraticaValutabile hPraticaRicevibile
  exact hValutabile

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
  intro hArgomento
  have hPrimoPasso := hArgomento.left
  have hMisurazioneORevisione := hPrimoPasso.left
  have hRegoleAffidabilita := hPrimoPasso.right
  have hMisurazioneAffidabile := hRegoleAffidabilita.left
  have hRevisioneAffidabile := hRegoleAffidabilita.right
  have hAffidabileDecisione := hArgomento.right
  have hRisultato :=
    Or.elim hMisurazioneORevisione hMisurazioneAffidabile hRevisioneAffidabile
  have hDecisione := hAffidabileDecisione hRisultato
  exact hDecisione

end Argomentazione

end Course.Shared.Lecture02.IT.Solutions
