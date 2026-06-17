/-!
# Lezione 1: Che cos'e un dimostratore di teoremi?

Autore: Stefano M. Nicoletti
Sito web: https://stefanonicoletti.com/

Data: 22 giugno 2026.
Durata: 2 ore.

-/

namespace Course.Shared.Lecture01.IT.Classroom

-- Tipi, #check, #eval

#check Prop
#check Nat
#check Float

--variable(a : Nat)
--#check a

#eval 3 + 1
#eval 3.5 + 2

-- Linguaggio naturale: se assumiamo che piove, allora possiamo concludere che piove.
example (Piove : Prop) (hPiove : Piove) : Piove := by
  sorry

-- Linguaggio naturale: se assumiamo che piove, allora possiamo concludere che piove.
example (Piove : Prop) (hPiove : Piove) : Piove := by
  exact hPiove

-- Linguaggio naturale: se piove, allora piove.
example (Piove : Prop) : Piove → Piove := by
  intro h --intro nomeInformativo, qualsiasi nome ci aiuti a ricordare l'ipotesi
  exact h

-- Linguaggio naturale: se piove allora prendo l'ombrello, e piove, allora questo implica che
-- prendo l'ombrello.
example (Piove PrendoOmbrello : Prop) :
    ((Piove → PrendoOmbrello) ∧ Piove) → PrendoOmbrello := by
  intro ipotesi
  have hPioveOmbrello := ipotesi.left
  have hPiove := ipotesi.right
  have hPrendoOmbrello := hPioveOmbrello hPiove
  exact hPrendoOmbrello

-- Dimostrazione più breve
example (Piove PrendoOmbrello : Prop) :
    ((Piove → PrendoOmbrello) ∧ Piove) → PrendoOmbrello := by
  intro h
  exact h.left h.right

-- Dichiaro le assunzioni in modo esplicito nel preambolo dell'esempio
-- Linguaggio naturale: assumiamo che, se piove, allora prendo l'ombrello;
-- assumiamo anche che piove; quindi prendo l'ombrello.
example (Piove PrendoOmbrello : Prop)
    (hPioveOmbrello : Piove → PrendoOmbrello) (hPiove : Piove) :
    PrendoOmbrello := by
  exact hPioveOmbrello hPiove

-- Codifichiamo, verifichiamo e usiamo lo schema di ragionamento valido. Le graffe indicano argomenti impliciti: spesso Lean riesce a inferirli dal tipo delle ipotesi.
-- Linguaggio naturale: se P è vero e da P segue Q, allora Q è vero.
theorem lecture01_modus_ponens
    {P Q : Prop}
    (hP : P) (hPQ : P → Q) :
    Q := by
  exact hPQ hP

example (Piove PrendoOmbrello : Prop)
    (hPioveOmbrello : Piove → PrendoOmbrello) (hPiove : Piove) :
    PrendoOmbrello := by
  exact lecture01_modus_ponens hPiove hPioveOmbrello

-- Linguaggio naturale: se abbiamo un'assunzione, se dall'assunzione segue
-- una conseguenza, e se dalla conseguenza segue una conclusione, allora abbiamo
-- la conclusione.
theorem lecture01_informal_argument_schema
    (Assunzione Conseguenza Conclusione : Prop) :
    (Assunzione ∧ (Assunzione → Conseguenza)) ∧
      (Conseguenza → Conclusione) →
    Conclusione := by
  intro hArgomento
  have hPrimoPasso := hArgomento.left
  have hAssunzione := hPrimoPasso.left
  have hPasso1 := hPrimoPasso.right
  have hPasso2 := hArgomento.right
  have hConseguenza := hPasso1 hAssunzione
  have hConclusione := hPasso2 hConseguenza
  exact hConclusione

-- Linguaggio naturale: se bevo vino allora mi ubriaco; ma non sono ubriaco;
-- dunque non ho bevuto vino.
theorem lecture01_wine_example
    (BevoVino Ubriaco : Prop) :
    ((BevoVino → Ubriaco) ∧ ¬Ubriaco) → ¬BevoVino := by
  intro hArgomento
  have hRegola := hArgomento.left
  have hNonUbriaco := hArgomento.right
  intro hBevoVino
  have hUbriaco := hRegola hBevoVino
  exact hNonUbriaco hUbriaco

-- Linguaggio naturale: se piove oppure nevica, e in ciascuno dei due casi
-- prendo l'ombrello, allora prendo l'ombrello.
example (Piove Nevica PrendoOmbrello : Prop) :
    ((Piove → PrendoOmbrello) ∧
      (Nevica → PrendoOmbrello)) ∧
    (Piove ∨ Nevica) →
    PrendoOmbrello := by
  intro hArgomento
  have hRegole := hArgomento.left
  have hPioveONevica := hArgomento.right
  have hPioveOmbrello := hRegole.left
  have hNevicaOmbrello := hRegole.right
  -- Non sappiamo quale lato della `∨` è valido, quindi consideriamo entrambi i casi.
  cases hPioveONevica with
  -- Primo caso: l'ipotesi `Piove ∨ Nevica` è vera perché vale `Piove`, dimostriamo `PrendoOmbrello`.
  | inl hPiove =>
      exact hPioveOmbrello hPiove
  -- Secondo caso: l'ipotesi `Piove ∨ Nevica` è vera perché vale `Nevica`, dimostriamo `PrendoOmbrello`.
  | inr hNevica =>
      exact hNevicaOmbrello hNevica

-- La stessa dimostrazione, usando direttamente `Or.elim`.
example (Piove Nevica PrendoOmbrello : Prop) :
    ((Piove → PrendoOmbrello) ∧
      (Nevica → PrendoOmbrello)) ∧
    (Piove ∨ Nevica) →
    PrendoOmbrello := by
  intro hArgomento
  have hRegole := hArgomento.left
  have hPioveONevica := hArgomento.right
  have hPioveOmbrello := hRegole.left
  have hNevicaOmbrello := hRegole.right
  apply Or.elim hPioveONevica
  -- Se vale il lato sinistro della `∨`, cioè `Piove`,
  -- usiamo la regola `Piove → PrendoOmbrello`.
  · intro hPiove
    exact hPioveOmbrello hPiove
  -- Se vale il lato destro della `∨`, cioè `Nevica`,
  -- usiamo la regola `Nevica → PrendoOmbrello`.
  · intro hNevica
    exact hNevicaOmbrello hNevica

-- Linguaggio naturale: se la fonte è autentica oppure i dati sono coerenti,
-- e ciascuno dei due casi supporta la tesi, e se una tesi supportata rende
-- plausibile la conclusione, allora la conclusione è plausibile.
theorem lecture01_history_of_science_example
    (FonteAutentica DatiCoerenti TesiSupportata ConclusionePlausibile : Prop) :
    ((FonteAutentica ∨ DatiCoerenti) ∧
      ((FonteAutentica → TesiSupportata) ∧
        (DatiCoerenti → TesiSupportata))) ∧
    (TesiSupportata → ConclusionePlausibile) →
    ConclusionePlausibile := by
  intro hArgomento
  have hPrimoPasso := hArgomento.left
  have hFonteODati := hPrimoPasso.left
  have hRegoleSupporto := hPrimoPasso.right
  have hFonteSupporta := hRegoleSupporto.left
  have hDatiSupportano := hRegoleSupporto.right
  have hSupportoConclude := hArgomento.right
  have hTesi :=
    Or.elim hFonteODati hFonteSupporta hDatiSupportano
  have hConclusione := hSupportoConclude hTesi
  exact hConclusione

end Course.Shared.Lecture01.IT.Classroom
