import Course.Shared.Lecture02.Common.Classroom

/-!
# Lezione 2: Regole di introduzione ed eliminazione

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Data: 6 luglio 2026.
Durata: 2 ore.

-/

namespace Course.Shared.Lecture02.IT.Classroom

open Course.Shared.Lecture02.Common.Classroom

-- Leggere i connettivi attraverso le loro regole di introduzione ed eliminazione.

-- ============================================================
-- IMPLICAZIONE: P → Q
-- ============================================================

-- Introduzione dell'implicazione.
-- Per dimostrare `P → Q`, assumiamo temporaneamente `P` e costruiamo `Q`.
-- Regola: se assumendo P riusciamo a dimostrare Q, allora abbiamo P → Q.
theorem lecture02_imp_intro (P Q : Prop) (hQ : Q) :
    P → Q := by
  intro hP
  -- hP : P è l'assunzione temporanea introdotta dalla regola.
  exact hQ

-- Eliminazione dell'implicazione.
-- Regola: da P → Q e P otteniamo Q. Questo è il modus ponens.
theorem lecture02_imp_elim (P Q : Prop) :
    (P → Q) → P → Q := by
  intro hPQ
  intro hP
  have hQ := hPQ hP
  exact hQ

-- ============================================================
-- CONGIUNZIONE: P ∧ Q
-- ============================================================

theorem lecture02_and_intro (P Q : Prop) (hP : P) (hQ : Q) :
    P ∧ Q := by
  -- Regola di introduzione: da P e Q otteniamo P ∧ Q.
  have hPAndQ := And.intro hP hQ
  exact hPAndQ

theorem lecture02_and_intro_with_apply (P Q : Prop) (hP : P) (hQ : Q) :
    P ∧ Q := by
  -- Stessa regola, usando esplicitamente il costruttore come tattica. Notare qui la creazione di più subgoals.
  apply And.intro
  · exact hP
  · exact hQ

theorem lecture02_and_elim_left (P Q : Prop) :
    P ∧ Q → P := by
  intro hPAndQ
  -- Regola di eliminazione sinistra: da P ∧ Q otteniamo P.
  exact hPAndQ.left

theorem lecture02_and_elim_right (P Q : Prop) :
    P ∧ Q → Q := by
  intro hPAndQ
  -- Regola di eliminazione destra: da P ∧ Q otteniamo Q.
  exact hPAndQ.right

-- ============================================================
-- DISGIUNZIONE: P ∨ Q
-- ============================================================

theorem lecture02_or_intro_left (P Q : Prop) :
    P → P ∨ Q := by
  intro hP
  -- Regola di introduzione sinistra: da P otteniamo P ∨ Q.
  exact Or.inl hP

theorem lecture02_or_intro_left_with_apply (P Q : Prop) :
    P → P ∨ Q := by
  intro hP
  -- Stessa regola, usando esplicitamente il costruttore sinistro.
  apply Or.inl
  exact hP

theorem lecture02_or_intro_right (P Q : Prop) :
    Q → P ∨ Q := by
  intro hQ
  -- Regola di introduzione destra: da Q otteniamo P ∨ Q.
  exact Or.inr hQ

theorem lecture02_or_intro_right_with_apply (P Q : Prop) :
    Q → P ∨ Q := by
  intro hQ
  -- Stessa regola, usando esplicitamente il costruttore destro.
  apply Or.inr
  exact hQ

theorem lecture02_or_elim (P Q : Prop) :
    P ∨ Q → Q ∨ P := by
  intro hPOrQ
  -- Regola di eliminazione: da P ∨ Q dobbiamo trattare il caso P e il caso Q. In ciascuno di questi due casi dobbiamo dimostrare lo stesso goal (Q ∨ P nella fattispecie).
  cases hPOrQ with
  | inl hP =>
      -- Caso 1: abbiamo una dimostrazione di P.
      exact Or.inr hP
  | inr hQ =>
      -- Caso 2: abbiamo una dimostrazione di Q.
      exact Or.inl hQ

theorem lecture02_or_elim_with_or_elim (P Q : Prop) :
    P ∨ Q → Q ∨ P := by
  intro hPOrQ
  -- `Or.elim` è la stessa regola: una dimostrazione per il caso P e una per il caso Q. Notare come si modifica il goal.
  apply Or.elim hPOrQ
  · intro hP
    exact Or.inr hP
  · intro hQ
    exact Or.inl hQ

-- ============================================================
-- FALSE E NEGAZIONE
-- ============================================================

theorem lecture02_false_elim_with_apply (P : Prop) :
    False → P := by
  intro hFalse
  -- Regola di eliminazione: da False possiamo ottenere qualunque proposizione P.
  apply False.elim -- exfalso
  exact hFalse

theorem lecture02_false_elim (P : Prop) :
    False → P := by
  intro hFalse
  -- Stessa regola, usando `exact`.
  exact False.elim hFalse

-- Vediamo ora la forma che la negazione assume in Lean. Come dimostriamo che P e la sua negazione producono una contraddizione?
theorem lecture02_not_elim (P : Prop) :
    P → ¬P → False := by
  intro hP
  intro hNonP
  -- Regola di eliminazione: P e ¬P producono False.
  exact hNonP hP

-- Come è fatto ¬P? Equivale a P → False. Vediamolo con un esempio:
theorem lecture02_not_intro (P Q : Prop) :
    (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hNonQ
  -- Regola di introduzione: per dimostrare ¬P, assumiamo P e deriviamo False (una contraddizione). Osservare come cambia il goal
  intro hP
  have hQ := hPQ hP
  exact hNonQ hQ

theorem lecture02_vino_modus_tollens
    (BevoVino Ubriaco : Prop) :
    ((BevoVino → Ubriaco) ∧ ¬Ubriaco) → ¬BevoVino := by
  intro assunzione
  have hBevoUbriaco := assunzione.left
  have hNonUbriaco := assunzione.right
  intro hBevoVino
  have hUbriaco := hBevoUbriaco hBevoVino
  exact hNonUbriaco hUbriaco

-- ============================================================
-- BICONDIZIONALE: P ↔ Q
-- ============================================================

theorem lecture02_iff_intro (P Q : Prop) :
    (P → Q) → (Q → P) → (P ↔ Q) := by
  intro hPQ
  intro hQP
  -- Regola di introduzione: da P → Q e Q → P otteniamo P ↔ Q.
  apply Iff.intro
  · exact hPQ
  · exact hQP
  -- O semplicemente: exact Iff.intro hPQ hQP

theorem lecture02_iff_elim_left (P Q : Prop) :
    (P ↔ Q) → P → Q := by
  intro hIff
  intro hP
  -- Regola di eliminazione sinistra-destra: `Iff.mp` estrae la direzione P → Q.
  exact Iff.mp hIff hP

theorem lecture02_iff_elim_right (P Q : Prop) :
    (P ↔ Q) → Q → P := by
  intro hIff
  intro hQ
  -- Regola di eliminazione destra-sinistra: `Iff.mpr` estrae la direzione Q → P.
  exact Iff.mpr hIff hQ


-- ============================================================
-- CONTRAPPOSIZIONE
-- ============================================================

theorem lecture02_contrapposizione_avanti (P Q : Prop) :
    (P → Q) → (¬Q → ¬P) := by
  intro hPQ
  intro hNonQ
  -- Goal: ¬P, cioè P → False.
  intro hP
  have hQ := hPQ hP
  exact hNonQ hQ

theorem lecture02_contrapposizione_classica (P Q : Prop) :
    (¬Q → ¬P) → (P → Q) := by
  intro hContrapp
  intro hP
  -- Goal: Q.
  -- Costruttivamente non sappiamo costruire Q direttamente da questi dati.
  -- Usiamo quindi il terzo escluso su Q.
  cases Classical.em Q with
  | inl hQ =>
      -- Caso Q: abbiamo esattamente il goal.
      exact hQ
  | inr hNonQ =>
      -- Caso ¬Q: da hContrapp otteniamo ¬P, che contraddice hP.
      have hNonP := hContrapp hNonQ
      exfalso
      exact hNonP hP

theorem lecture02_contrapposizione_completa (P Q : Prop) :
    (P → Q) ↔ (¬Q → ¬P) := by
  apply Iff.intro
  · -- Direzione costruttiva.
    exact lecture02_contrapposizione_avanti P Q
  · -- Direzione classica.
    exact lecture02_contrapposizione_classica P Q

-- ============================================================
-- DIMOSTRAZIONE PER CONTRADDIZIONE
-- ============================================================

theorem lecture02_proof_by_contradiction (P : Prop) :
    (¬P → False) → P := by
  intro hContraddizione
  -- Dimostrazione per assurdo:
  -- assumere ¬P porta a False, dunque classicamente concludiamo P. Usiamo il terzo escluso su P:
  cases Classical.em P with
  | inl hP =>
      exact hP
  | inr hNonP =>
      exfalso
      exact hContraddizione hNonP

theorem lecture02_by_contradiction_classical (P : Prop) :
    (¬P → False) → P := by
  intro hContraddizione
  -- La stessa dimostrazione classica, usando direttamente il principio dedicato.
  exact Classical.byContradiction hContraddizione

-- ============================================================
-- ESEMPI PIÙ ELABORATI
-- ============================================================
-- Linguaggio naturale: se abbiamo un'assunzione, se dall'assunzione segue
-- una conseguenza, e se dalla conseguenza segue una conclusione, allora abbiamo
-- la conclusione.
example (Assunzione Conseguenza Conclusione : Prop) :
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
  | inl hPiove =>
      exact hPioveOmbrello hPiove
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
  · intro hPiove
    exact hPioveOmbrello hPiove
  · intro hNevica
    exact hNevicaOmbrello hNevica

-- Linguaggio naturale: se la fonte è autentica oppure i dati sono coerenti,
-- e ciascuno dei due casi supporta la tesi, e se una tesi supportata rende
-- plausibile la conclusione, allora la conclusione è plausibile.
example (FonteAutentica DatiCoerenti TesiSupportata ConclusionePlausibile : Prop) :
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

-- Vediamo una dimostrazione classica rispetto alla doppia negazione.
theorem lecture02_double_negation_classical (P : Prop) :
    ¬¬P → P := by
  intro hNonNonP
  -- Usiamo il terzo escluso: o P, oppure ¬P.
  cases Classical.em P with
  | inl hP =>
      exact hP
  | inr hNonP =>
      -- Nel caso ¬P, hNonNonP produce una contraddizione.
      exfalso -- apply False.elim
      exact hNonNonP hNonP

end Course.Shared.Lecture02.IT.Classroom
