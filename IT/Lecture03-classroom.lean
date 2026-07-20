/-!
# Lezione 3: Dalla deduzione naturale alle dimostrazioni in Lean

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Data: 20 luglio 2026.
Durata: 2 ore.

-/

namespace Course.Shared.Lecture03.IT.Classroom

-- Ogni esempio segue lo stesso percorso:
-- regola di deduzione naturale, lettura in linguaggio naturale, istanza concreta,
-- costruzione del termine richiesto nel proof state.

-- ============================================================
-- IMPLICAZIONE: A → B
-- ============================================================

-- Introduzione dell'implicazione, →I.
-- Per dimostrare `A → B`, introduciamo l'assunzione temporanea `A` e costruiamo `B`.
-- Esempio: se piove e fa freddo, allora piove.
theorem lecture03_imp_intro
    (Piove FaFreddo : Prop) :
    Piove ∧ FaFreddo → Piove := by
  intro hPioveEFaFreddo
  have hPiove := hPioveEFaFreddo.left
  exact hPiove

-- Eliminazione dell'implicazione, →E: modus ponens.
-- Da `A → B` e `A` otteniamo `B`.
-- Esempio: se piove, prendo l'ombrello; piove; dunque prendo l'ombrello.
theorem lecture03_imp_elim
    (Piove PrendoOmbrello : Prop)
    (hPioveOmbrello : Piove → PrendoOmbrello)
    (hPiove : Piove) :
    PrendoOmbrello := by
  have hPrendoOmbrello := hPioveOmbrello hPiove
  exact hPrendoOmbrello

-- ============================================================
-- CONGIUNZIONE: A ∧ B
-- ============================================================

-- Introduzione della congiunzione, ∧I.
-- Da una dimostrazione di A e una di B costruiamo una dimostrazione di A ∧ B.
-- Esempio: piove; fa freddo; dunque piove e fa freddo.
theorem lecture03_and_intro
    (Piove FaFreddo : Prop)
    (hPiove : Piove)
    (hFaFreddo : FaFreddo) :
    Piove ∧ FaFreddo := by
  apply And.intro
  · exact hPiove
  · exact hFaFreddo

-- Eliminazione sinistra della congiunzione, ∧Eₗ.
-- Da `A ∧ B` selezioniamo la componente A.
-- Esempio: piove e fa freddo; dunque piove.
theorem lecture03_and_elim_left
    (Piove FaFreddo : Prop)
    (hPioveEFaFreddo : Piove ∧ FaFreddo) :
    Piove := by
  have hPiove := hPioveEFaFreddo.left
  exact hPiove

-- Eliminazione destra della congiunzione, ∧Eᵣ.
-- Da `A ∧ B` selezioniamo la componente B.
-- Esempio: piove e fa freddo; dunque fa freddo.
theorem lecture03_and_elim_right
    (Piove FaFreddo : Prop)
    (hPioveEFaFreddo : Piove ∧ FaFreddo) :
    FaFreddo := by
  have hFaFreddo := hPioveEFaFreddo.right
  exact hFaFreddo

-- ============================================================
-- DISGIUNZIONE: A ∨ B
-- ============================================================

-- Introduzione sinistra della disgiunzione, ∨Iₗ.
-- Da A costruiamo A ∨ B scegliendo il lato sinistro.
-- Esempio: piove; dunque piove oppure nevica.
theorem lecture03_or_intro_left
    (Piove Nevica : Prop)
    (hPiove : Piove) :
    Piove ∨ Nevica := by
  apply Or.inl
  exact hPiove

-- Introduzione destra della disgiunzione, ∨Iᵣ.
-- Da B costruiamo A ∨ B scegliendo il lato destro.
-- Esempio: nevica; dunque piove oppure nevica.
theorem lecture03_or_intro_right
    (Piove Nevica : Prop)
    (hNevica : Nevica) :
    Piove ∨ Nevica := by
  apply Or.inr
  exact hNevica

-- Eliminazione della disgiunzione, ∨E.
-- Da `A ∨ B`, `A → C` e `B → C` otteniamo C ragionando per casi.
-- Esempio: piove oppure nevica; in entrambi i casi prendo l'ombrello;
-- dunque prendo l'ombrello.
theorem lecture03_or_elim
    (Piove Nevica PrendoOmbrello : Prop)
    (hPioveONevica : Piove ∨ Nevica)
    (hPioveOmbrello : Piove → PrendoOmbrello)
    (hNevicaOmbrello : Nevica → PrendoOmbrello) :
    PrendoOmbrello := by
  cases hPioveONevica with
  | inl hPiove =>
      have hPrendoOmbrello := hPioveOmbrello hPiove
      exact hPrendoOmbrello
  | inr hNevica =>
      have hPrendoOmbrello := hNevicaOmbrello hNevica
      exact hPrendoOmbrello

-- ============================================================
-- NEGAZIONE E FALSITÀ
-- ============================================================

-- Introduzione della negazione, ¬I.
-- Per dimostrare `¬A`, introduciamo l'assunzione A e deriviamo False.
-- Esempio: se bevo caffè resto sveglio, ma non resto sveglio; dunque non ho
-- bevuto caffè.
theorem lecture03_not_intro
    (BevoCaffe RestoSveglio : Prop)
    (hCaffeSveglio : BevoCaffe → RestoSveglio)
    (hNonSveglio : ¬RestoSveglio) :
    ¬BevoCaffe := by
  intro hBevoCaffe
  have hRestoSveglio := hCaffeSveglio hBevoCaffe
  have hContraddizione : False := hNonSveglio hRestoSveglio
  exact hContraddizione

-- Eliminazione della negazione, ¬E.
-- Da ¬A e A otteniamo False.
-- Esempio: il laboratorio è aperto e non è aperto; le assunzioni sono contraddittorie.
theorem lecture03_not_elim
    (LaboratorioAperto : Prop)
    (hLaboratorioAperto : LaboratorioAperto)
    (hLaboratorioNonAperto : ¬LaboratorioAperto) :
    False := by
  have hContraddizione := hLaboratorioNonAperto hLaboratorioAperto
  exact hContraddizione

-- Introduzione di True, ⊤I.
-- True ha un costruttore canonico e non richiede premesse.
theorem lecture03_true_intro : True := by
  exact True.intro -- Oppure: trivial

-- Eliminazione di False, ⊥E.
-- Da una contraddizione possiamo ottenere qualunque proposizione.
-- Esempio: da assunzioni contraddittorie concludiamo che piove.
theorem lecture03_false_elim
    (Piove : Prop)
    (hContraddizione : False) :
    Piove := by
  apply False.elim -- Oppure: exfalso
  exact hContraddizione

-- ============================================================
-- BICONDIZIONALE: A ↔ B
-- ============================================================

-- Introduzione del bicondizionale, ↔I.
-- Costruiamo entrambe le direzioni e le uniamo.
-- Esempio: `Piove ∧ FaFreddo` equivale a `FaFreddo ∧ Piove`.
theorem lecture03_iff_intro
    (Piove FaFreddo : Prop) :
    Piove ∧ FaFreddo ↔ FaFreddo ∧ Piove := by
  apply Iff.intro
  · intro hPioveEFaFreddo
    apply And.intro
    · exact hPioveEFaFreddo.right
    · exact hPioveEFaFreddo.left
  · intro hFaFreddoEPiove
    apply And.intro
    · exact hFaFreddoEPiove.right
    · exact hFaFreddoEPiove.left

-- Eliminazione sinistra-destra del bicondizionale, ↔Eₗ.
-- Estraiamo A → B e la applichiamo ad A.
theorem lecture03_iff_elim_left
    (NumeroPari DivisibilePerDue : Prop)
    (hEquivalenza : NumeroPari ↔ DivisibilePerDue)
    (hNumeroPari : NumeroPari) :
    DivisibilePerDue := by
  have hDirezione := Iff.mp hEquivalenza
  have hDivisibilePerDue := hDirezione hNumeroPari
  exact hDivisibilePerDue

-- Eliminazione destra-sinistra del bicondizionale, ↔Eᵣ.
-- Estraiamo B → A e la applichiamo a B.
theorem lecture03_iff_elim_right
    (NumeroPari DivisibilePerDue : Prop)
    (hEquivalenza : NumeroPari ↔ DivisibilePerDue)
    (hDivisibilePerDue : DivisibilePerDue) :
    NumeroPari := by
  have hDirezione := Iff.mpr hEquivalenza
  have hNumeroPari := hDirezione hDivisibilePerDue
  exact hNumeroPari

-- ============================================================
-- RIDUZIONE ALL'ASSURDO: REGOLA CLASSICA
-- ============================================================

-- Da `¬A → False` concludiamo classicamente A.
-- Esempio: se non piove, non prendo l'ombrello; ma prendo l'ombrello;
-- concludiamo classicamente che piove.
theorem lecture03_reductio_ad_absurdum
    (Piove PrendoOmbrello : Prop)
    (hNonPioveNonOmbrello : ¬Piove → ¬PrendoOmbrello)
    (hPrendoOmbrello : PrendoOmbrello) :
    Piove := by
  apply Classical.byContradiction
  intro hNonPiove
  have hNonPrendoOmbrello := hNonPioveNonOmbrello hNonPiove
  have hContraddizione := hNonPrendoOmbrello hPrendoOmbrello
  exact hContraddizione

end Course.Shared.Lecture03.IT.Classroom
