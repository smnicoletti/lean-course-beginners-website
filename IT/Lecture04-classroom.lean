/-!
# Lezione 4: Logica classica e quantificatori

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture04.IT.Classroom

-- ============================================================
-- RIDUZIONE ALL'ASSURDO: REGOLA CLASSICA
-- ============================================================

-- Da `¬A → False` concludiamo classicamente A.
-- Esempio: se non piove, non prendo l'ombrello; ma prendo l'ombrello;
-- concludiamo classicamente che piove.
theorem lecture04_reductio_ad_absurdum
    (Piove PrendoOmbrello : Prop)
    (hNonPioveNonOmbrello : ¬Piove → ¬PrendoOmbrello)
    (hPrendoOmbrello : PrendoOmbrello) :
    Piove := by
  apply Classical.byContradiction
  intro hNonPiove
  have hNonPrendoOmbrello := hNonPioveNonOmbrello hNonPiove
  have hContraddizione := hNonPrendoOmbrello hPrendoOmbrello
  exact hContraddizione

-- ============================================================
-- IL LINGUAGGIO DELLA LOGICA DEI PREDICATI
-- ============================================================

section LinguaggioDeiPredicati

-- Le dichiarazioni `variable` restano disponibili soltanto fino al relativo
-- `end`. Dentro la sezione, Lean aggiunge a ciascun teorema solo i parametri
-- che il suo enunciato usa effettivamente: gli altri non compaiono nel proof state.

-- `variable` introduce parametri locali: non crea nuovi oggetti globali.
-- `constant` fisserebbe invece un simbolo globale.
-- Qui il tipo assunto temporaneamente rappresenta il dominio del discorso.
variable (Cosa : Type)

-- Questi parametri ricevono un'interpretazione quando usiamo un teorema.
variable (ipazia hannah roma atene : Cosa)

-- Un predicato prende un oggetto e restituisce una proposizione.
variable (Persona Citta Filosofa Curiosa : Cosa → Prop)

-- Una funzione prende un oggetto e restituisce un oggetto.
variable (madreDi : Cosa → Cosa)

-- Una relazione prende due oggetti del dominio.
variable (Conosce Visita : Cosa → Cosa → Prop)

#check ipazia
#check Filosofa
#check Filosofa ipazia
#check madreDi
#check madreDi ipazia
#check Curiosa (madreDi ipazia)
#check Conosce ipazia hannah
#check Visita ipazia atene

-- «Ogni filosofa è curiosa».
#check ∀ x : Cosa, Filosofa x → Curiosa x

-- «Esiste una filosofa curiosa».
#check ∃ x : Cosa, Filosofa x ∧ Curiosa x

end LinguaggioDeiPredicati

-- ============================================================
-- ESERCIZI DI FORMALIZZAZIONE
-- ============================================================

section EserciziDiFormalizzazione

variable (Cosa : Type)
variable (Studentessa Legge Comprende : Cosa → Prop)

-- ------------------------------------------------------------
-- ESERCIZIO: DAL LINGUAGGIO NATURALE A LEAN
-- ------------------------------------------------------------

-- Formalizziamo:
--
-- 1. Ogni studentessa legge.
-- 2. Qualche studentessa legge.
-- 3. Ogni studentessa che legge comprende.
-- 4. Esiste una studentessa che legge e comprende.

-- SOLUZIONI

-- 1. «Ogni studentessa legge».
#check ∀ x : Cosa, Studentessa x → Legge x

-- 2. «Qualche studentessa legge».
#check ∃ x : Cosa, Studentessa x ∧ Legge x

-- 3. «Ogni studentessa che legge comprende».
#check ∀ x : Cosa, Studentessa x → Legge x → Comprende x

-- 4. «Esiste una studentessa che legge e comprende».
#check ∃ x : Cosa, Studentessa x ∧ Legge x ∧ Comprende x

end EserciziDiFormalizzazione

end Course.Shared.Lecture04.IT.Classroom
