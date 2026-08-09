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

-- Introduciamo ora gli ingredienti richiesti dagli esercizi sulle funzioni.
variable (madreDi : Cosa → Cosa)
variable (ipazia : Cosa)
variable (Curiosa : Cosa → Prop)
variable (Conosce : Cosa → Cosa → Prop)

-- ------------------------------------------------------------
-- ESERCIZIO: FORMALIZZARE CON UNA FUNZIONE
-- ------------------------------------------------------------

-- Formalizziamo:
--
-- 1. La madre di Ipazia è curiosa.
-- 2. Ogni studentessa conosce la propria madre.
-- 3. Esiste una studentessa la cui madre legge.

-- SOLUZIONI

-- 1. «La madre di Ipazia è curiosa».
#check Curiosa (madreDi ipazia)

-- 2. «Ogni studentessa conosce la propria madre».
#check ∀ x : Cosa, Studentessa x → Conosce x (madreDi x)

-- 3. «Esiste una studentessa la cui madre legge».
#check ∃ x : Cosa, Studentessa x ∧ Legge (madreDi x)

-- Introduciamo `Persona` soltanto per gli esercizi che lo richiedono.
variable (Persona : Cosa → Prop)

-- ------------------------------------------------------------
-- ESERCIZIO: RELAZIONI E QUANTIFICATORI ANNIDATI
-- ------------------------------------------------------------

-- Usando `Conosce : Cosa → Cosa → Prop`, formalizziamo:
--
-- 1. Ogni persona conosce qualcuno.
-- 2. Qualcuno conosce ogni persona.
-- 3. Nessuno conosce ogni persona.

-- SOLUZIONI

-- 1. «Ogni persona conosce qualcuno».
#check ∀ x : Cosa, Persona x →
  ∃ y : Cosa, Persona y ∧ Conosce x y

-- 2. «Qualcuno conosce ogni persona».
#check ∃ x : Cosa, Persona x ∧
  ∀ y : Cosa, Persona y → Conosce x y

-- 3. «Nessuno conosce ogni persona».
#check ¬∃ x : Cosa, Persona x ∧
  ∀ y : Cosa, Persona y → Conosce x y

end EserciziDiFormalizzazione

-- ============================================================
-- QUANTIFICATORE UNIVERSALE: ∀
-- ============================================================

-- Introduzione del quantificatore universale, ∀I.
-- `A x` sopra la linea della regola è una premessa.
-- Il goal universale viene aperto introducendo una cosa nuova e arbitraria `x`.
-- Soltanto il primo `intro` applica ∀I; i due `intro` successivi introducono
-- separatamente le assunzioni delle implicazioni.
-- Esempio: ogni persona curiosa è curiosa.
theorem lecture04_forall_intro
    (Cosa : Type)
    (Persona Curiosa : Cosa → Prop) :
    ∀ y : Cosa, Persona y → Curiosa y → Curiosa y := by
  intro x
  intro hXPersona
  intro hXCuriosa
  exact hXCuriosa

-- Eliminazione del quantificatore universale, ∀E.
-- Applichiamo una regola universale a Marta e poi usiamo la premessa concreta.
-- Esempio: ogni studentessa legge; Marta è studentessa; dunque Marta legge.
theorem lecture04_forall_elim
    (Cosa : Type)
    (Studentessa Legge : Cosa → Prop)
    (marta : Cosa)
    (hOgniStudentessaLegge :
      ∀ x : Cosa, Studentessa x → Legge x)
    (hMartaStudentessa : Studentessa marta) :
    Legge marta := by
  have hSeMartaStudentessaAlloraLegge := hOgniStudentessaLegge marta
  have hMartaLegge := hSeMartaStudentessaAlloraLegge hMartaStudentessa
  exact hMartaLegge

-- ============================================================
-- QUANTIFICATORE ESISTENZIALE: ∃
-- ============================================================

-- Introduzione del quantificatore esistenziale, ∃I.
-- `marta : Cosa` dice che Marta è un elemento del dominio.
-- Scegliamo Marta come testimone e usiamo l'assunzione che legge.
theorem lecture04_exists_intro
    (Cosa : Type)
    (Legge : Cosa → Prop)
    (marta : Cosa)
    (hMartaLegge : Legge marta) :
    ∃ x : Cosa, Legge x := by
  apply Exists.intro marta
  exact hMartaLegge

-- Eliminazione del quantificatore esistenziale, ∃E.
-- Apriamo l'esistenziale, usiamo il testimone senza presupporne l'identità
-- e dimostriamo una conclusione che non dipende dalla sua identità.
-- Esempio: qualcuno ha fatto una segnalazione; se qualcuno fa una
-- segnalazione, inizia un'indagine; dunque inizia un'indagine.
theorem lecture04_exists_elim
    (Cosa : Type)
    (HaFattoSegnalazione : Cosa → Prop)
    (IniziaIndagine : Prop)
    (hQualcunoHaFattoSegnalazione : ∃ x : Cosa, HaFattoSegnalazione x)
    (hChiFaSegnalazioneAvviaIndagine :
      ∀ x : Cosa, HaFattoSegnalazione x → IniziaIndagine) :
    IniziaIndagine := by
  apply Exists.elim hQualcunoHaFattoSegnalazione
  intro y
  intro hYHaFattoSegnalazione
  have hIndagine :=
    hChiFaSegnalazioneAvviaIndagine y hYHaFattoSegnalazione
  exact hIndagine

-- Esempio più complesso: combiniamo ∃E, ∀E e ∃I.
-- Qualcuna ha un ombrello; chiunque abbia un ombrello resta asciutta;
-- dunque qualcuna resta asciutta.
theorem lecture04_exists_elim_combined
    (Cosa : Type)
    (HaOmbrello RestaAsciutta : Cosa → Prop)
    (hQualcunaHaOmbrello : ∃ x : Cosa, HaOmbrello x)
    (hChiHaOmbrelloRestaAsciutta :
      ∀ x : Cosa, HaOmbrello x → RestaAsciutta x) :
    ∃ x : Cosa, RestaAsciutta x := by
  apply Exists.elim hQualcunaHaOmbrello
  intro x hXHaOmbrello
  apply Exists.intro x
  have hXRestaAsciutta := hChiHaOmbrelloRestaAsciutta x hXHaOmbrello
  exact hXRestaAsciutta

end Course.Shared.Lecture04.IT.Classroom
