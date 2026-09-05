/-!
# Lezione 5: Regole dei quantificatori

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture05.IT.Classroom

section EserciziDiFormalizzazione

variable (Cosa : Type)
variable (Studentessa Legge Comprende : Cosa → Prop)

-- ------------------------------------------------------------
-- RIPASSO DALLA LEZIONE 4
-- ------------------------------------------------------------

-- 1. Ogni studentessa legge.
-- 2. Qualche studentessa legge.
-- 3. Ogni studentessa che legge comprende.
-- 4. Esiste una studentessa che legge e comprende.

#check ∀ x : Cosa, Studentessa x → Legge x
#check ∃ x : Cosa, Studentessa x ∧ Legge x
#check ∀ x : Cosa, Studentessa x → Legge x → Comprende x
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
-- Il goal universale viene aperto introducendo una cosa nuova e arbitraria `x`.
-- Soltanto il primo `intro` applica ∀I; i due `intro` successivi introducono
-- separatamente le assunzioni delle implicazioni.
-- Esempio: ogni persona curiosa è curiosa.
theorem lecture05_forall_intro
    (Cosa : Type)
    (Persona Curiosa : Cosa → Prop) :
    ∀ y : Cosa, Persona y → Curiosa y → Curiosa y := by
  intro x
  intro hXPersona
  intro hXCuriosa
  exact hXCuriosa

-- Perché `x` deve essere arbitraria?
-- Da una proprietà della sola Ipazia non possiamo concludere che la proprietà
-- valga per ogni cosa. Dopo `intro x`, il goal riguarda la nuova `x`, mentre
-- `hIpaziaCuriosa` riguarda soltanto `ipazia`.
-- Nel goal `∀ y : Cosa, Curiosa y`, `y` è legata dal quantificatore. Dopo
-- `intro x`, `x` è la nuova variabile locale usata al posto di `y`.
--
-- Lean respingerebbe questo tentativo:
--
-- example
--     (Cosa : Type)
--     (Curiosa : Cosa → Prop)
--     (ipazia : Cosa)
--     (hIpaziaCuriosa : Curiosa ipazia) :
--     ∀ y : Cosa, Curiosa y := by
--   intro x
--   exact hIpaziaCuriosa

-- Vediamo la stessa difficoltà riutilizzando deliberatamente il nome `x`.
-- Il primo `x` è un oggetto particolare dichiarato tra i parametri. Quando
-- `intro x` introduce la cosa arbitraria del quantificatore, Lean evita la
-- collisione mostrando il vecchio oggetto come `x✝` nel tactic state:
--
-- x✝ : Cosa
-- hXCuriosa : Curiosa x✝
-- x : Cosa
-- ⊢ Curiosa x
--
-- `hXCuriosa` riguarda quindi il vecchio `x✝`, non la nuova `x` arbitraria.
-- Lean respingerebbe anche questo tentativo:
--
-- example
--     (Cosa : Type)
--     (Curiosa : Cosa → Prop)
--     (x : Cosa)
--     (hXCuriosa : Curiosa x) :
--     ∀ y : Cosa, Curiosa y := by
--   intro x
--   exact hXCuriosa


-- Eliminazione del quantificatore universale, ∀E.
-- Applichiamo una regola universale a Marta e poi usiamo l'assunzione concreta.
-- Esempio: ogni studentessa legge; Marta è studentessa; dunque Marta legge.
theorem lecture05_forall_elim
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

-- Il termine usato in ∀E può anche essere costruito da una funzione.
-- Applichiamo l'assunzione universale al termine `madreDi ipazia`.
theorem lecture05_forall_elim_function_term
    (Cosa : Type)
    (Curiosa : Cosa → Prop)
    (madreDi : Cosa → Cosa)
    (ipazia : Cosa)
    (hOgniCosaCuriosa : ∀ x : Cosa, Curiosa x) :
    Curiosa (madreDi ipazia) := by
  have hMadreDiIpaziaCuriosa := hOgniCosaCuriosa (madreDi ipazia)
  exact hMadreDiIpaziaCuriosa

-- ============================================================
-- QUANTIFICATORE ESISTENZIALE: ∃
-- ============================================================

-- Introduzione del quantificatore esistenziale, ∃I.
-- `marta : Cosa` dice che Marta è un elemento del dominio.
-- Scegliamo Marta come testimone e usiamo l'assunzione che legge.
theorem lecture05_exists_intro
    (Cosa : Type)
    (Legge : Cosa → Prop)
    (marta : Cosa)
    (hMartaLegge : Legge marta) :
    ∃ x : Cosa, Legge x := by
  apply Exists.intro marta
  exact hMartaLegge

-- Anche il testimone di ∃I può essere un termine costruito.
theorem lecture05_exists_intro_function_term
    (Cosa : Type)
    (Curiosa : Cosa → Prop)
    (madreDi : Cosa → Cosa)
    (ipazia : Cosa)
    (hMadreDiIpaziaCuriosa : Curiosa (madreDi ipazia)) :
    ∃ x : Cosa, Curiosa x := by
  apply Exists.intro (madreDi ipazia)
  exact hMadreDiIpaziaCuriosa

-- Eliminazione del quantificatore esistenziale, ∃E.
-- Apriamo l'esistenziale, usiamo il testimone senza presupporne l'identità
-- e dimostriamo una conclusione che non dipende dalla sua identità.
-- Esempio: qualcuno ha fatto una segnalazione; se qualcuno fa una
-- segnalazione, inizia un'indagine; dunque inizia un'indagine.
theorem lecture05_exists_elim
    (Cosa : Type)
    (HaFattoSegnalazione : Cosa → Prop)
    (IniziaIndagine : Prop)
    (hQualcunoHaFattoSegnalazione : ∃ x : Cosa, HaFattoSegnalazione x)
    (hChiFaSegnalazioneAvviaIndagine :
      (x : Cosa) → HaFattoSegnalazione x → IniziaIndagine) :
    IniziaIndagine := by
  apply Exists.elim hQualcunoHaFattoSegnalazione
  intro y
  intro hYHaFattoSegnalazione
  have hSeYFaSegnalazioneAlloraIniziaIndagine :=
    hChiFaSegnalazioneAvviaIndagine y
  have hIniziaIndagine :=
    hSeYFaSegnalazioneAlloraIniziaIndagine hYHaFattoSegnalazione
  exact hIniziaIndagine

-- `IniziaIndagine` è fissato prima che introduciamo il testimone locale `y`.
-- La conclusione non dipende quindi dall'identità di chi ha segnalato.

-- Esempio più complesso: combiniamo ∃E, ∀E e ∃I.
-- Qualcuna ha un ombrello; chiunque abbia un ombrello resta asciutta;
-- dunque qualcuna resta asciutta.
theorem lecture05_exists_elim_combined
    (Cosa : Type)
    (HaOmbrello RestaAsciutta : Cosa → Prop)
    (hQualcunaHaOmbrello : ∃ x : Cosa, HaOmbrello x)
    (hChiHaOmbrelloRestaAsciutta :
      ∀ x : Cosa, HaOmbrello x → RestaAsciutta x) :
    ∃ x : Cosa, RestaAsciutta x := by
  apply Exists.elim hQualcunaHaOmbrello
  intro y hYHaOmbrello
  apply Exists.intro y
  have hSeYHaOmbrelloAlloraRestaAsciutta :=
    hChiHaOmbrelloRestaAsciutta y
  have hYRestaAsciutta :=
    hSeYHaOmbrelloAlloraRestaAsciutta hYHaOmbrello
  exact hYRestaAsciutta

-- ============================================================
-- ESEMPI PIÙ COMPLESSI: REGOLE COMBINATE
-- ============================================================

-- Combiniamo ∀I, →I, ∀E e ∧I.
-- Ogni studentessa che legge prende appunti; ogni studentessa che legge
-- comprende; dunque ogni studentessa che legge prende appunti e comprende.
theorem lecture05_forall_conjunction_combined
    (Cosa : Type)
    (Studentessa Legge PrendeAppunti Comprende : Cosa → Prop)
    (hChiLeggePrendeAppunti :
      ∀ x : Cosa, Studentessa x → Legge x → PrendeAppunti x)
    (hChiLeggeComprende :
      ∀ x : Cosa, Studentessa x → Legge x → Comprende x) :
    ∀ x : Cosa,
      Studentessa x → Legge x → PrendeAppunti x ∧ Comprende x := by
  intro x
  intro hXStudentessa
  intro hXLegge
  apply And.intro
  · have hSeXStudentessaAlloraLeggeImplicaAppunti :=
      hChiLeggePrendeAppunti x
    have hSeXLeggeAlloraPrendeAppunti :=
      hSeXStudentessaAlloraLeggeImplicaAppunti hXStudentessa
    have hXPrendeAppunti := hSeXLeggeAlloraPrendeAppunti hXLegge
    exact hXPrendeAppunti
  · have hSeXStudentessaAlloraLeggeImplicaComprende :=
      hChiLeggeComprende x
    have hSeXLeggeAlloraComprende :=
      hSeXStudentessaAlloraLeggeImplicaComprende hXStudentessa
    have hXComprende := hSeXLeggeAlloraComprende hXLegge
    exact hXComprende

-- Combiniamo ∃E, ∨E, ∀E e ∃I.
-- Qualcuno visita Roma oppure Atene; chi visita una delle due città vede un
-- museo; dunque qualcuno vede un museo.
theorem lecture05_exists_or_combined
    (Cosa : Type)
    (VisitaRoma VisitaAtene VedeMuseo : Cosa → Prop)
    (hQualcunoVisitaUnaCitta :
      ∃ x : Cosa, VisitaRoma x ∨ VisitaAtene x)
    (hChiVisitaRomaVedeMuseo :
      ∀ x : Cosa, VisitaRoma x → VedeMuseo x)
    (hChiVisitaAteneVedeMuseo :
      ∀ x : Cosa, VisitaAtene x → VedeMuseo x) :
    ∃ x : Cosa, VedeMuseo x := by
  apply Exists.elim hQualcunoVisitaUnaCitta
  intro y
  intro hYVisitaRomaOVisitaAtene
  cases hYVisitaRomaOVisitaAtene with
  | inl hYVisitaRoma =>
      apply Exists.intro y
      have hSeYVisitaRomaAlloraVedeMuseo := hChiVisitaRomaVedeMuseo y
      have hYVedeMuseo := hSeYVisitaRomaAlloraVedeMuseo hYVisitaRoma
      exact hYVedeMuseo
  | inr hYVisitaAtene =>
      apply Exists.intro y
      have hSeYVisitaAteneAlloraVedeMuseo := hChiVisitaAteneVedeMuseo y
      have hYVedeMuseo := hSeYVisitaAteneAlloraVedeMuseo hYVisitaAtene
      exact hYVedeMuseo

-- Combiniamo quantificatori annidati, ∃E, ∃I e ∧I.
-- Ogni persona conosce almeno una persona; dunque, per ogni persona, esiste
-- qualcuno che essa conosce e che è una persona.
theorem lecture05_nested_quantifiers_combined
    (Cosa : Type)
    (Persona : Cosa → Prop)
    (Conosce : Cosa → Cosa → Prop)
    (hOgniPersonaConosceQualcuno :
      ∀ x : Cosa, Persona x →
        ∃ y : Cosa, Persona y ∧ Conosce x y) :
    ∀ x : Cosa, Persona x →
      ∃ y : Cosa, Conosce x y ∧ Persona y := by
  intro x
  intro hXPersona
  have hSeXPersonaAlloraConosceQualcuno :=
    hOgniPersonaConosceQualcuno x
  have hXConosceQualcuno :=
    hSeXPersonaAlloraConosceQualcuno hXPersona
  apply Exists.elim hXConosceQualcuno
  intro y
  intro hYPersonaEXConosceY
  apply Exists.intro y
  apply And.intro
  · exact hYPersonaEXConosceY.right
  · exact hYPersonaEXConosceY.left

-- Combiniamo ∃E, ∧E, ∀E e ¬E.
-- Chiunque abbia consegnato riceve una conferma; ma qualcuno ha consegnato
-- senza ricevere una conferma; dunque le assunzioni sono contraddittorie.
theorem lecture05_exists_negation_combined
    (Cosa : Type)
    (HaConsegnato HaRicevutoConferma : Cosa → Prop)
    (hChiHaConsegnatoRiceveConferma :
      ∀ x : Cosa, HaConsegnato x → HaRicevutoConferma x)
    (hControesempio :
      ∃ x : Cosa, HaConsegnato x ∧ ¬HaRicevutoConferma x) :
    False := by
  apply Exists.elim hControesempio
  intro y
  intro hYHaConsegnatoENonHaRicevutoConferma
  have hYHaConsegnato := hYHaConsegnatoENonHaRicevutoConferma.left
  have hYNonHaRicevutoConferma :=
    hYHaConsegnatoENonHaRicevutoConferma.right
  have hSeYHaConsegnatoAlloraRiceveConferma :=
    hChiHaConsegnatoRiceveConferma y
  have hYHaRicevutoConferma :=
    hSeYHaConsegnatoAlloraRiceveConferma hYHaConsegnato
  have hContraddizione :=
    hYNonHaRicevutoConferma hYHaRicevutoConferma
  exact hContraddizione

-- Combiniamo ∃E, ∀E, ↔E e ∃I.
-- Per ogni oggetto, essere un quadrato equivale ad avere quattro lati uguali;
-- esiste un quadrato; dunque esiste qualcosa con quattro lati uguali.
theorem lecture05_exists_iff_combined
    (Cosa : Type)
    (Quadrato HaQuattroLatiUguali : Cosa → Prop)
    (hEquivalenza :
      ∀ x : Cosa, Quadrato x ↔ HaQuattroLatiUguali x)
    (hEsisteQuadrato : ∃ x : Cosa, Quadrato x) :
    ∃ x : Cosa, HaQuattroLatiUguali x := by
  apply Exists.elim hEsisteQuadrato
  intro y
  intro hYQuadrato
  apply Exists.intro y
  have hEquivalenzaPerY := hEquivalenza y
  have hDirezione := Iff.mp hEquivalenzaPerY
  have hYHaQuattroLatiUguali := hDirezione hYQuadrato
  exact hYHaQuattroLatiUguali

end Course.Shared.Lecture05.IT.Classroom
