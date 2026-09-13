/-!
# Lezione 6: Tipi induttivi, ricorsione e induzione

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.IT.Classroom

-- ============================================================
-- DAI TIPI ASTRATTI AI TIPI INDUTTIVI
-- ============================================================

-- Nelle lezioni precedenti dichiaravamo `Cosa : Type`, senza specificare
-- quali valori appartenessero al tipo o come fossero costruiti.
-- Un tipo induttivo elenca invece tutti i modi in cui possiamo costruire
-- i suoi valori. Questi modi si chiamano costruttori.
inductive Semaforo where
  | rosso
  | giallo
  | verde

#check Semaforo
#check Semaforo.rosso
#check Semaforo.giallo
#check Semaforo.verde

-- Il pattern matching definisce separatamente il risultato della funzione
-- per ciascun costruttore. Qui recuperiamo anche l'idea di predicato:
-- `SiDeveFermare s` è una proposizione che dipende dal semaforo `s`.
def SiDeveFermare : Semaforo → Prop
  | .rosso => True
  | .giallo => True
  | .verde => False


-- Vogliamo dimostrare che ogni semaforo ha uno dei tre colori dichiarati.
-- `cases s` considera tutti i modi in cui `s` può essere stato costruito.
theorem lecture06_semaforo_ha_un_colore (s : Semaforo) :
    s = .rosso ∨ s = .giallo ∨ s = .verde := by
  cases s with
  | rosso =>
      apply Or.inl
      rfl
  | giallo =>
      apply Or.inr
      apply Or.inl
      rfl
  | verde =>
      apply Or.inr
      apply Or.inr
      rfl

-- ============================================================
-- COSTRUIAMO I NOSTRI NUMERI NATURALI
-- ============================================================

-- `zero` costruisce un naturale senza richiedere argomenti.
-- `succ` costruisce un nuovo naturale a partire da un naturale già costruito.
-- Non esistono altri modi di costruire un valore di tipo `Naturale`.
inductive Naturale where
  | zero
  | succ (n : Naturale)

open Naturale

-- Costruiamo i primi naturali senza usare i numerali di Lean.
def uno : Naturale := succ zero
def due : Naturale := succ uno
def tre : Naturale := succ due

#check zero
#check succ
#check uno
#check due
#check tre

-- ============================================================
-- DEFINIZIONI RICORSIVE
-- ============================================================

-- Una definizione ricorsiva segue i costruttori del dato.
-- La somma ricorre sul secondo argomento:
-- aggiungere zero non cambia il primo argomento.
-- aggiungere un successore produce il successore della somma precedente.
-- Una formulazione equivalente mette in evidenza prima il solo argomento fisso:
--
-- def somma (m : Naturale) : Naturale → Naturale
--   | zero => m
--   | succ n => succ (somma m n)
--
-- Qui preferiamo nominare subito entrambi gli argomenti e usare `match n with`
-- per mostrare separatamente che la ricorsione avviene sul secondo.
def somma (m n : Naturale) : Naturale :=
  match n with
  | zero => m
  | succ n => succ (somma m n)

-- Anche `doppio` segue i due costruttori di `Naturale`.
-- Nel secondo caso la chiamata ricorsiva usa il naturale più piccolo `n`.
def doppio (n : Naturale) : Naturale :=
  match n with
  | zero => zero
  | succ n => succ (succ (doppio n))

-- Verifichiamo due computazioni concrete.
example : somma uno uno = due := by
  rfl

example : doppio uno = due := by
  rfl

-- ============================================================
-- UGUAGLIANZA DEFINIZIONALE: RFL E UNFOLD
-- ============================================================

-- Queste uguaglianze seguono direttamente dalle equazioni con cui abbiamo
-- definito `somma` e `doppio`. Lean calcola entrambi i lati fino alla stessa
-- espressione. Per questo `rfl` è sufficiente.

theorem lecture06_somma_zero_destra (m : Naturale) :
    somma m zero = m := by
  rfl

theorem lecture06_somma_succ_destra (m n : Naturale) :
    somma m (succ n) = succ (somma m n) := by
  rfl

-- Nei primi due nomi, "destra" indica che `zero` o `succ n` compaiono come
-- secondo argomento di `somma`, cioè a destra. È proprio l'argomento analizzato
-- da `match n with`, quindi queste uguaglianze seguono subito dalla definizione.
-- Le corrispondenti proprietà con `zero` o `succ` a sinistra non si riducono
-- direttamente: le dimostreremo più avanti per induzione.

theorem lecture06_doppio_succ (n : Naturale) :
    doppio (succ n) = succ (succ (doppio n)) := by
  rfl

-- `unfold` apre esplicitamente una definizione nel goal.
-- È utile per vedere la computazione che `rfl` può eseguire automaticamente.
example : doppio uno = due := by
  unfold doppio
  unfold uno due
  rfl

-- ============================================================
-- RISCRIVERE CON UN'UGUAGLIANZA
-- ============================================================

-- Vogliamo dimostrare `somma a zero = b`, data l'assunzione `h : a = b`.
-- `rw [h]` sostituisce `a` con `b`. Poi il lato sinistro si riduce a `b`.
theorem lecture06_rw_avanti
    (a b : Naturale)
    (h : a = b) :
    somma a zero = b := by
  -- Sostituiamo `a` con `b`. Il goal diventa `somma b zero = b`.
  rw [h]
  -- La definizione di `somma` riduce ora il lato sinistro a `b`.
  rfl

-- La freccia verso sinistra usa l'uguaglianza nella direzione opposta:
-- sostituisce `b` con `a`.
theorem lecture06_rw_indietro
    (a b : Naturale)
    (h : a = b) :
    somma b zero = a := by
  -- Usiamo `h` al contrario: sostituiamo `b` con `a`.
  rw [← h]
  -- Rimane `somma a zero = a`, che segue dalla definizione.
  rfl

-- ============================================================
-- INDUZIONE
-- ============================================================

-- `somma m zero = m` si riduce perché `somma` ricorre sul secondo argomento.
-- `somma zero n = n` non può invece ridursi finché `n` è sconosciuto.
-- Dimostriamo il secondo enunciato per induzione su `n`.
--
-- Come scegliamo la variabile d'induzione?
-- 1. Guardiamo quale definizione non permette ancora di ridurre il goal: qui `somma`.
-- 2. Guardiamo quale argomento viene analizzato dai casi della definizione:
--    `somma` distingue `zero` e `succ n` nel secondo argomento.
-- 3. Facciamo induzione sulla variabile che occupa quella posizione: qui `n`.
-- Nel passo `succ`, l'ipotesi induttiva riguarderà così la chiamata
-- ricorsiva `somma zero n` che compare dopo avere aperto la definizione.
--
-- Nel caso base dimostriamo la proprietà per `zero`.
-- Nel passo induttivo `ih` assume la proprietà per `n`. Dobbiamo dimostrarla
-- per `succ n`. Usiamo esplicitamente `rw [ih]`.
theorem lecture06_zero_somma (n : Naturale) :
    somma zero n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Apriamo il caso successore: il goal contiene `somma zero n`.
      unfold somma
      -- Sostituiamo `somma zero n` con `n` usando l'ipotesi induttiva.
      rewrite [ih] -- Vediamo l'effetto esplicitamente
      rfl

-- Anche in questo goal la computazione è bloccata dal secondo argomento di
-- `somma`. Facciamo quindi induzione su `n`, non su `m`: nel passo successore
-- `ih` riguarda precisamente le due somme ricorsive con secondo argomento `n`.
theorem lecture06_succ_somma (m n : Naturale) :
    somma (succ m) n = succ (somma m n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Apriamo entrambe le somme nel caso in cui il secondo argomento
      -- sia `succ n`. Il goal interno riguarda ora il naturale più piccolo `n`.
      unfold somma
      -- `ih` sostituisce la somma con primo argomento `succ m` e secondo `n`.
      rewrite [ih] -- Osservate la differenza con: rewrite [← ih]
      rfl

-- ============================================================
-- ASSOCIATIVITÀ E COMMUTATIVITÀ
-- ============================================================

-- Associatività: raggruppare prima `a` e `b` oppure prima `b` e `c`
-- non cambia il risultato. Poiché `somma` ricorre sul secondo argomento,
-- guardiamo dove sono i secondi argomenti variabili. Scegliamo `c`: facendo
-- induzione su `c`, entrambe le espressioni esterne avanzano secondo le
-- equazioni di `somma` e `ih` coincide con l'uguaglianza rimasta all'interno.
theorem lecture06_somma_assoc (a b c : Naturale) :
    somma (somma a b) c = somma a (somma b c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      -- Riduciamo la somma esterna a sinistra nel caso `succ c`.
      rw [lecture06_somma_succ_destra]
      -- Riduciamo prima `somma b (succ c)` sul lato destro.
      rw [lecture06_somma_succ_destra]
      -- Riduciamo quindi la somma esterna ottenuta sul lato destro.
      rw [lecture06_somma_succ_destra]
      -- Abbiamo raggiunto la forma dettata dall'ipotesi induttiva.
      rw [ih]

-- Commutatività: scambiare gli argomenti non cambia la somma.
-- La definizione non tratta simmetricamente i due argomenti, quindi nel caso
-- base usiamo `zero_somma` e nel passo usiamo anche `succ_somma`.
-- Scegliamo `b` perché è il secondo argomento del lato sinistro: l'induzione
-- permette di ridurre quel lato secondo la definizione. Sul lato destro `b` è il primo argomento.
-- il lemma `succ_somma` compensa proprio questa asimmetria.
theorem lecture06_somma_comm (a b : Naturale) :
    somma a b = somma b a := by
  induction b with
  | zero =>
      -- A sinistra `somma a zero` si riduce a `a`. A destra dobbiamo spostare
      -- `zero` dalla prima posizione usando il lemma già dimostrato.
      rw [lecture06_zero_somma]
      rfl
  | succ b ih =>
      -- Il lato sinistro si riduce perché `succ b` è il secondo argomento.
      rw [lecture06_somma_succ_destra]
      -- Sul lato destro `succ b` è il primo argomento: usiamo `succ_somma`
      -- per portare `succ` all'esterno della somma.
      rw [lecture06_succ_somma]
      -- I due lati hanno ora lo stesso `succ`. All'interno resta il caso `b`.
      rw [ih]

-- ============================================================
-- IL SEMPLIFICATORE
-- ============================================================

-- `simp` applica automaticamente equazioni orientate verso forme più semplici.
-- Partiamo da una prova già compresa e confrontiamo tre livelli di controllo.

-- 1. Con `rw` scegliamo esplicitamente ogni riscrittura.
theorem lecture06_zero_somma_con_rw (n : Naturale) : somma zero n = n := by
  rw [lecture06_zero_somma]

-- 2. `simp only` usa soltanto le regole elencate.
theorem lecture06_zero_somma_con_simp_only (n : Naturale) : somma zero n = n := by
  simp only [lecture06_zero_somma]

-- 3. `simp [lemma]` aggiunge la regola indicata al simp-set per questo comando.
theorem lecture06_zero_somma_con_simp (n : Naturale) : somma zero n = n := by
  simp [lecture06_zero_somma]

-- Possiamo aggiungere lemmi al simp-set soltanto dentro una sezione.
-- Fuori dalla sezione l'attributo locale non ha effetto.
section SemplificazioneLocale

attribute [local simp] lecture06_zero_somma lecture06_succ_somma

theorem lecture06_succ_somma_con_simp (m n : Naturale) :
    somma (succ m) n = succ (somma m n) := by
  simp

end SemplificazioneLocale

-- `@[simp]` registra invece una regola per tutto il modulo successivo.
-- Lo usiamo solo per un'equazione canonica che riduce chiaramente il termine.
@[simp] theorem lecture06_doppio_zero :
    doppio zero = zero := by
  rfl

-- Non registriamo associatività e commutatività come regole `simp`.
-- In `somma a b = somma b a` i due lati hanno la stessa complessità: la regola
-- scambia soltanto gli argomenti. Anche l'associatività sposta le parentesi
-- senza eliminare alcuna operazione. Queste uguaglianze non indicano quindi
-- una forma evidentemente più semplice verso cui normalizzare ogni espressione.
-- Quando servono, le usiamo esplicitamente con `rw` nella direzione desiderata.

-- ============================================================
-- PROVA CONCLUSIVA
-- ============================================================

-- Esercizio: il doppio di una somma è la somma dei doppi.
-- Su quale variabile conviene fare induzione? Quali equazioni servono?
-- La riduzione di `somma m n` dipende da `n`, quindi scegliamo `n`. Nel passo
-- successore otteniamo l'ipotesi induttiva per `somma m n`, cioè per la
-- stessa chiamata ricorsiva che emerge dopo avere riscritto il goal.
theorem lecture06_doppio_somma (m n : Naturale) :
    doppio (somma m n) = somma (doppio m) (doppio n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Riduciamo `somma m (succ n)` sul lato sinistro.
      rw [lecture06_somma_succ_destra]
      -- Apriamo il doppio del successore appena ottenuto.
      rw [lecture06_doppio_succ]
      -- Apriamo anche `doppio (succ n)` sul lato destro.
      rw [lecture06_doppio_succ]
      -- Le due riscritture successive fanno attraversare alla somma i due
      -- costruttori `succ` prodotti dal doppio.
      rw [lecture06_somma_succ_destra]
      rw [lecture06_somma_succ_destra]
      -- Sotto i due successori rimane precisamente il caso induttivo per `n`.
      rw [ih]

-- La stessa dimostrazione, dopo avere compreso i passaggi, può essere abbreviata.
theorem lecture06_doppio_somma_breve (m n : Naturale) :
    doppio (somma m n) = somma (doppio m) (doppio n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [lecture06_somma_succ_destra, lecture06_doppio_succ, ih]

end Course.Shared.Lecture06.IT.Classroom
