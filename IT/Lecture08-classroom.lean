/-!
# Lezione 8: Verifica del software, automazione e LLM in Lean

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture08.IT.Classroom

-- ============================================================
-- ALTRE FORME DI AUTOMAZIONE
-- ============================================================

-- Le varianti con ? mostrano nell'Infoview un comando suggerito.

-- Vogliamo concludere a < c dalle assunzioni a < b e b < c.
-- exact? cerca nella libreria e prova a ricostruire gli argomenti necessari.
example (a b c : Nat) (hAB : a < b) (hBC : b < c) : a < c := by
  exact?

-- apply? cerca un'applicazione e prova a risolverne le premesse.
-- Può chiudere tutto oppure lasciare nuovi goal. Qui chiude tutto.
-- Vogliamo costruire una congiunzione da due assunzioni e un'implicazione.
example (P Q R : Prop) (hP : P) (hQ : Q) (hQR : Q → R) : P ∧ R := by
  apply?

-- Vogliamo P ∧ (Q ∨ R), sapendo che P e Q sono vere.
-- simp? usa queste assunzioni per semplificare i connettivi e propone
-- le regole sufficienti.
example (P Q R : Prop) (hP : P) (hQ : Q) : P ∧ (Q ∨ R) := by
  simp? [hP, hQ]

-- Vogliamo Q da P ∨ Q, P → R e ¬R.
-- grind? combina le informazioni: il caso P porta a contraddizione.
-- Il suggerimento `grind only` usa hPQ, hPR e hNotR direttamente dal goal.
-- Non servono teoremi aggiuntivi: grind distingue i casi di hPQ e combina
-- l'implicazione hPR con hNotR.
-- In `simp only [lemma]`, invece, fornivamo una regola per semplificare:
-- senza quel lemma, simp only non conosce automaticamente la proprietà
-- della funzione che avevamo dimostrato.
example (P Q R : Prop) (hPQ : P ∨ Q) (hPR : P → R) (hNotR : ¬R) : Q := by
  grind?

-- ============================================================
-- LISTE, POLIMORFISMO E VERIFICA DEL SOFTWARE
-- ============================================================

-- Nella Lezione 7 abbiamo introdotto brevemente le liste come tipo induttivo.
-- Ripartiamo ora da quella definizione per studiarla più a fondo.
-- Un test esegue il programma su input scelti e può mostrare un errore.
-- Una verifica formale enuncia una proprietà e la dimostra per tutti gli input
-- compresi nell'enunciato. I due strumenti rispondono quindi a domande diverse.
-- `α` rappresenta il tipo degli elementi. La stessa definizione costruisce
-- liste di naturali, stringhe o altri tipi. Questo riuso della stessa struttura
-- per tipi diversi si chiama polimorfismo parametrico.
inductive Lista (α : Type) where
  | vuota
  | cons (testa : α) (coda : Lista α)

open Lista

-- Una lista è vuota oppure è costruita aggiungendo un elemento davanti a una
-- lista più piccola. Questo esempio contiene tre stringhe.
def listaEsempio : Lista String :=
  cons "Ada" (cons "Ipazia" (cons "Eva" vuota))

-- Per rovesciare una lista ci serve concatenarne due. La definizione analizza
-- la prima lista: trasferisce un elemento alla volta davanti al risultato.
-- Le parentesi graffe in `{α : Type}` rendono `α` implicito: Lean lo ricava
-- dal tipo delle liste `xs` e `ys`, quindi scriviamo `concatena xs ys`.
def concatena {α : Type} (xs ys : Lista α) : Lista α :=
  match xs with
  | vuota => ys
  | cons x xs => cons x (concatena xs ys)

-- L'algoritmo ricorsivo lascia invariata la lista vuota. Nel caso `cons`,
-- rovescia prima la coda e colloca la testa in fondo al risultato.
def rovescia {α : Type} (xs : Lista α) : Lista α :=
  match xs with
  | vuota => vuota
  | cons x xs => concatena (rovescia xs) (cons x vuota)

-- Vogliamo dimostrare la proprietà seguente per ogni lista `xs`:
--
--   rovescia (rovescia xs) = xs
--
-- Questa è una proprietà importante, ma non caratterizza da sola l'algoritmo.
-- Anche la funzione identità soddisferebbe la stessa equazione.
--
-- Prima della proprietà finale dimostriamo alcuni lemmi che ci saranno utili:
-- la concatenazione con la lista vuota, l'associatività della concatenazione
-- e il comportamento di `rovescia` su una concatenazione.

-- Anche in un teorema, `{α : Type}` è un parametro implicito: il risultato
-- vale per ogni tipo di elementi. Quando usiamo il teorema su una lista `xs`,
-- Lean ricava `α` dal tipo di `xs`. Non è un'assunzione da dimostrare.
-- `concatena` analizza il primo argomento, quindi facciamo induzione su `xs`.
theorem lecture08_concatena_vuota_destra
    {α : Type} (xs : Lista α) :
    concatena xs vuota = xs := by
  induction xs with
  | vuota =>
      rfl
  | cons x xs ih =>
      simp [concatena, ih]

-- Questa uguaglianza elimina una concatenazione con la lista vuota e conduce
-- a una forma più semplice. La aggiungiamo quindi al simp-set locale.
attribute [local simp] lecture08_concatena_vuota_destra

-- Cambiare il raggruppamento di tre concatenazioni non cambia la lista.
-- Anche qui l'argomento che guida la computazione è `xs`.
theorem lecture08_concatena_assoc
    {α : Type} (xs ys zs : Lista α) :
    concatena (concatena xs ys) zs =
      concatena xs (concatena ys zs) := by
  induction xs with
  | vuota =>
      rfl
  | cons x xs ih =>
      simp [concatena, ih]

-- Non aggiungiamo l'associatività al simp-set. Cambia il raggruppamento, ma non
-- indica in generale una forma più semplice. Quando serve, la nominiamo.

-- Possiamo ora dimostrare che rovesciare una concatenazione scambia l'ordine
-- delle due parti.
theorem lecture08_rovescia_concatena
    {α : Type} (xs ys : Lista α) :
    rovescia (concatena xs ys) =
      concatena (rovescia ys) (rovescia xs) := by
  induction xs with
  | vuota =>
      simp [concatena, rovescia]
  | cons x xs ih =>
      -- Le definizioni e `ih` lasciano le stesse tre liste raggruppate in modo
      -- diverso sui due lati. Il goal rimasto mostra che serve l'associatività.
      -- La nominiamo qui, senza aggiungerla al simp-set.
      simp [concatena, rovescia, ih, lecture08_concatena_assoc]

-- Questa uguaglianza descrive la forma attesa del rovesciamento di una
-- concatenazione. La rendiamo disponibile a `simp` dentro questa sezione.
attribute [local simp] lecture08_rovescia_concatena

-- Proprietà di correttezza: rovesciare due volte restituisce la lista iniziale.
-- Non controlliamo soltanto alcuni esempi. La dimostrazione copre ogni lista,
-- perché segue i due modi in cui una `Lista α` può essere costruita.
theorem lecture08_rovescia_rovescia
    {α : Type} (xs : Lista α) :
    rovescia (rovescia xs) = xs := by
  induction xs with
  | vuota =>
      simp [rovescia]
  | cons x xs ih =>
      simp [rovescia, ih, concatena]


-- ============================================================
-- ALTRA AUTOMAZIONE: DECIDE E OMEGA
-- ============================================================

-- Da qui usiamo i naturali Nat e le liste List della libreria standard.
-- [2, 4, 6] è la sintassi Lean per una List Nat, diversa dalla nostra Lista.
-- Vogliamo verificare una concatenazione concreta e una disuguaglianza.
-- decide prova a verificare l'enunciato mediante un calcolo. Qui calcola la
-- concatenazione, confronta le liste e verifica che 7 < 10. Entrambi i
-- controlli danno esito positivo, quindi Lean chiude il goal.
-- Non ogni enunciato si risolve così: con variabili, il calcolo può bloccarsi.
example : ([2, 4] ++ [6] : List Nat) = [2, 4, 6] ∧ (7 : Nat) < 10 := by
  decide

-- Eva ha almeno 18 anni e Marta ha tre anni più di Eva.
-- Vogliamo dimostrare che Marta ha almeno 21 anni.
-- omega tratta l'aritmetica lineare (ovvero, uguaglianze e disuguaglianze
-- con somme e prodotti per costanti, senza prodotti fra due variabili).
example (etaEva etaMarta : Nat)
    (hDifferenza : etaEva + 3 = etaMarta) (hEta : 18 ≤ etaEva) :
    21 ≤ etaMarta := by
  omega

-- omega non è un solver generale per prodotti come x * y, con entrambi
-- i fattori variabili.

-- ============================================================
-- UN LLM COME ASSISTENTE PER LEAN
-- ============================================================

-- Obiettivo: se due liste rovesciate sono uguali, anche le liste originali
-- sono uguali. Questa è la dimostrazione prodotta da un LLM:
theorem lecture08_rovescia_iniettiva {α : Type} (xs ys : Lista α)
    (h : rovescia xs = rovescia ys) : xs = ys := by
  -- Riscriviamo xs come il suo doppio rovesciamento.
  rw [← lecture08_rovescia_rovescia xs]
  -- Usiamo h per sostituire rovescia xs con rovescia ys.
  rw [h]
  -- Il doppio rovesciamento di ys restituisce ys.
  rw [lecture08_rovescia_rovescia ys]


-- Controlliamo le dipendenze della dimostrazione. sorry introdurrebbe sorryAx.
-- Qui compare propext, l'assioma standard secondo cui due proposizioni
-- equivalenti (P ↔ Q) possono essere considerate uguali (P = Q).
-- La dipendenza viene dai lemmi precedenti dimostrati con simp: per esempio,
-- simp usa eq_self per sostituire la proposizione `t = t` con `True`.
-- Questa sostituzione usa propext. Il teorema finale eredita la dipendenza
-- perché usa lecture08_rovescia_rovescia, anche se qui scriviamo soltanto rw.
#print axioms lecture08_rovescia_iniettiva

end Course.Shared.Lecture08.IT.Classroom
