# LEXLOG — Język Prawdy v0.1

+-------------------------------------------------------------+
|              CERTEUS - Język LEXLOG v0.1                    |
+-------------------------------------------------------------+
| PLIK: LEXLOG.md                                             |
| ROLA/ROLE: Specyfikacja języka dziedzinowego (DSL) do       |
|            formalizacji reguł i faktów prawnych.            |
+-------------------------------------------------------------+

## LEXLOG — A Language for Formalizing Legal Logic

## 1. Wprowadzenie / Introduction

PL: **LEXLOG** to precyzyjny, deklaratywny język do opisu logiki prawnej w sposób zrozumiały dla solverów SMT. Celem jest eliminacja niejednoznaczności i zapewnienie weryfikowalności rozumowania.
EN: **LEXLOG** is a precise, declarative language to describe legal logic in a machine-understandable way for SMT solvers. The goal is to eliminate ambiguity and ensure verifiable reasoning.

## 2. Podstawowe Konstrukcje (v0.1) / Basic Constructs (v0.1)

### Definicja (DEFINE)

PL: Definiuje stałe/zmienne logiczne reprezentujące kluczowe pojęcia.
EN: Defines logical constants/variables representing key concepts.

```lexlog
DEFINE czyn_ma_charakter_oszukanczy: Bool
DEFINE kwota_szkody: Real
```

### Przesłanka (PREMISE)

PL: Warunek, który musi być spełniony. Może odwoływać się do faktów z FACTLOG.
EN: A condition that must be met. May refer to facts from FACTLOG.

```lexlog
PREMISE P1: "Wprowadzenie w błąd"
    EXISTS (fact: FACTLOG WHERE role = 'introduction_into_error')
```

### Reguła (RULE)

PL: Łączy przesłanki w implikację prowadzącą do konkluzji.
EN: Combines premises into an implication leading to a conclusion.

```lexlog
RULE R_OSZUSTWO (P1, P2, P3) -> K1
```

### Konkluzja (CONCLUSION)

PL: Logiczny wniosek wynikający z reguły.
EN: Logical conclusion resulting from a rule.

```lexlog
CONCLUSION K1: "Czyn wypełnia znamiona oszustwa z art. 286 k.k."
    ASSERT (czyn_ma_charakter_oszukanczy == True)
```

## 3. Przykład dla Art. 286 k.k. (MVP) / Example for Art. 286 (MVP)

```lexlog
# --- Definicje dla Art. 286 k.k. ---
DEFINE cel_korzysci_majatkowej: Bool
DEFINE wprowadzenie_w_blad: Bool
DEFINE niekorzystne_rozporzadzenie_mieniem: Bool

# --- Przesłanki ---
PREMISE P_CEL: "Sprawca działał w celu osiągnięcia korzyści majątkowej"
    EXISTS (fact: FACTLOG WHERE role = 'intent_financial_gain')

PREMISE P_WPROWADZENIE: "Sprawca wprowadził ofiarę w błąd"
    EXISTS (fact: FACTLOG WHERE role = 'act_deception')

PREMISE P_ROZPORZADZENIE: "Nastąpiło niekorzystne rozporządzenie mieniem"
    EXISTS (fact: FACTLOG WHERE role = 'detrimental_property_disposal')

# --- Główna reguła ---
RULE R_286_OSZUSTWO (P_CEL, P_WPROWADZENIE, P_ROZPORZADZENIE) -> K_OSZUSTWO_STWIERDZONE

# --- Konkluzja ---
CONCLUSION K_OSZUSTWO_STWIERDZONE: "Czyn wypełnia znamiona z art. 286 k.k."
    ASSERT (cel_korzysci_majatkowej AND wprowadzenie_w_blad AND niekorzystne_rozporzadzenie_mieniem)
```

## 4. Konwencje / Conventions

- ID przesłanek: `P_*`, konkluzje: `K_*`.
- Aliasowanie do silników (MAPS_TO) jest opcjonalne w DSL — twarde mapowanie trzymamy w JSON `kk.mapping.json`.
- Dwujęzyczne komentarze i nagłówki ASCII zgodnie z „Standard Kodowania – Premium Code Style” (README).
